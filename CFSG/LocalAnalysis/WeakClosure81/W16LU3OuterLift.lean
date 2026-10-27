module

public import CFSG.RankThree.OddKernel.OddLift
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.BorelTits.Basic
public import CFSG.Quasithin.Background.CharTwoLocal

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open Subgroup

private lemma w16l_alpha_mem_center {X : Type*} [Group X] (α : MulAut X) (hα : α * α = 1)
    (z : X) : α z ∈ Subgroup.center X ↔ z ∈ Subgroup.center X := by
  have hαα : ∀ x : X, α (α x) = x := fun x => by
    rw [← MulAut.mul_apply, hα, MulAut.one_apply]
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h g
    obtain ⟨g', rfl⟩ := α.surjective g
    have h2 := congrArg α (h g')
    rw [map_mul, map_mul, hαα] at h2
    exact h2
  · intro h g
    have h2 := congrArg α (h (α g))
    rw [map_mul, map_mul, hαα] at h2
    exact h2

private lemma w16l_center_mul_inv {X : Type*} [Group X] {z a b : X}
    (hz : z ∈ Subgroup.center X) :
    (a * z⁻¹) * (b * z⁻¹) = a * b * (z⁻¹ * z⁻¹) := by
  have hz' : ∀ g : X, z⁻¹ * g = g * z⁻¹ := fun g =>
    (Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hz) g).symm
  calc (a * z⁻¹) * (b * z⁻¹)
      = a * (z⁻¹ * b) * z⁻¹ := by group
    _ = a * (b * z⁻¹) * z⁻¹ := by rw [hz' b]
    _ = a * b * (z⁻¹ * z⁻¹) := by group

private lemma w16l_pow_mul_mem {X : Type*} [Group X] {C Qh : Subgroup X}
    (hCN : C ≤ Subgroup.normalizer (Qh : Set X)) (d : X) (hdC : d ∈ C)
    (α : MulAut X) (he : α d * d ∈ Qh) :
    ∀ n : ℕ, α (d ^ n) * d ^ n ∈ Qh := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hdn : d ^ n ∈ C := Subgroup.pow_mem _ hdC n
    have hconj : (d ^ n)⁻¹ * (α d * d) * d ^ n ∈ Qh := by
      have hmem : (d ^ n)⁻¹ ∈ Subgroup.normalizer (Qh : Set X) :=
        hCN (Subgroup.inv_mem _ hdn)
      have hiff := Subgroup.mem_normalizer_iff.mp hmem (α d * d)
      rw [inv_inv] at hiff
      exact hiff.mp he
    have hEq : α (d ^ (n + 1)) * d ^ (n + 1)
        = (α (d ^ n) * d ^ n) * ((d ^ n)⁻¹ * (α d * d) * d ^ n) := by
      rw [pow_succ, map_mul]
      rw [show d ^ n * d = d * d ^ n by rw [← pow_succ, ← pow_succ']]
      group
    rw [hEq]
    exact Subgroup.mul_mem _ ih hconj

theorem w16l_exists_odd_subgroup_inverted {X : Type} [Group X] [Finite X] (Y : Subgroup X)
    (α : MulAut X) (hα : α * α = 1) (hαY : ∀ y ∈ Y, α y = y) {Qh : Subgroup X}
    (hQh : IsPGroup 2 Qh) (hZ : Odd (Nat.card (Subgroup.center X)))
    (hQC : Qh ≤ Subgroup.centralizer (Y : Set X))
    (hCN : Subgroup.centralizer (Y : Set X) ≤ Subgroup.normalizer (Qh : Set X))
    (hαQ : ∀ q ∈ Qh, α q ∈ Qh) {c : X} (hc : c ∈ Subgroup.centralizer (Y : Set X))
    (hco : Odd (orderOf c)) (hcZ : c ∉ Subgroup.center X)
    (hθ : ∃ q ∈ Qh, ∃ z ∈ Subgroup.center X, α c * c = q * z) :
    ∃ X₀ : Subgroup X, X₀ ≤ Subgroup.centralizer (Y : Set X) ∧ Odd (Nat.card X₀) ∧
      ¬ X₀ ≤ Subgroup.center X ∧
        ∀ g ∈ X₀, α g * g ∈ pCoreOf 2 (Subgroup.centralizer (Y : Set X)) := by
  classical
  have hαα : ∀ x : X, α (α x) = x := fun x => by
    rw [← MulAut.mul_apply, hα, MulAut.one_apply]
  obtain ⟨q, hq, z, hz, heq⟩ := hθ
  have hz_alpha : α z = z := by
    have h1 : c * α c = α q * α z := by
      have h := congrArg α heq
      rw [map_mul, map_mul, hαα] at h
      exact h
    have h2 : c * α c = (c * q * c⁻¹) * z := by
      calc c * α c = c * (α c * c) * c⁻¹ := by group
        _ = c * (q * z) * c⁻¹ := by rw [heq]
        _ = (c * q * c⁻¹) * z := by
              rw [show c * (q * z) * c⁻¹ = c * q * (z * c⁻¹) by group,
                show z * c⁻¹ = c⁻¹ * z by
                  exact (Subgroup.mem_center_iff.mp hz c⁻¹).symm]
              group
    have h3 : (c * q * c⁻¹) * z = α q * α z := h2.symm.trans h1
    have hmemQ : z * (α z)⁻¹ ∈ Qh := by
      have hz_inv : z * (α z)⁻¹ = (c * q * c⁻¹)⁻¹ * α q := by
        have hA : (c * q * c⁻¹) * (z * (α z)⁻¹) = α q := by
          rw [← mul_assoc, h3]; group
        rw [← hA]; group
      rw [hz_inv]
      exact Subgroup.mul_mem _
        (Subgroup.inv_mem _ ((Subgroup.mem_normalizer_iff.mp (hCN hc) q).mp hq))
        (hαQ q hq)
    have hmemZ : z * (α z)⁻¹ ∈ Subgroup.center X :=
      Subgroup.mul_mem _ hz (Subgroup.inv_mem _ ((w16l_alpha_mem_center α hα z).mpr hz))
    have hbot : Qh ⊓ Subgroup.center X = ⊥ :=
      CFSG.RankThree.OddKernel.inf_eq_bot_of_odd hQh hZ
    have h1 : z * (α z)⁻¹ = 1 := by
      have hmem : z * (α z)⁻¹ ∈ Qh ⊓ Subgroup.center X := ⟨hmemQ, hmemZ⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    have hz_eq : z = α z := by simpa using (mul_eq_one_iff_eq_inv.mp h1)
    exact hz_eq.symm
  set d : X := c * c * z⁻¹ with hd
  have hzC : z ∈ Subgroup.centralizer (Y : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h _
    exact Subgroup.mem_center_iff.mp hz h
  have hdC : d ∈ Subgroup.centralizer (Y : Set X) := by
    rw [hd]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hc) (Subgroup.inv_mem _ hzC)
  have hz_comm : ∀ g : X, z * g = g * z := fun g =>
    (Subgroup.mem_center_iff.mp hz g).symm
  have he : α d * d = q * (c⁻¹ * q * c) := by
    have hAd : α d * d = (α c * α c) * (c * c) * (z⁻¹ * z⁻¹) := by
      rw [hd, map_mul, map_mul, map_inv, hz_alpha]
      exact w16l_center_mul_inv hz
    have hfour : (α c * α c) * (c * c) = (α c * c) * (c⁻¹ * q * c) * z := by
      rw [show (α c * α c) * (c * c) = α c * (α c * c) * c by group]
      nth_rewrite 1 [heq]
      rw [show α c * (q * z) * c = α c * q * (z * c) by group, hz_comm c]
      group
    rw [hAd, hfour, heq]
    rw [show ((q * z) * (c⁻¹ * q * c) * z) * (z⁻¹ * z⁻¹)
          = q * (z * (c⁻¹ * q * c)) * z⁻¹ by group]
    rw [hz_comm (c⁻¹ * q * c)]
    group
  have hc_qc : c⁻¹ * q * c ∈ Qh := by
    have hc' : c⁻¹ ∈ Subgroup.centralizer (Y : Set X) := Subgroup.inv_mem _ hc
    have hmem := (Subgroup.mem_normalizer_iff.mp (hCN hc') q).mp hq
    rwa [inv_inv] at hmem
  have he_mem : α d * d ∈ Qh := by
    rw [he]
    exact Subgroup.mul_mem _ hq hc_qc
  have hd_odd : Odd (orderOf d) := by
    have hcomm : Commute (c * c) z⁻¹ :=
      Commute.inv_right (show Commute (c * c) z from Subgroup.mem_center_iff.mp hz (c * c))
    have hdvd : orderOf d ∣ orderOf (c * c) * orderOf (z⁻¹) := by
      rw [hd]
      exact hcomm.orderOf_mul_dvd_mul_orderOf
    have h2odd : Odd (orderOf (c * c)) := by
      rw [← pow_two]
      exact Odd.of_dvd_nat hco (orderOf_pow_dvd (x := c) 2)
    have hzinv_odd : Odd (orderOf (z⁻¹)) := by
      rw [orderOf_inv]
      exact Odd.of_dvd_nat hZ (Subgroup.orderOf_dvd_natCard (Subgroup.center X) hz)
    exact Odd.of_dvd_nat (h2odd.mul hzinv_odd) hdvd
  have hd_notZ : d ∉ Subgroup.center X := by
    intro hdZ
    have hc2Z : c * c ∈ Subgroup.center X := by
      have hmem : d * z ∈ Subgroup.center X := Subgroup.mul_mem _ hdZ hz
      rwa [show d * z = c * c by rw [hd]; group] at hmem
    obtain ⟨m, hm⟩ := hco
    have hc_eq : c = (c * c) ^ (m + 1) := by
      have h1 : c ^ (orderOf c + 1) = c := by
        rw [pow_succ, pow_orderOf_eq_one, one_mul]
      rw [hm] at h1
      have h2 : 2 * m + 1 + 1 = 2 * (m + 1) := by ring
      rw [h2, pow_mul, pow_two] at h1
      exact h1.symm
    refine hcZ ?_
    rw [hc_eq]
    exact Subgroup.pow_mem _ hc2Z (m + 1)
  have hQh_le : Qh ≤ pCoreOf 2 (Subgroup.centralizer (Y : Set X)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQC hCN hQh
  refine ⟨Subgroup.zpowers d, Subgroup.zpowers_le.mpr hdC, ?_, ?_, ?_⟩
  · rw [Nat.card_zpowers]
    exact hd_odd
  · intro hsub
    exact hd_notZ (hsub (Subgroup.mem_zpowers d))
  · intro g hg
    have hQg : α g * g ∈ Qh := by
      rw [mem_zpowers_iff_mem_range_orderOf] at hg
      obtain ⟨n, _, hn⟩ := Finset.mem_image.mp hg
      have h := w16l_pow_mul_mem hCN d hdC α he_mem n
      rwa [hn] at h
    exact hQh_le hQg

end CFSG.LocalAnalysis.WeakClosure81

end
