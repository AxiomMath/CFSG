module

import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.StandardType.FrameRoute.FS81

theorem exists_normal_complement_of_central_hall {X : Type} [Group X] [Finite X] {M N : Subgroup X}
    (hNM : N ≤ M) (hNc : ∀ n ∈ N, ∀ g ∈ M, g * n = n * g) {m : ℕ}
    (hm : Nat.card M = Nat.card N * m) (hcop : Nat.Coprime (Nat.card N) m) :
    ∃ K : Subgroup X, K ≤ M ∧ (K.subgroupOf M).Normal ∧ Nat.card K = m ∧ M ≤ K ⊔ N ∧
      ∀ g ∈ M, g ∈ K ↔ Nat.Coprime (orderOf g) (Nat.card N) := by
  let N' : Subgroup ↥M := N.subgroupOf M
  have hmap : N'.map M.subtype = N := by
    show (N.subgroupOf M).map M.subtype = N
    rw [Subgroup.subgroupOf_map_subtype N M, inf_of_le_left hNM]
  have hN'card : Nat.card N' = Nat.card N := by
    rw [← hmap, Subgroup.card_map_of_injective M.subtype_injective]
  have hN'normal : N'.Normal := ⟨fun n hn g => by
    have h1 : (g : X) * (n : X) = (n : X) * (g : X) := hNc (n : X) hn (g : X) g.2
    show ((g * n * g⁻¹ : ↥M) : X) ∈ N
    rw [show ((g * n * g⁻¹ : ↥M) : X) = (n : X) from by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, h1, mul_inv_cancel_right]]
    exact hn⟩
  have : N'.Normal := hN'normal
  have hN'index : N'.index = m := by
    have h := Subgroup.card_mul_index N'
    rw [hN'card] at h
    rw [hm] at h
    exact Nat.mul_left_cancel Nat.card_pos h
  have hcop' : Nat.Coprime (Nat.card N') N'.index := by
    rw [hN'card, hN'index]
    exact hcop
  obtain ⟨H', hH'⟩ := Subgroup.exists_right_complement'_of_coprime hcop'
  let K : Subgroup X := H'.map M.subtype
  have hKle : K ≤ M := Subgroup.map_subtype_le H'
  have hKcard : Nat.card K = m := by
    have hmapcard : Nat.card K = Nat.card H' :=
      Subgroup.card_map_of_injective M.subtype_injective
    have h := hH'.card_mul_card
    rw [hN'card, hm] at h
    rw [hmapcard]
    exact Nat.mul_left_cancel Nat.card_pos h
  have hKsub : K.subgroupOf M = H' := by
    change Subgroup.comap M.subtype (Subgroup.map M.subtype H') = H'
    exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective H'
  have hH'normal : H'.Normal := ⟨fun k hk g => by
    have hmem : g ∈ N' ⊔ H' := by
      rw [hH'.sup_eq_top]
      exact Subgroup.mem_top g
    rw [Subgroup.mem_sup_of_normal_left] at hmem
    obtain ⟨n, hn, h, hh, rfl⟩ := hmem
    have hcent : ∀ x : ↥M, n * x = x * n := by
      intro x
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact (hNc (n : X) hn (x : X) x.2).symm
    have hconj : n * (h * k * h⁻¹) * n⁻¹ = h * k * h⁻¹ := by
      rw [hcent (h * k * h⁻¹), mul_inv_cancel_right]
    have hgroup : (n * h) * k * (n * h)⁻¹ = n * (h * k * h⁻¹) * n⁻¹ := by
      rw [mul_inv_rev]
      simp only [mul_assoc]
    rw [hgroup, hconj]
    exact H'.mul_mem (H'.mul_mem hh hk) (H'.inv_mem hh)⟩
  have hKnormal : (K.subgroupOf M).Normal := by
    rw [hKsub]
    exact hH'normal
  have hsupEq : N ⊔ K = M := by
    have h := congrArg (Subgroup.map M.subtype) hH'.sup_eq_top
    rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype, hmap] at h
    exact h
  refine ⟨K, hKle, hKnormal, hKcard, ?_, ?_⟩
  · exact le_of_eq (by rw [← hsupEq, sup_comm])
  · intro g hg
    constructor
    · intro hgK
      have hdvd : orderOf g ∣ m := by
        have h := Subgroup.orderOf_dvd_natCard K hgK
        rwa [hKcard] at h
      exact (hcop.coprime_dvd_right hdvd).symm
    · intro hgcop
      have : (K.subgroupOf M).Normal := hKnormal
      have hgmem : (⟨g, hg⟩ : ↥M) ∈ N' ⊔ K.subgroupOf M := by
        rw [hKsub, hH'.sup_eq_top]
        exact Subgroup.mem_top _
      rw [Subgroup.mem_sup_of_normal_right] at hgmem
      obtain ⟨n, hn, k, hk, hnk⟩ := hgmem
      have hnN : (n : X) ∈ N := hn
      have hkK : (k : X) ∈ K := hk
      have hgnk : (n : X) * (k : X) = g := by
        have h := congrArg (fun x : ↥M => (x : X)) hnk
        rw [Subgroup.coe_mul] at h
        simpa using h
      have hcomm : Commute (n : X) (k : X) :=
        (hNc (n : X) hn (k : X) k.2).symm
      have hpow : ((n : X) * (k : X)) ^ orderOf g = 1 := by
        rw [hgnk, pow_orderOf_eq_one]
      have hmul : (n : X) ^ orderOf g * (k : X) ^ orderOf g = 1 := by
        rw [← hcomm.mul_pow (orderOf g)]
        exact hpow
      have hnpowK : (n : X) ^ orderOf g ∈ K := by
        have hkeq : (n : X) ^ orderOf g = ((k : X) ^ orderOf g)⁻¹ :=
          eq_inv_of_mul_eq_one_left hmul
        rw [hkeq]
        exact K.inv_mem (K.pow_mem hkK (orderOf g))
      have hnpowN : (n : X) ^ orderOf g ∈ N := N.pow_mem hnN (orderOf g)
      have hbot : N ⊓ K = ⊥ := by
        apply le_antisymm
        · intro x hx
          rw [Subgroup.mem_bot]
          have h1 : orderOf x ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hx.1
          have h2 : orderOf x ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hx.2
          rw [hKcard] at h2
          exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
        · exact bot_le
      have hnpow1 : (n : X) ^ orderOf g = 1 := by
        have hmem : (n : X) ^ orderOf g ∈ N ⊓ K := ⟨hnpowN, hnpowK⟩
        rw [hbot] at hmem
        simpa using hmem
      have horder : orderOf (n : X) = 1 := by
        have hdvde : orderOf (n : X) ∣ orderOf g :=
          orderOf_dvd_iff_pow_eq_one.mpr hnpow1
        have hdvdN : orderOf (n : X) ∣ Nat.card N :=
          Subgroup.orderOf_dvd_natCard N hnN
        exact Nat.eq_one_of_dvd_coprimes hgcop.symm hdvdN hdvde
      have hn1 : (n : X) = 1 := orderOf_eq_one_iff.mp horder
      rw [← hgnk, hn1, one_mul]
      exact hkK

end CFSG.StandardType.FrameRoute.FS81

end
