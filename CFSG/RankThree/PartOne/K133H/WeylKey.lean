module

public import CFSG.RankThree.PartOne.K133H.TorusImage
public import CFSG.RankThree.Chevalley.G2SplitPrimeToralCentralizers

public noncomputable section

namespace CFSG.RankThree.PartOne.K133H

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne

theorem eq_one_or_three_of_dvd_orderOf {X : Type*} [Group X] [Finite X]
    (hX : ∀ x : X, Odd (orderOf x) → orderOf x = 1 ∨ orderOf x = 3) (x : X) {r : ℕ}
    (hr : Odd r) (hrx : r ∣ orderOf x) : r = 1 ∨ r = 3 := by
  have hx0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨a, m, hm, hxm⟩ := Nat.exists_eq_two_pow_mul_odd hx0
  have hy : orderOf (x ^ (2 ^ a)) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (hxm ▸ dvd_mul_right _ _), hxm,
      Nat.mul_div_cancel_left _ (Nat.two_pow_pos a)]
  have hrm : r ∣ m := by
    have hc : Nat.Coprime r (2 ^ a) := Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hr)
    rw [hxm] at hrx
    exact hc.dvd_of_dvd_mul_left hrx
  rcases hX _ (hy ▸ hm) with h | h
  · rw [hy] at h
    rw [h] at hrm
    exact Or.inl (Nat.dvd_one.1 hrm)
  · rw [hy] at h
    rw [h] at hrm
    exact (Nat.dvd_prime Nat.prime_three).1 hrm

variable {k : Type} [Field k]

set_option linter.unusedSectionVars false

theorem exists_conj_eq_canonicalRep_of_mem_normalizer {τ : Tag} {V : Set (ModGL τ k)}
    (hVH : V ⊆ torusGroup τ k) {g : ModGL τ k}
    (hg : g ∈ adjointGroup τ k ⊓ Subgroup.normalizer V) :
    ∃ w : WeylGroup τ, ∀ x ∈ V, g * x * g⁻¹ =
      canonicalRep (coxeterSystem τ) k w * x * (canonicalRep (coxeterSystem τ) k w)⁻¹ := by
  obtain ⟨hgC, hgN⟩ := Subgroup.mem_inf.1 hg
  have hTB := triangular_borel_structure.{0, 0} τ k
  have hB := Chevalley_toral_centralizer_Bruhat_factors τ k 1
  have hg1 : g ∈ toralCentralizer τ k 1 :=
    mem_toralCentralizer.2 ⟨hgC, by rw [rootDiagUnit_one, one_mul, inv_one, mul_one]⟩
  obtain ⟨w, -, h, hh, u, hu, v, hv, hgeq⟩ := hB.1 g hg1
  have huU : u ∈ posUnipotent τ k := rootSpan_le_posUnipotent (fun α hα => hα.2) hu
  have hvI : v ∈ rootSpan τ k (inversionSet w) := rootSpan_mono Set.inter_subset_right hv
  have hnN := canonicalRep_mem_normalizer (R := k) w
  set n := canonicalRep (coxeterSystem τ) k w with hn
  refine ⟨w, fun x hx => ?_⟩
  have hxT := hVH hx
  have hyV : g * x * g⁻¹ ∈ V := (Subgroup.mem_set_normalizer_iff.1 hgN x).1 hx
  have hyT := hVH hyV
  have htT : n * x * n⁻¹ ∈ torusGroup τ k := (Subgroup.mem_normalizer_iff.1 hnN x).1 hxT
  have hu' : (n * x * n⁻¹)⁻¹ * u * (n * x * n⁻¹)⁻¹⁻¹ ∈ posUnipotent τ k :=
    (Subgroup.mem_normalizer_iff.1 (hTB.2.2.1 (inv_mem htT)) u).1 huU
  have hv' : x⁻¹ * v * x⁻¹⁻¹ ∈ rootSpan τ k (inversionSet w) := by
    have hmap := map_rootSpan_of_forall (S := inversionSet w)
      (f := (MulAut.conj x⁻¹).toMonoidHom) fun α hα =>
        map_conj_rootSubgroup_of_mem_torusGroup (inv_mem hxT) hα.1
    rw [← hmap]
    exact ⟨v, hvI, rfl⟩
  have heq : h * (n * x * n⁻¹) * ((n * x * n⁻¹)⁻¹ * u * (n * x * n⁻¹)⁻¹⁻¹) * n *
      (x⁻¹ * v * x⁻¹⁻¹) = g * x * g⁻¹ * h * u * n * v := by
    rw [hgeq]
    group
  obtain ⟨-, h1, -⟩ := hB.2.1 w w _ _ _ _ _ _ (mul_mem hh htT) (mul_mem hyT hh) hu' huU hv' hvI
    heq
  exact (mul_left_cancel (h1.trans (hTB.1 _ hyT _ hh))).symm

theorem exists_pow_canonicalRep_eq {τ : Tag} (w : WeylGroup τ) (j : ℕ) :
    ∃ k₀ ∈ torusGroup τ k, canonicalRep (coxeterSystem τ) k w ^ j =
      k₀ * canonicalRep (coxeterSystem τ) k (w ^ j) := by
  induction j with
  | zero => exact ⟨1, Subgroup.one_mem _, by rw [pow_zero, pow_zero, canonicalRep_one, one_mul]⟩
  | succ j ih =>
    obtain ⟨k₁, hk₁, h₁⟩ := ih
    obtain ⟨k₂, hk₂, h₂⟩ := canonicalRep_mul_mem (R := k) (τ := τ) w (w ^ j)
    have hc : canonicalRep (coxeterSystem τ) k w * k₁ * (canonicalRep (coxeterSystem τ) k w)⁻¹ ∈
        torusGroup τ k :=
      (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer (R := k) w) k₁).1 hk₁
    refine ⟨_, mul_mem hc hk₂, ?_⟩
    rw [pow_succ', pow_succ', h₁]
    calc canonicalRep (coxeterSystem τ) k w * (k₁ * canonicalRep (coxeterSystem τ) k (w ^ j))
        = (canonicalRep (coxeterSystem τ) k w * k₁ * (canonicalRep (coxeterSystem τ) k w)⁻¹) *
          (canonicalRep (coxeterSystem τ) k w * canonicalRep (coxeterSystem τ) k (w ^ j)) := by
          group
      _ = _ := by rw [h₂]; group

theorem exists_orderOf_dvd_of_mem_torusImage {τ : Tag} {V : Subgroup (ModGL τ k)}
    (hVH : V ≤ torusGroup τ k) {β : MulAut V} (hβ : β ∈ torusImage V (adjointGroup τ k)) :
    ∃ w : WeylGroup τ, orderOf β ∣ orderOf w := by
  obtain ⟨g, hgN, hgC, rfl⟩ := mem_torusImage_iff.1 hβ
  obtain ⟨w, hw⟩ := exists_conj_eq_canonicalRep_of_mem_normalizer (V := (V : Set (ModGL τ k)))
    (fun x hx => hVH hx) (g := g) (Subgroup.mem_inf.2 ⟨hgC, hgN⟩)
  set n := canonicalRep (coxeterSystem τ) k w with hn
  have hnN : n ∈ Subgroup.normalizer (V : Set (ModGL τ k)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← hw x hx]
      exact (Subgroup.mem_normalizer_iff.1 hgN x).1 hx
    · intro hx
      have hx' : g⁻¹ * (n * x * n⁻¹) * g ∈ V := by
        have := (Subgroup.mem_normalizer_iff.1 hgN (g⁻¹ * (n * x * n⁻¹) * g)).2
          (by simpa [mul_assoc] using hx)
        exact this
      have h2 := hw _ hx'
      have h3 : n * x * n⁻¹ = n * (g⁻¹ * (n * x * n⁻¹) * g) * n⁻¹ := by
        rw [← h2]
        group
      have h4 : x = g⁻¹ * (n * x * n⁻¹) * g :=
        mul_left_cancel (mul_right_cancel h3)
      rw [h4]
      exact hx'
  have hβn : V.normalizerMonoidHom ⟨g, hgN⟩ = V.normalizerMonoidHom ⟨n, hnN⟩ := by
    refine MulEquiv.ext fun v => Subtype.ext ?_
    exact hw v v.2
  obtain ⟨k₀, hk₀, hpow⟩ := exists_pow_canonicalRep_eq (k := k) w (orderOf w)
  rw [pow_orderOf_eq_one, canonicalRep_one, mul_one] at hpow
  refine ⟨w, orderOf_dvd_of_pow_eq_one ?_⟩
  rw [hβn, ← map_pow, ← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker,
    Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  intro x hx
  show x * (n ^ orderOf w) = (n ^ orderOf w) * x
  rw [hpow]
  exact (triangular_borel_structure.{0, 0} τ k).1 x (hVH hx) k₀ hk₀

theorem eq_one_or_three_of_mem_torusImage {τ : Tag}
    (hW : ∀ w : WeylGroup τ, Odd (orderOf w) → orderOf w = 1 ∨ orderOf w = 3)
    {V : Subgroup (ModGL τ k)} (hVH : V ≤ torusGroup τ k) {β : MulAut V}
    (hβ : β ∈ torusImage V (adjointGroup τ k)) (hodd : Odd (orderOf β)) :
    orderOf β = 1 ∨ orderOf β = 3 := by
  obtain ⟨w, hdvd⟩ := exists_orderOf_dvd_of_mem_torusImage hVH hβ
  exact eq_one_or_three_of_dvd_orderOf hW w hodd hdvd

end CFSG.RankThree.PartOne.K133H
