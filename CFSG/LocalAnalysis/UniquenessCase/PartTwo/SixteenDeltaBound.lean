module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTwentyThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16b_exists_pow_involution (V₀ V : Subgroup G) {t : G} {k : ℕ}
    (hk : orderOf t = 2 ^ k) (hct : ¬ CentralizesMod V₀ V t) :
    ∃ i : ℕ, ¬ CentralizesMod V₀ V (t ^ 2 ^ i) ∧ CentralizesMod V₀ V (t ^ 2 ^ i * t ^ 2 ^ i) := by
  classical
  have hex : ∃ j : ℕ, CentralizesMod V₀ V (t ^ 2 ^ j) := by
    refine ⟨k, fun v _ => ?_⟩
    have : t ^ 2 ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one t
    simp [this]
  set j := Nat.find hex with hj
  have hjspec : CentralizesMod V₀ V (t ^ 2 ^ j) := Nat.find_spec hex
  have hj0 : j ≠ 0 := by
    intro h0
    rw [h0] at hjspec
    exact hct (by simpa using hjspec)
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  refine ⟨i, Nat.find_min hex (by omega), ?_⟩
  have : t ^ 2 ^ i * t ^ 2 ^ i = t ^ 2 ^ j := by
    rw [hi, pow_succ 2 i, pow_mul, sq]
  rw [this]
  exact hjspec

theorem succ_le_deltaN_of_mBarGT (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) {n : ℕ}
    (hn : MBarGT D.M V₀ V n) (m : ℕ) : ((n + 1 : ℕ) : ℕ∞) ≤ deltaN m D.M V := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV : IsElemAbelian 2 V := h.isElemAbelian
  have hV2 : IsPGroup 2 V := hV.isPGroup
  have hVM : V ≤ D.M := h.pairFacts.le_M
  have hM0 : D.M ≤ normalizer (V₀ : Set G) := h.pairFacts.le_normalizer₀
  refine le_iInf fun U => le_iInf fun hU => ?_
  obtain ⟨hUV, t, ⟨htM, htC⟩, ⟨k, hk⟩, W, hWV, -, hUW, hWt, hP⟩ := hU
  by_cases hct : CentralizesMod V₀ V t
  · exfalso
    obtain ⟨w, hwW, hwt⟩ := SetLike.not_le_iff_exists.1 hWt
    have hwM : w ∈ D.M := hVM (hWV hwW)
    have hz1 : w⁻¹ * t⁻¹ * w * t ≠ 1 := by
      intro hz
      apply hwt
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      calc y * w = y * w * (w⁻¹ * y⁻¹ * w * y) := by rw [hz, mul_one]
        _ = w * y := by group
    have hc : t * w * t⁻¹ * w⁻¹ ∈ V₀ := hct w (hWV hwW)
    have hc1 : t⁻¹ * (t * w * t⁻¹ * w⁻¹)⁻¹ * t ∈ V₀ :=
      (Subgroup.mem_normalizer_iff''.1 (hM0 htM) _).1 (V₀.inv_mem hc)
    have hc2 : w⁻¹ * (t⁻¹ * (t * w * t⁻¹ * w⁻¹)⁻¹ * t) * w ∈ V₀ :=
      (Subgroup.mem_normalizer_iff''.1 (hM0 hwM) _).1 hc1
    have hzV₀ : w⁻¹ * t⁻¹ * w * t ∈ V₀ := by
      have e : w⁻¹ * t⁻¹ * w * t = w⁻¹ * (t⁻¹ * (t * w * t⁻¹ * w⁻¹)⁻¹ * t) * w := by group
      rw [e]
      exact hc2
    have hzW : w⁻¹ * t⁻¹ * w * t ∈ commElt W t := Subgroup.subset_closure ⟨w, hwW, rfl⟩
    have hXV : Subgroup.zpowers (w⁻¹ * t⁻¹ * w * t) ≤ V₀ := Subgroup.zpowers_le.2 hzV₀
    have hX1 : Subgroup.zpowers (w⁻¹ * t⁻¹ * w * t) ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hz1
    have hN := h.hyp62.normalizer_le _ hXV hX1
    have hcent_eq : centralizer ({w⁻¹ * t⁻¹ * w * t} : Set G) =
        centralizer (Subgroup.zpowers (w⁻¹ * t⁻¹ * w * t) : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hP _ hzW (((le_of_eq hcent_eq).trans (Subgroup.centralizer_le_normalizer _)).trans hN)
  · obtain ⟨i, hs1, hs2⟩ := s16b_exists_pow_involution V₀ V hk hct
    have hsM : t ^ 2 ^ i ∈ D.M := D.M.pow_mem htM _
    have hsub : (U : Set G) ⊆ centMod V₀ V (t ^ 2 ^ i) := by
      intro u hu
      refine ⟨hUV hu, ?_⟩
      have hut : Commute u t := (Subgroup.mem_centralizer_iff.1 htC u hu)
      have hus : Commute u (t ^ 2 ^ i) := hut.pow_right _
      have : t ^ 2 ^ i * u * (t ^ 2 ^ i)⁻¹ * u⁻¹ = 1 := by
        rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
        exact hus.symm.eq
      rw [this]
      exact V₀.one_mem
    have hcard : Nat.card U ≤ Nat.card (centMod V₀ V (t ^ 2 ^ i)) :=
      Nat.card_mono (Set.toFinite _) hsub
    have hle := hn.1 _ hsM hs1 hs2
    have hVU := E3.card_eq_two_pow_mul hV2 hUV
    have hpos : 0 < Nat.card U := Nat.card_pos
    have h3 : 2 ^ (n + 1) * Nat.card U ≤ 2 ^ E3.mQuot V U * Nat.card U := by
      calc 2 ^ (n + 1) * Nat.card U ≤ 2 ^ (n + 1) * Nat.card (centMod V₀ V (t ^ 2 ^ i)) :=
            Nat.mul_le_mul_left _ hcard
        _ ≤ Nat.card V := hle
        _ = 2 ^ E3.mQuot V U * Nat.card U := hVU
    have h4 := Nat.le_of_mul_le_mul_right h3 hpos
    have h5 : n + 1 ≤ E3.mQuot V U := (Nat.pow_le_pow_iff_right (by norm_num)).1 h4
    exact_mod_cast h5

theorem succ_le_deltaInf_of_mBarGT (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) {n : ℕ}
    (hn : MBarGT D.M V₀ V n) : ((n + 1 : ℕ) : ℕ∞) ≤ deltaInf D.M V :=
  succ_le_deltaN_of_mBarGT D h hn _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
