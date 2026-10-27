module

public import CFSG.Timmesfeld.Transvection.ModelSULowSpan

public section

namespace CFSG.Timmesfeld.Transvection

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.Timmesfeld.ARS CFSG.Timmesfeld.LieEmbed

namespace ModelRank

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

theorem suMat_mulVec_sub_eq [CharP F 2] {g : SU σ m} (hg : g * g = 1) (x : Fin m → F) :
    suMat σ m g *ᵥ (suMat σ m g *ᵥ x - x) = suMat σ m g *ᵥ x - x := by
  rw [Matrix.mulVec_sub, mulVec_mulVec, ← map_mul, hg, map_one, one_mulVec]
  have hx : -x = x := funext fun i => CharTwo.neg_eq (x i)
  have hgx : -(suMat σ m g *ᵥ x) = suMat σ m g *ᵥ x := funext fun _ => CharTwo.neg_eq _
  rw [sub_eq_add_neg, sub_eq_add_neg, hx, hgx, add_comm]

theorem uForm_sub_sub_eq_zero [CharP F 2] {g : SU σ m} (hg : g * g = 1) (x y : Fin m → F) :
    uForm σ (suMat σ m g *ᵥ x - x) (suMat σ m g *ᵥ y - y) = 0 := by
  have h1 : uForm σ (suMat σ m g *ᵥ x) (suMat σ m g *ᵥ y) = uForm σ x y :=
    uForm_mulVec σ g x y
  have h2 : uForm σ (suMat σ m g *ᵥ x) y = uForm σ x (suMat σ m g *ᵥ y) := by
    have h := uForm_mulVec σ g (suMat σ m g *ᵥ x) y
    rw [mulVec_mulVec, ← map_mul, hg, map_one, one_mulVec] at h
    exact h.symm
  simp only [uForm_sub_left, uForm_sub_right, h1, h2, CharTwo.sub_eq_add]
  rw [add_comm (uForm σ x (suMat σ m g *ᵥ y)) (uForm σ x y), CharTwo.add_self_eq_zero]

theorem uForm_sub_eq_zero_of_mulVec_eq {g : SU σ m} {p : Fin m → F}
    (hp : suMat σ m g *ᵥ p = p) (y : Fin m → F) :
    uForm σ p (suMat σ m g *ᵥ y - y) = 0 := by
  have h := uForm_mulVec σ g p y
  rw [hp] at h
  rw [uForm_sub_right, h, sub_self]

theorem suMat_mulVec_eq_of_forall_uForm_sub_eq_zero {g : SU σ m} {y : Fin m → F}
    (h : ∀ x, uForm σ (suMat σ m g *ᵥ x - x) y = 0) : suMat σ m g *ᵥ y = y := by
  have h1 : ∀ x, uForm σ x (suMat σ m g⁻¹ *ᵥ y - y) = 0 := by
    intro x
    have hx : uForm σ x (suMat σ m g⁻¹ *ᵥ y) = uForm σ (suMat σ m g *ᵥ x) y := by
      have h := uForm_mulVec σ g x (suMat σ m g⁻¹ *ᵥ y)
      rw [suMat_mulVec_suMat_inv_mulVec] at h
      exact h.symm
    rw [uForm_sub_right, hx, ← uForm_sub_left]
    exact h x
  have hz : suMat σ m g⁻¹ *ᵥ y - y = 0 := by
    funext i
    have hi := h1 (Pi.single (Fin.rev i) 1)
    rw [uForm_single_left, Fin.rev_rev] at hi
    exact hi
  have hzy : suMat σ m g⁻¹ *ᵥ y = y := sub_eq_zero.mp hz
  have hgy : suMat σ m g *ᵥ (suMat σ m g⁻¹ *ᵥ y) = suMat σ m g *ᵥ y := by rw [hzy]
  rw [mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, one_mulVec] at hgy
  exact hgy.symm

theorem suMat_mulVec_eq_of_commute [CharP F 2] (hσ : ∀ c, σ (σ c) = c) {p : Fin m → F}
    (hp : p ≠ 0) {T : Subgroup (SU σ m)} (hT : IsUTransGroup σ p T) {w : SU σ m}
    (hw : w * w = 1) (hc : ∀ t ∈ T, w * t = t * w) : suMat σ m w *ᵥ p = p := by
  have hw' : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  have hwN : w ∈ Subgroup.normalizer (T : Set (SU σ m)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    have h1 : t ∈ T → w * t * w⁻¹ = t := by
      intro ht
      rw [hc t ht]
      group
    have h2 : w * t * w⁻¹ ∈ T → t = w * t * w⁻¹ := by
      intro ht
      have hv : w * (w * t * w⁻¹) = (w * t * w⁻¹) * w := hc _ ht
      calc t = w⁻¹ * (w * t * w⁻¹) * w := by group
        _ = w * (w * t * w⁻¹) * w := by rw [hw']
        _ = ((w * t * w⁻¹) * w) * w := by rw [hv]
        _ = w * t * w⁻¹ := by rw [mul_assoc, hw, mul_one]
    constructor
    · intro ht
      rwa [h1 ht]
    · intro ht
      rw [h2 ht]
      exact ht
  rw [normalizer_eq_uLine hσ hp hT] at hwN
  obtain ⟨μ, -, hμp⟩ := hwN
  have h2 : suMat σ m w *ᵥ (suMat σ m w *ᵥ p) = p := by
    rw [mulVec_mulVec, ← map_mul, hw, map_one, one_mulVec]
  rw [hμp, mulVec_smul, hμp, smul_smul] at h2
  have hμμ : μ * μ = 1 := by
    have h : (μ * μ) • p = (1 : F) • p := by rw [h2, one_smul]
    exact (smul_left_inj hp).1 h
  have hμ2 : μ ^ 2 = 1 := by rw [pow_two, hμμ]
  have hμ1 : μ = 1 := by
    rcases sq_eq_one_iff.1 hμ2 with h | h
    · exact h
    · rwa [CharTwo.neg_eq] at h
  rwa [hμ1, one_smul] at hμp

theorem mem_lowRad_of_mem_centralizer [CharP F 2] (hσ : ∀ c, σ (σ c) = c) {g : SU σ m}
    (hg : g * g = 1) (hc : ∀ x ∈ lowRad σ m, g * x = x * g) : g ∈ lowRad σ m := by
  have hfix : ∀ a : Fin (m / 2),
      suMat σ m g *ᵥ (Pi.single (lowIdx a) 1 : Fin m → F) = Pi.single (lowIdx a) 1 := by
    intro a
    obtain ⟨T, hT⟩ := exists_isUTransGroup (σ := σ) hσ
      (uForm_single_self (σ := σ) (lowIdx_ne_rev a a))
    have hTQ : T ≤ lowRad σ m :=
      le_lowRad_of_isUTransGroup (single_lowIdx_mem_lowSpan a) hT
    exact suMat_mulVec_eq_of_commute hσ (single_one_ne_zero (lowIdx a)) hT hg
      fun t ht => hc t (hTQ ht)
  rw [mem_lowRad]
  constructor
  · intro y
    refine mem_lowSpan_of_forall_uForm_single_eq_zero (σ := σ)
      (x := suMat σ m g *ᵥ y - y) ?_ ?_
    · exact uForm_sub_sub_eq_zero hg y y
    · intro a
      have hzero : uForm σ (Pi.single (lowIdx a) 1 : Fin m → F)
          (suMat σ m g *ᵥ y - y) = 0 := uForm_sub_eq_zero_of_mulVec_eq (hfix a) y
      rw [← uForm_conj σ hσ (Pi.single (lowIdx a) 1) (suMat σ m g *ᵥ y - y), hzero,
        map_zero]
  · intro x hx
    rw [eq_sum_of_mem_lowSpan hx, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.mulVec_smul, hfix]

end ModelRank

end CFSG.Timmesfeld.Transvection
