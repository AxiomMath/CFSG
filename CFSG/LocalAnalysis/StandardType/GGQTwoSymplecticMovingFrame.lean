module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSymplecticMovingBlock
public import CFSG.LocalAnalysis.StandardType.GGQTwoSymplecticTorusActions
public import CFSG.Sporadic.Suz.Setup

public section

namespace CFSG.StandardType.QTwoSymplecticCav

open Matrix CFSG.Open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.StandardType.WitSpNs CFSG.LieType.Chevalley
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

private theorem orient_cube_character (a : Multiplicative (ZMod 3)) (ha : a ≠ 1) :
    (if Multiplicative.toAdd a = 2 then a⁻¹ else a) = Multiplicative.ofAdd (1 : ZMod 3) := by
  exact (by decide +kernel : ∀ a : Multiplicative (ZMod 3), a ≠ 1 →
    (if Multiplicative.toAdd a = 2 then a⁻¹ else a) = Multiplicative.ofAdd (1 : ZMod 3)) a ha

theorem movingU_mem_normalizer_of_full_frame
    (hK : Nat.card K = 2) {E : Subgroup (StatedSp n K)} {A₀ : StatedSp n K}
    {M : Matrix (Fin 2) (Fin 2) K} (hdet : M.det = 1) (hM : M * M + M + 1 = 0)
    {k : Fin n → ↥E →* Multiplicative (ZMod 3)}
    (hframe : ∀ g : ↥E, mat n K (A₀⁻¹ * g * A₀) =
      planeMat (fun j => M ^ (Multiplicative.toAdd (k j g)).val))
    (hsurj : ∀ v : Fin n → Multiplicative (ZMod 3), ∃ g : ↥E, ∀ j, k j g = v j)
    (i : Fin 4 → Fin n) (t : ↥E) :
    A₀ * movingU i k t * A₀⁻¹ ∈ Subgroup.normalizer (E : Set (StatedSp n K)) := by
  classical
  have hN : ∀ j, A₀ * longBlock K n j (movingW k t j) * A₀⁻¹ ∈
      Subgroup.normalizer (E : Set (StatedSp n K)) := by
    intro j
    unfold movingW
    split_ifs with h
    · exact longBlock_mem_normalizer_of_full_frame hK hdet hM hframe hsurj j
    · rw [map_one, mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
  have hprod : A₀ * movingU i k t * A₀⁻¹ =
      (A₀ * longBlock K n (i 0) (movingW k t (i 0)) * A₀⁻¹) *
      (A₀ * longBlock K n (i 1) (movingW k t (i 1)) * A₀⁻¹) *
      (A₀ * longBlock K n (i 2) (movingW k t (i 2)) * A₀⁻¹) *
      (A₀ * longBlock K n (i 3) (movingW k t (i 3)) * A₀⁻¹) := by
    unfold movingU
    group
  rw [hprod]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hN _) (hN _)) (hN _)) (hN _)

theorem exists_conj_movingU_of_full_frame
    (hK : Nat.card K = 2) {E : Subgroup (StatedSp n K)} {A₀ : StatedSp n K}
    {M : Matrix (Fin 2) (Fin 2) K} (hdet : M.det = 1) (hM : M * M + M + 1 = 0)
    {k : Fin n → ↥E →* Multiplicative (ZMod 3)}
    (hframe : ∀ g : ↥E, mat n K (A₀⁻¹ * g * A₀) =
      planeMat (fun j => M ^ (Multiplicative.toAdd (k j g)).val))
    (hsurj : ∀ v : Fin n → Multiplicative (ZMod 3), ∃ g : ↥E, ∀ j, k j g = v j)
    (i : Fin 4 → Fin n) (hi : Function.Injective i) (t g : ↥E) :
    ∃ g' : ↥E, (∀ j, k j g' = if j ∈ Set.range i ∧ Multiplicative.toAdd (k j t) = 2
        then (k j g)⁻¹ else k j g) ∧
      (A₀ * movingU i k t * A₀⁻¹) * g * (A₀ * movingU i k t * A₀⁻¹)⁻¹ = g' := by
  classical
  obtain ⟨g', hg'⟩ := hsurj (fun j =>
    if j ∈ Set.range i ∧ Multiplicative.toAdd (k j t) = 2 then (k j g)⁻¹ else k j g)
  refine ⟨g', hg', ?_⟩
  let U : StatedSp n K := movingU i k t
  have hU2 : U * U = 1 := movingU_mul_self i hi
  have hUi : U⁻¹ = U := inv_eq_of_mul_eq_one_right hU2
  have hWi : (WSL : SL(2, K))⁻¹ = WSL := inv_eq_of_mul_eq_one_right WSL_mul_self_of_char_two
  apply (MulAut.conj A₀⁻¹).injective
  apply mat_injective
  change mat n K (A₀⁻¹ * ((A₀ * U * A₀⁻¹) * (g : StatedSp n K) *
    (A₀ * U * A₀⁻¹)⁻¹) * A₀) = mat n K (A₀⁻¹ * g' * A₀)
  rw [show A₀⁻¹ * ((A₀ * U * A₀⁻¹) * (g : StatedSp n K) *
      (A₀ * U * A₀⁻¹)⁻¹) * A₀ = U * (A₀⁻¹ * g * A₀) * U by
        calc A₀⁻¹ * ((A₀ * U * A₀⁻¹) * (g : StatedSp n K) *
            (A₀ * U * A₀⁻¹)⁻¹) * A₀ = U * (A₀⁻¹ * g * A₀) * U⁻¹ := by group
          _ = U * (A₀⁻¹ * g * A₀) * U := by rw [hUi]]
  have hconj := mat_conj_four_longBlock i hi (movingW k t) (hframe g)
  change mat n K (U * (A₀⁻¹ * g * A₀) * U) = _ at hconj
  rw [hconj, hframe g']
  congr 1
  funext j
  by_cases hji : j ∈ Set.range i
  · rw [if_pos hji, hg']
    by_cases hj2 : Multiplicative.toAdd (k j t) = 2
    · rw [if_pos ⟨hji, hj2⟩]
      simp only [movingW, if_pos hj2]
      have h := congrArg (fun T : SL(2, K) => (T : Matrix (Fin 2) (Fin 2) K))
        (WSL_conj_pow_val hK hdet hM (k j g))
      rw [hWi] at h
      simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow, coe_mkSL] using h
    · rw [if_neg (fun h => hj2 h.2)]
      simp only [movingW, if_neg hj2, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, Matrix.mul_one]
  · rw [if_neg hji, hg', if_neg (fun h => hji h.1)]

theorem exists_aligned_moving_generator
    (hK : Nat.card K = 2) {E : Subgroup (StatedSp n K)} {A₀ : StatedSp n K}
    {M : Matrix (Fin 2) (Fin 2) K} (hdet : M.det = 1) (hM : M * M + M + 1 = 0)
    {k : Fin n → ↥E →* Multiplicative (ZMod 3)}
    (hframe : ∀ g : ↥E, mat n K (A₀⁻¹ * g * A₀) =
      planeMat (fun j => M ^ (Multiplicative.toAdd (k j g)).val))
    (hsurj : ∀ v : Fin n → Multiplicative (ZMod 3), ∃ g : ↥E, ∀ j, k j g = v j)
    (i : Fin 4 → Fin n) (hi : Function.Injective i) (t : ↥E)
    (hmoving : ∀ a, k (i a) t ≠ 1) :
    ∃ t' : ↥E, (∀ a, k (i a) t' = Multiplicative.ofAdd (1 : ZMod 3)) ∧
      (A₀ * movingU i k t * A₀⁻¹) * t * (A₀ * movingU i k t * A₀⁻¹)⁻¹ = t' := by
  classical
  obtain ⟨t', ht', heq⟩ := exists_conj_movingU_of_full_frame hK hdet hM hframe hsurj i hi t t
  refine ⟨t', ?_, heq⟩
  intro a
  have hia : i a ∈ Set.range i := ⟨a, rfl⟩
  simp only [ht', hia, true_and]
  exact orient_cube_character (k (i a) t) (hmoving a)

end CFSG.StandardType.QTwoSymplecticCav

end
