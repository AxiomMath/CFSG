module

public import CFSG.LocalAnalysis.StandardType.GGSelPSUEmbed
public import CFSG.LocalAnalysis.StandardType.GGSelectedRootMatch
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

public section

namespace CFSG.StandardType.SelectedRoot.SelPSU

open Matrix CFSG.LieType.Universal.Unitary
open CFSG.LieType.Steinberg (sl2Upper coe_sl2Upper sl2Lower coe_sl2Lower)
open CFSG.StandardType.PsiDiagChar (sl2Diag coe_sl2Diag)

variable {F : Type*} [Field F] {n : ℕ}

theorem fin_two_cases (a : Fin 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

@[expose] def pairCoord (i₀ : Fin n) : Fin 2 → Fin n := fun r => if r = 0 then i₀ else Fin.rev i₀

theorem pairCoord_zero (i₀ : Fin n) : pairCoord i₀ 0 = i₀ := by
  show (if (0 : Fin 2) = 0 then i₀ else Fin.rev i₀) = i₀
  rw [if_pos rfl]

theorem pairCoord_one (i₀ : Fin n) : pairCoord i₀ 1 = Fin.rev i₀ := by
  show (if (1 : Fin 2) = 0 then i₀ else Fin.rev i₀) = Fin.rev i₀
  rw [if_neg (show ¬ ((1 : Fin 2) = 0) by decide)]

theorem pairCoord_injective {i₀ : Fin n} (h : i₀ ≠ Fin.rev i₀) :
    Function.Injective (pairCoord i₀) := by
  intro a b hab
  rcases fin_two_cases a with rfl | rfl <;> rcases fin_two_cases b with rfl | rfl
  · rfl
  · rw [pairCoord_zero, pairCoord_one] at hab
    exact absurd hab h
  · rw [pairCoord_one, pairCoord_zero] at hab
    exact absurd hab.symm h
  · rfl

theorem pairCoord_rev (i₀ : Fin n) (r : Fin 2) :
    pairCoord i₀ (Fin.rev r) = Fin.rev (pairCoord i₀ r) := by
  have r0 : Fin.rev (0 : Fin 2) = 1 := by decide
  have r1 : Fin.rev (1 : Fin 2) = 0 := by decide
  rcases fin_two_cases r with rfl | rfl
  · rw [r0, pairCoord_one, pairCoord_zero]
  · rw [r1, pairCoord_zero, pairCoord_one, Fin.rev_rev]

theorem mem_range_pairCoord {i₀ x : Fin n} :
    x ∈ Set.range (pairCoord i₀) ↔ x = i₀ ∨ x = Fin.rev i₀ := by
  constructor
  · rintro ⟨r, rfl⟩
    rcases fin_two_cases r with rfl | rfl
    · exact Or.inl (pairCoord_zero i₀)
    · exact Or.inr (pairCoord_one i₀)
  · rintro (rfl | rfl)
    · exact ⟨0, pairCoord_zero _⟩
    · exact ⟨1, pairCoord_one _⟩

theorem sl2_isometry (σ : F ≃+* F) (k : Subfield F) (h2 : (2 : F) = 0)
    (hk : ∀ x ∈ k, σ x = x) (A : Matrix.SpecialLinearGroup (Fin 2) k) :
    conjTr σ (k.subtype.mapMatrix (A : Matrix (Fin 2) (Fin 2) k)) *
        (antidiag 2 : Matrix (Fin 2) (Fin 2) F) *
        k.subtype.mapMatrix (A : Matrix (Fin 2) (Fin 2) k) = antidiag 2 := by
  set M : Matrix (Fin 2) (Fin 2) F := k.subtype.mapMatrix (A : Matrix (Fin 2) (Fin 2) k) with hM
  have hfix : ∀ i j, σ (M i j) = M i j := fun i j => hk _ ((A : Matrix (Fin 2) (Fin 2) k) i j).2
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have h := A.2
    rw [Matrix.det_fin_two] at h
    have h' := congrArg k.subtype h
    simpa [hM] using h'
  have hconj : conjTr σ M = Mᵀ := by
    ext i j
    simp [conjTr, hfix]
  have r0 : Fin.rev (0 : Fin 2) = 1 := by decide
  have r1 : Fin.rev (1 : Fin 2) = 0 := by decide
  have a00 : (antidiag 2 : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 := by
    show (if (0 : Fin 2) = Fin.rev 0 then (1 : F) else 0) = 0
    rw [r0, if_neg (show ¬ ((0 : Fin 2) = 1) by decide)]
  have a01 : (antidiag 2 : Matrix (Fin 2) (Fin 2) F) 0 1 = 1 := by
    show (if (1 : Fin 2) = Fin.rev 0 then (1 : F) else 0) = 1
    rw [r0, if_pos rfl]
  have a10 : (antidiag 2 : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
    show (if (0 : Fin 2) = Fin.rev 1 then (1 : F) else 0) = 1
    rw [r1, if_pos rfl]
  have a11 : (antidiag 2 : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
    show (if (1 : Fin 2) = Fin.rev 1 then (1 : F) else 0) = 0
    rw [r1, if_neg (show ¬ ((1 : Fin 2) = 0) by decide)]
  have key : ∀ i j : Fin 2, (Mᵀ * (antidiag 2 : Matrix (Fin 2) (Fin 2) F) * M) i j =
      M 0 i * M 1 j + M 1 i * M 0 j := by
    intro i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, a00, a01, a10, a11]
    ring
  rw [hconj]
  ext i j
  rw [key]
  rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases j with rfl | rfl
  · rw [a00]
    linear_combination (M 0 0 * M 1 0) * h2
  · rw [a01]
    linear_combination hdet + (M 0 1 * M 1 0) * h2
  · rw [a10]
    linear_combination hdet + (M 0 1 * M 1 0) * h2
  · rw [a11]
    linear_combination (M 0 1 * M 1 1) * h2

section Chart

variable (σ : F ≃+* F) (k : Subfield F) {ι : Fin 2 → Fin n}

@[expose] noncomputable def chart (hι : Function.Injective ι)
    (hrev : ∀ r, ι (Fin.rev r) = Fin.rev (ι r)) (h2 : (2 : F) = 0) (hk : ∀ x ∈ k, σ x = x) :
    Matrix.SpecialLinearGroup (Fin 2) k →* SU σ n :=
  ((embGL hι).comp (Matrix.SpecialLinearGroup.toGL.comp
      (Matrix.SpecialLinearGroup.map k.subtype))).codRestrict (SU σ n) fun A =>
    mem_SU.mpr
      ⟨(det_embM hι ((Matrix.SpecialLinearGroup.map k.subtype A : Matrix.SpecialLinearGroup
          (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)).trans
        (Matrix.SpecialLinearGroup.map k.subtype A).2,
       embM_isometry hι hrev σ (sl2_isometry σ k h2 hk A)⟩

variable (hι : Function.Injective ι) (hrev : ∀ r, ι (Fin.rev r) = Fin.rev (ι r))
  (h2 : (2 : F) = 0) (hk : ∀ x ∈ k, σ x = x)

theorem coe_chart (A : Matrix.SpecialLinearGroup (Fin 2) k) :
    (((chart σ k hι hrev h2 hk A : SU σ n) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      embM ι (k.subtype.mapMatrix (A : Matrix (Fin 2) (Fin 2) k)) :=
  rfl

theorem chart_apply_image (A : Matrix.SpecialLinearGroup (Fin 2) k) (r s : Fin 2) :
    (((chart σ k hι hrev h2 hk A : SU σ n) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
        (ι r) (ι s) = ((A : Matrix (Fin 2) (Fin 2) k) r s : F) := by
  rw [coe_chart]
  exact (embM_apply_image hι _ r s).trans rfl

theorem chart_injective : Function.Injective (chart σ k hι hrev h2 hk) := by
  intro A A' h
  refine Matrix.SpecialLinearGroup.ext A A' fun r s => ?_
  have h1 := congrArg
    (fun g : SU σ n => ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) (ι r) (ι s)) h
  simp only [chart_apply_image] at h1
  exact Subtype.ext h1

end Chart

section Special

variable (σ : F ≃+* F) (k : Subfield F) {i₀ : Fin n} (hne : i₀ ≠ Fin.rev i₀)
  (h2 : (2 : F) = 0) (hk : ∀ x ∈ k, σ x = x)

include h2 hk in
theorem traceZero_of_mem (τ : k) : (τ : F) ∈ traceZero σ := by
  show (τ : F) + σ τ = 0
  rw [hk _ τ.2, ← two_mul, h2, zero_mul]

include h2 in
theorem fixed_of_mem_traceZero {ζ : F} (hζ : ζ ∈ traceZero σ) : σ ζ = ζ := by
  have hζ' : ζ + σ ζ = 0 := hζ
  linear_combination hζ' - ζ * h2

theorem chart_upper (τ : k) :
    chart σ k (pairCoord_injective hne) (pairCoord_rev i₀) h2 hk (sl2Upper τ) =
      longRootHom σ hne (Multiplicative.ofAdd ⟨(τ : F), traceZero_of_mem σ k h2 hk τ⟩) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_chart, coe_longRootHom]
  symm
  apply eq_embM_of_entries (pairCoord_injective hne)
  · intro r s
    rcases fin_two_cases r with rfl | rfl <;> rcases fin_two_cases s with rfl | rfl <;>
      simp [longRootMatrix, pairCoord_zero, pairCoord_one, Matrix.one_apply, Matrix.single_apply,
        hne, hne.symm, coe_sl2Upper]
  · intro x y hxy
    have hx : ¬(i₀ = x ∧ Fin.rev i₀ = y) := by
      rintro ⟨rfl, rfl⟩
      exact hxy ⟨mem_range_pairCoord.mpr (Or.inl rfl), mem_range_pairCoord.mpr (Or.inr rfl)⟩
    rw [longRootMatrix, Matrix.add_apply, Matrix.single_apply, if_neg hx, add_zero]

theorem chart_lower (τ : k) :
    chart σ k (pairCoord_injective hne) (pairCoord_rev i₀) h2 hk (sl2Lower τ) =
      longRootHom σ (i := Fin.rev i₀) (by rw [Fin.rev_rev]; exact hne.symm)
        (Multiplicative.ofAdd ⟨(τ : F), traceZero_of_mem σ k h2 hk τ⟩) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_chart, coe_longRootHom]
  symm
  apply eq_embM_of_entries (pairCoord_injective hne)
  · intro r s
    rcases fin_two_cases r with rfl | rfl <;> rcases fin_two_cases s with rfl | rfl <;>
      simp [longRootMatrix, pairCoord_zero, pairCoord_one, Matrix.one_apply, Matrix.single_apply,
        hne, hne.symm, Fin.rev_rev, coe_sl2Lower]
  · intro x y hxy
    have hx : ¬(Fin.rev i₀ = x ∧ i₀ = y) := by
      rintro ⟨rfl, rfl⟩
      exact hxy ⟨mem_range_pairCoord.mpr (Or.inr rfl), mem_range_pairCoord.mpr (Or.inl rfl)⟩
    rw [longRootMatrix, Fin.rev_rev, Matrix.add_apply, Matrix.single_apply, if_neg hx, add_zero]

@[expose] def dgn (a : kˣ) (i₀ : Fin n) : Fin n → F := fun s =>
  if s = i₀ then (((a : kˣ) : k) : F) else
    if s = Fin.rev i₀ then (((a⁻¹ : kˣ) : k) : F) else 1

include hne hk in
theorem dgn_unitary (a : kˣ) (s : Fin n) :
    σ (dgn k a i₀ s) * dgn k a i₀ (Fin.rev s) = 1 := by
  have hαβ : (((a : kˣ) : k) : F) * (((a⁻¹ : kˣ) : k) : F) = 1 := by
    have h := map_mul k.subtype ((a : kˣ) : k) ((a⁻¹ : kˣ) : k)
    rw [Units.mul_inv, map_one] at h
    exact h.symm
  have hβα : (((a⁻¹ : kˣ) : k) : F) * (((a : kˣ) : k) : F) = 1 := by
    rw [mul_comm]
    exact hαβ
  have hσα : σ (((a : kˣ) : k) : F) = (((a : kˣ) : k) : F) := hk _ ((a : kˣ) : k).2
  have hσβ : σ (((a⁻¹ : kˣ) : k) : F) = (((a⁻¹ : kˣ) : k) : F) := hk _ ((a⁻¹ : kˣ) : k).2
  have hne' : Fin.rev i₀ ≠ i₀ := hne.symm
  have d1 : dgn k a i₀ i₀ = (((a : kˣ) : k) : F) := by simp [dgn]
  have d2 : dgn k a i₀ (Fin.rev i₀) = (((a⁻¹ : kˣ) : k) : F) := by simp [dgn, hne']
  by_cases hs1 : s = i₀
  · rw [hs1, d1, d2, hσα, hαβ]
  · by_cases hs2 : s = Fin.rev i₀
    · rw [hs2, Fin.rev_rev, d2, d1, hσβ, hβα]
    · have hr1 : Fin.rev s ≠ i₀ := fun h => hs2 (by rw [← h, Fin.rev_rev])
      have hr2 : Fin.rev s ≠ Fin.rev i₀ := fun h => hs1 (Fin.rev_injective h)
      have e1 : dgn k a i₀ s = 1 := by simp [dgn, hs1, hs2]
      have e2 : dgn k a i₀ (Fin.rev s) = 1 := by simp [dgn, hr1, hr2]
      rw [e1, e2, map_one, one_mul]

theorem chart_sl2Diag_mat (a : kˣ) :
    (((chart σ k (pairCoord_injective hne) (pairCoord_rev i₀) h2 hk (sl2Diag a) : SU σ n) :
        GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal (dgn k a i₀) := by
  rw [coe_chart]
  symm
  apply eq_embM_of_entries (pairCoord_injective hne)
  · intro r s
    rcases fin_two_cases r with rfl | rfl <;> rcases fin_two_cases s with rfl | rfl <;>
      simp [dgn, pairCoord_zero, pairCoord_one, Matrix.diagonal_apply, hne, hne.symm,
        coe_sl2Diag]
  · intro x y hxy
    by_cases hxy' : x = y
    · subst hxy'
      have hx : ¬(x = i₀ ∨ x = Fin.rev i₀) := fun h =>
        hxy ⟨mem_range_pairCoord.mpr h, mem_range_pairCoord.mpr h⟩
      have hx' := not_or.mp hx
      simp [dgn, hx'.1, hx'.2]
    · rw [Matrix.diagonal_apply_ne _ hxy', Matrix.one_apply_ne hxy']

end Special

end CFSG.StandardType.SelectedRoot.SelPSU

end
