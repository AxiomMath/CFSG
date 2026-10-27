module

public import CFSG.RankThree.PartOne.KC.EvenSymplecticSL2Automorphisms
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bTensor

public section

namespace CFSG.RankThree.PartOne

namespace KCRootAxis

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem frobHom_eq_minorAut_sq (g : antiSp K) : frobHom K g = (minorAut K ^ 2) g :=
  (minorAut_pow_two g).symm

theorem frobHom_bijective : Function.Bijective (frobHom K) := by
  have h : (frobHom K : antiSp K → antiSp K) = ⇑(minorAut K ^ 2) := funext frobHom_eq_minorAut_sq
  rw [h]
  exact (minorAut K ^ 2).bijective

variable (K) in
@[expose] noncomputable def frobAut : MulAut (antiSp K) :=
  MulEquiv.ofBijective (frobHom K) frobHom_bijective

theorem frobAut_apply (g : antiSp K) : frobAut K g = frobHom K g :=
  rfl

theorem mat_frobAut (g : antiSp K) : mat (frobAut K g) = (mat g).map fun x => x ^ 2 :=
  glMat_frobHom g

theorem frobAut_eq_minorAut_sq : frobAut K = minorAut K ^ 2 :=
  MulEquiv.ext fun g => frobHom_eq_minorAut_sq g

theorem frobAut_minorAut (g : antiSp K) : frobAut K (minorAut K g) = minorAut K (frobAut K g) := by
  have h : Commute (minorAut K ^ 2) (minorAut K) := Commute.pow_left (Commute.refl _) 2
  rw [frobAut_eq_minorAut_sq]
  exact congrArg (fun α : MulAut (antiSp K) => α g) h.eq

theorem frobAut_pow_minorAut (k : ℕ) (g : antiSp K) :
    (frobAut K ^ k) (minorAut K g) = minorAut K ((frobAut K ^ k) g) := by
  induction k generalizing g with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, MulAut.mul_apply, MulAut.mul_apply, frobAut_minorAut, ih]

theorem frobAut_uElt (a b c d : K) :
    frobAut K (uElt a b c d) = uElt (a ^ 2) (b ^ 2) (c ^ 2) (d ^ 2) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  apply mat_ext
  rw [mat_frobAut]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, mat, glMat_uElt]
  linear_combination (a * b * d) * h2

theorem frobAut_aElt (v : Fin 2 → K) (c : K) :
    frobAut K (aElt v c) = aElt (fun i => v i ^ 2) (c ^ 2) := by
  rw [aElt, frobAut_uElt]
  simp [aElt]

theorem frobAut_sElt (M : SL₂ K) : frobAut K (sElt M) = sElt (frobSL K M) := by
  apply mat_ext
  rw [mat_frobAut, mat_sElt, mat_sElt]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sMat, frobSL, slFieldAut_apply, frobRingEquiv_apply]

theorem frobAut_dElt (l : Kˣ) : frobAut K (dElt l) = dElt (l ^ 2) := by
  apply mat_ext
  rw [mat_frobAut, mat_dElt, mat_dElt]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dMat]

theorem frobAut_mem_radA2_iff (x : antiSp K) : frobAut K x ∈ radA2 K ↔ x ∈ radA2 K := by
  constructor
  · rintro ⟨a, b, c, h⟩
    obtain ⟨a', ha⟩ := exists_sq_eq a
    obtain ⟨b', hb⟩ := exists_sq_eq b
    obtain ⟨c', hc⟩ := exists_sq_eq c
    refine ⟨a', b', c', (frobAut K).injective ?_⟩
    rw [h, frobAut_uElt, ha, hb, hc]
    simp
  · rintro ⟨a, b, c, rfl⟩
    exact ⟨a ^ 2, b ^ 2, c ^ 2, by rw [frobAut_uElt]; simp⟩

theorem frobAut_mem_radA1_iff (x : antiSp K) : frobAut K x ∈ radA1 K ↔ x ∈ radA1 K := by
  constructor
  · rintro ⟨b, c, d, h⟩
    obtain ⟨b', hb⟩ := exists_sq_eq b
    obtain ⟨c', hc⟩ := exists_sq_eq c
    obtain ⟨d', hd⟩ := exists_sq_eq d
    refine ⟨b', c', d', (frobAut K).injective ?_⟩
    rw [h, frobAut_uElt, hb, hc, hd]
    simp
  · rintro ⟨b, c, d, rfl⟩
    exact ⟨b ^ 2, c ^ 2, d ^ 2, by rw [frobAut_uElt]; simp⟩

theorem frobAut_mem_rootU₂_iff (x : antiSp K) : frobAut K x ∈ rootU₂ K ↔ x ∈ rootU₂ K := by
  constructor
  · rintro ⟨c, h⟩
    obtain ⟨c', hc⟩ := exists_sq_eq c
    refine ⟨c', (frobAut K).injective ?_⟩
    rw [h, frobAut_uElt, hc]
    simp
  · rintro ⟨c, rfl⟩
    exact ⟨c ^ 2, by rw [frobAut_uElt]; simp⟩

theorem frobAut_mem_rootU₁_iff (x : antiSp K) : frobAut K x ∈ rootU₁ K ↔ x ∈ rootU₁ K := by
  constructor
  · rintro ⟨b, h⟩
    obtain ⟨b', hb⟩ := exists_sq_eq b
    refine ⟨b', (frobAut K).injective ?_⟩
    rw [h, frobAut_uElt, hb]
    simp
  · rintro ⟨b, rfl⟩
    exact ⟨b ^ 2, by rw [frobAut_uElt]; simp⟩

theorem frobAut_mem_rootA_iff (i : Axis) (x : antiSp K) :
    frobAut K x ∈ rootA K i ↔ x ∈ rootA K i := by
  cases i
  · exact frobAut_mem_radA1_iff x
  · exact frobAut_mem_radA2_iff x

theorem frobAut_mem_rootU_iff (i : Axis) (x : antiSp K) :
    frobAut K x ∈ rootU K i ↔ x ∈ rootU K i := by
  cases i
  · exact frobAut_mem_rootU₁_iff x
  · exact frobAut_mem_rootU₂_iff x

theorem frobAut_pow_mem_iff {H : Subgroup (antiSp K)} (hH : ∀ x, frobAut K x ∈ H ↔ x ∈ H)
    (k : ℕ) (x : antiSp K) : (frobAut K ^ k) x ∈ H ↔ x ∈ H := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [pow_succ, MulAut.mul_apply, ih, hH]

theorem frobAut_rootCoord (i : Axis) (x : K) :
    frobAut K (rootCoord K i x) = rootCoord K i (x ^ 2) := by
  cases i
  · show frobAut K (uElt 0 x 0 0) = uElt 0 (x ^ 2) 0 0
    rw [frobAut_uElt]
    simp
  · show frobAut K (uElt 0 0 x 0) = uElt 0 0 (x ^ 2) 0
    rw [frobAut_uElt]
    simp

omit [Finite K] in
theorem rootCoord_injective (i : Axis) : Function.Injective (rootCoord K i) := by
  intro x y h
  cases i
  · exact (uElt_inj h).2.1
  · exact (uElt_inj h).2.2.1

theorem frobAut_sHom (i : Axis) (M : SL₂ K) :
    frobAut K (sHom K i M) = sHom K i (frobSL K M) := by
  cases i
  · show frobAut K (minorAut K (sElt M)) = minorAut K (sElt (frobSL K M))
    rw [frobAut_minorAut, frobAut_sElt]
  · exact frobAut_sElt M

end KCRootAxis

end CFSG.RankThree.PartOne
