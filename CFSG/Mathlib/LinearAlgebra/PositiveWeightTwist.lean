module

public import Mathlib.LinearAlgebra.Determinant
public import TauCeti.LinearAlgebra.Matrix.Diagonal

public noncomputable section

namespace CFSG.LinearAlgebra

open Polynomial

universe u v w
variable {k : Type u} [Field k] [Infinite k]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

theorem exists_det_one_sub_positive_diagonal_mul_ne_zero
    (A : Matrix ι ι k) (w : ι → ℕ) (hw : ∀ i, 0 < w i) :
    ∃ t : k, t ≠ 0 ∧ (1 - Matrix.diagonal (fun i => t ^ w i) * A).det ≠ 0 := by
  classical
  let P : Matrix ι ι k[X] :=
    1 - Matrix.diagonal (fun i => X ^ w i) * A.map C
  have hzero : (Polynomial.evalRingHom (0 : k)).mapMatrix P = 1 := by
    ext i j
    change Polynomial.eval (0 : k) (P i j) = (1 : Matrix ι ι k) i j
    by_cases hij : i = j
    · subst j
      simp [P, Matrix.diagonal_mul, (hw i).ne']
    · simp [P, Matrix.diagonal_mul, hij, (hw i).ne']
  have hdetzero : Polynomial.eval (0 : k) P.det = 1 := by
    change (Polynomial.evalRingHom (0 : k)) P.det = 1
    rw [(Polynomial.evalRingHom (0 : k)).map_det P, hzero, Matrix.det_one]
  have hP : P.det ≠ 0 := by
    intro h
    rw [h, Polynomial.eval_zero] at hdetzero
    exact zero_ne_one hdetzero
  have hXP : X * P.det ≠ 0 := mul_ne_zero Polynomial.X_ne_zero hP
  obtain ⟨t, ht⟩ : ∃ t : k, Polynomial.eval t (X * P.det) ≠ 0 := by
    by_contra! hn
    exact hXP (Polynomial.zero_of_eval_zero _ hn)
  rw [Polynomial.eval_mul, Polynomial.eval_X] at ht
  have ht0 : t ≠ 0 := (mul_ne_zero_iff.mp ht).1
  have hdt : Polynomial.eval t P.det ≠ 0 := (mul_ne_zero_iff.mp ht).2
  refine ⟨t, ht0, ?_⟩
  have hmap : (Polynomial.evalRingHom t).mapMatrix P =
      1 - Matrix.diagonal (fun i => t ^ w i) * A := by
    ext i j
    change Polynomial.eval t (P i j) = (1 - Matrix.diagonal (fun i => t ^ w i) * A) i j
    by_cases hij : i = j <;>
      simp [P, Matrix.diagonal_mul, hij] <;> ring
  change (Polynomial.evalRingHom t) P.det ≠ 0 at hdt
  rwa [(Polynomial.evalRingHom t).map_det P, hmap] at hdt

theorem exists_bijective_one_sub_positive_weight_twist
    {V : Type*} [AddCommGroup V] [Module k V]
    (b : Module.Basis ι k V) (w : ι → ℕ) (hw : ∀ i, 0 < w i)
    (D : kˣ → Module.End k V)
    (hD : ∀ (s : kˣ) (i : ι), D s (b i) = ((s : k) ^ w i) • b i)
    (F : Module.End k V) :
    ∃ s : kˣ, Function.Bijective ((LinearMap.id : Module.End k V) - (D s).comp F) := by
  classical
  let : Module.Finite k V := Module.Finite.of_basis b
  obtain ⟨t, ht, hdet⟩ := exists_det_one_sub_positive_diagonal_mul_ne_zero
    (LinearMap.toMatrix b b F) w hw
  let s : kˣ := Units.mk0 t ht
  have hdiag : LinearMap.toMatrix b b (D s) = Matrix.diagonal (fun i => t ^ w i) :=
    b.toMatrix_eq_diagonal_of_basis (D s) _ (fun i => by simpa only [s, Units.val_mk0] using hD s i)
  have hm : LinearMap.toMatrix b b (LinearMap.id - (D s).comp F) =
      1 - Matrix.diagonal (fun i => t ^ w i) * LinearMap.toMatrix b b F := by
    rw [map_sub, LinearMap.toMatrix_id b,
      LinearMap.toMatrix_comp (v₁ := b) (v₂ := b) (v₃ := b) (D s) F, hdiag]
  have hd : LinearMap.det (LinearMap.id - (D s).comp F) ≠ 0 := by
    rw [← LinearMap.det_toMatrix b, hm]
    exact hdet
  refine ⟨s, ?_⟩
  exact (LinearMap.equivOfDetNeZero (LinearMap.id - (D s).comp F) hd).bijective

theorem range_sup_eq_top_of_mapQ_surjective
    {R : Type*} [Ring R]
    {V : Type*} [AddCommGroup V] [Module R V]
    (N : Submodule R V) (F : Module.End R V)
    (hF : N ≤ N.comap F)
    (hs : Function.Surjective (N.mapQ N F hF)) : F.range ⊔ N = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨q, hq⟩ := hs (N.mkQ x)
  obtain ⟨y, hy⟩ := N.mkQ_surjective q
  rw [← hy, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.mkQ_apply] at hq
  have hN : x - F y ∈ N := (Submodule.Quotient.eq N).mp hq.symm
  exact Submodule.mem_sup.mpr ⟨F y, ⟨y, rfl⟩, x - F y, hN, by abel⟩

theorem exists_range_one_sub_comp_sup_eq_top_of_positive_quotient_weights
    {V : Type*} [AddCommGroup V] [Module k V]
    (N : Submodule k V) (b : Module.Basis ι k (V ⧸ N))
    (w : ι → ℕ) (hw : ∀ i, 0 < w i)
    (D : kˣ → Module.End k V) (hD : ∀ s, N ≤ N.comap (D s))
    (hweights : ∀ (s : kˣ) (i : ι),
      N.mapQ N (D s) (hD s) (b i) = ((s : k) ^ w i) • b i)
    (F : Module.End k V) (hF : N ≤ N.comap F) :
    ∃ s : kˣ, LinearMap.range (LinearMap.id - (D s).comp F) ⊔ N = ⊤ := by
  let DQ (s : kˣ) := N.mapQ N (D s) (hD s)
  let FQ := N.mapQ N F hF
  obtain ⟨s, hs⟩ := exists_bijective_one_sub_positive_weight_twist b w hw DQ hweights FQ
  have hp : N ≤ N.comap (LinearMap.id - (D s).comp F) := by
    intro x hx
    exact N.sub_mem hx (hD s (hF hx))
  have heq : N.mapQ N (LinearMap.id - (D s).comp F) hp =
      (LinearMap.id : Module.End k (V ⧸ N)) - (DQ s).comp FQ := by
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := N.mkQ_surjective q
    simp only [Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.sub_apply,
      LinearMap.id_apply, LinearMap.comp_apply, DQ, FQ]
    change N.mkQ (x - D s (F x)) = N.mkQ x - N.mkQ (D s (F x))
    exact map_sub N.mkQ _ _
  refine ⟨s, range_sup_eq_top_of_mapQ_surjective N _ hp ?_⟩
  rw [heq]
  exact hs.surjective

end CFSG.LinearAlgebra
