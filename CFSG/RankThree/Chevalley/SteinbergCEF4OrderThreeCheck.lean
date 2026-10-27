module

public import CFSG.RankThree.Chevalley.SteinbergCEF4LatticeTools

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 RootSpace
  CFSG.LieType.Steinberg.Adjoint

namespace F4Weyl

@[expose] def f4OrderThreeMatrix : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ :=
  !![0, 1, -1, 0; 1, 1, -1, -1; 2, 2, -2, -1; 0, 2, -1, -1]

theorem weylMatrix_f4OrderThree : weylMatrix (f4Coxeter ^ 4) = f4OrderThreeMatrix := by
  rw [f4Coxeter_pow, weylMatrix_f4WordProd]
  decide

theorem f4OrderThreeMatrix_relation :
    f4OrderThreeMatrix * f4OrderThreeMatrix + f4OrderThreeMatrix + 1 = 0 := by
  decide

theorem f4OrderThreeMatrix_ne_one : f4OrderThreeMatrix ≠ 1 := by
  decide

theorem f4OrderThreeMatrix_cube :
    f4OrderThreeMatrix * f4OrderThreeMatrix * f4OrderThreeMatrix = 1 := by
  decide

theorem f4OrderThree_relation (x : Fin Tag.F4.rank → ℤ) :
    (1 : ℤ) • ((f4Coxeter ^ 4) • ((f4Coxeter ^ 4) • x)) + (1 : ℤ) • ((f4Coxeter ^ 4) • x) +
      (1 : ℤ) • x = 0 := by
  simp only [one_smul, ← weylMatrix_mulVec]
  rw [weylMatrix_f4OrderThree]
  have h : (f4OrderThreeMatrix * f4OrderThreeMatrix + f4OrderThreeMatrix + 1).mulVec x = 0 := by
    rw [f4OrderThreeMatrix_relation, Matrix.zero_mulVec]
  rwa [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at h

theorem orderOf_f4OrderThree : orderOf (f4Coxeter ^ 4) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ ?_
  · apply weylMatrix_injective
    rw [weylMatrix_pow, weylMatrix_f4OrderThree, weylMatrix_one, pow_three, ← mul_assoc,
      f4OrderThreeMatrix_cube]
  · intro h
    apply f4OrderThreeMatrix_ne_one
    rw [← weylMatrix_f4OrderThree, h, weylMatrix_one]

@[expose] def f4OrderThreeBasis : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ :=
  Matrix.of fun (i j : Fin Tag.F4.rank) =>
    (![Pi.single (f4Index 0) 1, (f4Coxeter ^ 4) • Pi.single (f4Index 0) 1,
      Pi.single (f4Index 2) 1, (f4Coxeter ^ 4) • Pi.single (f4Index 2) 1] :
        Fin 4 → Fin Tag.F4.rank → ℤ) j i

@[expose] def f4OrderThreeBasisMatrix : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ :=
  !![1, 0, 0, -1; 0, 1, 0, -1; 0, 2, 1, -2; 0, 0, 0, -1]

theorem f4OrderThreeBasis_eq : f4OrderThreeBasis = f4OrderThreeBasisMatrix := by
  rw [f4OrderThreeBasis, f4Coxeter_pow, f4WordProd_smul, f4WordProd_smul]
  decide

theorem det_f4OrderThreeBasis : f4OrderThreeBasis.det = -1 := by
  rw [f4OrderThreeBasis_eq]
  have h : detLaplace 4 f4OrderThreeBasisMatrix = -1 := by decide
  exact (detLaplace_eq_det 4 f4OrderThreeBasisMatrix).symm.trans h

theorem bijective_mulVec_f4OrderThreeBasis : Function.Bijective f4OrderThreeBasis.mulVec := by
  have hdet : IsUnit f4OrderThreeBasis.det := by
    rw [det_f4OrderThreeBasis]
    exact isUnit_one.neg
  have h1 := Matrix.mul_nonsing_inv f4OrderThreeBasis hdet
  have h2 := Matrix.nonsing_inv_mul f4OrderThreeBasis hdet
  refine ⟨fun x y hxy => ?_, fun y => ⟨f4OrderThreeBasis⁻¹.mulVec y, ?_⟩⟩
  · have := congrArg f4OrderThreeBasis⁻¹.mulVec hxy
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec,
      Matrix.one_mulVec] at this
  · rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

theorem order_three_restriction_check :
    ∀ J : Finset (Fin Tag.F4.rank), J.Nonempty → J ≠ Finset.univ →
      ∀ c₀ ∈ colChoices J (f4Index 0), ∀ c₁ ∈ colChoices J (f4Index 1),
        ∀ c₂ ∈ colChoices J (f4Index 2), ∀ c₃ ∈ colChoices J (f4Index 3),
        (∀ i ∈ J, colMap (cols4 c₀ c₁ c₂ c₃) (cols4 c₀ c₁ c₂ c₃ i) + cols4 c₀ c₁ c₂ c₃ i +
          Pi.single i 1 = 0) →
        (∀ β ∈ parabolicRootList J, colMap (cols4 c₀ c₁ c₂ c₃) β ∈ parabolicRootList J) →
        (J = {f4Index 0, f4Index 1} ∧
          (cols4 c₀ c₁ c₂ c₃ = (fun i => if i ∈ J then f4WordAct [0, 1] (Pi.single i 1) else 0) ∨
            cols4 c₀ c₁ c₂ c₃ =
              (fun i => if i ∈ J then f4WordAct [1, 0] (Pi.single i 1) else 0))) ∨
        (J = {f4Index 2, f4Index 3} ∧
          (cols4 c₀ c₁ c₂ c₃ = (fun i => if i ∈ J then f4WordAct [2, 3] (Pi.single i 1) else 0) ∨
            cols4 c₀ c₁ c₂ c₃ =
              (fun i => if i ∈ J then f4WordAct [3, 2] (Pi.single i 1) else 0))) := by
  decide +kernel

theorem parabolicRootList_card_01 :
    (parabolicRootList {f4Index 0, f4Index 1}).toFinset.card = 6 := by
  decide

theorem parabolicRootList_card_23 :
    (parabolicRootList {f4Index 2, f4Index 3}).toFinset.card = 6 := by
  decide

theorem iform_parabolicRootList_01 :
    ∀ β ∈ parabolicRootList {f4Index 0, f4Index 1}, iform β β = 4 := by
  decide

theorem iform_parabolicRootList_23 :
    ∀ β ∈ parabolicRootList {f4Index 2, f4Index 3}, iform β β = 2 := by
  decide

end F4Weyl

end CFSG.RankThree.Chevalley
