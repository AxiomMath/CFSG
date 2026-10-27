module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6BridgeScalars
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.CTP.SpSwap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.Sp6Bridge

open Matrix CFSG.Open Module Representation
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.RankThree.PartOne.CTP
open scoped MatrixGroups

variable {K k : Type} [Field K] [Field k]

@[expose] noncomputable def symplecticMatrices {r : ℕ} {G : Type} [Group G]
    (π : G →* StatedSp r K) : G →* Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  (mat r K).comp π

theorem factorsFinrankLe_shortBlock (φ : K →+* k) :
    FactorsFinrankLe (matrixMapRep
      (symplecticMatrices (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1))) φ) 2 := by
  apply factorsFinrankLe_matrixMapRep_of_lower_block_zero
  intro g i j
  rw [show symplecticMatrices (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1)) g =
    mat 2 K (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1) g) from rfl, mat_shortBlock]
  rfl

theorem factorsFinrankLe_longBlock (φ : K →+* k) :
    FactorsFinrankLe (matrixMapRep (symplecticMatrices (longBlock K 2 1)) φ) 2 := by
  let e : Fin 2 ⊕ Fin 2 ≃ Fin 2 ⊕ Fin 2 :=
    { toFun := Sum.elim
        (fun i => if i = 0 then Sum.inl 1 else Sum.inr 1)
        (fun i => if i = 0 then Sum.inl 0 else Sum.inr 0)
      invFun := Sum.elim
        (fun i => if i = 0 then Sum.inr 0 else Sum.inl 0)
        (fun i => if i = 0 then Sum.inr 1 else Sum.inl 1)
      left_inv := by rintro (i | i) <;> fin_cases i <;> rfl
      right_inv := by rintro (i | i) <;> fin_cases i <;> rfl }
  apply factorsFinrankLe_of_equiv
    (reindexMatrixRepEquiv (symplecticMatrices (longBlock K 2 1)) φ e).symm
  apply factorsFinrankLe_matrixMapRep_of_lower_block_zero
  intro g i j
  change mat 2 K (longBlock K 2 1 g) (e (Sum.inr i)) (e (Sum.inl j)) = 0
  rw [mat_longBlock]
  fin_cases i <;> fin_cases j <;> simp [e, CFSG.LieType.Steinberg.Sp.blockMat]

section Powers

variable [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem matrixMapRep_fieldSp {G : Type} [Group G] (π : G →* StatedSp 2 K)
    (σ : K ≃+* K) (φ : K →+* k) :
    matrixMapRep (symplecticMatrices ((CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp
      2 K σ).toMonoidHom.comp π)) φ =
      matrixMapRep (symplecticMatrices π) (φ.comp σ.toRingHom) := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  ext i
  change (((mat 2 K (π g)).map σ).map φ *ᵥ v) i =
    ((mat 2 K (π g)).map (φ.comp σ.toRingHom) *ᵥ v) i
  rw [Matrix.map_map]
  rfl

theorem factorsFinrankLe_exceptional_pow_blocks : ∀ j : ℕ, ∀ φ : K →+* k,
    FactorsFinrankLe (matrixMapRep (symplecticMatrices
      ((exceptionalSpAut K ^ j).toMonoidHom.comp
        (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1)))) φ) 2 ∧
    FactorsFinrankLe (matrixMapRep (symplecticMatrices
      ((exceptionalSpAut K ^ j).toMonoidHom.comp (longBlock K 2 1))) φ) 2 := by
  intro j
  induction j using Nat.twoStepInduction with
  | zero =>
    intro φ
    simpa using ⟨factorsFinrankLe_shortBlock φ, factorsFinrankLe_longBlock φ⟩
  | one =>
    intro φ
    obtain ⟨Fr, hFr⟩ := exists_frobenius_equiv (K := K)
    have hs : (exceptionalSpAut K).toMonoidHom.comp
        (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1)) =
        (longBlock K 2 1).comp (Matrix.SpecialLinearGroup.map (n := Fin 2) Fr.toRingHom) :=
      MonoidHom.ext fun A => exceptionalSpAut_shortBlock hFr A
    have hl : (exceptionalSpAut K).toMonoidHom.comp (longBlock K 2 1) =
        shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1) :=
      MonoidHom.ext fun A => exceptionalSpAut_longBlock A
    simp only [pow_one, hs, hl]
    constructor
    · change FactorsFinrankLe ((matrixMapRep (symplecticMatrices (longBlock K 2 1)) φ).comp
        (Matrix.SpecialLinearGroup.map (n := Fin 2) Fr.toRingHom)) 2
      exact factorsFinrankLe_comp _ _ (factorsFinrankLe_longBlock φ)
    · exact factorsFinrankLe_shortBlock φ
  | more j ih _ =>
    intro φ
    obtain ⟨Fr, hFr⟩ := exists_frobenius_equiv (K := K)
    have hpow : (exceptionalSpAut K ^ (j + 2)).toMonoidHom =
        (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp 2 K Fr).toMonoidHom.comp
          (exceptionalSpAut K ^ j).toMonoidHom := by
      apply MonoidHom.ext
      intro g
      change (exceptionalSpAut K ^ (j + 2)) g =
        CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp 2 K Fr
          ((exceptionalSpAut K ^ j) g)
      rw [show j + 2 = 2 + j by omega, pow_add, MulAut.mul_apply, pow_two,
        MulAut.mul_apply, exceptionalSpAut_sq hFr]
    simp only [hpow, MonoidHom.comp_assoc]
    rw [matrixMapRep_fieldSp, matrixMapRep_fieldSp]
    exact ih (φ.comp Fr.toRingHom)

end Powers

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.Sp6Bridge
