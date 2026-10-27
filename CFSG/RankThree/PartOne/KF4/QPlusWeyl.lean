module

public import CFSG.RankThree.PartOne.KF4.Lattice3
public import CFSG.RankThree.PartOne.KE.EvenE7E8QPlusWeyl
public import CFSG.RankThree.Chevalley.SteinbergBTTrialitySplitPrimePlane

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
open CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.SteinbergBT.TrialityPlane
open scoped Matrix

@[expose] def qpCox : WeylGroup Tag.F4 :=
  (coxeterSystem Tag.F4).wordProd [f4Index 0, f4Index 1, f4Index 2, f4Index 3]

@[expose] def qpCoxMat : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ :=
  !![0, 1, 0, -1; 1, 1, 0, -1; 0, 2, 0, -1; 0, 0, 1, -1]

@[expose] def qpNeg : WeylGroup Tag.F4 := qpCox ^ 6

theorem weylMatrix_qpCox : weylMatrix qpCox = qpCoxMat :=
  weylMatrix_wordProd_of' (ω := [f4Index 0, f4Index 1, f4Index 2, f4Index 3])
    (by decide +kernel)

theorem weylMatrix_qpNeg : weylMatrix qpNeg = -1 := by
  have h6 : qpCoxMat ^ 6 = -1 := by decide +kernel
  rw [qpNeg, weylMatrix_pow, weylMatrix_qpCox, h6]

theorem qpNeg_smul (x : Fin Tag.F4.rank → ℤ) : qpNeg • x = -x := by
  rw [← weylMatrix_mulVec, weylMatrix_qpNeg, Matrix.neg_mulVec, Matrix.one_mulVec]

theorem qpNeg_comm (w : WeylGroup Tag.F4) : qpNeg * w = w * qpNeg := by
  apply weylMatrix_injective
  rw [weylMatrix_mul, weylMatrix_mul, weylMatrix_qpNeg]
  simp

section Rep

variable (M : Type) [Field M]

@[expose] def qpRep : ModGL Tag.F4 M := canonicalRep (coxeterSystem Tag.F4) M qpNeg

variable {M}

theorem qpRep_mem_monomial : qpRep M ∈ monomialSubgroup Tag.F4 M :=
  canonicalRep_mem_monomialSubgroup M qpNeg

theorem qpRep_mem_adjointGroup : qpRep M ∈ adjointGroup Tag.F4 M :=
  canonicalRep_mem_adjointGroup _ M qpNeg

theorem weylQuotientHom_qpRep :
    weylQuotientHom Tag.F4 M ⟨qpRep M, qpRep_mem_monomial⟩ = qpNeg :=
  weylQuotientHom_eq (mapsRootLines_canonicalRep qpNeg)

theorem weylQuotientHom_qpRep_smul (u : Fin Tag.F4.rank → ℤ) :
    weylQuotientHom Tag.F4 M ⟨qpRep M, qpRep_mem_monomial⟩ • u = -u := by
  rw [weylQuotientHom_qpRep, qpNeg_smul]

variable [CharP M 2]

theorem qpRep_comm (w : WeylGroup Tag.F4) :
    canonicalRep (coxeterSystem Tag.F4) M w * qpRep M =
      qpRep M * canonicalRep (coxeterSystem Tag.F4) M w := by
  rw [qpRep, ← qplus_canonicalRep_mul, ← qplus_canonicalRep_mul, qpNeg_comm]

theorem qpRep_conj_pinnedX {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot Tag.F4 α) (c : M) :
    qpRep M * pinnedX Tag.F4 M α c * (qpRep M)⁻¹ = pinnedX Tag.F4 M (-α) c := by
  have h2 : (2 : M) = 0 := CharP.cast_eq_zero M 2
  rw [qpRep, canonicalRep_mul_pinnedX_mul_inv_of_two h2 qpNeg hα c, qpNeg_smul]

omit [CharP M 2] in
theorem qpRep_conj_rootDiagUnit (a : Fin Tag.F4.rank → Mˣ) :
    qpRep M * rootDiagUnit Tag.F4 a * (qpRep M)⁻¹ = (rootDiagUnit Tag.F4 a)⁻¹ :=
  canonicalRep_conj_rootDiagUnit_of_neg qpNeg_smul a

theorem qpRep_conj_canonicalRep (w : WeylGroup Tag.F4) :
    qpRep M * canonicalRep (coxeterSystem Tag.F4) M w * (qpRep M)⁻¹ =
      canonicalRep (coxeterSystem Tag.F4) M w := by
  rw [← qpRep_comm w]
  group

end Rep

end CFSG.RankThree.PartOne.KF4
