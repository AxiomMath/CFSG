module

public import CFSG.LocalAnalysis.StandardType.GGLieInnerDiagDefs
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgUnitaryBlock
import CFSG.LocalAnalysis.StandardType.GGLieInnerDiagLinear
import CFSG.LocalAnalysis.StandardType.GGLieInnerDiagUnitarySelfDual
import CFSG.LocalAnalysis.StandardType.GGLieInnerDiagUnitaryPaired
import CFSG.LocalAnalysis.StandardType.GGLieInnerDiagUnitaryLift
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.LinUnitUnitaryBlocks
import CFSG.LocalAnalysis.StandardType.GGLieSU3FixedLift
import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherUnitary
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits

public section

namespace CFSG.StandardType.SCFourCover

section Unitary

open Polynomial CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.HardMathSupport.Solomon.Coordinator.LieComp

theorem ggInnerDiagOnComps_primeFormP_four {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) :
    GGInnerDiagOnComps (primeFormP h (idGram K 4)) := by
  classical
  intro x y hx3 hx1 hy3 hxy T hT hstab
  obtain ⟨A, B, c, hxA, hyB, hA3, hAB⟩ := exists_primeFormP_lift_four h hx3 hxy
  rw [hxA] at hT
  rw [hyB] at hstab ⊢
  have H : UnitaryPrimaryData h.bar (idForm h 4)
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin 4) K)) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks.primaryData_toLin'
      h A.2 Nat.prime_three (by norm_num) hA3
  have hq2 : 2 ≤ 2 ^ f :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.one_le
  obtain ⟨⟨a, ha⟩, hTa⟩ := exists_good_primaryFactor_of_component (h := h) (n := 4)
    (x := Matrix.GeneralLinearGroup.toLin (A : GL (Fin 4) K)) hq2 A rfl H T hT
  have hT' : T = unitaryBlockComponent h
      (x := Matrix.GeneralLinearGroup.toLin (A : GL (Fin 4) K)) (a : K[X]) := hTa
  subst hT'
  by_cases hself : dualPoly h.bar (a : K[X]) = a
  · exact Or.inr (Or.inl
      (ggUnitaryOn_unitaryBlock_selfDual h A B hA3 hAB a ha hself hT.2.2 hstab))
  · exact Or.inr (Or.inr
      (ggLinearOn_unitaryBlock_paired h A B hA3 hAB a ha hself hT.2.2 hstab))

end Unitary

open CFSG CFSG.Assembly in
theorem ggInnerDiagOnComps_suFour {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) :
    GGInnerDiagOnComps ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n)) := by
  let h := CFSG.StandardType.TableBU.unitaryFieldData_of_card hK hn
  let e : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n)) ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)) :=
    MulEquiv.ofBijective (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
      ⟨ggLieSU3Fixed_projMk_injective (K := K) (n := n) hK, QuotientGroup.mk'_surjective _⟩
  exact ggInnerDiagOnComps_of_mulEquiv
    (e.trans (CFSG.StandardType.InndiagSU.projEquiv h (d := 4) (by norm_num))).symm
    (ggInnerDiagOnComps_primeFormP_four h)

end CFSG.StandardType.SCFourCover

end
