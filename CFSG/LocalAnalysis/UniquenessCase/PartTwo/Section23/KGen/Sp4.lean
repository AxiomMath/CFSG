module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KGen.Core
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KGen.PerfectLine
import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusInverters
import CFSG.GH74.GLS.Stage4.T2P56Core
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.Module
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KGen

open CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open Matrix

private def sl2M (K : Type) [Field K] : SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, -1; 1, -1], by simp [Matrix.det_fin_two_of]⟩

private lemma sl2M_pow_three (K : Type) [Field K] : sl2M K ^ 3 = 1 := by
  rw [show (3 : ℕ) = 1 + 1 + 1 from rfl, pow_succ, pow_succ, pow_one]
  apply Subtype.ext
  change (!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) K) * !![0, -1; 1, -1] *
    !![0, -1; 1, -1] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private lemma sl2M_ne_one (K : Type) [Field K] : sl2M K ≠ 1 := fun h => by
  have h00 := congrArg (fun A : SpecialLinearGroup (Fin 2) K =>
    (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp [sl2M] at h00

private lemma orderOf_sl2M (K : Type) [Field K] : orderOf (sl2M K) = 3 :=
  orderOf_eq_prime (sl2M_pow_three K) (sl2M_ne_one K)

private lemma lam_one_mulVec_single_inl_zero (K : Type) [Field K]
    (g : SpecialLinearGroup (Fin 2) K) :
    (((lam (1 : Fin 2) g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ Pi.single (Sum.inl (0 : Fin 2)) 1 =
      Pi.single (Sum.inl (0 : Fin 2)) 1 := by
  rw [coe_lam, Matrix.mulVec_single_one]
  funext x
  rw [Matrix.col_apply,
    pairMat_apply_of_ne' (y := Sum.inl (0 : Fin 2))
      (g := (g : Matrix (Fin 2) (Fin 2) K)) (x := x) (by simp) (by simp),
    Matrix.one_eq_pi_single, Pi.single_apply, Pi.single_apply]
  simp only [eq_comm]

private lemma lam_zero_sl2W_mulVec (K : Type) [Field K] :
    (((lam (0 : Fin 2) (sl2W : SpecialLinearGroup (Fin 2) K) : StatedSp 2 K) :
        GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        Pi.single (Sum.inl (0 : Fin 2)) 1 =
      Pi.single (Sum.inr (0 : Fin 2)) 1 := by
  rw [coe_lam_sl2W, Matrix.mulVec_single_one]
  funext x
  rw [Matrix.col_apply, CFSG.LieType.Universal.SpecialLinear.signedPerm_apply,
    Equiv.swap_apply_left, Pi.single_apply]
  simp

private lemma lam_zero_sl2W_not_mem_lineStab (K : Type) [Field K] :
    (lam (0 : Fin 2) (sl2W : SpecialLinearGroup (Fin 2) K) : StatedSp 2 K) ∉
      KTabD.lineStab (StatedSp 2 K) (Pi.single (Sum.inl (0 : Fin 2)) 1) := by
  rw [KTabD.mem_lineStab]
  rintro ⟨c, hc⟩
  have h := congrFun hc (Sum.inr (0 : Fin 2))
  rw [lam_zero_sl2W_mulVec] at h
  simp at h

theorem genLine_statedSp_two {K : Type} [Field K] [Finite K] (hK : 4 ≤ Nat.card K) :
    KGenProof.GenLine 3 (StatedSp 2 K) (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) := by
  refine genLine_of_perfect (L₀ := (lam (1 : Fin 2)).range) (g := lam (1 : Fin 2) (sl2M K))
    (w₀ := lam (0 : Fin 2) (sl2W : SpecialLinearGroup (Fin 2) K)) ?_ ?_ ⟨sl2M K, rfl⟩ ?_
    (by norm_num) (lam_zero_sl2W_not_mem_lineStab K) ?_
  · rintro _ ⟨g, rfl⟩
    exact lam_one_mulVec_single_inl_zero K g
  · exact CFSG.GH74.GLS.Stage4.Rest.perfect_of_sl2
      (MonoidHom.ofInjective (lam_injective (1 : Fin 2))).symm hK
  · rw [orderOf_lam]
    exact orderOf_sl2M K
  · rw [(commute_lam_lam (i := 0) (j := 1) (by decide) (sl2W : SpecialLinearGroup (Fin 2) K)
      (sl2M K)).mul_inv_cancel]
    exact Subgroup.mem_zpowers _

end CFSG.LocalAnalysis.UniquenessCase.UC22.KGen
