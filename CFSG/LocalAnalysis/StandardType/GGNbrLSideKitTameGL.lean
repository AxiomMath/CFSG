module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsDefs
import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitComm
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3LInput
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD76c
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDown
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultSporadic
public import CFSG.LocalAnalysis.GLTheoremA.S4.YS02Holds
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Transitive
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Inputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.Sporadic.HeldB.Common
public import Certificates.Certificate14953
public import Certificates.Certificate7233Base
public import Certificates.Certificate8166

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Open.StatedAPI

private theorem kitTame_range_eq_commutator_of_perfect {X B Ab : Type*} [Group X] [Group B]
    [CommGroup Ab] (θ : X →* B) (hX : commutator X = ⊤) (D : B →* Ab) (hD : D.ker ≤ θ.range) :
    θ.range = commutator B := by
  refine le_antisymm ?_ ?_
  · rw [MonoidHom.range_eq_map, ← hX, _root_.commutator_def, Subgroup.map_commutator,
      _root_.commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  · refine le_trans ?_ hD
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)

private theorem kitTame_isSolvable_gl_of_le_one {E : Type*} [Field E] {m : ℕ} (hm : m ≤ 1) :
    Group.IsSolvable (Matrix.GeneralLinearGroup (Fin m) E) := by
  refine Group.isSolvable_of_comm fun a b => Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm with rfl | rfl
  · exact Matrix.ext fun i => i.elim0
  · ext i j
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_one, Fin.sum_univ_one,
      Subsingleton.elim i 0, Subsingleton.elim j 0]
    exact mul_comm _ _

private theorem kitTame_group_gl (r : ℕ) (K : Type) [Field K] [Finite K] :
    CFSG.IsQuasisimple ↥(commutator (Matrix.GeneralLinearGroup (Fin r) K)) ∨
      Group.IsSolvable (Matrix.GeneralLinearGroup (Fin r) K) := by
  classical
  haveI := Fintype.ofFinite K
  rcases Nat.lt_or_ge r 2 with hr | hr
  · right
    haveI : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin r) K) :=
      kitTame_isSolvable_gl_of_le_one (by omega)
    infer_instance
  · by_cases hsmall : r = 2 ∧ Nat.card K ≤ 3
    · right
      obtain ⟨rfl, hK3⟩ := hsmall
      have hcard : Nat.card K = 2 ∨ Nat.card K = 3 := by
        have h2 : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
        omega
      haveI : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) K) :=
        CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable K hcard
      infer_instance
    · left
      have hcond : 3 ≤ r ∨ ∃ s : Finset K, s.card = 4 := by
        rcases Nat.lt_or_ge r 3 with h3 | h3
        · have hr2 : r = 2 := by omega
          subst hr2
          right
          have h4 : 4 ≤ Nat.card K := by
            have h2 : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
            by_contra hcon
            exact hsmall ⟨rfl, by omega⟩
          have h4' : 4 ≤ (Finset.univ : Finset K).card := by
            simpa [Nat.card_eq_fintype_card] using h4
          obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4'
          exact ⟨s, hs⟩
        · exact Or.inl h3
      have hqSL : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin r) K) :=
        CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_SL hr hcond
      have hperf : commutator (Matrix.SpecialLinearGroup (Fin r) K) = ⊤ :=
        Group.isPerfect_def.mp hqSL.1
      let θ : Matrix.SpecialLinearGroup (Fin r) K →* Matrix.GeneralLinearGroup (Fin r) K :=
        Matrix.SpecialLinearGroup.toGL
      have hθ : θ.range = commutator (Matrix.GeneralLinearGroup (Fin r) K) := by
        refine kitTame_range_eq_commutator_of_perfect θ hperf
          (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin r) K →* Kˣ) fun g hg => ?_
        rw [MonoidHom.mem_ker] at hg
        have hdet : (g : Matrix (Fin r) (Fin r) K).det = 1 := by
          have := congrArg Units.val hg
          simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
        exact ⟨⟨g, hdet⟩, Units.ext rfl⟩
      have e : Matrix.SpecialLinearGroup (Fin r) K ≃*
          ↥(commutator (Matrix.GeneralLinearGroup (Fin r) K)) :=
        (Subgroup.topEquiv.symm.trans
            (Subgroup.equivMapOfInjective (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin r) K))
              θ Matrix.SpecialLinearGroup.toGL_injective)).trans
          (MulEquiv.subgroupCongr ((MonoidHom.range_eq_map θ).symm.trans hθ))
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e hqSL

theorem ggNbrLSideTame_gl {X : Type} [Group X] {A : Subgroup X} {r : ℕ} {K : Type} [Field K]
    [Finite K] (φ : ↥A ≃* GL (Fin r) K) :
    CFSG.IsQuasisimple ↥⁅A, A⁆ ∨ Group.IsSolvable ↥A := by
  exact CFSG.StandardType.GGNbrLSideKit.tame_of_mulEquiv φ (kitTame_group_gl r K)

end CFSG.StandardType
