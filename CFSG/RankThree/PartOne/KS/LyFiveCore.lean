module

public import CFSG.RankThree.PartOne.KS.LyFiveL1V
public import Certificates.Certificate14970
public import CFSG.RankThree.PartOne.KS.LyFiveCheck
public import CFSG.RankThree.PartOne.KS.LyFiveY
public import CFSG.RankThree.PartOne.KS.LyFiveXCore
public import CFSG.RankThree.PartOne.KS.LyFiveCover
public import CFSG.RankThree.PartOne.KS.LyFiveOuter
public import CFSG.Sporadic.Schreier.LyCheckSep
public import CFSG.Sporadic.Ly.KeySpec
public import CFSG.Sporadic.He.FpSpec
import Certificates.Kernel.SporSch.Ly.SepGlue
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.KS.PlaneWitness
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.Schreier.LyFixedSet

public section

namespace CFSG.RankThree.PartOne.LyFive

open CFSG.Sporadic.Ly CFSG.RankThree.Native Subgroup

theorem lyFive_cover_J :
    ∀ w : J, orderOf w = 5 → ∃ g : J, ∃ r ∈ ({lyFiveXJ, lyFiveVJ 0 * lyFiveVJ 1} : Set J),
      ∃ e : ℕ, 1 ≤ e ∧ e ≤ 4 ∧ g * w * g⁻¹ = r ^ e :=
  Certificates.certificate14970

theorem lyFive_card_x :
    Nat.card (Subgroup.centralizer ({lyFiveXJ} : Set J)) = 2250000 :=
  card_centralizer_xJ_eq_of_checks lyFive_check_class.1

theorem lyFive_card_y :
    Nat.card (Subgroup.centralizer ({lyFiveVJ 0 * lyFiveVJ 1} : Set J)) = 3750 :=
  card_centralizer_yJ_eq lyFive_check_class.2.1 lyFive_check_class1 lyFive_check_class.2.2

theorem fiveCore_J :
    FiveCore J :=
  fiveCore_of_cover (T := J) (x := lyFiveXJ) (y := lyFiveVJ 0 * lyFiveVJ 1) lyFive_cover_J
    lyFiveXJ_pow5 lyFiveYJ_pow5
    (fiveCoreAt'_xJ_of_checks lyFive_check_class.1)
    (fiveCoreAt'_yJ_of_checks lyFive_check_class.2.1 lyFive_check_class1 lyFive_check_class.2.2)

theorem lyFive_card_centralizer
    {w : J} (hw : orderOf w = 5) :
    Nat.card (Subgroup.centralizer ({w} : Set J)) = 2250000 ∨
      Nat.card (Subgroup.centralizer ({w} : Set J)) = 3750 := by
  have h := card_centralizer_of_cover (T := J) (x := lyFiveXJ) (y := lyFiveVJ 0 * lyFiveVJ 1)
    lyFive_cover_J lyFiveXJ_pow5 lyFiveYJ_pow5 hw
  rw [lyFive_card_x, lyFive_card_y] at h
  exact h

theorem lyFive_exists_involution
    {w : J} (hw : orderOf w = 5) :
    ∃ u : J, orderOf u = 2 ∧ u * w = w * u := by
  refine exists_involution_of_cover (T := J) (x := lyFiveXJ) (y := lyFiveVJ 0 * lyFiveVJ 1)
    lyFive_cover_J lyFiveXJ_pow5 lyFiveYJ_pow5 ?_ ?_ hw
  · refine exists_involution_of_even_card (T := J) ?_
    rw [lyFive_card_x]
    norm_num
  · refine exists_involution_of_even_card (T := J) ?_
    rw [lyFive_card_y]
    norm_num

theorem hpt_all_J
    {w : J} (hw : orderOf w = 5)
    {v : MulAut J} (hv : v * v = 1)
    (hfix : ∀ g ∈ Subgroup.centralizer ({w} : Set J), v g = g) : ∃ x : J, MulAut.conj x = v :=
  hpt_J hw (lyFive_exists_involution hw) hv hfix

theorem hpt_all_J_fun
    {w : J} (hw : orderOf w = 5)
    {f : J → J} (hmul : ∀ x y, f (x * y) = f x * f y) (hinv : ∀ x, f (f x) = x)
    (hfix : ∀ g ∈ Subgroup.centralizer ({w} : Set J), f g = g) :
    ∃ j : J, ∀ x, f x = j * x * j⁻¹ := by
  let v : MulAut J :=
    { toFun := f
      invFun := f
      left_inv := hinv
      right_inv := hinv
      map_mul' := hmul }
  have hv : v * v = 1 := MulEquiv.ext fun x => hinv x
  obtain ⟨j, hj⟩ := hpt_all_J hw hv (fun g hg => hfix g hg)
  refine ⟨j, fun x => ?_⟩
  have := congrArg (fun φ : MulAut J => φ x) hj
  simp only [MulAut.conj_apply] at this
  exact this.symm

end CFSG.RankThree.PartOne.LyFive
