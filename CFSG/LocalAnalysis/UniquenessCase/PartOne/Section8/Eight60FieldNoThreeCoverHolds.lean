module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight60FieldAssembly
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LieType.Steinberg.CentralExt.PSLMultiplier
import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
import CFSG.LieType.Steinberg.CentralExt.UnitaryPerfect
import CFSG.LocalAnalysis.ComponentClassification.Helpers
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Mult
public import CFSG.Blueprint.LieModelAPI
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LieType.CurtisTits.Symplectic
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatch
import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Core
import CFSG.RankThree.PartTwo.Sec19.Item194Used

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open (StatedProj StatedSL StatedSU)
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)

private theorem eight60FieldNTC_isQuasisimple {K : Type} [Group K]
    (hq : CFSG.Open.IsQuasisimple K) : CFSG.IsQuasisimple K :=
  ⟨⟨hq.1⟩, hq.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hq⟩

private theorem eight60FieldNTC_finite {X : Type} [Group X] {Q : Type} [Group Q] [Finite Q]
    (e : X ⧸ Subgroup.center X ≃* Q) (hc : Nat.card (Subgroup.center X) = 3) : Finite X := by
  have h1 : Finite (Subgroup.center X) := Nat.finite_of_card_ne_zero (by omega)
  have h2 : Finite (X ⧸ Subgroup.center X) := Finite.of_equiv Q e.symm.toEquiv
  exact Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := Subgroup.center X)).symm

private theorem eight60FieldNTC_psl {X : Type} [Group X] {p f : ℕ}
    (hX : ThreeCover (fun Y _ => LieModel Y .PSL 5 p f) X) : False := by
  obtain ⟨hq, hc, hS⟩ := hX
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hS.statedClassicalModel_of_ne_zero (by norm_num)
  have : Fintype K := Fintype.ofFinite K
  let e' : X ⧸ Subgroup.center X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 5) K :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 5 K).symm
  have : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 5) K) := inferInstance
  have := eight60FieldNTC_finite e' hc
  obtain ⟨-, ⟨row⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_hopfMultiplier_of_five_le (k := K) (n := 5)
      (by norm_num)
  have hcard : Nat.card (Multiplicative (ZMod (Nat.gcd 5 (Fintype.card K - 1)))) =
      Nat.gcd 5 (Fintype.card K - 1) := by
    have : NeZero (Nat.gcd 5 (Fintype.card K - 1)) :=
      ⟨(Nat.gcd_pos_of_pos_left _ (by norm_num)).ne'⟩
    simp
  have hdvd := CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.card_center_dvd_of_row
    (eight60FieldNTC_isQuasisimple hq) e' ⟨row⟩ hcard
  rw [hc] at hdvd
  have h35 : 3 ∣ 5 := hdvd.trans (Nat.gcd_dvd_left _ _)
  omega

private theorem eight60FieldNTC_psu
    {X : Type} [Group X] {p f : ℕ}
    (hX : ThreeCover (fun Y _ => LieModel Y .PSU 5 p f) X) : False := by
  obtain ⟨hq, hc, hS⟩ := hX
  obtain ⟨⟨hp, hf, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hS.statedClassicalModel_of_ne_zero (by norm_num)
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := CFSG.LieType.Steinberg.charP_of_card_eq_sq_pow hp hK
  have : Finite (StatedProj (StatedSU 5 (p ^ f) K)) := inferInstance
  have := eight60FieldNTC_finite e hc
  obtain ⟨-, ⟨row⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SUOdd.psu_odd_hopfMultiplier (F := K) (p := p) (f := f) hK
      (by omega) (n := 5) (by norm_num) (by decide) (by simp)
  have hcard : Nat.card (Multiplicative (ZMod (Nat.gcd 5 (p ^ f + 1)))) = Nat.gcd 5 (p ^ f + 1) := by
    have : NeZero (Nat.gcd 5 (p ^ f + 1)) := ⟨(Nat.gcd_pos_of_pos_left _ (by norm_num)).ne'⟩
    simp
  have hdvd := CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.card_center_dvd_of_row
    (eight60FieldNTC_isQuasisimple hq) e ⟨row⟩ hcard
  rw [hc] at hdvd
  have h35 : 3 ∣ 5 := hdvd.trans (Nat.gcd_dvd_left _ _)
  omega

theorem eight60FieldNoThreeCover_holds :
    Eight60FieldNoThreeCover :=
  fun _ _ _ _ => ⟨eight60FieldNTC_psl, eight60FieldNTC_psu⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
