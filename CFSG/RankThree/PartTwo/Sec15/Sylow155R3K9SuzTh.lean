module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3K9CritJ2
public import Certificates.Certificate1020
public import Certificates.Certificate1021
public import Certificates.Certificate1022
public import Certificates.Certificate2289
public import Certificates.Certificate2292
public import Certificates.Certificate2293
public import Certificates.Certificate2294
public import Certificates.Certificate2295
public import Certificates.Certificate2304
public import Certificates.Certificate2305
public import Certificates.Certificate2306
public import Certificates.Certificate2308
public import Certificates.Certificate2309
public import Certificates.Certificate2311
public import Certificates.Certificate2313
public import Certificates.Certificate2314
public import Certificates.Certificate2315
public import Certificates.Certificate2317
public import Certificates.Certificate2321
public import Certificates.Certificate2322
public import Certificates.Certificate2323
public import Certificates.Certificate2324
public import Certificates.Certificate2325
public import Certificates.Certificate3173
public import Certificates.Certificate9130
public import Certificates.Certificate9131
public import Certificates.Certificate9219
public import Certificates.Certificate9220
public import Certificates.Certificate10012
public import Certificates.Certificate10088
public import Certificates.Certificate10089
public import Certificates.Certificate10090
public import Certificates.Certificate10091
public import Certificates.Certificate10092
public import Certificates.Certificate13637
public import Certificates.Certificate13650
public import Certificates.Certificate13651
public import Certificates.Certificate17251
public import Certificates.Certificate17252
public import Certificates.Certificate17305
public import Certificates.Certificate17306
public import Certificates.Certificate17307
public import Certificates.Certificate17320
public import Certificates.Certificate17321
public import Certificates.Certificate17322
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzA
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzB
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzFuse
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThCensus
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThShapeZ
import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.ThThree
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzThree
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThThreeClose
import CFSG.RankThree.PartOne.SPOR.Outer
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSporThCent
import CFSG.Sporadic.Bridge.SuzSurj
import CFSG.Sporadic.Bridge.ThSurj
import CFSG.Sporadic.SuzOddCore.Outer
import CFSG.Sporadic.SuzOddCore.Perms
import CFSG.Sporadic.SuzOddCore.SmallModel
import CFSG.Sporadic.Th
import CFSG.Sporadic.Th.Setup
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47LThree
public import CFSG.RankThree.PartTwo.Sec4.Item47SpFour
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.ThBase
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Certificates.Certificate3173Base
public import Certificates.Certificate9131Base
import CFSG.GH74.GLS.Balance.SolvAPIDefs
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThCentU
import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
import CFSG.RankThree.PartTwo.Sec11.Inverter1118Proof
import CFSG.RankThree.PartTwo.Sec11.Inverter1118ProofSteps
import CFSG.RankThree.PartTwo.Sec11.Item1121Proof
import CFSG.RankThree.PartTwo.Sec11.Item119K
import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL
import CFSG.RankThree.PartTwo.Sec20.OneSteps
import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
import CFSG.RankThree.PartTwo.Sec4.Item41NarrowGriess
import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
import CFSG.Walter.J1Props
import Certificates.Certificate8166

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG.RankThree.PartTwo.Sec4 (Spor)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

private theorem forall_goodJ2_of_mulEquiv {T T' : Type} [Group T] [Group T'] (e : T ≃* T')
    (h : ∀ x : T', orderOf x = 3 → GoodJ2 (Subgroup.centralizer ({x} : Set T'))) :
    ∀ x : T, orderOf x = 3 → GoodJ2 (Subgroup.centralizer ({x} : Set T)) := fun x hx =>
  GoodJ2.of_mulEquiv_centralizer e (h (e x) (by rwa [MulEquiv.orderOf_eq]))

private theorem not_dvd_j2_of_dvd_of_le {n : ℕ} (h37 : 3 ^ 7 ∣ n) (h13 : 13 ∣ n)
    (hle : n ≤ 63685439) (hpos : 0 < n) : ¬ 604800 ∣ n := by
  intro h
  have h' : 3 ^ 7 * 13 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h37 h13
  have h1 : Nat.lcm 604800 (3 ^ 7 * 13) ∣ n := Nat.lcm_dvd h h'
  have h2 : Nat.lcm 604800 (3 ^ 7 * 13) = 636854400 := by norm_num
  have h3 : 636854400 ≤ n := h2 ▸ Nat.le_of_dvd hpos h1
  exact absurd (h3.trans hle) (by norm_num)

section Suz

open CFSG.HardMathSupport.Dickson.I271 (fuseXA fuseXB fuseXA_pow fuseXB_pow suz_exists_conj_classes
  aSub_eq card_aSub)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT (yPerm yPerm_pow Cy_eq)
open CFSG.Sporadic.SuzOddCore (suzM suzEquivM)


private theorem goodJ2_suz_B :
    GoodJ2 (Subgroup.centralizer ({fuseXB} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) := by
  obtain ⟨hcard, -, hle, hnorm, hcent⟩ := CFSG.HardMathSupport.Dickson.I271.TabSuzB.caseB_spec
  exact goodJ2_of_selfCentralizing3 hle hnorm
    (IsPGroup.of_card (n := 6) (by rw [hcard]; norm_num)) hcent (by rw [hcard]; norm_num)

private theorem goodJ2_suz_C :
    GoodJ2 (Subgroup.centralizer ({yPerm} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) := by
  obtain ⟨hCeq, hcard⟩ := Cy_eq
  rw [← hCeq]
  exact goodJ2_of_not_dvd_twentyFive (by rw [hcard]; norm_num)

private theorem goodJ2_suz_A :
    GoodJ2 (Subgroup.centralizer ({fuseXA} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) := by
  rw [← aSub_eq]
  exact goodJ2_of_not_dvd_twentyFive (by rw [card_aSub]; norm_num)


private theorem goodJ2_suz (x : Equiv.Perm (Fin 1782)) (hx : x ∈ suzM) (hxo : orderOf x = 3) :
    GoodJ2 (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) := by
  obtain ⟨k, hk, c, hc, e, he, rfl⟩ := suz_exists_conj_classes hx hxo
  rcases hc with rfl | rfl | rfl
  · exact GoodJ2.conj hk fuseXA_pow he goodJ2_suz_A
  · exact GoodJ2.conj hk fuseXB_pow he goodJ2_suz_B
  · exact GoodJ2.conj hk yPerm_pow he goodJ2_suz_C


private theorem noCfgJ2_suz :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .Suz) → NoCfgJ2 S := by
  intro S _ _ _ hna ⟨e⟩
  have hout : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Suz)) := by
    rw [CFSG.Sporadic.SuzOddCore.outer_carrier_suz.1]
    norm_num
  exact noCfgJ2_of_subgroupModel (e.trans suzEquivM)
    (CFSG.RankThree.PartTwo.Sec4.RonanK429H.center_eq_bot_of_simple_nonab hna)
    (CFSG.RankThree.PartTwo.Sec4.RonanK429H.not_three_dvd_outer_of_mulEquiv e hout) goodJ2_suz


theorem rowOfK9_suz : RowOfK9 (Spor .Suz) :=
  rowOfK9_spor (s := .Suz) CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv noCfgJ2_suz

end Suz

section Th

open CFSG.Sporadic.Th (J thEquivJ)
open CFSG.HardMathSupport.Dickson.I271 (thS thZ thU th_census th_orderOf card_centralizer_zJ_dvd)


private theorem goodJ2_thZ :
    GoodJ2 (Subgroup.centralizer ({thZ} : Set ↥J)) :=
  goodJ2_of_card_dvd (M := 2 ^ 3 * 3 ^ 10) card_centralizer_zJ_dvd (by norm_num)

private theorem goodJ2_thU :
    GoodJ2 (Subgroup.centralizer ({thU} : Set ↥J)) :=
  goodJ2_of_not_dvd_twentyFive (by
    rw [CFSG.RankThree.PartTwo.Sec4.RonanK432.th_card_centralizer_U]
    norm_num)


private theorem goodJ2_thS :
    GoodJ2 (Subgroup.centralizer ({thS} : Set ↥J)) := by
  haveI : Finite ↥J := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.finite_J
  obtain ⟨hs, -, hu, -, hsu, hC⟩ := CFSG.HardMathSupport.Dickson.Sec6.th3_facts
  have hC' : Nat.card (Subgroup.centralizer ({thS} : Set ↥J)) ≤ 63685439 := hC
  have h37 : 3 ^ 7 ∣ Nat.card (Subgroup.centralizer ({thS} : Set ↥J)) := by
    obtain ⟨⟨P, hPC, hP, hP7⟩, -⟩ :=
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.thThreeResidual_holds thS hs
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    have h7n : 7 ≤ n := by
      rw [hn] at hP7
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hP7
    exact (pow_dvd_pow 3 h7n).trans (hn ▸ Subgroup.card_dvd_of_le hPC)
  have h13 : 13 ∣ Nat.card (Subgroup.centralizer ({thS} : Set ↥J)) := by
    obtain ⟨w, hw, hwC⟩ : ∃ w : ↥J, orderOf w = 13 ∧ w ∈ Subgroup.centralizer ({thS} : Set ↥J) :=
      ⟨_, hu, Subgroup.mem_centralizer_singleton_iff.2 hsu.symm⟩
    have := Subgroup.orderOf_dvd_natCard _ hwC
    rwa [hw] at this
  exact goodJ2_of_card_dvd (M := Nat.card (Subgroup.centralizer ({thS} : Set ↥J))) dvd_rfl
    (not_dvd_j2_of_dvd_of_le h37 h13 hC' Nat.card_pos)


private theorem goodJ2_thJ (x : ↥J) (hx : orderOf x = 3) :
    GoodJ2 (Subgroup.centralizer ({x} : Set ↥J)) := by
  obtain ⟨k, c, hc, e, he, rfl⟩ := th_census x hx
  obtain ⟨hs, hz, hu⟩ := th_orderOf
  have hg : GoodJ2 (Subgroup.centralizer ({c} : Set ↥J)) ∧ c ^ 3 = 1 := by
    rcases hc with rfl | rfl | rfl
    · exact ⟨goodJ2_thS, by rw [← hs]; exact pow_orderOf_eq_one _⟩
    · exact ⟨goodJ2_thZ, by rw [← hz]; exact pow_orderOf_eq_one _⟩
    · exact ⟨goodJ2_thU, by rw [← hu]; exact pow_orderOf_eq_one _⟩
  have ha : GoodJ2 (Subgroup.centralizer ({c ^ e} : Set ↥J)) := by
    rw [CFSG.RankThree.PartTwo.Sec4.RonanK429H.centralizer_pow_of_pow_three hg.2 he]
    exact hg.1
  exact GoodJ2.of_isConj (isConj_iff.mpr ⟨k, rfl⟩) ha


private theorem noCfgJ2_th :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .Th) → NoCfgJ2 S := by
  intro S _ _ _ hna ⟨e⟩
  have hout : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Th)) := by
    rw [show Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Th)) = 1 from
      CFSG.RankThree.PartOne.SPOR.card_outer_Th_native]
    norm_num
  have hnat : ∀ x : Blueprint.NativeSporadic.Th, orderOf x = 3 →
      GoodJ2 (Subgroup.centralizer ({x} : Set Blueprint.NativeSporadic.Th)) :=
    @forall_goodJ2_of_mulEquiv Blueprint.NativeSporadic.Th ↥J Units.instGroup _ thEquivJ
      goodJ2_thJ
  exact noCfgJ2_of_model (G' := Blueprint.NativeSporadic.Th) e
    (CFSG.RankThree.PartTwo.Sec4.RonanK429H.center_eq_bot_of_simple_nonab hna)
    (CFSG.RankThree.PartTwo.Sec4.RonanK429H.not_three_dvd_outer_of_mulEquiv e hout) hnat


theorem rowOfK9_th : RowOfK9 (Spor .Th) :=
  rowOfK9_spor (s := .Th) CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv noCfgJ2_th

end Th

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
