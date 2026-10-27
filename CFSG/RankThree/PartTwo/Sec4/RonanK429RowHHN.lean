module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp
public import CFSG.Sporadic.Bridge.HNSurj
public import CFSG.Sporadic.HNSchreier.Intrinsic
public import CFSG.Sporadic.HNSchreier.ThreeCent
public import CFSG.RankThree.PartOne.SPOR.Outer
public import CFSG.GH74.GLS.Balance.SolvAPIDefs
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118Proof
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118ProofSteps
public import CFSG.RankThree.PartTwo.Sec11.Item1121Proof
public import CFSG.RankThree.PartTwo.Sec11.Item119K
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL
public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowGriess
public import CFSG.Walter.J1Props
public import Certificates.Certificate8166

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

open CFSG.Sporadic.HNSchreier

section Certs


theorem good429_hn_s1 : Good429 (Subgroup.centralizer ({sJ 0} : Set JH)) := by
  haveI : Finite JH := Finite.of_equiv _ hnEquivJ.toEquiv
  obtain ⟨-, -, -, hC, -, -, -, hcard, -⟩ := ctuc_hn_three_centralizers_exact
  have hDC : L1J ≤ Subgroup.centralizer ({sJ 0} : Set JH) := by
    rw [show Subgroup.centralizer ({sJ 0} : Set JH) = CJ (sJ 0) from rfl, hC]
    exact le_sup_right
  have hDcard : Nat.card L1J = 181440 := by
    rw [Subgroup.card_map_of_injective iotaA_injective, card_alt3]
  haveI : Group.IsPerfect alt3 := ⟨commutator_alt3⟩
  haveI : Group.IsPerfect L1J := Group.IsPerfect.map _
  refine good429_of_residual (B := 57) hDC ?_ hDcard (by norm_num) (by norm_num) (by decide)
    (not_isType429_quot_of_noEqOK (B := 57) hDcard (by norm_num) (by norm_num) (by decide))
  rw [hDcard]
  exact (show Nat.card (CJ (sJ 0)) = 544320 from hcard).le.trans (by norm_num)

theorem good429_hn (x : JH) (hx : orderOf x = 3) :
    Good429 (Subgroup.centralizer ({x} : Set JH)) := by
  haveI : Finite JH := Finite.of_equiv _ hnEquivJ.toEquiv
  obtain ⟨hcls, -, -, -, -, h3B, -⟩ := ctuc_hn_intrinsic_three_class_and_alternating_localization
  rcases (hcls x).mp hx with h | h
  · exact good429_hn_s1.of_isConj h
  · exact good429_of_card (B := 31) (h3B x h) (by norm_num) (by decide)

theorem good429_hn_native :
    ∀ x : Blueprint.NativeSporadic.HN, orderOf x = 3 →
      Good429 (Subgroup.centralizer ({x} : Set Blueprint.NativeSporadic.HN)) :=
  @forall_good429_of_mulEquiv Blueprint.NativeSporadic.HN ↥JH Units.instGroup _ hnEquivJ good429_hn

theorem noCfgS429_hn :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .HN) → NoCfgS429 S := by
  intro S _ _ _ hna ⟨e⟩
  have hout : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .HN)) := by
    rw [RankThree.PartOne.SPOR.card_outer_HN]; norm_num
  exact noCfgS429_of_model (G' := Blueprint.NativeSporadic.HN) e
    (center_eq_bot_of_simple_nonab hna) (not_three_dvd_outer_of_mulEquiv e hout) good429_hn_native

theorem rowSOf429_hn :
    RowSOf429 (Spor .HN) :=
  rowSOf429_spor CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv noCfgS429_hn

end Certs

end CFSG.RankThree.PartTwo.Sec4.RonanK429H
