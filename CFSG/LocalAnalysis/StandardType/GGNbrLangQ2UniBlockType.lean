module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2UniSquare
import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagLinear
import CFSG.LocalAnalysis.StandardType.MarkingClassical
import CFSG.Timmesfeld.Orders.Classical
import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSG.Timmesfeld.Orders.Distinct
import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSL
import CFSG.LieType.SemisimpleCentralizers.OrderThree.CenterQuot
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUTypes
import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily
import CFSG.Quasithin.Background.GoldschmidtListedSolv
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUnitary
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
import CFSG.Quasithin.Background.A3StructureFacts
import CFSG.Quasithin.Background.F9FiveStruct
import CFSG.Quasithin.Background.F9G2
import CFSG.Quasithin.Background.F9Geometry
import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
import CFSG.Quasithin.EmptyFaithful.S1421Defs
import CFSG.Quasithin.EmptyFaithful.S142Statements
import CFSG.Quasithin.H13.A5S1326
import CFSG.Quasithin.H13.A5Top
import CFSG.Quasithin.H13.StatementsL3

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
open CFSG.Open (StatedSU StatedProj)
open CFSG.StandardType.ClassicalBlocks (GUFull)

theorem q2Uni_linearBlock_false {H : Type} [Group H] {F C : Subgroup H}
    (hC : IsComponentOf C F) {b : ℕ} {D : Type} [Field D] [Finite D] [CharP D 2]
    (e : ↥F ≃* GL (Fin b) D) {d m : ℕ} {E : Type} [Field E] (hE : UnitaryFieldData 2 m E)
    (hd : 3 ≤ d) (hdm : ¬ (d = 3 ∧ m = 1))
    (θ : ↥C ⧸ Subgroup.center ↥C ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m))) :
    False := by
  by_cases hb : 2 ≤ b
  · haveI : Fintype D := Fintype.ofFinite D
    have hb1 : 1 ≤ b := by omega
    obtain ⟨n, -, hcardF⟩ := FiniteField.card D 2
    let f : ℕ := (n : ℕ)
    have hDcard : Nat.card D = 2 ^ f := by
      rw [Nat.card_eq_fintype_card, hcardF]
    have hf : 1 ≤ f := by
      rcases Nat.eq_zero_or_pos f with h0 | h
      · rw [h0, pow_zero] at hDcard
        have := Finite.one_lt_card (α := D)
        omega
      · exact h
    have hcardL : Nat.card (LargeEvenProj (LargeEvenSLGroup (Fin b) D)) =
        Open.ordA (b - 1) (2 ^ f) := by
      rw [largeEvenSLGroup_eq_statedSL, largeEvenProj_eq_statedProj]
      rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (n := b) hb1, hDcard,
        Open.ordA, Nat.sub_add_cancel hb1, Nat.mul_comm (b - 1) b]
    have hEcard : Nat.card E = (2 ^ m) ^ 2 := unitaryFieldData_card_sq hE
    haveI : Finite E := hE.finite
    have hneR : (d, 2 ^ m) ≠ (3, 2) := by
      intro h
      obtain ⟨hd3, hq2⟩ := Prod.mk.inj h
      exact hdm ⟨hd3, Nat.pow_right_injective (le_refl 2) hq2⟩
    have hadmR : Open.StatedLieAdmissible .PSU d 2 m :=
      ⟨Nat.prime_two, hE.one_le, hd, hneR⟩
    have hSCM_R : Open.StatedClassicalModel
        (LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m))) .PSU d 2 m :=
      statedClassicalModel_unitary d m hEcard hadmR
    have hcardR : Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m))) =
        Open.ordTwistedA (d - 1) (2 ^ m) :=
      (Timmesfeld.card_statedClassicalModel_two hSCM_R).2.1 rfl
    have hcard_eq : Nat.card (LargeEvenProj (LargeEvenSLGroup (Fin b) D)) =
        Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m))) :=
      Nat.card_congr ((linearBlockQuotientMarking e hC).symm.trans θ).toEquiv
    have hOrder : Open.ordA (b - 1) (2 ^ f) = Open.ordTwistedA (d - 1) (2 ^ m) :=
      hcardL.symm.trans (hcard_eq.trans hcardR)
    exact (Timmesfeld.Orders.ordA_ne_ordTwistedA (n := b - 1) (f := f) (u := d - 1) (g := m)
      (by omega) hf (by omega) hE.one_le) hOrder
  · have hble1 : b ≤ 1 := by omega
    have hsubSL : Subsingleton (LargeEvenProj (LargeEvenSLGroup (Fin b) D)) := by
      rw [largeEvenSLGroup_eq_statedSL, largeEvenProj_eq_statedProj]
      haveI : Subsingleton ↥(Open.StatedSL b D) :=
        CFSG.LieType.SemisimpleCentralizers.Held.hct_subsingleton_statedSL_of_le_one hble1
      infer_instance
    haveI : Subsingleton (LargeEvenProj (LargeEvenSLGroup (Fin b) D)) := hsubSL
    have hsubq : Subsingleton (↥C ⧸ Subgroup.center ↥C) :=
      Equiv.subsingleton (linearBlockQuotientMarking e hC).toEquiv
    haveI : Nontrivial (↥C ⧸ Subgroup.center ↥C) := hC.2.2.2.toNontrivial
    exact (not_subsingleton _ hsubq).elim

private theorem cuq2ub_ordA_one_two_pow (k : ℕ) (hk : 1 ≤ k) :
    CFSG.Open.ordA 1 (2 ^ k) = 2 ^ k * ((2 ^ k) ^ 2 - 1) := by
  rw [CFSG.Open.ordA]
  have hg : Nat.gcd 2 ((2 ^ k) - 1) = 1 :=
    Nat.coprime_two_left.mpr (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one hk)
  rw [hg, Nat.div_one]
  norm_num

theorem q2Uni_unitaryBlock_params {H : Type} [Group H] {F C : Subgroup H}
    (hC : IsComponentOf C F) {a k : ℕ} {D : Type} [Field D] (hD : UnitaryFieldData 2 k D)
    (e : ↥F ≃* ↥(TableB.unitGroup (ι := Fin a) hD.bar)) {d m : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData 2 m E) (hd : 3 ≤ d) (hdm : ¬ (d = 3 ∧ m = 1))
    (θ : ↥C ⧸ Subgroup.center ↥C ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m))) :
    3 ≤ a ∧ ¬ (a = 3 ∧ k = 1) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite D := hD.finite
  haveI : CharP D 2 := hD.charP
  let e' : ↥F ≃* ↥(GUFull a (2 ^ k) D) := e.trans (guFullEquivUnitGroup hD).symm
  let φ : ↥C ≃* ↥(LargeEvenSUGroup (Fin a) D (2 ^ k)) :=
    componentEquivLargeEvenSUOfUnitaryFull (unitaryFieldData_card_sq hD) e' hC
  have ha2 : 2 ≤ a := by
    have hqs : CFSG.Assembly.IsQuasisimple (StatedSU a (2 ^ k) D) :=
      CFSG.Assembly.IsQuasisimple.of_mulEquiv φ.symm hC.2.2
    exact CFSG.LieType.SemisimpleCentralizers.OrderThree.two_le_of_isQuasisimple_statedSU hqs
  refine ⟨?_, ?_⟩
  · by_contra h3
    have ha : a = 2 := by omega
    subst ha
    have hcenter : Subgroup.center ↥(LargeEvenSUGroup (Fin 2) D (2 ^ k)) = ⊥ :=
      CFSG.ComponentClassification.RankTwoClassical.center_statedSU_two_eq_bot
        (K := D) (f := k) (unitaryFieldData_card_sq hD)
    have hcardCZ : Nat.card (↥C ⧸ Subgroup.center ↥C) = 2 ^ k * ((2 ^ k) ^ 2 - 1) := by
      have h1 : Nat.card (↥C ⧸ Subgroup.center ↥C) =
          Nat.card (↥(LargeEvenSUGroup (Fin 2) D (2 ^ k)) ⧸
            Subgroup.center ↥(LargeEvenSUGroup (Fin 2) D (2 ^ k))) :=
        Nat.card_congr (QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ)).toEquiv
      rw [h1]
      have e2 : ↥(LargeEvenSUGroup (Fin 2) D (2 ^ k)) ⧸
            Subgroup.center ↥(LargeEvenSUGroup (Fin 2) D (2 ^ k)) ≃*
          ↥(LargeEvenSUGroup (Fin 2) D (2 ^ k)) :=
        (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
      rw [Nat.card_congr e2.toEquiv]
      exact CFSG.RankThree.SubgroupLists.card_statedSU_two (K := D) (r := 2) (f := k)
        (unitaryFieldData_card_sq hD)
    have hcardR : Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m))) =
        CFSG.Open.ordTwistedA (d - 1) (2 ^ m) := by
      change Nat.card (StatedProj (StatedSU d (2 ^ m) E)) =
        CFSG.Open.ordTwistedA (d - 1) (2 ^ m)
      rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two hE.one_le
        (unitaryFieldData_card_sq hE) (by omega : 2 ≤ d), CFSG.Open.ordTwistedA,
        Nat.sub_add_cancel (by omega : 1 ≤ d), Nat.mul_comm d (d - 1)]
    have h2 : Nat.card (↥C ⧸ Subgroup.center ↥C) =
        CFSG.Open.ordTwistedA (d - 1) (2 ^ m) :=
      (Nat.card_congr θ.toEquiv).trans hcardR
    have hEq : CFSG.Open.ordA 1 (2 ^ k) = CFSG.Open.ordTwistedA (d - 1) (2 ^ m) := by
      rw [cuq2ub_ordA_one_two_pow k hD.one_le, ← hcardCZ, h2]
    exact (CFSG.Timmesfeld.Orders.ordA_ne_ordTwistedA (n := 1) (f := k) (u := d - 1) (g := m)
      le_rfl hD.one_le (by omega) hE.one_le) hEq
  · rintro ⟨rfl, rfl⟩
    haveI : Group.IsSolvable (LargeEvenSUGroup (Fin 3) D (2 ^ 1)) :=
      CFSG.Quasithin.isSolvable_statedSU_one (F := D) (unitaryFieldData_card_sq hD)
    haveI hsolvC : Group.IsSolvable ↥C :=
      Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
    haveI : Group.IsPerfect ↥C := ⟨hC.2.2.1⟩
    haveI : Nontrivial (↥C ⧸ Subgroup.center ↥C) := hC.2.2.2.toNontrivial
    haveI : Nontrivial ↥C := (QuotientGroup.mk'_surjective (Subgroup.center ↥C)).nontrivial
    exact Group.IsPerfect.not_isSolvable ↥C hsolvC

end CFSG.StandardType
