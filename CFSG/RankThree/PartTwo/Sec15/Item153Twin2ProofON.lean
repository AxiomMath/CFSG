module

public import CFSG.RankThree.PartTwo.Sec15.Item156StepsProofD
public import CFSG.RankThree.PartTwo.Sec17.RouteForms
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofRead
import CFSG.RankThree.PartTwo.Sec15.Item153ClaimsKS
import CFSG.RankThree.PartTwo.Sec14.Item145BotNo135
import CFSG.RankThree.PartTwo.Sec14.Concl142HJPoint
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec4.Item426RestModels

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] def Step156ONXK (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB,
    Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) CFSG.Blueprint.NativeSporadic.ON →
      ∃ (c₀ : G) (X₁ : Subgroup G), Subgroup.zpowers c₀ ∈ omegaA A ∧
        X₁ ∈ scriptY0 A LB ∧ X₁ ≤ Y ∧
        Sec4.IsTripleCover (↥X₁ ⧸ CFSG.pCore 2 ↥X₁) (alternatingGroup (Fin 6)) ∧
        c₀ ∈ Late.sectionCentralizer A X₁ (CFSG.Open.pCoreOf 2 X₁)

@[expose] noncomputable def Step156ONXKR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step156ONXK A (lB A)

namespace Proof153Twin2

omit [Finite G] in
theorem center_eq_bot_of_mulEquiv' {X T : Type*} [Group X] [Group T] (e : X ≃* T)
    (hT : Subgroup.center T = ⊥) : Subgroup.center X = ⊥ := by
  refine Subgroup.eq_bot_of_card_eq _ ?_
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hT, Subgroup.card_bot]

theorem exists_hj_point_of_on
    (h134 : Item134) (h48 : Sec4.Item4_8) {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h148 : Item148 A (lB A)) {Y : Subgroup G}
    (hY : Y ∈ scriptY4 A (lB A))
    (hON : Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) CFSG.Blueprint.NativeSporadic.ON) :
    ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
      Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hJ2c : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥ := sporadicModels131.2.2.2
  have hYΔ : Y = deltaZero A (lB A) Y :=
    rank3II_15_1_of' h134 CFSG.Sporadic.J2.isSimpleGroup_J2 h48 h415 hJ2c h hY
  have hq : IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY.2.2.2
  have hZ3 : IsPGroup 3 (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) :=
    IsPGroup.of_card (n := 1) (by rw [hON.1, pow_one])
  have h3 : 3 ∣ Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
    rw [card_of_isTripleCover hON]
    exact dvd_mul_right 3 _
  have hcore : CFSG.pPrimeCore 3 ↥Y = CFSG.pCore 2 ↥Y :=
    pPrimeCore_three_eq_pCore_two (pPrimeCore_three_eq_bot_of_isQuasisimple hq h3 hZ3)
  have hqbar : IsQuasisimple (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) :=
    Proof1515.isQuasisimple_quot_pPrimeCore hY
  have hZbar : Subgroup.center (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) ≠ ⊥ := by
    intro hbot
    have h1 : Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊥ :=
      center_eq_bot_of_mulEquiv' (QuotientGroup.quotientMulEquivOfEq hcore).symm hbot
    have h2 := hON.1
    rw [h1, Subgroup.card_bot] at h2
    omega
  have hcen : ∀ {T : Type} [Group T], Subgroup.center T = ⊥ →
      (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) ≃* T → False := fun hT e =>
    hZbar (center_eq_bot_of_mulEquiv' e hT)
  rcases Proof1515.cases148_of_mem_scriptY4 h148 h.isElemAbelian.1 hY hYΔ with
    ⟨c', hc', -, L', hL', hcases⟩ | ⟨c', L', hc', hL', hJ, -⟩ | ⟨⟨φ⟩, -⟩ |
      ⟨c', L', n, m, hc', hL', hn, -, hiso, -⟩
  · rcases hcases with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨p, f, e', hp, hf, -, -, hε⟩ | ⟨hJ, -⟩
    ·
      exfalso
      have hqL : IsQuasisimple (↥L' ⧸ aschbacherSolvableCore 3 ↥L') :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv φ hqbar
      exact hcen (center_eq_bot_of_quasisimple_types hqL (h.chosen136.2 c' hc' L' hL').1) φ
    ·
      exact (hcen (alternatingGroup.center_eq_bot (by simp)) φ).elim
    ·
      exfalso
      rcases hε with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
      · exact Sec4.Item426Rest.false_of_projSL hqbar hZbar φ
      · exact Sec4.Item426Rest.false_of_projSU hqbar hZbar le_rfl hf φ
    ·
      exact ⟨c', L', hc', hL', hJ⟩
  ·
    exact ⟨c', L', hc', hL', hJ⟩
  ·
    exact (hcen (alternatingGroup.center_eq_bot (by simp)) φ).elim
  ·
    exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rcases hiso with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
    · exact Sec4.Item426Rest.false_of_projSL hqbar hZbar φ
    · exact Sec4.Item426Rest.false_of_projSU hqbar hZbar le_rfl (by omega) φ

end Proof153Twin2

open Proof153Twin2

theorem step156ONX_of
    (h134 : Item134) (h48 : Sec4.Item4_8) {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h148 : Item148 A (lB A)) (hK : Step156ONXK A (lB A)) :
    Step156ONX A (lB A) := by
  intro Y hY hON
  obtain ⟨c₀, X₁, hc₀, hX₁, hX₁Y, h6, hcX⟩ := hK Y hY hON
  obtain ⟨c', L', hc', hL', hJ⟩ := exists_hj_point_of_on h134 h48 h h148 hY.prop.1 hON
  have h' : Sec14Std G A c' L' := { h with zpowers_mem_omegaA := hc', mem_lA := hL' }
  obtain ⟨L₀, hL₀, hJ₀⟩ := allPointsHJ_of_j2 h134 h48 h' hJ c₀ hc₀
  exact ⟨c₀, L₀, X₁, hc₀, hL₀, hJ₀, hX₁, hX₁Y, Or.inr h6, hcX, Or.inl h6⟩

theorem step156ONXR_of
    (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8) (hK : Step156ONXKR) :
    Step156ONXR :=
  fun G _ _ A c L hR => step156ONX_of h134 h48 hR.toSec14Std (h148 G A c L hR) (hK G A c L hR)

end CFSG.RankThree.PartTwo.Sec15
