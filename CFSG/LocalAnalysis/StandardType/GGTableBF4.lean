module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4Torus
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Bstar
public import CFSG.LocalAnalysis.StandardType.GGTableBF4EndNode
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplectic
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeA
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley

@[expose] def GGF4ThreeRankInput :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 3 ∣ Nat.card K - 1 → GGF4ToralRankInput K 3

theorem largeEvenSplit_F4_iff {p : ℕ} {lab : LargeEvenLabel} (htag : lab.tag = .F4) :
    LargeEvenSplit p lab ↔ p ∣ 2 ^ lab.n - 1 ∨ (lab.n = 1 ∧ p = 3) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag
  subst htag
  simp [LargeEvenSplit, LargeEvenUntwisted]


theorem ggF4ToralRankInput_of_three {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) (h3 : p = 3 → GGF4ThreeRankInput) :
    GGF4ToralRankInput K p := by
  by_cases hp3 : p = 3
  · subst hp3
    exact h3 rfl K hpq
  · have h5 : 5 ≤ p := by
      have h2 := hp.two_le
      have h4 : p ≠ 4 := by
        rintro rfl
        exact absurd hp (by decide)
      omega
    exact TableBF4.ggF4ToralRankInput_of_five_le hp h5 hpq

theorem recipeChevalleyF4_tableB {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) (hpn : p ∣ 2 ^ n - 1)
    (h3 : p = 3 → GGF4ThreeRankInput) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeChevalley LargeEvenCartanF4 (2 ^ n) false Q) :
    LargeEvenRecipeChevalley LargeEvenCartanF4 (2 ^ n) false fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have : CharP K 2 := charP_two_of_card hK
  have hp2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  have hT := ggF4ToralRankInput_of_three hp hp2 hpq h3
  exact ⟨K, inferInstance, inferInstance, hK, hQ, 4, TableBF4.ggTorusLift_F4 hp hp2 hpq,
    TableBF4.ggBstarBound_F4_of_input hn hK hp hpq hT _,
    TableBF4.ggEndNode_F4_of_input (ringChar.eq K 2) hp hp2 hpq hT⟩

theorem largeEvenLabelAll_tableB_F4 {lab : LargeEvenLabel} (htag : lab.tag = .F4)
    (hlab : LargeEvenInLambda2 lab) {p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ lab.n - 1)
    (h3 : p = 3 → GGF4ThreeRankInput) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag
  subst htag
  intro Q hQ
  exact recipeChevalleyF4_tableB hlab.1 hp hpn h3 hQ

theorem largeEvenLabelAll_tableB_F4_five {lab : LargeEvenLabel} (htag : lab.tag = .F4)
    (hlab : LargeEvenInLambda2 lab) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpn : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I :=
  largeEvenLabelAll_tableB_F4 htag hlab hp hpn fun h => by omega

theorem TableBF4.ggBstarInputOn_of_labelAll {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I) :
    GGBstarInputOn S := by
  intro G _ _ p B x L hT hM
  have hp : p.Prime := hT.2.2.2.2.2.1.1
  have hnc := ggLNoncyclicInput_holds G p B x L hT
  have hM' := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  exact exists_ggBstar_of_marking hT hnc
    (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨⟨hP.1.2.2.1, hP.1.2.2.2⟩, hP.2⟩) hM')

@[expose] def GGTableBF4Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .F4 ∧ p ∣ 2 ^ lab.n - 1

@[expose] def GGTableBF4LabelFive (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .F4 ∧ p ∣ 2 ^ lab.n - 1 ∧ 5 ≤ p

theorem ggBstarInputOn_F4 (h3 : GGF4ThreeRankInput) : GGBstarInputOn GGTableBF4Label :=
  TableBF4.ggBstarInputOn_of_labelAll fun _ _ hp hlab h =>
    (largeEvenLabelAll_tableB_F4 h.1 hlab hp h.2 fun _ => h3).mono
      fun _ _ _ _ ⟨r, h1, h2, _⟩ => ⟨r, h1, h2⟩

theorem ggStdSubPreInputOn_F4 (h3 : GGF4ThreeRankInput) : GGStdSubPreInputOn GGTableBF4Label :=
  ggStdSubPreInputOn_of_labels fun _ _ hp hlab h =>
    (largeEvenLabelAll_tableB_F4 h.1 hlab hp h.2 fun _ => h3).mono
      fun _ _ _ _ ⟨r, h1, _, h4⟩ => ⟨r, h1, h4⟩

theorem ggBstarInputOn_F4_five : GGBstarInputOn GGTableBF4LabelFive :=
  TableBF4.ggBstarInputOn_of_labelAll fun _ _ hp hlab h =>
    (largeEvenLabelAll_tableB_F4_five h.1 hlab hp h.2.2 h.2.1).mono
      fun _ _ _ _ ⟨r, h1, h2, _⟩ => ⟨r, h1, h2⟩

theorem ggStdSubPreInputOn_F4_five : GGStdSubPreInputOn GGTableBF4LabelFive :=
  ggStdSubPreInputOn_of_labels fun _ _ hp hlab h =>
    (largeEvenLabelAll_tableB_F4_five h.1 hlab hp h.2.2 h.2.1).mono
      fun _ _ _ _ ⟨r, h1, _, h4⟩ => ⟨r, h1, h4⟩

end CFSG.StandardType
