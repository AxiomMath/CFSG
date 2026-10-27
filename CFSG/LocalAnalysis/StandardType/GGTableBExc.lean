module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBstar
public import CFSG.LocalAnalysis.StandardType.GGTableBExcEndNode
public import CFSG.LocalAnalysis.StandardType.GGTableBF4
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLevi
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourLevi
public import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCentrallyClosed

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.SeitzReduction.EPilot

@[expose] def GGE8SmallToralRankInput :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → p ≠ 2 → p < 11 →
    p ∣ Nat.card K - 1 → GGExcToralRankInput .E8 K p

@[expose] def GGE7SmallToralRankInput :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → p ≠ 2 → p < 11 →
    p ∣ Nat.card K - 1 → GGExcToralRankInput .E7 K p

theorem largeEvenSplit_E_iff {p : ℕ} {lab : LargeEvenLabel}
    (htag : lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8) :
    LargeEvenSplit p lab ↔ p ∣ 2 ^ lab.n - 1 ∨ (lab.n = 1 ∧ p = 3) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag
  rcases htag with rfl | rfl | rfl <;> simp [LargeEvenSplit, LargeEvenUntwisted]


namespace TableBExc

theorem ggExcToralRankInput_E8 {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1)
    (hsmall : p < 11 → GGE8SmallToralRankInput) : GGExcToralRankInput .E8 K p := by
  by_cases h11 : p < 11
  · exact hsmall h11 K p hp hp2 h11 hpq
  · exact ggExcToralRankInput_E8_of_eleven_le hp (by omega) hpq

theorem ggExcToralRankInput_E7 {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1)
    (hsmall : p < 11 → GGE7SmallToralRankInput) : GGExcToralRankInput .E7 K p := by
  by_cases h11 : p < 11
  · exact hsmall h11 K p hp hp2 h11 hpq
  · exact ggExcToralRankInput_E7_of_eleven_le hp (by omega) hpq

theorem recipeChevalleyE8_tableB {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) (hpn : p ∣ 2 ^ n - 1)
    (hT₀ : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], p ∣ Nat.card K - 1 →
      GGExcToralRankInput .E8 K p) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeChevalley (LargeEvenCartanE 8) (2 ^ n) false Q) :
    LargeEvenRecipeChevalley (LargeEvenCartanE 8) (2 ^ n) false fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have : CharP K 2 := charP_two_of_card hK
  have hp2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  have hT := hT₀ K hpq
  exact ⟨K, inferInstance, inferInstance, hK, hQ, 8, ggTorusLift_E8 hp hp2 hpq,
    ggBstarBound_of_input (Or.inr rfl) hn hK hp hpq hT _,
    ggEndNode_of_input (Or.inr (Or.inr rfl)) (ringChar.eq K 2) (full_of_E7_E8 (Or.inr rfl))
      (idImage_subset_inn_E8 K) hp hp2 hpq CFSG.SeitzReduction.E8Pilot.isQuasisimple_e7Levi hT⟩

theorem recipeChevalleyE7_tableB {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) (hpn : p ∣ 2 ^ n - 1)
    (hT₀ : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], p ∣ Nat.card K - 1 →
      GGExcToralRankInput .E7 K p) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeChevalley (LargeEvenCartanE 7) (2 ^ n) false Q) :
    LargeEvenRecipeChevalley (LargeEvenCartanE 7) (2 ^ n) false fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have : CharP K 2 := charP_two_of_card hK
  have hp2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  have hT := hT₀ K hpq
  exact ⟨K, inferInstance, inferInstance, hK, hQ, 7, ggTorusLift_E7 hp hp2 hpq,
    ggBstarBound_of_input (Or.inl rfl) hn hK hp hpq hT _,
    ggEndNode_of_input (Or.inr (Or.inl rfl)) (ringChar.eq K 2) (full_of_E7_E8 (Or.inl rfl))
      (idImage_subset_inn_E7 K) hp hp2 hpq CFSG.SeitzReduction.E7Pilot.isQuasisimple_perpLevi_E7
      hT⟩

end TableBExc

theorem largeEvenLabelAll_tableB_E8_of_toral {lab : LargeEvenLabel} (htag : lab.tag = .E8)
    (hlab : LargeEvenInLambda2 lab) {p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ lab.n - 1)
    (hT : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], p ∣ Nat.card K - 1 →
      GGExcToralRankInput .E8 K p) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag
  subst htag
  intro Q hQ
  exact TableBExc.recipeChevalleyE8_tableB hlab.1 hp hpn hT hQ

theorem largeEvenLabelAll_tableB_E8 {lab : LargeEvenLabel} (htag : lab.tag = .E8)
    (hlab : LargeEvenInLambda2 lab) {p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ lab.n - 1)
    (hsmall : p < 11 → GGE8SmallToralRankInput) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I :=
  largeEvenLabelAll_tableB_E8_of_toral htag hlab hp hpn fun _ _ _ _ hpq =>
    TableBExc.ggExcToralRankInput_E8 hp (ne_two_of_dvd_two_pow_sub_one hlab.1 hpn) hpq hsmall

theorem largeEvenLabelAll_tableB_E7_of_toral {lab : LargeEvenLabel} (htag : lab.tag = .E7)
    (hlab : LargeEvenInLambda2 lab) {p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ lab.n - 1)
    (hT : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], p ∣ Nat.card K - 1 →
      GGExcToralRankInput .E7 K p) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag
  subst htag
  intro Q hQ
  exact TableBExc.recipeChevalleyE7_tableB hlab.1 hp hpn hT hQ

theorem largeEvenLabelAll_tableB_E7 {lab : LargeEvenLabel} (htag : lab.tag = .E7)
    (hlab : LargeEvenInLambda2 lab) {p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ lab.n - 1)
    (hsmall : p < 11 → GGE7SmallToralRankInput) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I :=
  largeEvenLabelAll_tableB_E7_of_toral htag hlab hp hpn fun _ _ _ _ hpq =>
    TableBExc.ggExcToralRankInput_E7 hp (ne_two_of_dvd_two_pow_sub_one hlab.1 hpn) hpq hsmall

theorem largeEvenLabelAll_tableB_E8_eleven {lab : LargeEvenLabel} (htag : lab.tag = .E8)
    (hlab : LargeEvenInLambda2 lab) {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (hpn : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I :=
  largeEvenLabelAll_tableB_E8 htag hlab hp hpn fun h => by omega

theorem largeEvenLabelAll_tableB_E7_eleven {lab : LargeEvenLabel} (htag : lab.tag = .E7)
    (hlab : LargeEvenInLambda2 lab) {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (hpn : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I :=
  largeEvenLabelAll_tableB_E7 htag hlab hp hpn fun h => by omega

@[expose] def GGTableBE7E8Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .E7 ∨ lab.tag = .E8) ∧ p ∣ 2 ^ lab.n - 1

@[expose] def GGTableBE7E8LabelEleven (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .E7 ∨ lab.tag = .E8) ∧ p ∣ 2 ^ lab.n - 1 ∧ 11 ≤ p

theorem largeEvenLabelAll_tableB_E7E8 {p : ℕ} {lab : LargeEvenLabel} (h : GGTableBE7E8Label p lab)
    (hlab : LargeEvenInLambda2 lab) (hp : p.Prime) (h7 : p < 11 → GGE7SmallToralRankInput)
    (h8 : p < 11 → GGE8SmallToralRankInput) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I := by
  rcases h.1 with ht | ht
  · exact largeEvenLabelAll_tableB_E7 ht hlab hp h.2 h7
  · exact largeEvenLabelAll_tableB_E8 ht hlab hp h.2 h8

theorem ggBstarInputOn_E7E8 (h7 : GGE7SmallToralRankInput) (h8 : GGE8SmallToralRankInput) :
    GGBstarInputOn GGTableBE7E8Label :=
  TableBF4.ggBstarInputOn_of_labelAll fun _ _ hp hlab h =>
    (largeEvenLabelAll_tableB_E7E8 h hlab hp (fun _ => h7) fun _ => h8).mono
      fun _ _ _ _ ⟨r, h1, h2, _⟩ => ⟨r, h1, h2⟩

theorem ggStdSubPreInputOn_E7E8 (h7 : GGE7SmallToralRankInput) (h8 : GGE8SmallToralRankInput) :
    GGStdSubPreInputOn GGTableBE7E8Label :=
  ggStdSubPreInputOn_of_labels fun _ _ hp hlab h =>
    (largeEvenLabelAll_tableB_E7E8 h hlab hp (fun _ => h7) fun _ => h8).mono
      fun _ _ _ _ ⟨r, h1, _, h4⟩ => ⟨r, h1, h4⟩

theorem ggBstarInputOn_E7E8_eleven : GGBstarInputOn GGTableBE7E8LabelEleven :=
  TableBF4.ggBstarInputOn_of_labelAll fun _ _ hp hlab h =>
    (largeEvenLabelAll_tableB_E7E8 ⟨h.1, h.2.1⟩ hlab hp (fun h' => by have := h.2.2; omega)
      fun h' => by have := h.2.2; omega).mono fun _ _ _ _ ⟨r, h1, h2, _⟩ => ⟨r, h1, h2⟩

theorem ggStdSubPreInputOn_E7E8_eleven : GGStdSubPreInputOn GGTableBE7E8LabelEleven :=
  ggStdSubPreInputOn_of_labels fun _ _ hp hlab h =>
    (largeEvenLabelAll_tableB_E7E8 ⟨h.1, h.2.1⟩ hlab hp (fun h' => by have := h.2.2; omega)
      fun h' => by have := h.2.2; omega).mono fun _ _ _ _ ⟨r, h1, _, h4⟩ => ⟨r, h1, h4⟩

end CFSG.StandardType
