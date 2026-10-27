module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoBstar
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoEndNode
public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeSplit
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Two

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def GGTableBExcTwoLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .E7 ∨ lab.tag = .E8) ∧ lab.n = 1 ∧ p = 3

@[expose] def GGTableBE7E8AllLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .E7 ∨ lab.tag = .E8) ∧ LargeEvenSplit p lab


theorem largeEvenLabelAll_tableB_E7Two {lab : LargeEvenLabel} (htag : lab.tag = .E7)
    (hn : lab.n = 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift 3 r R ∧ GGBstarBound 3 r R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hn
  subst htag hn
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK])
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  exact ⟨K, inferInstance, inferInstance, hK, hQ', 6, TableBExcTwo.ggTorusLift_E7Two,
    TableBExcTwo.ggBstarBound_E7Two hK2 _⟩

theorem largeEvenLabelAll_tableB_E8Two {lab : LargeEvenLabel} (htag : lab.tag = .E8)
    (hn : lab.n = 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift 3 r R ∧ GGBstarBound 3 r R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hn
  subst htag hn
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK])
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  exact ⟨K, inferInstance, inferInstance, hK, hQ', 7, TableBExcTwo.ggTorusLift_E8Two,
    TableBExcTwo.ggBstarBound_E8Two hK2 _⟩

theorem ggBstarInputOn_E7E8Two : GGBstarInputOn GGTableBExcTwoLabel :=
  TableBF4.ggBstarInputOn_of_labelAll fun _ _ _ _ h => by
    obtain ⟨htag, hn, rfl⟩ := h
    rcases htag with htag | htag
    · exact largeEvenLabelAll_tableB_E7Two htag hn
    · exact largeEvenLabelAll_tableB_E8Two htag hn

theorem ggBstarInputOn_E7E8_all : GGBstarInputOn GGTableBE7E8AllLabel := by
  refine GGBstarInputOn.mono_split (ggBstarInputOn_E7E8_split_holds.or ggBstarInputOn_E7E8Two)
    fun p lab h _ => ?_
  obtain ⟨htag, hs⟩ := h
  rcases (largeEvenSplit_E_iff (Or.inr htag)).mp hs with hpn | ⟨hn, hp3⟩
  · exact Or.inl ⟨htag, hpn⟩
  · exact Or.inr ⟨htag, hn, hp3⟩

theorem largeEvenLabelAll_endNode_E7E8Two
    (hF7 : TableBExcTwo.GGE7TwoRootFusionInput)
    (hF8 : TableBExcTwo.GGE8TwoRootFusionInput) {lab : LargeEvenLabel}
    (htag : lab.tag = .E7 ∨ lab.tag = .E8) (hn : lab.n = 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift 3 r R ∧ GGEndNode 3 r R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hn
  subst hn
  rcases htag with rfl | rfl
  · intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK])
    have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
    exact ⟨K, inferInstance, inferInstance, hK, hQ', 6, TableBExcTwo.ggTorusLift_E7Two,
      TableBExcTwo.ggEndNode_E7Two hF7 hK2⟩
  · intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK])
    have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
    exact ⟨K, inferInstance, inferInstance, hK, hQ', 7, TableBExcTwo.ggTorusLift_E8Two,
      TableBExcTwo.ggEndNode_E8Two hF8 hK2⟩


theorem ggStdSubPreInputOn_E7E8Two (hF7 : TableBExcTwo.GGE7TwoRootFusionInput)
    (hF8 : TableBExcTwo.GGE8TwoRootFusionInput) : GGStdSubPreInputOn GGTableBExcTwoLabel :=
  ggStdSubPreInputOn_of_labels fun _ _ _ _ h => by
    obtain ⟨htag, hn, rfl⟩ := h
    exact largeEvenLabelAll_endNode_E7E8Two hF7 hF8 htag hn

theorem ggStdSubPreInputOn_E7E8_all (hF7 : TableBExcTwo.GGE7TwoRootFusionInput)
    (hF8 : TableBExcTwo.GGE8TwoRootFusionInput) : GGStdSubPreInputOn GGTableBE7E8AllLabel := by
  refine GGStdSubPreInputOn.mono_split
    (ggStdSubPreInputOn_E7E8_split_holds.or (ggStdSubPreInputOn_E7E8Two hF7 hF8))
    fun p lab h _ => ?_
  obtain ⟨htag, hs⟩ := h
  rcases (largeEvenSplit_E_iff (Or.inr htag)).mp hs with hpn | ⟨hn, hp3⟩
  · exact Or.inl ⟨htag, hpn⟩
  · exact Or.inr ⟨htag, hn, hp3⟩

theorem ggBstarInputOn_of_notE7E8All {S : ℕ → LargeEvenLabel → Prop}
    (h : GGBstarInputOn fun p lab => S p lab ∧ ¬ GGTableBE7E8AllLabel p lab) :
    GGBstarInputOn S := by
  refine GGBstarInputOn.mono_split (ggBstarInputOn_E7E8_all.or h) fun p lab hS _ => ?_
  by_cases hE : GGTableBE7E8AllLabel p lab
  · exact Or.inl hE
  · exact Or.inr ⟨hS, hE⟩

theorem ggStdSubPreInputOn_of_notE7E8All (hF7 : TableBExcTwo.GGE7TwoRootFusionInput)
    (hF8 : TableBExcTwo.GGE8TwoRootFusionInput) {S : ℕ → LargeEvenLabel → Prop}
    (h : GGStdSubPreInputOn fun p lab => S p lab ∧ ¬ GGTableBE7E8AllLabel p lab) :
    GGStdSubPreInputOn S := by
  refine GGStdSubPreInputOn.mono_split ((ggStdSubPreInputOn_E7E8_all hF7 hF8).or h)
    fun p lab hS _ => ?_
  by_cases hE : GGTableBE7E8AllLabel p lab
  · exact Or.inl hE
  · exact Or.inr ⟨hS, hE⟩

theorem ggTableBOtherRest4_cases_of_noF4E7E8 {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (h : GGTableBOtherRest4 p lab)
    (hF : ¬ GGTableBF4AllLabel p lab) (hE : ¬ GGTableBE7E8AllLabel p lab)
    (hs : LargeEvenSplit p lab) :
    lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .triD4 ∨ lab.tag = .twF4 ∨ lab.tag = .G2der ∨
      lab.tag = .twF4der := by
  rcases ggTableBOtherRest4_cases hp hlab h hs with h1 | h1 | h1 | h1 | h1 | h1 | ⟨ht, -⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1))))
  · exfalso
    rcases ht with ht | ht
    · exact hF ⟨ht, hs⟩
    · exact hE ⟨ht, hs⟩

end CFSG.StandardType
