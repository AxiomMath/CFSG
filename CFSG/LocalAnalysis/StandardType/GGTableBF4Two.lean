module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoBstar
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Split
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoTableB

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def GGTableBF4TwoLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .F4 ∧ lab.n = 1 ∧ p = 3

@[expose] def GGTableBF4AllLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .F4 ∧ LargeEvenSplit p lab


theorem largeEvenLabelAll_tableB_F4Two {lab : LargeEvenLabel} (htag : lab.tag = .F4)
    (hn : lab.n = 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift 3 r R ∧ GGBstarBound 3 r R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hn
  subst htag hn
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK])
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  exact ⟨K, inferInstance, inferInstance, hK, hQ', 3, TableBF4Two.ggTorusLift_F4Two,
    TableBF4Two.ggBstarBound_F4Two hK2 3 _⟩

theorem ggBstarInputOn_F4Two : GGBstarInputOn GGTableBF4TwoLabel :=
  TableBF4.ggBstarInputOn_of_labelAll fun _ _ _ _ h => by
    obtain ⟨htag, hn, rfl⟩ := h
    exact largeEvenLabelAll_tableB_F4Two htag hn

theorem ggBstarInputOn_F4_all : GGBstarInputOn GGTableBF4AllLabel :=
  TableBF4.ggBstarInputOn_of_labelAll fun p lab hp hlab h => by
    obtain ⟨htag, hs⟩ := h
    rcases (largeEvenSplit_F4_iff htag).mp hs with hpn | ⟨hn, rfl⟩
    · exact (largeEvenLabelAll_tableB_F4_split htag hlab hp hpn).mono
        fun _ _ _ _ ⟨r, h1, h2, _⟩ => ⟨r, h1, h2⟩
    · exact largeEvenLabelAll_tableB_F4Two htag hn

@[expose] def GGF4TwoEndNodeAdmInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    GGEndNodeAdm 3 3 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K)

theorem largeEvenLabelAll_endNodeAdm_F4Two (hE : GGF4TwoEndNodeAdmInput) {lab : LargeEvenLabel}
    (htag : lab.tag = .F4) (hn : lab.n = 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift 3 r R ∧ GGEndNodeAdm 3 r R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hn
  subst htag hn
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK])
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  exact ⟨K, inferInstance, inferInstance, hK, hQ', 3, TableBF4Two.ggTorusLift_F4Two, hE K hK2⟩

theorem ggStdSubPreInputOn_F4Two (hE : GGF4TwoEndNodeAdmInput) :
    GGStdSubPreInputOn GGTableBF4TwoLabel :=
  ggStdSubPreInputOn_of_labels_adm ggLNoncyclicInput_holds fun _ _ _ _ h => by
    obtain ⟨htag, hn, rfl⟩ := h
    exact largeEvenLabelAll_endNodeAdm_F4Two hE htag hn

theorem ggStdSubPreInputOn_F4_all (hE : GGF4TwoEndNodeAdmInput) :
    GGStdSubPreInputOn GGTableBF4AllLabel :=
  ggStdSubPreInputOn_of_labels_adm ggLNoncyclicInput_holds fun p lab hp hlab h => by
    obtain ⟨htag, hs⟩ := h
    rcases (largeEvenSplit_F4_iff htag).mp hs with hpn | ⟨hn, rfl⟩
    · exact (largeEvenLabelAll_tableB_F4_split htag hlab hp hpn).mono
        fun _ _ _ _ ⟨r, h1, _, h3⟩ => ⟨r, h1, ggEndNodeAdm_of_ggEndNode h3⟩
    · exact largeEvenLabelAll_endNodeAdm_F4Two hE htag hn

end CFSG.StandardType
