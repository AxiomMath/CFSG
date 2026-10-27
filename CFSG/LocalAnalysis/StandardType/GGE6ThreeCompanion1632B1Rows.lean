module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1632GeomRows
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1632FrobTriv
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1632Rat
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1632RatOne
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1632RatOpp
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1632Lang

public section

namespace CFSG.StandardType.S2MathAs1E6Companion1625

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587

private theorem ltrb1rows_lang {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (row : LargeEvenLabel → LargeEvenLabel → Prop) : LangOnConnectedOn Omega row :=
  fun _ _ _ _ _ ρ _ _ _ _ _ => langOnConnectedAt_producer ρ

theorem b1On_r1_holds
    (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    B1On Omega CFSG.StandardType.GGE6ThreeR1Labels1585 1 1 := by
  have ha := b1aOn_holds Omega
  have hb := b1bOn_holds Omega
  have hg := b1GeomOn_r1_holds Omega
  exact b1On_of_pieces ha hb hg (b1RatOn_one_of_geom_one ha hb hg)

theorem b1On_r3_holds
    (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    B1On Omega CFSG.StandardType.GGE6ThreeR3Labels1585 3 3 := by
  have ha := b1aOn_holds Omega
  have hb := b1bOn_holds Omega
  have hg := b1GeomOn_r3_holds Omega
  have hF : FrobeniusTrivialOn Omega CFSG.StandardType.GGE6ThreeR3Labels1585 :=
    frobeniusTrivialOn_of_geom_three Omega (fun labL labJ h => by
      unfold CFSG.StandardType.GGE6ThreeR3Labels1585 at h
      rcases h with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩) hg
  exact b1On_of_pieces ha hb hg
    (b1RatOn_of_frobenius_trivial ha hb hg hF (ltrb1rows_lang _))

theorem b1On_r4_holds
    (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    B1On Omega CFSG.StandardType.GGE6ThreeR4Labels1585 1 1 := by
  have ha := b1aOn_holds Omega
  have hb := b1bOn_holds Omega
  have hg := b1GeomOn_r4_holds Omega
  exact b1On_of_pieces ha hb hg (b1RatOn_one_of_geom_one ha hb hg)

theorem b1On_r16_holds
    (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    B1On Omega CFSG.StandardType.GGE6ThreeR16Labels1585 3 3 := by
  have ha := b1aOn_holds Omega
  have hb := b1bOn_holds Omega
  have hg := b1GeomOn_r16_holds Omega
  have hF : FrobeniusTrivialOn Omega CFSG.StandardType.GGE6ThreeR16Labels1585 :=
    frobeniusTrivialOn_of_geom_three Omega (fun labL labJ h => by
      unfold CFSG.StandardType.GGE6ThreeR16Labels1585 at h
      rcases h with ⟨⟨h1, h2⟩ | ⟨h1, h2⟩, -⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩) hg
  exact b1On_of_pieces ha hb hg
    (b1RatOn_of_frobenius_trivial ha hb hg hF (ltrb1rows_lang _))

theorem b1On_r4Opp_holds
    (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    B1On Omega CFSG.StandardType.GGE6ThreeR4OppLabels1585 1 1 := by
  have ha := b1aOn_holds Omega
  have hb := b1bOn_holds Omega
  have hg := b1GeomOn_r4Opp_holds Omega
  exact b1On_of_pieces ha hb hg (b1RatOn_one_of_geom_one ha hb hg)

end CFSG.StandardType.S2MathAs1E6Companion1625

end
