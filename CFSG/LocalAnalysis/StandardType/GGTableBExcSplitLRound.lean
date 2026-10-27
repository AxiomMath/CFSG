module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLBstarE6
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE6
public import CFSG.LocalAnalysis.StandardType.GGAssemblyElevenDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGExcLIDLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGExcLVacLabel p lab ∨ GGExcLSplitLabel p lab ∨ GGExcLSplitE6Label p lab

@[expose] def GGExcLTableBLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGExcLSplitLabel p lab ∨ GGExcLSplitE6Label p lab

section Proved

theorem ggBstarInnerDiagLInputOn_excLID (T : ℕ → LargeEvenLabel → Prop) :
    GGBstarInnerDiagLInputOn fun p lab => T p lab ∧ GGExcLIDLabel p lab := by
  have h' := ((ggBstarInnerDiagLInputOn_excLVac T).or (ggBstarInnerDiagLInputOn_excLSplit T)).or
    (ggBstarInnerDiagLInputOn_excLSplitE6 T)
  intro G _ _ p B Bs x L D J hC hL
  refine (h' G p B Bs x L D J hC (hL.mono fun p lab hlab => ?_)).mono fun p lab hlab => ?_
  · rcases hlab.2 with h1 | h1 | h1
    · exact Or.inl (Or.inl ⟨hlab.1, h1⟩)
    · exact Or.inl (Or.inr ⟨hlab.1, h1⟩)
    · exact Or.inr ⟨hlab.1, h1⟩
  · rcases hlab with (h1 | h1) | h1
    · exact ⟨h1.1, Or.inl h1.2⟩
    · exact ⟨h1.1, Or.inr (Or.inl h1.2)⟩
    · exact ⟨h1.1, Or.inr (Or.inr h1.2)⟩

theorem ggBstarInnerDiagLInputOn_of_not_excLID {S : ℕ → LargeEvenLabel → Prop}
    (h : GGBstarInnerDiagLInputOn fun p lab => S p lab ∧ ¬ GGExcLIDLabel p lab) :
    GGBstarInnerDiagLInputOn S := by
  have h' := (ggBstarInnerDiagLInputOn_excLID S).or h
  intro G _ _ p B Bs x L D J hC hL
  refine (h' G p B Bs x L D J hC (hL.mono fun p lab hlab => ?_)).mono fun p lab hlab => ?_
  · by_cases h1 : GGExcLIDLabel p lab
    · exact Or.inl ⟨hlab, h1⟩
    · exact Or.inr ⟨hlab, h1⟩
  · rcases hlab with h1 | h1
    · exact h1.1
    · exact h1.1

theorem ggTableBIrredInputOn_excLTableB : GGTableBIrredInputOn GGExcLTableBLabel :=
  (ggTableBIrredInputOn_excSplit.or ggTableBIrredInputOn_F4).mono fun _ _ h => by
    rcases h with ⟨htag, hpn⟩ | ⟨h6, hp3, hpn⟩
    · rcases htag with h7 | h8 | h4
      · exact Or.inl ⟨Or.inr (Or.inl h7), hpn⟩
      · exact Or.inl ⟨Or.inr (Or.inr h8), hpn⟩
      · exact Or.inr ⟨h4, hpn⟩
    · exact Or.inl ⟨Or.inl ⟨h6, hp3⟩, hpn⟩

theorem ggBstarInnerDiagLInputOn_excLTableB : GGBstarInnerDiagLInputOn GGExcLTableBLabel := by
  have h' := (ggBstarInnerDiagLInputOn_excLSplit fun _ _ => True).or
    (ggBstarInnerDiagLInputOn_excLSplitE6 fun _ _ => True)
  intro G _ _ p B Bs x L D J hC hL
  refine (h' G p B Bs x L D J hC (hL.mono fun p lab hlab => ?_)).mono fun p lab hlab => ?_
  · rcases hlab with h1 | h1
    · exact Or.inl ⟨trivial, h1⟩
    · exact Or.inr ⟨trivial, h1⟩
  · rcases hlab with h1 | h1
    · exact Or.inl h1.2
    · exact Or.inr h1.2

theorem ggTableBCxInputOn_excLTableB : GGTableBCxInputOn GGExcLTableBLabel :=
  ggTableBCxInputOn_of_irred ggBstarInnerDiagLInputOn_excLTableB ggTableBIrredInputOn_excLTableB

theorem ggTableBModuleInputOn_excLTableB : GGTableBModuleInputOn GGExcLTableBLabel :=
  ggTableBModuleInputOn_of_irred ggBstarInnerDiagLInputOn_excLTableB
    ggTableBIrredInputOn_excLTableB

theorem ggTableBActionInputOn_excLTableB : GGTableBActionInputOn GGExcLTableBLabel :=
  ggTableBActionInputOn_of_irred ggBstarInnerDiagLInputOn_excLTableB
    ggTableBIrredInputOn_excLTableB

theorem ggTableBCxInputOn_of_not_excLTableB {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBCxInputOn fun p lab => S p lab ∧ ¬ GGExcLTableBLabel p lab) :
    GGTableBCxInputOn S :=
  (ggTableBCxInputOn_excLTableB.or h).mono fun p lab hS => by
    by_cases h3 : GGExcLTableBLabel p lab
    · exact Or.inl h3
    · exact Or.inr ⟨hS, h3⟩

theorem ggTableBModuleInputOn_of_not_excLTableB {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBModuleInputOn fun p lab => S p lab ∧ ¬ GGExcLTableBLabel p lab) :
    GGTableBModuleInputOn S :=
  (ggTableBModuleInputOn_excLTableB.or h).mono fun p lab hS => by
    by_cases h3 : GGExcLTableBLabel p lab
    · exact Or.inl h3
    · exact Or.inr ⟨hS, h3⟩

theorem ggTableBActionInputOn_of_not_excLTableB {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBActionInputOn fun p lab => S p lab ∧ ¬ GGExcLTableBLabel p lab) :
    GGTableBActionInputOn S :=
  (ggTableBActionInputOn_excLTableB.or h).mono fun p lab hS => by
    by_cases h3 : GGExcLTableBLabel p lab
    · exact Or.inl h3
    · exact Or.inr ⟨hS, h3⟩

end Proved

@[expose] def GGExcSplitNoTransvectionInput :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n p : ℕ), Nat.card K = 2 ^ n → p.Prime →
    p ∣ 2 ^ n - 1 →
      (p ≠ 3 →
        GGNoTransvectionTorus p 6 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K)) ∧
      GGNoTransvectionTorus p 7 (TableBExc.RecipeGroup .E7 K) (TableBExc.RecipeID .E7 K) ∧
      GGNoTransvectionTorus p 8 (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K) ∧
      GGNoTransvectionTorus p 4 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K)

section Tv

theorem ggLTransvectionCenterInputOn_excLTableB_of (hX : GGExcSplitNoTransvectionInput) :
    GGLTransvectionCenterInputOn GGExcLTableBLabel := by
  refine ggLTransvectionCenterInputOn_of_labels' ggLNoncyclicInput_holds fun p lab hp hlab h => ?_
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  rcases h with ⟨htag, hpn⟩ | ⟨htag, hp3, hpn⟩
  · dsimp only at htag hpn hn
    have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hn hpn
    rcases htag with rfl | rfl | rfl <;> intro Q hQ <;> dsimp only [LargeEvenRawDatum] at hQ ⊢ <;>
      refine recipeChevalley_and (fun K _ _ hK => ?_) hQ <;>
      have : CharP K 2 := charP_two_of_card hK <;>
      have hpq : p ∣ Nat.card K - 1 := (by rw [hK]; exact hpn)
    · exact ⟨7, TableBExc.ggTorusLift_E7 hp hp2 hpq, (hX K n p hK hp hpn).2.1⟩
    · exact ⟨8, TableBExc.ggTorusLift_E8 hp hp2 hpq, (hX K n p hK hp hpn).2.2.1⟩
    · exact ⟨4, TableBF4.ggTorusLift_F4 hp hp2 hpq, (hX K n p hK hp hpn).2.2.2⟩
  · dsimp only at htag hpn hn
    subst htag
    have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hn hpn
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    refine recipeChevalley_and (fun K _ _ hK => ?_) hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
    exact ⟨6, TableBExc.ggTorusLift_E6 hp hp2 hp3 hpq, (hX K n p hK hp hpn).1 hp3⟩

theorem ggLTransvectionCenterInputOn_of_not_excLTableB (hX : GGExcSplitNoTransvectionInput)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : GGLTransvectionCenterInputOn fun p lab => S p lab ∧ ¬ GGExcLTableBLabel p lab) :
    GGLTransvectionCenterInputOn S := by
  have h' := (ggLTransvectionCenterInputOn_excLTableB_of hX).or h
  intro G _ _ p B Bs x L D J hC hL
  refine h' G p B Bs x L D J hC (hL.mono fun p lab hlab => ?_)
  by_cases h1 : GGExcLTableBLabel p lab
  · exact Or.inl h1
  · exact Or.inr ⟨hlab, h1⟩

end Tv

@[expose] def GGCorFourTwoOpenLIDRound12Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGCorFourTwoOpenLIDRest3Label p lab ∧ ¬ GGExcLIDLabel p lab

@[expose] def GGCorFourTwoOpenTableBRound12Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGCorFourTwoOpenTableBRound11Label p lab ∧ ¬ GGExcLTableBLabel p lab

@[expose] def GGCorFourTwoOpenLineRound12Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGCorFourTwoOpenLineRound11Label p lab ∧ ¬ GGExcLLineAllLabel p lab

@[expose] def GGCorFourTwoOpenTvRound12Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGCorFourTwoOpenTvRest3Label p lab ∧ ¬ GGExcLTableBLabel p lab

section Round

theorem ggBstarInnerDiagLInputOn_rest3_of_round12
    (h : GGBstarInnerDiagLInputOn GGCorFourTwoOpenLIDRound12Label) :
    GGBstarInnerDiagLInputOn GGCorFourTwoOpenLIDRest3Label :=
  ggBstarInnerDiagLInputOn_of_not_excLID h

theorem ggTableBCxInputOn_round11_of_round12
    (h : GGTableBCxInputOn GGCorFourTwoOpenTableBRound12Label) :
    GGTableBCxInputOn GGCorFourTwoOpenTableBRound11Label :=
  ggTableBCxInputOn_of_not_excLTableB h

theorem ggTableBModuleInputOn_round11_of_round12
    (h : GGTableBModuleInputOn GGCorFourTwoOpenTableBRound12Label) :
    GGTableBModuleInputOn GGCorFourTwoOpenTableBRound11Label :=
  ggTableBModuleInputOn_of_not_excLTableB h

theorem ggTableBActionInputOn_round11_of_round12
    (h : GGTableBActionInputOn GGCorFourTwoOpenTableBRound12Label) :
    GGTableBActionInputOn GGCorFourTwoOpenTableBRound11Label :=
  ggTableBActionInputOn_of_not_excLTableB h

theorem ggLTransvectionCenterInputOn_rest3_of_round12 (hX : GGExcSplitNoTransvectionInput)
    (h : GGLTransvectionCenterInputOn GGCorFourTwoOpenTvRound12Label) :
    GGLTransvectionCenterInputOn GGCorFourTwoOpenTvRest3Label :=
  ggLTransvectionCenterInputOn_of_not_excLTableB hX h

theorem ggLNoInvariantLineInputOn_round11_of_round12
    (h : GGLNoInvariantLineInputOn GGCorFourTwoOpenLineRound12Label) :
    GGLNoInvariantLineInputOn GGCorFourTwoOpenLineRound11Label :=
  ggLNoInvariantLineInputOn_of_not_excLLineAll h

end Round

end CFSG.StandardType

end
