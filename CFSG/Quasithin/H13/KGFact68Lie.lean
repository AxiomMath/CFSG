module

public import CFSG.Quasithin.H13.KGFact68LieRed
public import CFSG.Quasithin.H13.KGFact68Alt

public section

namespace CFSG.Quasithin.H13.KG68

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem sqtkCharTwoLie_of_isL34OrG24 {X : Type} [Group X] (h : Ch1.IsL34OrG24 X) :
    Ch1.SQTKCharTwoLie X := by
  rcases h with h | h
  · exact Or.inl (Or.inl ⟨2, Or.inr (Or.inl ⟨by norm_num, h⟩)⟩)
  · exact Or.inl (Or.inl ⟨2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨le_rfl, h⟩))))⟩)

theorem e68ComponentFactsLie_of
    (hInn : Ch1.EvenLieAutInner) (hU33 : U33AutInner)
    (hCS : ∀ (S : Type) [Group S] [Finite S], (Ch1.SQTKCharTwoLie S ∨
      Assembly.LowTwoRank.StatedClassicalModel S .PSU 3 3 1) → CartanSinger S) :
    E6.E68ComponentFactsLie := by
  intro Y _ _ L A R z hcase h
  obtain ⟨hS, hlie, -⟩ := hcase
  rcases hlie with hq | he | hu
  · exact e68Concl_of_cartanSinger h hS (fun β hβ hP => hInn ↥L hq β hβ hP)
      (hCS ↥L (Or.inl hq))
  · exfalso
    obtain ⟨e⟩ := he
    have hZ := center_eq_bot_of_simple h hS
    exact not_e68Hyp_of_alt6 h
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e))
      (by rw [hZ, Subgroup.card_bot]; decide)
  · exact e68Concl_of_cartanSinger h hS (fun β hβ hP => hU33 ↥L hu β hβ hP)
      (hCS ↥L (Or.inr hu))

theorem e68ComponentFactsCover_of (hInn : Ch1.EvenLieAutInner)
    (hCS : ∀ (S : Type) [Group S] [Finite S], Ch1.IsL34OrG24 S → CartanSingerCover S) :
    E6.E68ComponentFactsCover := by
  intro Y _ _ L A R z hcase h
  obtain ⟨-, hZP, hS, -⟩ := hcase
  exact e68Concl_of_cartanSingerCover h hZP (MulEquiv.refl _)
    (fun β hβ hP => hInn _ (sqtkCharTwoLie_of_isL34OrG24 hS) β hβ hP) (hCS _ hS)

end CFSG.Quasithin.H13.KG68
