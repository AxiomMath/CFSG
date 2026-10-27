module

public import CFSG.Quasithin.Vol2.Ch10SecKITs
public import CFSG.Quasithin.Vol2.Ch10SecKITu
public import CFSG.Quasithin.Vol2.Ch10SecQ34B0
public import CFSG.Quasithin.Vol2.Ch10SecKITe

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch10.SecF
open CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

theorem factTwoL2BlocksSL3_of (h36 : A36ForSQTK) (h312 : Vol2Native.A312ListFactsCat)
    (hLF : Ch10.A312LeviField) (hK1 : KGRank2ParabolicOrder) (hK3 : KGTwoA5Generate)
    (hK4 : KGMathieuNatBlock) (hK5 : KGJ4NoA5Block) :
    FactTwoL2BlocksSL3 := by
  intro G _ _ M T L X₁ X₂ n hn hM hT hL hX₁ hX₂ hne hX₁L hX₂L h₁ h₂
  have h₁' : IsNatBlock X₁ n := h₁
  have h₂' : IsNatBlock X₂ n := h₂
  have hq := isQuasisimple_Y h36 hM hT hL hX₁ hX₁L h₁' hn
  have hTs := C10E4.isSylowTwoOf_quot hT hL
  have hYc := C10E4.sqtkHypCat_quot (le_of_mem_cComp hL) (SQTKGroup.isSQTKCat hM)
  have hB₁ := xbar_mem_lFamily hT hL hX₁ hX₁L
  have hB₂ := xbar_mem_lFamily hT hL hX₂ hX₂L
  have hne₁ := xbar_ne_top hT hL hX₁ hne hX₁L hX₂L h₁' h₂'
  have hne₂ := xbar_ne_top hT hL hX₂ (Ne.symm hne) hX₂L hX₁L h₂' h₁'
  have hbar := xbar_ne hT hL hX₁ hX₂ hne hX₁L hX₂L
  have hA₁ := h312 _ hq hYc.isSQTKCat hYc.o2 _ hTs _ hB₁ hne₁
  have hA₂ := h312 _ hq hYc.isSQTKCat hYc.o2 _ hTs _ hB₂ hne₂
  rcases rows_blk (xbar_barData h₁' hn hX₁L) hA₁ (xbar_cards h₁' hn hX₁L) with hC₁ | ⟨rfl, ho₁⟩
  · exact (concl_of_C2 hLF hK1 hT hL hX₁ hX₁L h₁' hn hq hC₁).elim Or.inl (Or.inr ∘ Or.inl)
  rcases rows_blk (xbar_barData h₂' hn hX₂L) hA₂ (xbar_cards h₂' hn hX₂L) with hC₂ | ⟨-, ho₂⟩
  · exact (concl_of_C2 hLF hK1 hT hL hX₂ hX₂L h₂' hn hq hC₂).elim Or.inl (Or.inr ∘ Or.inl)
  have hJ4 : ¬ IsSporadic .J4 ↥(⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) := fun h =>
    false_of_J4 hK5 hT hL hX₁ hX₁L h₁' (ho₁.imp And.left And.left) h
  rcases ho₁ with ⟨hc₁, ho₁⟩ | ⟨hc₁, ho₁⟩
  · rcases ho₂ with ⟨hc₂, -⟩ | ⟨hc₂, -⟩
    · exact (false_of_typeB kgA7OneA5_holds hK3 hK5 hT hL hX₁ hX₂ hX₁L hX₂L h₁' h₂' hbar hc₁ hc₂
        ho₁).elim
    · exact (false_of_cross hc₂ ho₁ hJ4).elim
  · rcases ho₁ with h | h | h | h
    · rcases ho₂ with ⟨-, ho₂⟩ | ⟨hc₂, -⟩
      · exact (false_of_cross hc₁ ho₂ hJ4).elim
      · exact (false_of_M22 hK4 hT hL hX₁ hX₂ hX₁L hX₂L h₁' h₂' hbar hc₁ hc₂ (Or.inl h)).elim
    · rcases ho₂ with ⟨-, ho₂⟩ | ⟨hc₂, -⟩
      · exact (false_of_cross hc₁ ho₂ hJ4).elim
      · exact (false_of_M22 hK4 hT hL hX₁ hX₂ hX₁L hX₂L h₁' h₂' hbar hc₁ hc₂ (Or.inr h)).elim
    · exact Or.inr (Or.inr ⟨rfl, concl_M23 hT hL hX₁ hX₁L h₁' hq hc₁ h⟩)
    · exact (hJ4 h).elim

end CFSG.Quasithin.Vol2.Ch10.SecB
