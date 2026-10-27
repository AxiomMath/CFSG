module

public import CFSG.Quasithin.Vol2.Ch5StatementsDS
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112Slice
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Concl

variable {G : Type} [Group G]

@[expose] def F112ConclWith (P : Subgroup G → Subgroup G → Subgroup G → Prop)
    (L1 L2 S : Subgroup G) : Prop :=
  ∃ L1' L2' : Subgroup G, ((L1' = L1 ∧ L2' = L2) ∨ (L1' = L2 ∧ L2' = L1)) ∧
    (centerOf S ≤ Subgroup.centralizer (L1 : Set G) ∨
        centerOf S ≤ Subgroup.centralizer (L2 : Set G) →
      centerOf S ≤ Subgroup.centralizer (L1' : Set G)) ∧
    P L1' L2' S ∧ F112Second L1' L2' S

theorem F112ConclWith.symm {P : Subgroup G → Subgroup G → Subgroup G → Prop}
    {L1 L2 S : Subgroup G} (h : F112ConclWith P L1 L2 S) : F112ConclWith P L2 L1 S := by
  obtain ⟨L1', L2', hsw, hZ, hl, h2⟩ := h
  exact ⟨L1', L2', hsw.symm, fun hc => hZ hc.symm, hl, h2⟩

end Concl

@[expose] def DSAConc : F112Conc :=
  fun _ _ _ L1 L2 S => F112ConclWith F112ListA L1 L2 S

end CFSG.Quasithin.H13
