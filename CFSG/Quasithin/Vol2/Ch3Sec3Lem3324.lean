module

public import CFSG.Quasithin.Vol2.Ch3Sec3Sec
public import CFSG.Quasithin.Vol2.Ch3Sec3StatementsB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3

@[expose] def Obs3_3_24 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsAltBlockType L 6 ∨ CFSG.Quasithin.IsHatA6Block L ∨ IsG2Block L ∨
      IsPSL 3 2 1 ↥(autOn L (vPlus L T))

@[expose] def Step3_3_24 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsPSL 3 2 1 ↥(autOn L (vPlus L T)) →
    HasNoncentralTwoChief L 2 → ¬ HasNoncentralTwoChief L 4 →
    ¬ D ≤ Subgroup.normalizer (pCoreOf 2
      (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T) : Set G) → False

theorem stmt3_3_24_of (h23 : Stmt3_3_23) (hObs : Obs3_3_24) (hS : Step3_3_24) : Stmt3_3_24 := by
  intro G _ _ T M L D h
  rcases hObs G T M L D h with hA | hH | hG | hP
  · exact Or.inl hA
  · exact Or.inr (Or.inl hH)
  · exact Or.inr (Or.inr (Or.inl hG))
  · rcases h23 G T M L D h hP with ⟨hLn, -⟩ | ⟨⟨hk2, hk4⟩, hD⟩
    · exact Or.inr (Or.inr (Or.inr hLn))
    · exact (hS G T M L D h hP hk2 hk4 hD).elim

end CFSG.Quasithin.H13
