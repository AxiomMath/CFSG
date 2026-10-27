module

public import CFSG.Quasithin.Background.C126Glue
public import CFSG.Quasithin.Background.C126Solv
public import CFSG.Quasithin.Background.C126Split2
public import CFSG.Quasithin.Background.C118BridgeOne

public section

namespace CFSG.Quasithin.C126

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem concl_of_concl1 {C₁ C₂ : Subgroup G → Subgroup G} {H T : Subgroup G} (hF : CharTwo H)
    (hT : IsSylowTwoOf T H) (h : Concl1 C₁ C₂ H T) :
    C₁ T ≤ centerOf H ∨ H ≤ Subgroup.normalizer (C₂ T : Set G) ∨ Blocks H T := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (blocks_of_oneBlock hF hT h))

theorem c126Statement_of_cases {C₁ C₂ : Subgroup G → Subgroup G} (hC : IsGNChoice C₁ C₂)
    (he23 : E2.E23Statement) (hN : NatStmt C₁ C₂) (hS : A5Stmt C₁ C₂) : C126Statement C₁ C₂ := by
  intro H T hSQ hT hF hmin
  obtain ⟨M, hMP⟩ := exists_minParabolic hT hmin
  obtain ⟨-, hVel, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)
  by_cases hJ : thompsonJ T ≤ Subgroup.centralizer (VZ T H : Set G)
  · rcases C1Pack.c126_of_commutator_eq_bot hC hMP hF hJ with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hc := he23 G H T M (VZ T H) hVel hMP (C1GN.isSQTKTC_iff_sqtkGroup.1 hSQ) hF hred hJ
    rcases case_split hVel T hred.2.1 hc with hsolv | hnat | ha5
    · exact concl_of_concl1 hF hT (concl1_of_perfectCore_le hC hMP hSQ hF hsolv)
    · exact concl_of_concl1 hF hT (hN hC H T M (VZ T H) hVel hMP hSQ hF hred rfl hJ hnat)
    · exact concl_of_concl1 hF hT (hS hC H T M (VZ T H) hVel hMP hSQ hF hred rfl hJ ha5)

end CFSG.Quasithin.C126

namespace CFSG.Quasithin

theorem theoremC126_of_cases (he23 : E2.E23Statement)
    (hN : ∀ (G : Type) [Group G] [Finite G] (C₁ C₂ : Subgroup G → Subgroup G),
      C126.NatStmt C₁ C₂)
    (hS : ∀ (G : Type) [Group G] [Finite G] (C₁ C₂ : Subgroup G → Subgroup G),
      C126.A5Stmt C₁ C₂) : TheoremC126 :=
  fun G _ _ C₁ C₂ hC => C126.c126Statement_of_cases hC he23 (hN G C₁ C₂) (hS G C₁ C₂)

end CFSG.Quasithin
