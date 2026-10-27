module

public import CFSG.Quasithin.Background.C1PackNat
public import CFSG.Quasithin.Background.C1GNBlocks

public section

namespace CFSG.Quasithin.C1Pack

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem pRank_le_two_of_isSQTKTC {P : Subgroup G} (h : IsSQTKTC P) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p P ≤ 2 := by
  intro p hp hp2
  have : Fact p.Prime := ⟨hp⟩
  have h1 : CFSG.Open.pRank p (⊤ : Subgroup ↥P) ≤ 2 := h.2 p hp hp2
  have h2 : CFSG.Open.pRank p (⊤ : Subgroup ↥P) = CFSG.Open.pRank p P :=
    pRank_top_subtype (p := p) P
  omega

theorem inClassG_of_solvable_minParabolic {P S MP : Subgroup G} (h : MinParabolic P S MP)
    (hF : CharTwo P) (hsolv : Group.IsSolvable ↥P)
    (hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p P ≤ 2)
    (hJ : ¬ thompsonJ S ≤ Subgroup.centralizer (VZ S P : Set G)) (hS : baum S = S) :
    InClassG P S := by
  obtain ⟨-, hVel, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo h.isSylow hF (le_refl _)
  obtain ⟨L, hL, hnat⟩ := exists_single_block hVel h hsolv hSQT hred hJ hS
  obtain ⟨hn1, -, -⟩ := isNatL2Section_fstarPre hVel hred.2.1 hL hnat
  exact ⟨h.isSylow, hF, (minParabolic_iff.1 h).1, 1, le_rfl, hn1⟩

end CFSG.Quasithin.C1Pack
