module

public import CFSG.Quasithin.Background.G117CanonMain
public import CFSG.Quasithin.Background.G117CanonG2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

namespace Canon

open CFSG.Quasithin.G11.G117 CFSG.Assembly.LowTwoRank

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem step10
    {Q : ConclPred} (hQ : QContains Q)
    (hG2 : SzG11S.NoConfigG2) (hD : G22DerivedFacts) : Step10 Q := by
  intro V _ _ _ B Γ v₁ W X X₀ L m c h10
  obtain ⟨n, ⟨hn1, hd, -, -, hnat⟩, hend, -⟩ := h10
  have hdV : Module.finrank (ZMod 2) V = 6 * n := by
    rwa [finrank_top] at hd
  by_cases hn2 : 2 ≤ n
  · exact hG2 V B Γ v₁ W X X₀ L c.setup.conf c.props n hn2
      (isG2NaturalModule_of_restrictRange_top hnat)
  · have hn : n = 1 := by omega
    subst hn
    have hnatV := isG2NaturalModule_of_restrictRange_top hnat
    obtain ⟨φ, -⟩ := hnat
    let e := (restrictRangeTop (normalClosure Γ L)).trans φ
    have hautH : Nat.card (MulAut ↥(normalClosure Γ L)) = 12096 := by
      rw [Nat.card_congr (MulAut.congr e).toEquiv]
      exact hD.2
    have hC1 : Γ ⊓ Subgroup.centralizer (normalClosure Γ L : Set (GLV V)) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      exact eq_one_of_commute_of_endIsField_one hend (Subgroup.mem_centralizer_iff.1 hx.2)
    have hle := natCard_le_aut_mul_centralizer (Γ := Γ) (normalClosure_normal Γ L)
    rw [hC1, Subgroup.card_bot, hautH] at hle
    have hΓle : Nat.card ↥Γ ≤ 12096 := by omega
    have hC : ∀ c' : GLV V, (∀ h ∈ normalClosure Γ L, h * c' = c' * h) → c' = 1 :=
      fun c' hc' => eq_one_of_commute_of_endIsField_one hend hc'
    rcases isG2NaturalModule_overgroup hnatV c.h108.H_le (normalClosure_normal Γ L) hC hΓle with
      ⟨-, h⟩ | ⟨-, h⟩
    · exact c.setup.notConcl (hQ.c6' B Γ X ⟨by omega, h⟩)
    · exact c.setup.notConcl (hQ.c6 B Γ X ⟨by omega, h⟩)

end Canon

end G11

end CFSG.Quasithin
