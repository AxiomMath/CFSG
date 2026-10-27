module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3Main

public section

namespace CFSG.Quasithin.E2P.Asc80

open CFSG.Quasithin.A38c15 CFSG.Quasithin.B6 CFSG.QuasithinUnique

@[expose] def Asc80L3Stmt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (H : Type) [Group H] [Finite H] (K T M : Subgroup H),
    K.Normal → IsSimpleGroup ↥K → IsPSL 3 p 1 ↥K → Subgroup.centralizer (K : Set H) = ⊥ →
    IsSylowTwoOf T ⊤ → K ⊔ T = ⊤ → IsUniqueMaxOver ⊤ T M →
    M ⊓ K = K ⊓ Subgroup.centralizer (zOf (T ⊓ K) : Set H) ∧ p % 4 = 3 ∧ E2.InducesOuter T K

@[expose] def Asc80U3Stmt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (H : Type) [Group H] [Finite H] (K T M : Subgroup H),
    K.Normal → IsSimpleGroup ↥K → IsPSU 3 p 1 ↥K → Subgroup.centralizer (K : Set H) = ⊥ →
    IsSylowTwoOf T ⊤ → K ⊔ T = ⊤ → IsUniqueMaxOver ⊤ T M →
    M ⊓ K = K ⊓ Subgroup.centralizer (zOf (T ⊓ K) : Set H) ∧ p % 4 = 1

theorem asc80L3Stmt_of (hirr : SL3OddIrr) : Asc80L3Stmt :=
  fun _ _ hp2 _ _ _ _ _ _ hK hs hmodel hc hT hsup hM => asc80L3 hirr hp2 hK hs hmodel hc hT hsup hM

theorem asc80L3Eps_of (h1 : Asc80L3Stmt) (h2 : Asc80U3Stmt) : Asc80L3Eps := by
  intro p hp hp2 H _ _ K T M hK hs hmod hc hT hsup hM
  have : Fact p.Prime := ⟨hp⟩
  rcases hmod with hL | hU
  · obtain ⟨h, h4, hout⟩ := h1 p hp2 H K T M hK hs hL hc hT hsup hM
    exact ⟨h, Or.inl ⟨hL, h4, hout⟩⟩
  · obtain ⟨h, h4⟩ := h2 p hp2 H K T M hK hs hU hc hT hsup hM
    exact ⟨h, Or.inr ⟨hU, h4⟩⟩

end CFSG.Quasithin.E2P.Asc80
