module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection7.Defs
public import CFSG.Walter.Bender1970.S1.Rank
import CFSG.Walter.Transitivity.Step

public section

namespace CFSG.Walter

open CFSG CFSG.Walter.Transitivity

private theorem transitivity_of_card_eq {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)
    (hT : IsMulCommutative (T : Subgroup G)) {V : Subgroup G} (hVT : V ≤ T)
    (hVcomm : IsMulCommutative V) (hVexp : ∀ x ∈ V, x ^ 2 = 1) (hVcard : 8 ≤ Nat.card V)
    (hsolv : ∀ t : G, orderOf t = 2 →
      Group.IsSolvable (Subgroup.centralizer ({t} : Set G)))
    {q : Nat.Primes} (hq : q.val ≠ 2) (n : ℕ) :
    ∀ X : Subgroup G, Nat.card X = n → (T : Subgroup G) ≤ X →
      ConjugationActionTransitiveOn (X ⊓ Subgroup.centralizer ((T : Subgroup G) : Set G))
        (section7HStarFamily X (T : Subgroup G) ({q} : Set Nat.Primes)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X hXn hTX
  have houter : ∀ Y : Subgroup G, (T : Subgroup G) ≤ Y → Nat.card Y < Nat.card X →
      ConjugationActionTransitiveOn (Y ⊓ Subgroup.centralizer ((T : Subgroup G) : Set G))
        (section7HStarFamily Y (T : Subgroup G) ({q} : Set Nat.Primes)) :=
    fun Y hTY hY => ih _ (hXn ▸ hY) Y rfl hTY
  have key : ∀ m : ℕ,
      ∀ Q₁ ∈ section7HStarFamily X (T : Subgroup G) ({q} : Set Nat.Primes),
      ∀ Q₂ ∈ section7HStarFamily X (T : Subgroup G) ({q} : Set Nat.Primes),
      Nat.card G - Nat.card (Q₁ ⊓ Q₂ : Subgroup G) = m →
        ∃ k : (X ⊓ Subgroup.centralizer ((T : Subgroup G) : Set G) : Subgroup G),
          Q₂ = Q₁.conjBy (k : G) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ihm =>
    intro Q₁ hQ₁ Q₂ hQ₂ hm
    refine exists_conjBy_step T hT hTX hVT hVcomm hVexp hVcard hsolv hq houter
      (fun R₁ hR₁ R₂ hR₂ hlt => ihm _ ?_ R₁ hR₁ R₂ hR₂ rfl) hQ₁ hQ₂
    have := Subgroup.card_le_card_group (R₁ ⊓ R₂)
    omega
  exact fun Q₁ hQ₁ Q₂ hQ₂ => key _ Q₁ hQ₁ Q₂ hQ₂ rfl

theorem thompson_transitivity_of_le
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)
    (hT : IsMulCommutative (T : Subgroup G)) (hrank : 3 ≤ rank (T : Subgroup G))
    (hsolv : ∀ t : G, orderOf t = 2 →
      Group.IsSolvable (Subgroup.centralizer ({t} : Set G)))
    {q : Nat.Primes} (hq : q.val ≠ 2) {X : Subgroup G} (hTX : (T : Subgroup G) ≤ X) :
    ConjugationActionTransitiveOn (X ⊓ Subgroup.centralizer ((T : Subgroup G) : Set G))
      (section7HStarFamily X (T : Subgroup G) ({q} : Set Nat.Primes)) := by
  obtain ⟨V, hVT, hV, hVcard⟩ := CFSG.SectionRank.exists_pRank one_lt_two (T : Subgroup G)
  rw [← rank_eq_pRank_of_isPGroup Nat.prime_two T.isPGroup'] at hVcard
  have hV8 : 8 ≤ Nat.card V :=
    hVcard ▸ (Nat.pow_le_pow_right two_pos hrank : 2 ^ 3 ≤ 2 ^ rank (T : Subgroup G))
  exact transitivity_of_card_eq T hT hVT hV.1 hV.2 hV8 hsolv hq _ X rfl hTX

theorem thompson_transitivity
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)
    (hT : IsMulCommutative (T : Subgroup G)) (hrank : 3 ≤ rank (T : Subgroup G))
    (hsolv : ∀ t : G, orderOf t = 2 →
      Group.IsSolvable (Subgroup.centralizer ({t} : Set G)))
    {q : Nat.Primes} (hq : q.val ≠ 2) :
    ConjugationActionTransitiveOn (Subgroup.centralizer ((T : Subgroup G) : Set G))
      (section7HStarFamily (⊤ : Subgroup G) (T : Subgroup G) ({q} : Set Nat.Primes)) := by
  intro Q₁ hQ₁ Q₂ hQ₂
  obtain ⟨k, hk⟩ := thompson_transitivity_of_le T hT hrank hsolv hq le_top Q₁ hQ₁ Q₂ hQ₂
  exact ⟨⟨k, k.2.2⟩, hk⟩

end CFSG.Walter
