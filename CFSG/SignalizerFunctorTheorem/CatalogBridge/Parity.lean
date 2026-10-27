module

import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.Basic

public section

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem two_dvd_card_of_simple_nonabelian {X : Type*} [Group X] [Finite X]
    (hsimple : IsSimpleGroup X) (hnonab : ∃ a b : X, a * b ≠ b * a) : 2 ∣ Nat.card X := by
  by_contra h
  have hodd : Odd (Nat.card X) := Nat.odd_iff.mpr (by omega)
  have hsolv : Group.IsSolvable X := CFSG.FeitThompson.isSolvable_of_odd_natCard X hodd
  obtain ⟨a, b, hab⟩ := hnonab
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv a b)

theorem ne_two_of_coprime_card_of_simple_nonabelian {X : Type*} [Group X] [Finite X]
    (hsimple : IsSimpleGroup X) (hnonab : ∃ a b : X, a * b ≠ b * a) {p : ℕ}
    (hcop : Nat.Coprime p (Nat.card X)) : p ≠ 2 := by
  rintro rfl
  have h2 := two_dvd_card_of_simple_nonabelian hsimple hnonab
  have := Nat.eq_one_of_dvd_coprimes hcop (dvd_refl 2) h2
  omega

@[expose] def NoOddOuter (X : Type*) [Group X] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ Nat.card X → ¬ p ∣ Nat.card (Outer X)

theorem card_outer_eq_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    Nat.card (Outer X) = Nat.card (Outer Y) :=
  Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv

theorem NoOddOuter.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : NoOddOuter Y) : NoOddOuter X := fun p hp hp2 hpX hpO => by
  refine h p hp hp2 (by rwa [← Nat.card_congr e.toEquiv]) ?_
  rwa [← Nat.card_congr
    (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]

theorem hypothesisA_of_noOddOuter {X : Type*} [Group X] [Finite X] (hno : NoOddOuter X)
    (hsimple : IsSimpleGroup X) (hnonab : ∃ a b : X, a * b ≠ b * a) {p : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card X)) : signalizerMcBrideHypothesisA p X := by
  have hpX : ¬ p ∣ Nat.card X := (Nat.Prime.coprime_iff_not_dvd hp).mp hcop
  have hp2 := ne_two_of_coprime_card_of_simple_nonabelian hsimple hnonab hcop
  exact hypothesisA_of_not_dvd_card_mulAut hp hsimple hnonab hcop
    (not_dvd_card_mulAut_of_not_dvd_outer hp hpX (hno p hp hp2 hpX))

theorem NoOddOuter.of_card_outer_le_two {X : Type*} [Group X] [Finite X]
    (h : Nat.card (Outer X) ≤ 2) : NoOddOuter X := fun p hp hp2 _ hpO => by
  have := Nat.le_of_dvd Nat.card_pos hpO
  have := hp.two_le
  omega

theorem NoOddOuter.of_isPGroup_two {X : Type*} [Group X] [Finite X] (h : IsPGroup 2 (Outer X)) :
    NoOddOuter X := fun p hp hp2 _ hpO => by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h
  rw [hk] at hpO
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hpO))

theorem NoOddOuter.of_card_outer_le {X : Type*} [Group X] [Finite X] {N : ℕ}
    (h : Nat.card (Outer X) ≤ N)
    (hsmall : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≤ N → q ∣ Nat.card X) : NoOddOuter X :=
  fun p hp hp2 hpX hpO =>
    hpX (hsmall p hp hp2 ((Nat.le_of_dvd Nat.card_pos hpO).trans h))

theorem NoOddOuter.of_no_large_prime {X : Type*} [Group X] [Finite X]
    (h : ∀ q : ℕ, q.Prime → 5 ≤ q → ¬ q ∣ Nat.card (Outer X)) (h3 : 3 ∣ Nat.card X) :
    NoOddOuter X := fun p hp hp2 hpX hpO => by
  have hp3 : p ≠ 3 := fun h' => hpX (h' ▸ h3)
  have h5 : 5 ≤ p := by
    have h2 := hp.two_le
    by_contra hlt
    have : p = 2 ∨ p = 3 ∨ p = 4 := by omega
    rcases this with rfl | rfl | rfl
    · exact hp2 rfl
    · exact hp3 rfl
    · exact absurd hp (by norm_num)
  exact h p hp h5 hpO

end CFSG.SignalizerFunctorTheorem.CatalogBridge
