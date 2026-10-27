module

public import CFSG.Permutation.FiveTransitive.ElementaryShortOrbitSemiregular
public import CFSG.Permutation.FiveTransitive.ThreeSwapLocalFixedCounts
public import CFSG.Permutation.FiveTransitive.ThreeSwapEvenCounts

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.ElementaryNormalizerSemiregular

open MulAction FixedNormalizerAction

theorem semiregular
    {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (heven : ∀ g : G, Equiv.Perm.sign (toPermHom G X g) = 1)
    (hdegree : Fintype.card X % 4 = 3)
    (hmax : ∀ g : G, orderOf g = 2 → (fixedBy X g).ncard ≤ 7)
    (Q : Subgroup G) (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (hfree : ∀ (q : Q) (t : X), t ∉ fixedPoints Q X → q • t = t → q = 1)
    (K : Subgroup (Normalizer Q)) (hsquare : ∀ k : K, k ^ 2 = 1)
    (hcomm : IsMulCommutative K)
    (a b c d : K) (haQ : a.val ∈ Inside Q) (hane : a ≠ 1)
    (e : Fin 6 ↪ Fixed (X := X) Q)
    (hb : toPermHom (Normalizer Q) (Fixed (X := X) Q) b.val = Equiv.swap (e 0) (e 1))
    (hc : toPermHom (Normalizer Q) (Fixed (X := X) Q) c.val = Equiv.swap (e 2) (e 3))
    (hd : toPermHom (Normalizer Q) (Fixed (X := X) Q) d.val = Equiv.swap (e 4) (e 5)) :
    let E := (fixedBy X b \ fixedPoints Q X) ∪ (fixedBy X (a * b) \ fixedPoints Q X)
    E.ncard = 4 ∧ (∀ g : K, g ≠ 1 → ∀ t ∉ fixedPoints Q X ∪ E, g • t ≠ t) ∧
      ∀ (g : K) (t : X), t ∈ E → g • t ∈ E := by
  classical
  let _ : CommGroup K := { (inferInstance : Group K) with
    mul_comm := isMulCommutative_iff.mp hcomm }
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  have haf : f a.val = 1 := by
    apply Equiv.ext
    intro y
    apply Subtype.ext
    exact mem_fixedPoints.mp (by simpa only [fixed_eq Q] using y.property)
      (⟨a.val.val, haQ⟩ : Q)
  have hfix : fixedBy X a = fixedPoints Q X := by
    ext t
    constructor
    · intro ht
      by_contra hout
      have he := hfree ⟨a.val.val, haQ⟩ t hout ht
      exact hane (Subtype.ext (Subtype.ext (congrArg (fun q : Q => q.val) he)))
    · intro ht
      exact mem_fixedPoints.mp ht (⟨a.val.val, haQ⟩ : Q)
  have hmaxK (g : K) (hg : g ≠ 1) : (fixedBy X g).ncard ≤ 7 := by
    have hs : g.val.val ^ 2 = 1 := congrArg (fun k : K => k.val.val) (hsquare g)
    have hn : g.val.val ≠ 1 := fun h => hg (Subtype.ext (Subtype.ext h))
    exact hmax g.val.val (orderOf_eq_prime hs hn)
  have hcount (u : K) (v w : Fixed (X := X) Q) (hne : v ≠ w)
      (hu : f u.val = Equiv.swap v w) :
      (fixedBy X u \ fixedPoints Q X).ncard = 2 := by
    have hlocal := ThreeSwapEvenCounts.local_five Q hseven u.val v w hne hu
    have hn : u.val ≠ 1 := by
      intro h
      have hh := hu
      rw [h, map_one] at hh
      exact hne (Equiv.swap_eq_one_iff.mp hh.symm)
    have ho : orderOf u.val = 2 := orderOf_eq_prime
      (congrArg Subtype.val (hsquare u)) hn
    have hh := NormalizerEvenCoset.fixed_card_eq_two heven hdegree hmax Q u.val hlocal 1
      (by simpa only [OneMemClass.coe_one, one_mul] using ho)
    rw [NormalizerFixedComplement.fixed_card] at hh
    change (fixedBy X u.val.val \ fixedPoints Q X).ncard = 2
    simpa only [OneMemClass.coe_one, one_mul] using hh
  have hacount (u : K) (v w : Fixed (X := X) Q) (hne : v ≠ w)
      (hu : f u.val = Equiv.swap v w) :
      (fixedBy X (a * u) \ fixedPoints Q X).ncard = 2 := by
    apply hcount (a * u) v w hne
    change f (a.val * u.val) = _
    rw [map_mul, haf, one_mul, hu]
  have hpair := ThreeSwapLocalFixedCounts.actual_pair_counts Q hseven e
    b.val c.val d.val hb hc hd
  have hseven' : (fixedBy X a).ncard = 7 := by
    rw [hfix]
    simpa only [fixed_eq Q, Nat.card_coe_set_eq] using hseven
  obtain ⟨hE, hsemi⟩ := ElementaryShortOrbitSemiregular.semiregular
    (fun g => by simpa only [pow_two] using hsquare g) hmaxK a b c d hseven'
    (by rw [hfix]; exact hcount b _ _ (e.injective.ne (by decide)) hb)
    (by rw [hfix]; exact hacount b _ _ (e.injective.ne (by decide)) hb)
    (by rw [hfix]; exact hcount c _ _ (e.injective.ne (by decide)) hc)
    (by rw [hfix]; exact hacount c _ _ (e.injective.ne (by decide)) hc)
    (by rw [hfix]; exact hcount d _ _ (e.injective.ne (by decide)) hd)
    (by rw [hfix]; exact hacount d _ _ (e.injective.ne (by decide)) hd)
    (by rw [hfix]; exact hpair.1)
    (by rw [hfix]; exact hpair.2.1)
    (by rw [hfix]; exact hpair.2.2)
  rw [hfix] at hE hsemi
  refine ⟨hE, hsemi, ?_⟩
  intro g t ht
  rcases ht with ht | ht
  · exact Or.inl (by rw [← hfix] at ht ⊢; exact ElementaryPairOrientation.invariant_difference a b g t ht)
  · exact Or.inr (by rw [← hfix] at ht ⊢; exact ElementaryPairOrientation.invariant_difference a (a * b) g t ht)

end FiveTransitive.ElementaryNormalizerSemiregular

end CFSG
