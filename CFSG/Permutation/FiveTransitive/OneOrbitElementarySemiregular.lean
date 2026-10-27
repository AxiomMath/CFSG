module

public import CFSG.Permutation.FiveTransitive.OneOrbitOrderFourCentralizerConsumer
public import CFSG.Permutation.FiveTransitive.ElementaryNormalizerSemiregular
public import CFSG.Permutation.FiveTransitive.NormalizerUniqueOrbitGeometry
public import CFSG.Permutation.FiveTransitive.NormalizerEvenCentralizerTwo
public import CFSG.Permutation.FiveTransitive.NormalizerOrbitCoset

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.OneOrbitElementarySemiregular

open MulAction FixedNormalizerAction

private theorem centralizer_two
    {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (heven : ∀ g : G, Equiv.Perm.sign (toPermHom G X g) = 1)
    (hdegree : Fintype.card X % 4 = 3)
    (hmax : ∀ g : G, orderOf g = 2 → (fixedBy X g).ncard ≤ 7)
    (Q : Subgroup G) (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥)
    (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (hfree : ∀ (q : Q) (t : X), t ∉ fixedPoints Q X → q • t = t → q = 1)
    (K : Subgroup (Normalizer Q)) (hsquare : ∀ k : K, k ^ 2 = 1)
    (u : K) (p r : Fixed (X := X) Q) (hpr : p ≠ r)
    (hu : toPermHom (Normalizer Q) (Fixed (X := X) Q) u.val = Equiv.swap p r) :
    Nat.card ((Subgroup.centralizer ({u.val.val} : Set G)).subgroupOf Q) = 2 := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlocal := ThreeSwapEvenCounts.local_five Q hseven u.val p r hpr hu
  have hun : u.val ≠ 1 := by
    intro h
    rw [h, map_one] at hu
    exact hpr (Equiv.swap_eq_one_iff.mp hu.symm)
  have huorder : orderOf u.val = 2 := orderOf_eq_prime
    (congrArg Subtype.val (hsquare u)) hun
  have hc := (NormalizerEvenCentralizerTwo.actual_coset
    heven hdegree hmax Q hQ hne hfree u.val hlocal 1 (by simpa using huorder)).1
  simpa only [OneMemClass.coe_one, one_mul] using hc

theorem semiregular
    {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (heven : ∀ g : G, Equiv.Perm.sign (toPermHom G X g) = 1)
    (hdegree : Fintype.card X % 4 = 3)
    (hmax : ∀ g : G, orderOf g = 2 → (fixedBy X g).ncard ≤ 7)
    (Q : Subgroup G) (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥) (hQfour : Nat.card Q = 4)
    (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (hfree : ∀ (q : Q) (t : X), t ∉ fixedPoints Q X → q • t = t → q = 1)
    (B K : Subgroup (Normalizer Q)) (hB : IsPGroup 2 B) (hKB : K ≤ B)
    (hker : B ⊓ (toPermHom (Normalizer Q) (Fixed (X := X) Q)).ker = Inside Q)
    (hmap : K.map (toPermHom (Normalizer Q) (Fixed (X := X) Q)) =
      B.map (toPermHom (Normalizer Q) (Fixed (X := X) Q)))
    (hsquare : ∀ k : K, k ^ 2 = 1) (hcomm : IsMulCommutative K)
    (a b c d : K) (haQ : a.val ∈ Inside Q) (hane : a ≠ 1)
    (e : Fin 6 ↪ Fixed (X := X) Q)
    (hb : toPermHom (Normalizer Q) (Fixed (X := X) Q) b.val = Equiv.swap (e 0) (e 1))
    (hc : toPermHom (Normalizer Q) (Fixed (X := X) Q) c.val = Equiv.swap (e 2) (e 3))
    (hd : toPermHom (Normalizer Q) (Fixed (X := X) Q) d.val = Equiv.swap (e 4) (e 5))
    (hone : Nat.card (Function.fixedPoints
      (NormalizerSevenOrbitCount.orbitPerm (X := X) Q b.val)) ≤ 1)
    (z : NormalizerFixedComplement.Domain (X := X) Q) (hz : b.val • z = z) :
    let O := orbit Q z.val
    O.ncard = 4 ∧ O ⊆ (fixedPoints Q X)ᶜ ∧
      O = (fixedBy X b.val.val \ fixedPoints Q X) ∪
        (fixedBy X (a.val.val * b.val.val) \ fixedPoints Q X) ∧
      (∀ (u : B) (t : X), t ∉ fixedPoints Q X ∪ O → u.val.val • t = t → u = 1) := by
  let O := orbit Q z.val
  let E := (fixedBy X b \ fixedPoints Q X) ∪ (fixedBy X (a * b) \ fixedPoints Q X)
  obtain ⟨hEcard, hsemi, _⟩ := ElementaryNormalizerSemiregular.semiregular
    heven hdegree hmax Q hseven hfree K hsquare hcomm a b c d haQ hane e hb hc hd
  change E.ncard = 4 at hEcard
  have hOcard : O.ncard = 4 := (NormalizerUniqueOrbitGeometry.orbit_card Q hfree z).trans hQfour
  have hEO : E ⊆ O := by
    intro t ht
    rcases ht with ht | ht
    · exact NormalizerUniqueOrbitGeometry.fixed_mem_orbit Q b.val hone z hz b.val rfl t ht.2 ht.1
    · apply NormalizerUniqueOrbitGeometry.fixed_mem_orbit Q b.val hone z hz (a * b).val ?_ t ht.2 ht.1
      exact NormalizerOrbitCoset.orbitPerm_mul Q ⟨a.val, haQ⟩ b.val
  have hEOeq : E = O := Set.eq_of_subset_of_ncard_le hEO (by omega)
  refine ⟨hOcard, NormalizerUniqueOrbitGeometry.orbit_outside Q z, hEOeq.symm, ?_⟩
  apply OneOrbitOrderFourCentralizerConsumer.semiregular_of_centralizer_card_two hmax Q hQfour
    B K hB hKB hker hmap hsquare hcomm a b c d haQ hane e hb hc hd
    (centralizer_two heven hdegree hmax Q hQ hne hseven hfree K hsquare b _ _ (e.injective.ne (by decide)) hb)
    (centralizer_two heven hdegree hmax Q hQ hne hseven hfree K hsquare c _ _ (e.injective.ne (by decide)) hc)
    (centralizer_two heven hdegree hmax Q hQ hne hseven hfree K hsquare d _ _ (e.injective.ne (by decide)) hd)
    (fixedPoints Q X ∪ O)
  intro k t ht hfix
  by_contra hk
  apply hsemi k hk t ?_ hfix
  change t ∉ fixedPoints Q X ∪ E
  rwa [hEOeq]

end FiveTransitive.OneOrbitElementarySemiregular

end CFSG
