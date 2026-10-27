module

public import CFSG.Permutation.FiveTransitive.ElementaryNormalizerSemiregular
public import CFSG.Permutation.FiveTransitive.NormalizerUniqueOrbitGeometry
public import CFSG.Permutation.FiveTransitive.InvariantExceptionalFour
public import CFSG.Permutation.FiveTransitive.NormalizerOrbitCoset

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.NormalizerOneOrbitCardFour

open MulAction FixedNormalizerAction

theorem card_four_of_elementary
    {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (heven : ∀ g : G, Equiv.Perm.sign (toPermHom G X g) = 1)
    (hdegree : Fintype.card X % 4 = 3)
    (hmax : ∀ g : G, orderOf g = 2 → (fixedBy X g).ncard ≤ 7)
    (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (hfree : ∀ (q : Q) (t : X), t ∉ fixedPoints Q X → q • t = t → q = 1)
    (K : Subgroup (Normalizer Q)) (hsquare : ∀ k : K, k ^ 2 = 1)
    (hcomm : IsMulCommutative K) (h8 : 8 ∣ Nat.card K)
    (a b c d : K) (haQ : a.val ∈ Inside Q) (hane : a ≠ 1)
    (e : Fin 6 ↪ Fixed (X := X) Q)
    (hb : toPermHom (Normalizer Q) (Fixed (X := X) Q) b.val = Equiv.swap (e 0) (e 1))
    (hc : toPermHom (Normalizer Q) (Fixed (X := X) Q) c.val = Equiv.swap (e 2) (e 3))
    (hd : toPermHom (Normalizer Q) (Fixed (X := X) Q) d.val = Equiv.swap (e 4) (e 5))
    (hone : Nat.card (Function.fixedPoints
      (NormalizerSevenOrbitCount.orbitPerm (X := X) Q b.val)) ≤ 1)
    (z : NormalizerFixedComplement.Domain (X := X) Q) (hz : b.val • z = z)
    (hO : ∀ (g : K) (t : X), t ∈ orbit Q z.val → g.val.val • t ∈ orbit Q z.val) :
    Nat.card Q = 4 := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let E := (fixedBy X b \ fixedPoints Q X) ∪ (fixedBy X (a * b) \ fixedPoints Q X)
  obtain ⟨hEcard, hsemi, hstable⟩ := ElementaryNormalizerSemiregular.semiregular
    heven hdegree hmax Q hseven hfree K hsquare hcomm a b c d haQ hane e hb hc hd
  change E.ncard = 4 at hEcard
  have hEO : E ⊆ orbit Q z.val := by
    intro t ht
    rcases ht with ht | ht
    · exact NormalizerUniqueOrbitGeometry.fixed_mem_orbit Q b.val hone z hz b.val rfl t ht.2 ht.1
    · apply NormalizerUniqueOrbitGeometry.fixed_mem_orbit Q b.val hone z hz (a * b).val ?_ t ht.2 ht.1
      exact NormalizerOrbitCoset.orbitPerm_mul Q ⟨a.val, haQ⟩ b.val
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
  have hcard : (orbit Q z.val).ncard = Nat.card Q := NormalizerUniqueOrbitGeometry.orbit_card Q hfree z
  have hfour : (orbit Q z.val).ncard = 4 :=
    InvariantExceptionalFour.ncard_eq_four h8 (orbit Q z.val) E hEO hO hstable hEcard k
      (hcard.trans hk) (by
        intro g t ht hE hfix
        by_contra hg
        exact hsemi g hg t (fun h => h.elim (NormalizerUniqueOrbitGeometry.orbit_outside Q z ht) hE) hfix)
  exact hcard.symm.trans hfour

end FiveTransitive.NormalizerOneOrbitCardFour

end CFSG
