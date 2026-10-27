module

public import CFSG.Permutation.FiveTransitive.NormalizerOneOrbitSemiregularActual
public import CFSG.Permutation.FiveTransitive.HighDegreePairExceptionContradiction

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.NormalizerOneOrbitExclusion

open MulAction FixedNormalizerAction

theorem not_one_fixed_orbit
    {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (hcard : 28 ≤ Fintype.card X) (h5 : IsMultiplyPretransitive G X 5)
    (heven : ∀ g : G, Equiv.Perm.sign (toPermHom G X g) = 1)
    (hdegree : Fintype.card X % 4 = 3)
    (hmax : ∀ g : G, orderOf g = 2 → (fixedBy X g).ncard ≤ 7)
    (Q A : Subgroup G) (hQA : Q ≤ A) (hA : IsPGroup 2 A)
    (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥)
    (hseven : Nat.card (fixedPoints Q X) = 7)
    (hfree : ∀ (q : Q) (t : X), t ∉ fixedPoints Q X → q • t = t → q = 1)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (himage : Image (X := X) Q = ⊤)
    (x : Normalizer Q) (hx : x.val ∈ A) (hxQ : x.val ∉ Q)
    (hlocal : (fixedBy X x.val ∩ fixedPoints Q X).ncard = 5) :
    Nat.card (Function.fixedPoints
      (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x)) ≠ 1 := by
  intro hone
  classical
  let _ := Fintype.ofFinite (Fixed (X := X) Q)
  obtain ⟨q, e, P, a, K, z, _, hvQ, hvorder, _, _, _, _, _, _, _, _, _, haorder,
      hav, _, _, _, _, _, _, _, _, _, _, _, _, hOout, hOeq, _, hsemi, _⟩ :=
    NormalizerOneOrbitSemiregularActual.exists_semiregular heven hdegree hmax Q A hQA hA
      hQ hne hseven hfree S hS himage x hx hxQ hlocal hone
  let v := q.val * x
  let aQ : Q := ⟨a.val.val, a.property⟩
  have hseven' : Nat.card (Fixed (X := X) Q) = 7 := by
    simpa only [fixed_eq Q] using hseven
  have hvlocal : (fixedBy X v.val ∩ fixedPoints Q X).ncard = 5 := by
    change (fixedBy X (q.val.val * x.val) ∩ fixedPoints Q X).ncard = 5
    rw [TwoGroupCosetFixedBound.coset_fixed_inter Q ⟨q.val.val, q.property⟩ x.val]
    exact hlocal
  apply HighDegreePairExceptionContradiction.contradiction hcard h5 hmax Q hseven' hfree
    S hS himage e P aQ haorder v hvorder hvQ hav hvlocal (orbit Q z.val)
  · intro y hy
    refine ⟨hOout hy, ?_⟩
    rw [hOeq] at hy
    exact hy.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  · intro b y hyF hyO hby
    exact hsemi b y (fun h => h.elim hyF hyO) hby

end FiveTransitive.NormalizerOneOrbitExclusion

end CFSG
