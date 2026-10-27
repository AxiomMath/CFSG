module

public import CFSG.Permutation.FiveTransitive.NormalizerSevenOrbitCount

public section

namespace CFSG

namespace FiveTransitive.FourShortOrbits

open MulAction NormalizerFixedComplement

private theorem mem_two_point_set {Y : Type*} [Finite Y]
    (s : Set Y) (hs : s.ncard = 2) (p q : Y) (hp : p ∈ s) (hq : q ∈ s)
    (hne : p ≠ q) {r : Y} (hr : r ∈ s) : r = p ∨ r = q := by
  have he : ({p, q} : Set Y) = s := Set.eq_of_subset_of_ncard_le (by
    intro y hy
    rcases hy with rfl | hy
    · exact hp
    · simpa only [Set.mem_singleton_iff] using (hy ▸ hq)) (by
      rw [hs, Set.ncard_pair hne])
  rw [← he] at hr
  exact hr

variable {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem four_fixed_orbits
    (Q : Subgroup G) (hQcard : Nat.card Q = 2)
    (a x : G) (haQ : a ∈ Q) (hfix : fixedPoints Q X = fixedBy X a)
    (hax : Commute a x)
    (hfree : ∀ (q : Q) (z : X), z ∉ fixedPoints Q X → q • z = z → q = 1)
    (hxcard : (fixedBy X x \ fixedPoints Q X).ncard = 2)
    (haxcard : (fixedBy X (a * x) \ fixedPoints Q X).ncard = 2)
    (S : Set X) (hScard : S.ncard = 4)
    (hSout : S ⊆ (fixedBy X a ∪ fixedBy X x ∪ fixedBy X (a * x))ᶜ)
    (u : Normalizer Q) (hua : Commute u.val a) (hux : Commute u.val x)
    (huS : ∀ z ∈ S, u.val • z = z) :
    4 ≤ Nat.card (Function.fixedPoints (NormalizerSevenOrbitCount.orbitPerm (X := X) Q u)) := by
  let T := fixedBy X x \ fixedPoints Q X
  let U := fixedBy X (a * x) \ fixedPoints Q X
  let E := T ∪ U ∪ S
  let aN : Normalizer Q := ⟨a, Q.le_normalizer haQ⟩
  have hcomp (n : Normalizer Q) (z : X) (hz : z ∉ fixedPoints Q X) :
      n.val • z ∉ fixedPoints Q X := (n • (⟨z, hz⟩ : Domain (X := X) Q)).property
  have hstable (n : Normalizer Q) (v : G) (hnv : Commute n.val v)
      (z : X) (hz : z ∈ fixedBy X v \ fixedPoints Q X) :
      n.val • z ∈ fixedBy X v \ fixedPoints Q X := by
    refine ⟨?_, hcomp n z hz.2⟩
    change v • (n.val • z) = n.val • z
    rw [← mul_smul, ← hnv.eq, mul_smul, hz.1]
  have hdisj : Disjoint T U := Set.disjoint_left.mpr (by
    intro z hzT hzU
    apply hzT.2
    rw [hfix]
    change a • z = z
    have hxz : x • z = z := hzT.1
    have haxz : (a * x) • z = z := hzU.1
    simpa only [mul_smul, hxz] using haxz)
  have hdisjS : Disjoint (T ∪ U) S := Set.disjoint_left.mpr (by
    intro z hz hzS
    apply hSout hzS
    rcases hz with hz | hz
    · exact Or.inl (Or.inr hz.1)
    · exact Or.inr hz.1)
  have hEcard : E.ncard = 8 := by
    dsimp only [E]
    rw [Set.ncard_union_eq hdisjS, Set.ncard_union_eq hdisj, hxcard, haxcard, hScard]
  have hEout : E ⊆ (fixedPoints Q X)ᶜ := by
    intro z hz
    rcases hz with (hz | hz) | hz
    · exact hz.2
    · exact hz.2
    · intro hh
      apply hSout hz
      rw [hfix] at hh
      exact Or.inl (Or.inl hh)
  have hpair (V : Set X) (hV : V.ncard = 2)
      (haV : ∀ z ∈ V, a • z ∈ V) (huV : ∀ z ∈ V, u.val • z ∈ V)
      (z : X) (hzV : z ∈ V) (hzout : z ∉ fixedPoints Q X) :
      u.val • z = z ∨ u.val • z = a • z := by
    apply mem_two_point_set V hV z (a • z) hzV (haV z hzV) ?_ (huV z hzV)
    intro he
    apply hzout
    rw [hfix]
    exact he.symm
  have hpoints (z : X) (hz : z ∈ E) :
      u.val • z = z ∨ u.val • z = a • z := by
    rcases hz with (hz | hz) | hz
    · exact hpair T hxcard (hstable aN x hax) (hstable u x hux) z hz hz.2
    · exact hpair U haxcard (hstable aN (a * x) ((Commute.refl a).mul_right hax))
        (hstable u (a * x) (hua.mul_right hux)) z hz hz.2
    · exact Or.inl (huS z hz)
  let P := fun O : orbitRel.Quotient (Inside Q) (Domain (X := X) Q) =>
    NormalizerSevenOrbitCount.orbitPerm (X := X) Q u O = O
  have hfixed (z : X) (hz : z ∈ E) : P (Quotient.mk'' (⟨z, hEout hz⟩ : Domain (X := X) Q)) := by
    change (Quotient.mk'' (u • (⟨z, hEout hz⟩ : Domain (X := X) Q)) :
      orbitRel.Quotient (Inside Q) (Domain (X := X) Q)) = _
    apply Quotient.sound
    apply mem_orbit_iff.mpr
    rcases hpoints z hz with he | he
    · refine ⟨1, ?_⟩
      rw [one_smul]
      apply Subtype.ext
      change z = u.val • z
      exact he.symm
    · refine ⟨⟨aN, haQ⟩, ?_⟩
      exact Subtype.ext he.symm
  let f : E → {z : Domain (X := X) Q // P (Quotient.mk'' z)} :=
    fun z => ⟨⟨z.val, hEout z.property⟩, hfixed z.val z.property⟩
  have hf : Function.Injective f := by
    intro z w he
    exact Subtype.ext (congrArg (fun v => v.val.val) he)
  have hle := Nat.card_le_card_of_injective f hf
  rw [Nat.card_coe_set_eq, hEcard,
    FreeActionTransporterCount.card_orbit_preimage (free_inside Q hfree)] at hle
  have hInside : Nat.card (Inside Q) = 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q.le_normalizer).toEquiv).trans hQcard
  rw [hInside] at hle
  change 8 ≤ 2 * Nat.card (Function.fixedPoints
    (NormalizerSevenOrbitCount.orbitPerm (X := X) Q u)) at hle
  omega

end FiveTransitive.FourShortOrbits

end CFSG
