module

public import CFSG.Permutation.FiveTransitive.FourShortOrbits
public import CFSG.Permutation.FiveTransitive.HighDegreeRegularFourSeed
public import CFSG.Permutation.FiveTransitive.InvolutionSylowPreimageNormalizer

public section

namespace CFSG

namespace FiveTransitive.HighDegreeFourShortOrbits

open MulAction NormalizerFixedComplement Research.HallRegularOrbits

variable {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]

private theorem exists_four_fixed_orbits
    (hcard : 28 ≤ Fintype.card X) (h5 : IsMultiplyPretransitive G X 5)
    (hmax : ∀ t : G, orderOf t = 2 → (fixedBy X t).ncard ≤ 7)
    (Q : Subgroup G) (a : G) (hQ : Q = Subgroup.zpowers a) (ha : orderOf a = 2)
    (hfree : ∀ (q : Q) (z : X), z ∉ fixedPoints Q X → q • z = z → q = 1)
    (x : Normalizer Q) (hx : orderOf x.val = 2) (hxne : x.val ≠ a)
    (hxcard : (fixedBy X x.val \ fixedPoints Q X).ncard = 2)
    (haxcard : (fixedBy X (a * x.val) \ fixedPoints Q X).ncard = 2) :
    ∃ u : Normalizer Q, orderOf u.val = 2 ∧ u.val ∉ Q ∧
      Commute u.val a ∧ Commute u.val x.val ∧
      4 ≤ Nat.card (Function.fixedPoints
        (NormalizerSevenOrbitCount.orbitPerm (X := X) Q u)) ∧
      ∃ z : X, (regularFourSet a x.val z).ncard = 4 ∧
        regularFourSet a x.val z ⊆ (fixedBy X a ∪ fixedBy X x.val ∪ fixedBy X (a * x.val))ᶜ ∧
        ∀ y ∈ regularFourSet a x.val z, u.val • y = y := by
  have haQ : a ∈ Q := by rw [hQ]; exact Subgroup.mem_zpowers a
  have hfix : fixedPoints Q X = fixedBy X a := by
    ext z
    constructor
    · intro hz
      exact hz ⟨a, haQ⟩
    · intro hz q
      have hle : Q ≤ stabilizer G z := by
        rw [hQ]
        exact Subgroup.zpowers_le.mpr hz
      exact hle q.property
  have hQcard : Nat.card Q = 2 := by rw [hQ, Nat.card_zpowers, ha]
  have hxa : Commute x.val a := by
    have hle : Normalizer Q ≤ Subgroup.centralizer ({a} : Set G) := by
      change Subgroup.normalizer (Q : Set G) ≤ Subgroup.centralizer ({a} : Set G)
      rw [hQ, InvolutionSylowPreimageNormalizer.normalizer_zpowers_eq_centralizer a ha]
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle x.property)
  obtain ⟨z, u, hScard, hSout, _, _, hu2, huS, hua, hux⟩ :=
    HighDegreeRegularFourSeed.exists_fixing_regular_four hcard h5 hmax a x.val ha hx hxa.symm hxne.symm
  have huN : u ∈ Normalizer Q := by
    change u ∈ Subgroup.normalizer (Q : Set G)
    rw [hQ, InvolutionSylowPreimageNormalizer.normalizer_zpowers_eq_centralizer a ha]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hua.eq
  let uN : Normalizer Q := ⟨u, huN⟩
  have hzS : z ∈ regularFourSet a x.val z := by simp only [regularFourSet, Set.mem_insert_iff, true_or]
  have hzout : z ∉ fixedPoints Q X := by
    intro hh
    apply hSout hzS
    rw [hfix] at hh
    exact Or.inl (Or.inl hh)
  have huQ : u ∉ Q := by
    intro hh
    have he : u = 1 := congrArg Subtype.val (hfree ⟨u, hh⟩ z hzout (huS z hzS))
    rw [he, orderOf_one] at hu2
    omega
  refine ⟨uN, hu2, huQ, hua, hux, ?_, z, hScard, hSout, huS⟩
  exact FourShortOrbits.four_fixed_orbits Q hQcard a x.val haQ hfix hxa.symm hfree
    hxcard haxcard (regularFourSet a x.val z) hScard hSout uN hua hux huS

theorem exists_of_card_two
    (hcard : 28 ≤ Fintype.card X) (h5 : IsMultiplyPretransitive G X 5)
    (hmax : ∀ t : G, orderOf t = 2 → (fixedBy X t).ncard ≤ 7)
    (Q : Subgroup G) (hQcard : Nat.card Q = 2) (a : Q) (ha : orderOf a.val = 2)
    (hfree : ∀ (q : Q) (z : X), z ∉ fixedPoints Q X → q • z = z → q = 1)
    (x : Normalizer Q) (hx : orderOf x.val = 2) (hxQ : x.val ∉ Q)
    (hcoset : ∀ q : Q, (fixedBy X (q.val * x.val) \ fixedPoints Q X).ncard = 2) :
    ∃ u : Normalizer Q, orderOf u.val = 2 ∧ u.val ∉ Q ∧
      Commute u.val a.val ∧ Commute u.val x.val ∧
      4 ≤ Nat.card (Function.fixedPoints
        (NormalizerSevenOrbitCount.orbitPerm (X := X) Q u)) ∧
      ∃ z : X, (regularFourSet a.val x.val z).ncard = 4 ∧
        regularFourSet a.val x.val z ⊆
          (fixedBy X a.val ∪ fixedBy X x.val ∪ fixedBy X (a.val * x.val))ᶜ ∧
        ∀ y ∈ regularFourSet a.val x.val z, u.val • y = y := by
  have hgen : Subgroup.zpowers a.val = Q :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr a.property) (by
      rw [Nat.card_zpowers, ha, hQcard])
  have hne : x.val ≠ a.val := fun he => hxQ (he ▸ a.property)
  have hxcard : (fixedBy X x.val \ fixedPoints Q X).ncard = 2 := by
    simpa only [OneMemClass.coe_one, one_mul] using hcoset 1
  exact exists_four_fixed_orbits hcard h5 hmax Q a.val hgen.symm ha hfree
    x hx hne hxcard (hcoset a)

end FiveTransitive.HighDegreeFourShortOrbits

end CFSG
