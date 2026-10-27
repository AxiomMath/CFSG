module

public import CFSG.Permutation.FiveTransitive.NormalizerSevenOrbitCount
public import CFSG.Permutation.FiveTransitive.ThreeSwapEvenCounts

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.CyclicTwoSwapSquare

open MulAction FixedNormalizerAction

theorem square_ne_one
    {G X : Type*} [Group G] [Fintype X] [MulAction G X]
    (heven : ∀ g : G, Equiv.Perm.sign (toPermHom G X g) = 1)
    (hdegree : Fintype.card X % 4 = 3)
    (hmax : ∀ g : G, orderOf g = 2 → (fixedBy X g).ncard ≤ 7)
    (Q : Subgroup G) (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (x : Normalizer Q) (p r : Fixed (X := X) Q) (hpr : p ≠ r)
    (hx : toPermHom (Normalizer Q) (Fixed (X := X) Q) x = Equiv.swap p r)
    (hzero : Nat.card (Function.fixedPoints
      (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x)) = 0) : x ^ 2 ≠ 1 := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hx2
  have hxn : x ≠ 1 := by
    intro he
    rw [he, map_one] at hx
    exact hpr (Equiv.swap_eq_one_iff.mp hx.symm)
  have hxorder : orderOf x = 2 := orderOf_eq_prime hx2 hxn
  have hlocal := ThreeSwapEvenCounts.local_five Q hseven x p r hpr hx
  have htwo := NormalizerEvenCoset.fixed_card_eq_two heven hdegree hmax Q x hlocal 1
    (by simpa only [OneMemClass.coe_one, one_mul] using hxorder)
  simp only [OneMemClass.coe_one, one_mul] at htwo
  obtain ⟨t⟩ : Nonempty (fixedBy (NormalizerFixedComplement.Domain (X := X) Q) x) :=
    Finite.card_pos_iff.mp (by omega)
  have hf : NormalizerSevenOrbitCount.orbitPerm (X := X) Q x (Quotient.mk'' t.val) =
      Quotient.mk'' t.val := by
    change Quotient.mk'' (x • t.val) = Quotient.mk'' t.val
    rw [t.property]
  have hpos : 0 < Nat.card (Function.fixedPoints
      (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x)) :=
    Finite.card_pos_iff.mpr ⟨⟨Quotient.mk'' t.val, hf⟩⟩
  omega

theorem square_eq_generator
    {G X : Type*} [Group G] [Fintype X] [MulAction G X]
    (heven : ∀ g : G, Equiv.Perm.sign (toPermHom G X g) = 1)
    (hdegree : Fintype.card X % 4 = 3)
    (hmax : ∀ g : G, orderOf g = 2 → (fixedBy X g).ncard ≤ 7)
    (Q : Subgroup G) (hQ : Nat.card Q = 2)
    (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (B : Subgroup (Normalizer Q))
    (hker : B ⊓ (toPermHom (Normalizer Q) (Fixed (X := X) Q)).ker = Inside Q)
    (a : Inside Q) (ha : a ≠ 1)
    (x : B) (p r : Fixed (X := X) Q) (hpr : p ≠ r)
    (hx : toPermHom (Normalizer Q) (Fixed (X := X) Q) x.val = Equiv.swap p r)
    (hzero : Nat.card (Function.fixedPoints
      (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x.val)) = 0) : x.val ^ 2 = a.val := by
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  have hmem : x.val ^ 2 ∈ Inside Q := by
    apply hker.le
    change x.val ^ 2 ∈ B ∧ x.val ^ 2 ∈ f.ker
    refine ⟨B.pow_mem x.property 2, ?_⟩
    rw [MonoidHom.mem_ker, map_pow, hx]
    simp only [pow_two, Equiv.swap_mul_self]
  have hne := square_ne_one heven hdegree hmax Q hseven x.val p r hpr hx hzero
  have hI : Nat.card (Inside Q) = 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q.le_normalizer).toEquiv).trans hQ
  obtain ⟨u, _, hu⟩ := (Nat.card_eq_two_iff' (1 : Inside Q)).mp hI
  have hs : (⟨x.val ^ 2, hmem⟩ : Inside Q) ≠ 1 := fun he => hne (congrArg Subtype.val he)
  exact congrArg Subtype.val ((hu _ hs).trans (hu a ha).symm)

end FiveTransitive.CyclicTwoSwapSquare

end CFSG
