module

public import CFSG.Permutation.FiveTransitive.NormalizerOrbitFamily

public section

namespace CFSG

namespace FiveTransitive.OrbitFamilyKernelFixed

open MulAction

theorem card_family_le_fixed
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (Q : Subgroup G) (m : ℕ) (hm : ¬ 5 ∣ m)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 5 = 1)
    (hker : NormalizerOrbitFamily.toPermHom (X := X) Q m g = 1) :
    Nat.card (NormalizerOrbitFamily.Family (X := X) Q m) ≤ Nat.card (fixedBy X g.val) := by
  classical
  let B := NormalizerOrbitFamily.Family (X := X) Q m
  have hfixed (O : B) : ∃ x : X, x ∈ O.val.orbit ∧ g.val • x = x := by
    apply NormalizerOrbitFamily.exists_fixed_of_preserved Q g hg O.val
    · exact congrArg (fun e : Equiv.Perm B => (e O).val) hker
    · rwa [O.property]
  choose x hx hfix using hfixed
  let f : B → fixedBy X g.val := fun O => ⟨x O,hfix O⟩
  have hf : Function.Injective f := by
    intro A B h
    have he : x A = x B := congrArg Subtype.val h
    apply Subtype.ext
    have hA := orbitRel.Quotient.mem_orbit.mp (hx A)
    have hB := orbitRel.Quotient.mem_orbit.mp (hx B)
    exact hA.symm.trans ((congrArg Quotient.mk'' he).trans hB)
  exact Nat.card_le_card_of_injective f hf

end FiveTransitive.OrbitFamilyKernelFixed

end CFSG
