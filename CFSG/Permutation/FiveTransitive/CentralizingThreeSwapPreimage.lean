module

public import CFSG.Permutation.FiveTransitive.RestrictedPreimageSylow
public import CFSG.Permutation.FiveTransitive.FixedNormalizerCyclicPreimageSylow
public import CFSG.Permutation.FiveTransitive.ThreeSwapTwoGroup

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.CentralizingThreeSwapPreimage

open MulAction FixedNormalizerAction

theorem exists_subgroup
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    (Q : Subgroup G) (hcyclic : IsCyclic Q)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (himage : ((Subgroup.centralizer (Q : Set G)).subgroupOf (Normalizer Q)).map
      (toPermHom (Normalizer Q) (Fixed (X := X) Q)) = ⊤)
    (e : Fin 6 ↪ Fixed (X := X) Q) :
    ∃ B : Subgroup (Normalizer Q), IsPGroup 2 B ∧ Inside Q ≤ B ∧
      B ≤ (Subgroup.centralizer (Q : Set G)).subgroupOf (Normalizer Q) ∧
      B.map (toPermHom (Normalizer Q) (Fixed (X := X) Q)) = ThreeSwapTwoGroup.subgroup e ∧
      B ⊓ (toPermHom (Normalizer Q) (Fixed (X := X) Q)).ker = Inside Q := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : IsCyclic Q := hcyclic
  let _ : CommGroup Q := IsCyclic.commGroup
  have hQp : IsPGroup 2 Q := by
    rw [← hS]
    exact S.isPGroup'.map (fixingSubgroup G (fixedPoints Q X)).subtype
  have hIp : IsPGroup 2 (Inside Q) := hQp.comap_subtype
  have hIC : Inside Q ≤ (Subgroup.centralizer (Q : Set G)).subgroupOf (Normalizer Q) := by
    intro q hq
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro r hr
    exact congrArg (fun t : Q => t.val) (mul_comm (⟨r, hr⟩ : Q) ⟨q.val, hq⟩)
  exact RestrictedPreimageSylow.exists_lift
    (toPermHom (Normalizer Q) (Fixed (X := X) Q))
    ((Subgroup.centralizer (Q : Set G)).subgroupOf (Normalizer Q)) (Inside Q)
    himage hIp hIC (FixedNormalizerCyclicPreimageSylow.inside_le_kernel Q)
    (FixedNormalizerCyclicPreimageSylow.kernel_pgroup_le_inside Q S hS)
    (ThreeSwapTwoGroup.subgroup e) (ThreeSwapTwoGroup.isTwoGroup e).1

end FiveTransitive.CentralizingThreeSwapPreimage

end CFSG
