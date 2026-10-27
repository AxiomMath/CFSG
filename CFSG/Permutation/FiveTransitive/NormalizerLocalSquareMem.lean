module

public import CFSG.Permutation.FiveTransitive.FixedNormalizerCyclicPreimageSylow
public import CFSG.Permutation.FiveTransitive.SevenLocalSquare

public section

namespace CFSG

namespace FiveTransitive.NormalizerLocalSquareMem

open MulAction FixedNormalizerAction

private theorem square_mem_of_local
    {G X : Type*} [Group G] [MulAction G X]
    (Q : Subgroup G)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (A : Subgroup G) (hA : IsPGroup 2 A)
    (x : Normalizer Q) (hx : x.val ∈ A)
    (hsquare : (toPermHom (Normalizer Q) (Fixed (X := X) Q) x) ^ 2 = 1) :
    x.val ^ 2 ∈ Q := by
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  have hker : x ^ 2 ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact hsquare
  have hp : IsPGroup 2 (Subgroup.zpowers (x ^ 2)) :=
    hA.comap_subtype.to_le (show Subgroup.zpowers (x ^ 2) ≤ A.subgroupOf (Normalizer Q) from
      Subgroup.zpowers_le.mpr (A.pow_mem hx 2))
  exact FixedNormalizerCyclicPreimageSylow.kernel_pgroup_le_inside Q S hS
    (Subgroup.zpowers (x ^ 2)) (Subgroup.zpowers_le.mpr hker) hp (Subgroup.mem_zpowers _)

theorem square_mem
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (Q : Subgroup G)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (A : Subgroup G) (hA : IsPGroup 2 A)
    (hseven : Nat.card (fixedPoints Q X) = 7)
    (x : Normalizer Q) (hx : x.val ∈ A)
    (hlocal : (fixedBy X x.val ∩ fixedPoints Q X).ncard = 5) :
    x.val ^ 2 ∈ Q := by
  apply square_mem_of_local Q S hS A hA x hx
  rw [← map_pow]
  apply Equiv.ext
  intro y
  apply Subtype.ext
  exact SevenLocalSquare.square_fixes Q hseven x.val x.property hlocal y.val (by simpa only [fixed_eq Q] using y.property)

theorem generated_pgroup
    {G : Type*} [Group G] (Q A : Subgroup G) (hQA : Q ≤ A) (hA : IsPGroup 2 A)
    (x : Normalizer Q) (hx : x.val ∈ A) :
    IsPGroup 2 ↥(Inside Q ⊔ Subgroup.zpowers x : Subgroup (Normalizer Q)) :=
  hA.comap_subtype.to_le (show Inside Q ⊔ Subgroup.zpowers x ≤ A.subgroupOf (Normalizer Q) from
    sup_le (fun _ hq => hQA hq) (Subgroup.zpowers_le.mpr hx))

end FiveTransitive.NormalizerLocalSquareMem

end CFSG
