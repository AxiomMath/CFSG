module

public import CFSG.Permutation.FiveTransitive.ThirtyTwoTwoGroupPairQuotient
public import CFSG.Permutation.FiveTransitive.ThirtyTwoTwoGroupPairCount

public section

namespace CFSG

namespace FiveTransitive.ThirtyTwoTwoGroupSmallCenter

open MulAction

private theorem center_orbit_card
    {X : Type*} [Finite X] (R : Subgroup (Equiv.Perm X))
    (htrans : IsPretransitive R X) (x : X) :
    Nat.card (orbit (Subgroup.center R) x) = Nat.card (Subgroup.center R) := by
  let Z := Subgroup.center R
  let f : Z → orbit Z x := fun c => ⟨c • x,mem_orbit_iff.mpr ⟨c,rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b he
      exact FreeActionTransporterCount.smul_injective (TransitiveCenterFree.free htrans) x
        (congrArg Subtype.val he)
    · intro y
      obtain ⟨c,hc⟩ := mem_orbit_iff.mp y.property
      exact ⟨c,Subtype.ext hc⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem card_le_thirty_two
    {X : Type*} [Fintype X] [DecidableEq X] (hX : Nat.card X = 32)
    (R : Subgroup (Equiv.Perm X)) (hR : IsPGroup 2 R)
    (htrans : IsPretransitive R X)
    (g : Subgroup.normalizer (R : Set (Equiv.Perm X))) (hg : g ^ 5 = 1)
    (hfixed : Nat.card (Function.fixedPoints g.val) = 2)
    (hZ : Nat.card (Subgroup.center R) = 2)
    (K : Subgroup (Equiv.Perm X)) (hKR : K ≤ R)
    (hmin : ∀ k : K, k ≠ 1 → 27 ≤ k.val.support.card) : Nat.card K ≤ 32 := by
  classical
  let Z := Subgroup.center R
  let O := orbitRel.Quotient Z X
  let b := CharacteristicOrbitRepresentation.orbitHom (X := X) R Z
  let rho := b.comp (CharacteristicOrbitRepresentation.inclusion R)
  have hrho : Nat.card rho.range = 16 :=
    (ThirtyTwoTwoGroupPairQuotient.data hX R hR htrans g hg hfixed hZ).2.2
  let f := rho.comp (Subgroup.inclusion hKR)
  have hsub : f.range ≤ rho.range := by
    rintro _ ⟨k,rfl⟩
    exact ⟨Subgroup.inclusion hKR k,rfl⟩
  have himage : Nat.card f.range ≤ 16 := by
    have hh := Subgroup.card_le_of_le hsub
    rwa [hrho] at hh
  have horbit (x : X) : Nat.card (orbit f.ker x) ≤ 2 := by
    have hsuborb : orbit f.ker x ⊆ orbit Z x := by
      rintro y ⟨k,rfl⟩
      have he := DFunLike.congr_fun k.property (Quotient.mk'' x : O)
      change (Quotient.mk'' (k.val.val x) : O) = Quotient.mk'' x at he
      exact Quotient.exact he
    have hh := Set.ncard_le_ncard hsuborb
    rw [← Nat.card_coe_set_eq,← Nat.card_coe_set_eq,center_orbit_card R htrans x,hZ] at hh
    exact hh
  have hbound (k : f.ker) (hk : k ≠ 1) : Nat.card (fixedBy X k) ≤ 5 := by
    have hne : k.val ≠ 1 := fun he => hk (Subtype.ext he)
    have hm := hmin k.val hne
    change Nat.card (Function.fixedPoints k.val.val) ≤ 5
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,k.val.val.sum_cycleType,
      ← Nat.card_eq_fintype_card (α := X),hX]
    omega
  have hker : Nat.card f.ker ≤ 2 := ThirtyTwoTwoGroupPairCount.card_le_two
    (by rwa [← Nat.card_eq_fintype_card]) horbit hbound
  have hm := f.ker.card_mul_index
  rw [Subgroup.index_ker] at hm
  change Nat.card f.ker * Nat.card f.range = Nat.card K at hm
  have hh := Nat.mul_le_mul hker himage
  rw [hm] at hh
  exact hh

end FiveTransitive.ThirtyTwoTwoGroupSmallCenter

end CFSG
