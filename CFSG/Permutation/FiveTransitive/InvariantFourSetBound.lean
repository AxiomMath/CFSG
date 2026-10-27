module

public import CFSG.Permutation.FiveTransitive.OyamaThreeOrbitOrders
public import CFSG.Permutation.FiveTransitive.EvenSixFreeFour

public section

namespace CFSG

namespace FiveTransitive.InvariantFourSetBound

open MulAction

theorem card_le_two
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (horb:OyamaThreeOrbitOrders.ThreeOrbits G X)
    (K:Subgroup G) (hK:IsPGroup 2 K) (hsq:∀k:K,k*k=1)
    (b:Fin 4 ↪ X) (hnorm:K≤Subgroup.normalizer (stabilizer G b:Set G))
    (hfree:∀k:K,∀x∈Set.range b,k • x=x → k=1) : Nat.card K≤2 := by
  classical
  obtain ⟨R,hR⟩ := NormalizerInvariantSylow.exists_of_pgroup 2 G (stabilizer G b) K hK hnorm
  let A := (R:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
  let F := fixedPoints A X
  let f := FixedSetNormalizerHom.fixedPermHom G X A
  let J := f.range
  let φ:K →* Equiv.Perm F := f.comp (Subgroup.inclusion hR)
  let H := φ.range
  let _ := Fintype.ofFinite F
  let _ : DecidableEq F := Classical.decEq _
  have hbase:Set.range b⊆F := by
    rintro _ ⟨i,rfl⟩
    rw [mem_fixedPoints]
    intro a
    obtain ⟨r,hr,he⟩ := a.property
    change a.val • b i=b i
    rw [←he]
    exact DFunLike.congr_fun r.property i
  have hφ:Function.Injective φ := by
    apply φ.ker_eq_bot_iff.mp
    apply bot_unique
    intro k hk
    change k=1
    have hp:φ k=1 := hk
    have hv := congrArg (fun q:Equiv.Perm F => (q ⟨b 0,hbase ⟨0,rfl⟩⟩).val) hp
    exact hfree k (b 0) ⟨0,rfl⟩ hv
  have hHJ:H≤J := by
    rintro q ⟨k,rfl⟩
    exact ⟨Subgroup.inclusion hR k,rfl⟩
  have hHsq:∀h:H,h*h=1 := by
    intro h
    obtain ⟨k,rfl⟩ := φ.rangeRestrict_surjective h
    have he := congrArg φ.rangeRestrict (hsq k)
    simpa only [map_mul,map_one] using he
  let O:Set F := {x|x.val∈Set.range b}
  let E:O ≃ Set.range b := {
    toFun := fun x => ⟨x.val.val,x.property⟩
    invFun := fun x => ⟨⟨x.val,hbase x.property⟩,x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hO:O.ncard=4 := by
    rw [←Nat.card_coe_set_eq,Nat.card_congr E,Nat.card_coe_set_eq]
    simpa only [Nat.card_fin] using Set.ncard_range_of_injective b.injective
  have hHfree:∀h:H,h≠1 → ∀x∈O,h • x≠x := by
    intro h hh x hx hfix
    obtain ⟨k,hk⟩ := φ.rangeRestrict_surjective h
    have hfix' : k • x.val=x.val := by
      have he := congrArg Subtype.val hfix
      rw [←hk] at he
      exact he
    have hk1:k=1 := hfree k x.val hx hfix'
    apply hh
    rw [←hk,hk1,map_one]
  have h6:Nat.card F=6 := (hcond.2.1 b R).1
  have hle := EvenSixFreeFour.card_le_two h6 J H
    (OyamaNormalizerTwoTransitive.image_le_alternating hcond b R) hHJ
    (OyamaThreeOrbitOrders.normalizer_pair_fixer_card hcond horb b R) hHsq O hO hHfree
  have hcard:Nat.card K=Nat.card H := Nat.card_congr
    (Equiv.ofBijective φ.rangeRestrict ⟨fun x y h => hφ (congrArg Subtype.val h),φ.rangeRestrict_surjective⟩)
  rwa [hcard]

end FiveTransitive.InvariantFourSetBound

end CFSG
