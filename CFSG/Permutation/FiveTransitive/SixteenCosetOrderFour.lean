module

public import CFSG.Permutation.FiveTransitive.HigherTwoCycleShape

public section

namespace CFSG

namespace FiveTransitive.SixteenCosetOrderFour

open MulAction Equiv CyclePatternRoots

variable {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]

omit [Finite G] [Fintype X] [FaithfulSMul G X] in
private theorem coset_same_on_fixed (S : Subgroup G) (b : G)
    (hb : b ∈ Subgroup.normalizer (S : Set G)) (a : G) (hab : a * b⁻¹ ∈ S)
    (x : X) (hx : x ∈ fixedPoints S X) : a • x = b • x := by
  have hf := mem_fixedPoints.mp (FixedSetNormalizerPerm.smul_mem_fixedPoints G X S b hb hx)
    (⟨a * b⁻¹,hab⟩ : S)
  change (a * b⁻¹) • (b • x) = b • x at hf
  simpa only [mul_smul, inv_smul_smul] using hf

theorem fixed_subset_common
    (hlocal : SixLocalSylowExponentTwo.EvenSixLocal G X)
    (hinv : ∀ u : G, orderOf u = 2 →
      Nat.card (Function.fixedPoints (toPerm u : Perm X)) ≤ 6)
    (S : Subgroup G) (hF : (fixedPoints S X).ncard = 6)
    (b : G) (hb : b ∈ Subgroup.normalizer (S : Set G)) (hb2 : b * b = 1)
    (htwo : (fixedBy X b ∩ fixedPoints S X).ncard = 2)
    (a : G) (ha : orderOf a = 4) (hab : a * b⁻¹ ∈ S) :
    fixedBy X a ⊆ fixedPoints S X := by
  let F := fixedPoints S X
  let D := F \ fixedBy X b
  have hD : D.ncard = 4 := by
    have hc := Set.ncard_inter_add_ncard_sdiff_eq_ncard F (fixedBy X b)
    have ht : (F ∩ fixedBy X b).ncard = 2 := by rwa [Set.inter_comm]
    change (F \ fixedBy X b).ncard = 4
    change F.ncard = 6 at hF
    omega
  let f : D → TwoRoot (toPerm a : Perm X) := fun x => ⟨x.val, by
    have he := coset_same_on_fixed S b hb a hab x.val x.property.1
    have he' := coset_same_on_fixed S b hb a hab (b • x.val)
      (FixedSetNormalizerPerm.smul_mem_fixedPoints G X S b hb x.property.1)
    constructor
    · change a • (a • x.val) = x.val
      rw [he,he',← mul_smul,hb2,one_smul]
    · change a • x.val ≠ x.val
      rw [he]
      exact x.property.2⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : TwoRoot (toPerm a : Perm X) => z.val) h)
  have hlo : 4 ≤ Nat.card (TwoRoot (toPerm a : Perm X)) := by
    have h := Nat.card_le_card_of_injective f hf
    rw [Nat.card_coe_set_eq,hD] at h
    exact h
  have hfour := TwoPowerPeriodWitness.four_card_pos_of_order_four (toPerm a : Perm X)
    ((HigherTwoCycleShape.order_toPerm a).trans ha)
  have hshape := LocalEvenCycleShape.two_power_shape hlocal hinv a 2 (by decide) ha hfour
  have htwoa : Nat.card (TwoRoot (toPerm a : Perm X)) = 4 := by omega
  have hfix := (HigherTwoCycleShape.four_two_points_order_four hlocal hinv a 2 ha hfour htwoa).2
  have hglobal : (fixedBy X a).ncard = 2 := by
    rw [Nat.card_coe_set_eq] at hfix
    exact hfix
  have hinter : fixedBy X a ∩ F = fixedBy X b ∩ F := by
    ext x
    constructor
    · rintro ⟨ha,hx⟩
      exact ⟨(coset_same_on_fixed S b hb a hab x hx).symm.trans ha,hx⟩
    · rintro ⟨hb',hx⟩
      exact ⟨(coset_same_on_fixed S b hb a hab x hx).trans hb',hx⟩
  have he : fixedBy X a ∩ F = fixedBy X a :=
    Set.eq_of_subset_of_ncard_le Set.inter_subset_left (by rw [hinter,htwo,hglobal])
  intro x hx
  have hx' : x ∈ fixedBy X a ∩ F := by rw [he]; exact hx
  exact hx'.2

end FiveTransitive.SixteenCosetOrderFour

end CFSG
