module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.ElementaryHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeFixedSets

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TripleSylowMaximality

open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

universe u v

variable {G : Type u} [Group G] [Finite G]

theorem normal_join_odd_prime_quotient
    (L R : Subgroup G) [L.Normal] {p : ℕ} (hp : p.Prime)
    (hpodd : Odd p) (hRp : IsPGroup p R) :
    Odd (Nat.card ((L ⊔ R : Subgroup G) ⧸ L.subgroupOf (L ⊔ R))) := by
  let : Fact p.Prime := ⟨hp⟩
  let K := L ⊔ R
  let LK := L.subgroupOf K
  let fK := QuotientGroup.mk' LK
  let f : R →* (K ⧸ LK) := fK.comp (Subgroup.inclusion (le_sup_right : R ≤ K))
  have hfsurj : Function.Surjective f := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective LK q
    obtain ⟨l, hl, r, hr, hprod⟩ := Subgroup.mem_sup_of_normal_left.mp k.property
    let lK : K := ⟨l, (le_sup_left : L ≤ K) hl⟩
    let rK : K := ⟨r, (le_sup_right : R ≤ K) hr⟩
    have hprodK : lK * rK = k := Subtype.ext hprod
    have hlone : fK lK = 1 := by
      change lK ∈ fK.ker
      rw [QuotientGroup.ker_mk']
      exact hl
    refine ⟨⟨r, hr⟩, ?_⟩
    change fK rK = fK k
    rw [← hprodK, map_mul, hlone, one_mul]
  obtain ⟨n, hn⟩ := (hRp.of_surjective f hfsurj).exists_card_eq
  rw [hn]
  exact hpodd.pow

theorem normal_join_odd_prime_involution_mem
    (L R : Subgroup G) [L.Normal] {p : ℕ} (hp : p.Prime)
    (hpodd : Odd p) (hRp : IsPGroup p R)
    (x : (L ⊔ R : Subgroup G)) (hx : orderOf x = 2) : (x : G) ∈ L := by
  let K := L ⊔ R
  let LK := L.subgroupOf K
  let f := QuotientGroup.mk' LK
  have hodd : Odd (Nat.card (K ⧸ LK)) :=
    normal_join_odd_prime_quotient L R hp hpodd hRp
  have hsquare : (f x) ^ 2 = 1 := by
    rw [← map_pow, (orderOf_eq_prime_iff.mp hx).1, map_one]
  have hqone : f x = 1 := square_one_eq_one_of_mem_odd_subgroup
    (⊤ : Subgroup (K ⧸ LK)) (by simpa only [Subgroup.card_top] using hodd)
    (Subgroup.mem_top _) hsquare
  have hmem : x ∈ f.ker := hqone
  rw [QuotientGroup.ker_mk'] at hmem
  exact hmem

omit [Finite G] in
theorem original_restricted_stabilizer
    (H A : Subgroup G) (Delta : Set (pointRightCosetSpace H))
    (hstable : ∀ a ∈ A, ∀ omega ∈ Delta, pointRightCosetMul H omega a ∈ Delta)
    (omega : Delta) :
    letI := pointInvariantSetInverseRightAction H A Delta hstable
    MulAction.stabilizer A omega = (rightCosetStabilizer H omega.val).subgroupOf A := by
  let := pointInvariantSetInverseRightAction H A Delta hstable
  ext a
  rw [MulAction.mem_stabilizer_iff]
  change (⟨pointRightCosetMul H omega.val (a : G)⁻¹, _⟩ : Delta) = omega ↔
    (a : G) ∈ rightCosetStabilizer H omega.val
  rw [Subtype.ext_iff, ← mem_point_right_stabilizer_iff H omega.val (a : G)⁻¹]
  exact (rightCosetStabilizer H omega.val).inv_mem_iff

def original_restricted_fixed_equiv
    (H A : Subgroup G) (Delta : Set (pointRightCosetSpace H))
    (hstable : ∀ a ∈ A, ∀ omega ∈ Delta, pointRightCosetMul H omega a ∈ Delta)
    (Q : Subgroup A) :
    letI := pointInvariantSetInverseRightAction H A Delta hstable
    {omega : Delta // omega ∈ fixedPointsOfSubgroup A Delta Q} ≃
      (Delta ∩ pointFixedSet H (Q.map A.subtype) : Set (pointRightCosetSpace H)) := by
  letI := pointInvariantSetInverseRightAction H A Delta hstable
  refine
    { toFun := fun omega => ⟨omega.val.val, omega.val.property, ?_⟩
      invFun := fun omega => ⟨⟨omega.val, omega.property.1⟩, ?_⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  · intro q hq
    obtain ⟨qA, hqA, rfl⟩ := Subgroup.mem_map.mp hq
    change pointRightCosetMul H omega.val.val (qA : G) = omega.val.val
    have hf := omega.property qA⁻¹ (Q.inv_mem hqA)
    change (⟨pointRightCosetMul H omega.val.val (qA⁻¹ : A).val⁻¹, _⟩ : Delta) = omega.val at hf
    simpa only [Subgroup.coe_inv, inv_inv] using congrArg Subtype.val hf
  · intro q hq
    apply Subtype.ext
    exact omega.property.2 q.val⁻¹
      (Subgroup.mem_map_of_mem A.subtype (Q.inv_mem hq))

end CFSG.ShultStronglyClosedTI.TripleSylowMaximality
