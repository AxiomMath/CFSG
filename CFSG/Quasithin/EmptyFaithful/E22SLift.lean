module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.RankThree.SubgroupLists.CentralThreeLift
public import CFSG.Assembly.Defs

public section

namespace CFSG.Quasithin.E22S

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.SubgroupLists CFSG.Open
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem scalars_pow_three (z : SL(3, K)) (hz : z ∈ scalars 3 K) : z ^ 3 = 1 := by
  obtain ⟨c, hc, hzc⟩ := mem_scalars.mp hz
  have hc' : (c : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
  have h3 : ((z ^ 3 : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      ((1 : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) := by
    rw [Matrix.SpecialLinearGroup.coe_pow, hzc, ← map_pow, hc', map_one,
      Matrix.SpecialLinearGroup.coe_one]
  exact Matrix.SpecialLinearGroup.ext _ _ (fun i j => congrFun (congrFun h3 i) j)

theorem commute_of_proj_commute_two {x y : SL(3, K)} (hx : x ^ 2 = 1)
    (h : proj 3 K x * proj 3 K y = proj 3 K y * proj 3 K x) : x * y = y * x :=
  commute_of_commute_mk (scalars_le_center 3 K) scalars_pow_three (n := 2) (by norm_num) hx h

@[expose] def invLifts (A : Subgroup (projectiveSL 3 K)) (hA : IsElemAbelian 2 A) :
    Subgroup SL(3, K) where
  carrier := {x | proj 3 K x ∈ A ∧ x ^ 2 = 1}
  one_mem' := ⟨by rw [map_one]; exact A.one_mem, one_pow 2⟩
  mul_mem' := by
    rintro x y ⟨hxA, hx2⟩ ⟨hyA, hy2⟩
    have hc : x * y = y * x := commute_of_proj_commute_two hx2 (by
      have := hA.1.is_comm.comm ⟨proj 3 K x, hxA⟩ ⟨proj 3 K y, hyA⟩
      exact congrArg Subtype.val this)
    refine ⟨by rw [map_mul]; exact A.mul_mem hxA hyA, ?_⟩
    calc (x * y) ^ 2 = x ^ 2 * y ^ 2 := by
          rw [pow_two, pow_two, pow_two, mul_assoc, ← mul_assoc y x y, ← hc]; group
      _ = 1 := by rw [hx2, hy2, one_mul]
  inv_mem' := by
    rintro x ⟨hxA, hx2⟩
    refine ⟨by rw [map_inv]; exact A.inv_mem hxA, ?_⟩
    rw [inv_pow, hx2, inv_one]

theorem exists_invLift {A : Subgroup (projectiveSL 3 K)} (hA : IsElemAbelian 2 A)
    {a : projectiveSL 3 K} (ha : a ∈ A) : ∃ x ∈ invLifts A hA, proj 3 K x = a := by
  obtain ⟨x, hxa, hx2⟩ := exists_lift_pow_eq_one (scalars_le_center 3 K) scalars_pow_three
    (n := 2) (by norm_num) a (hA.2 a ha)
  exact ⟨x, ⟨by rw [show proj 3 K x = a from hxa]; exact ha, hx2⟩, hxa⟩

theorem card_le_card_invLifts [Finite K] {A : Subgroup (projectiveSL 3 K)}
    (hA : IsElemAbelian 2 A) : Nat.card A ≤ Nat.card (invLifts A hA) := by
  refine Nat.card_le_card_of_surjective
    (fun x => (⟨proj 3 K x, x.2.1⟩ : A)) fun a => ?_
  obtain ⟨x, hx, hxa⟩ := exists_invLift hA a.2
  exact ⟨⟨x, hx⟩, Subtype.ext hxa⟩

end CFSG.Quasithin.E22S
