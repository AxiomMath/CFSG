module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps107Base
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps107Three
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Ctx
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Bridge
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13OneBA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem w107_commutes_center {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} (hctx : Is135Context Y L)
    (hU : LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 4 3 1) {t : MulAut W} (htY : t ∈ Y)
    (ht2 : orderOf t = 2) (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) :
    ∀ z ∈ Subgroup.center ↥L, t * (z : MulAut W) = (z : MulAut W) * t := by
  intro x hx
  by_contra hne
  obtain ⟨x', hx'c, hx'val⟩ := w107_conj_center_mem hctx htY hx
  let y : ↥L := x * x'⁻¹
  have hyc : y ∈ Subgroup.center ↥L :=
    (Subgroup.center ↥L).mul_mem hx ((Subgroup.center ↥L).inv_mem hx'c)
  have hyval : (y : MulAut W) =
      (x : MulAut W) * (t * (x : MulAut W) * t⁻¹)⁻¹ := by
    show ((x * x'⁻¹ : ↥L) : MulAut W) = _
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hx'val]
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht2, pow_two] at h
    exact h
  have httinv : t⁻¹ * t⁻¹ = 1 := by
    rw [← mul_inv_rev t t, htt, inv_one]
  have htu : t * (t * (x : MulAut W) * t⁻¹) * t⁻¹ = (x : MulAut W) := by
    calc t * (t * (x : MulAut W) * t⁻¹) * t⁻¹
        = (t * t) * (x : MulAut W) * (t⁻¹ * t⁻¹) := by group
      _ = (x : MulAut W) := by rw [htt, httinv, one_mul, mul_one]
  have htuinv : t * (t * (x : MulAut W) * t⁻¹)⁻¹ * t⁻¹ = (x : MulAut W)⁻¹ := by
    calc t * (t * (x : MulAut W) * t⁻¹)⁻¹ * t⁻¹
        = t * (t * (x : MulAut W)⁻¹ * t⁻¹) * t⁻¹ := by group
      _ = (t * t) * (x : MulAut W)⁻¹ * (t⁻¹ * t⁻¹) := by group
      _ = (x : MulAut W)⁻¹ := by rw [htt, httinv, one_mul, mul_one]
  have hconj : t * (y : MulAut W) * t⁻¹ = (y : MulAut W)⁻¹ := by
    rw [hyval]
    calc t * ((x : MulAut W) * (t * (x : MulAut W) * t⁻¹)⁻¹) * t⁻¹
        = (t * (x : MulAut W) * t⁻¹) *
            (t * (t * (x : MulAut W) * t⁻¹)⁻¹ * t⁻¹) := by group
      _ = (t * (x : MulAut W) * t⁻¹) * (x : MulAut W)⁻¹ := by rw [htuinv]
      _ = ((x : MulAut W) * (t * (x : MulAut W) * t⁻¹)⁻¹)⁻¹ := by group
  have hy1 : y ≠ 1 := by
    intro hy
    apply hne
    have hyval1 : (x : MulAut W) * (t * (x : MulAut W) * t⁻¹)⁻¹ = 1 := by
      have h := congrArg (fun z : ↥L => (z : MulAut W)) hy
      rw [hyval] at h
      simpa using h
    have hxeq : (x : MulAut W) = t * (x : MulAut W) * t⁻¹ := by
      have h2 : (x : MulAut W) = (x : MulAut W) *
          (t * (x : MulAut W) * t⁻¹)⁻¹ * (t * (x : MulAut W) * t⁻¹) := by group
      rw [hyval1, one_mul] at h2
      exact h2
    have hXt : (x : MulAut W) * t = t * (x : MulAut W) := by
      conv_lhs => rw [hxeq]
      group
    exact hXt.symm
  have hdvd : orderOf y ∣ Nat.card (Subgroup.center ↥L) :=
    Subgroup.orderOf_dvd_natCard (Subgroup.center ↥L) hyc
  have hodd : Odd (orderOf y) := (w135_odd_card_center hctx).of_dvd_nat hdvd
  have hord_ne1 : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.mp h)
  have hord_ne0 : orderOf y ≠ 0 := by
    rintro h0
    rw [h0] at hodd
    exact absurd hodd (by decide)
  let p : ℕ := (orderOf y).minFac
  have hp : p.Prime := Nat.minFac_prime hord_ne1
  have hpdvd : p ∣ orderOf y := Nat.minFac_dvd _
  have hp2 : p ≠ 2 := hodd.ne_two_of_dvd_nat hpdvd
  let y' : ↥L := y ^ (orderOf y / p)
  have hy'ord : orderOf y' = p := orderOf_pow_orderOf_div hord_ne0 hpdvd
  have hy'ordW : orderOf (y' : MulAut W) = p := by
    rw [Subgroup.orderOf_coe, hy'ord]
  have hy'c : y' ∈ Subgroup.center ↥L := (Subgroup.center ↥L).pow_mem hyc _
  have hy'1 : y' ≠ 1 := by
    intro h
    have h1 : orderOf y' = 1 := by rw [h, orderOf_one]
    rw [hy'ord] at h1
    exact hp.ne_one h1
  have hy'val : (y' : MulAut W) = (y : MulAut W) ^ (orderOf y / p) := rfl
  have hconjy' : t * (y' : MulAut W) * t⁻¹ = (y' : MulAut W)⁻¹ := by
    rw [hy'val]
    exact w16g_conj_pow_inv hconj _
  have hXcard : Nat.card (Subgroup.zpowers (y' : MulAut W)) = p := by
    rw [Nat.card_zpowers, hy'ordW]
  have hXrank : IsElemAbelianOfRank p 1 ↥(Subgroup.zpowers (y' : MulAut W)) :=
    w16g_isElemAbelianOfRank_one_of_card hp hXcard
  have hinv : ∀ a ∈ Subgroup.zpowers (y' : MulAut W), t * a * t⁻¹ = a⁻¹ := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    calc t * (y' : MulAut W) ^ k * t⁻¹
        = MulAut.conj t ((y' : MulAut W) ^ k) := (MulAut.conj_apply t _).symm
      _ = (MulAut.conj t (y' : MulAut W)) ^ k := map_zpow (MulAut.conj t) _ _
      _ = ((y' : MulAut W)⁻¹) ^ k := by rw [MulAut.conj_apply, hconjy']
      _ = ((y' : MulAut W) ^ k)⁻¹ := by rw [inv_zpow]
  have hcommtop : commSub (⊤ : Subgroup W) (Subgroup.zpowers (y' : MulAut W)) = ⊤ :=
    w107_commSub_center_eq_top hctx hy'c hy'1
  have heq := rk_commSub_eq_two_mul_of_inverted (W := W) hW ht2 hp hp2
    (Nat.one_pos) hXrank hinv
  rw [hcommtop, rk_top] at heq
  have hrk : rk W ≤ 6 := by
    rw [heq]
    calc 2 * rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) ≤ 2 * 3 :=
          Nat.mul_le_mul_left 2 (w107_rk_commSub_zpowers_le_three hm)
      _ = 6 := by norm_num
  exact w107_false_of_rk_le_six hW hU hrk

end CFSG.LocalAnalysis.WeakClosure81
