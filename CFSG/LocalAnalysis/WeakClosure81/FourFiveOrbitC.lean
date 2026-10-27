module

public import CFSG.LocalAnalysis.WeakClosure81.FourFiveOrbit

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.Quasithin.A1b CFSG.Quasithin.E2.E22N Subgroup
open scoped Pointwise
open CFSG.Quasithin (IsSylowIn)

variable {Q : Type} [Group Q] [Finite Q]

private theorem fourFive_exists_pow_two_mem_of_mem_sup {Y S : Subgroup Q} (hS2 : IsPGroup 2 S)
    (hSY : S ≤ Subgroup.normalizer (Y : Set Q)) {x : Q} (hx : x ∈ Y ⊔ S) :
    ∃ a : ℕ, x ^ 2 ^ a ∈ Y := by
  have hx' : x ∈ ((S ⊔ Y : Subgroup Q) : Set Q) := by rw [sup_comm]; exact hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right S Y hSY] at hx'
  obtain ⟨s, hs, y, hy, rfl⟩ := hx'
  obtain ⟨a, ha⟩ := hS2 ⟨s, hs⟩
  have ha' : s ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hm : ∀ m : ℕ, ∃ y' ∈ Y, (s * y) ^ m = s ^ m * y' := by
    intro m
    induction m with
    | zero => exact ⟨1, Y.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨y', hy', he⟩ := ih
      have hyc : s⁻¹ * y' * s⁻¹⁻¹ ∈ Y :=
        (Subgroup.mem_normalizer_iff.mp (hSY (S.inv_mem hs)) y').mp hy'
      refine ⟨(s⁻¹ * y' * s⁻¹⁻¹) * y, Y.mul_mem hyc hy, ?_⟩
      rw [pow_succ, he, pow_succ]
      group
  obtain ⟨y', hy', he⟩ := hm (2 ^ a)
  exact ⟨a, by rw [he, ha', one_mul]; exact hy'⟩

theorem fourFive_isSylowIn_of_le {T U : Subgroup Q} (hT : IsSylowIn 2 T ⊤) (hTU : T ≤ U) :
    IsSylowIn 2 T U :=
  ⟨hTU, hT.isPGroup, fun hdvd => hT.not_dvd_relIndex
    (hdvd.trans ⟨U.relIndex ⊤,
      (Subgroup.relIndex_mul_relIndex T U ⊤ hTU le_top).symm⟩)⟩

theorem fourFive_normal_inf_centralizer {U X : Subgroup Q}
    (h : U ≤ Subgroup.normalizer (X : Set Q)) :
    ((U ⊓ Subgroup.centralizer (X : Set Q)).subgroupOf U).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
  have hNC : Subgroup.normalizer (X : Set Q) ≤
      Subgroup.normalizer (Subgroup.centralizer (X : Set Q) : Set Q) :=
    Subgroup.le_normalizer_of_normal_subgroupOf (Subgroup.centralizer_le_normalizer (X : Set Q))
  exact (le_inf Subgroup.le_normalizer (h.trans hNC)).trans
    Subgroup.inf_normalizer_le_normalizer_inf

theorem fourFive_orbit_centralizer_le {T N J X U C : Subgroup Q} (hT : IsSylowIn 2 T ⊤)
    (hN : FourFiveNMN N) (hJ : IsComponentOf J N) (hX : X = ⨆ t ∈ T, conjSub t J)
    (hU : U = X ⊔ T) (hC : C = U ⊓ Subgroup.centralizer (X : Set Q)) : C ≤ T := by
  have hTN : T ≤ Subgroup.normalizer (X : Set Q) := fourFive_le_normalizer_orbit hX
  have hTU : T ≤ U := by rw [hU]; exact le_sup_right
  have hUN : U ≤ Subgroup.normalizer (X : Set Q) := by
    rw [hU]
    exact sup_le Subgroup.le_normalizer hTN
  have hCU : C ≤ U := hC.le.trans inf_le_left
  have hCnormal : (C.subgroupOf U).Normal := by
    rw [hC]
    exact fourFive_normal_inf_centralizer hUN
  have hCX : C ⊓ X = ⊥ := by
    rw [hC, inf_assoc, inf_comm (Subgroup.centralizer (X : Set Q)) X,
      fourFive_orbit_inf_centralizer hN hJ hX, inf_bot_eq]
  have hC2 : IsPGroup 2 C := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro c
    obtain ⟨k, hk⟩ := fourFive_exists_pow_two_mem_of_mem_sup hT.isPGroup hTN
      (show (c : Q) ∈ X ⊔ T from hU ▸ hCU c.2)
    have hcC : (c : Q) ^ 2 ^ k ∈ C := C.pow_mem c.2 (2 ^ k)
    have hbot : (c : Q) ^ 2 ^ k ∈ (⊥ : Subgroup Q) := by
      rw [← hCX]
      exact ⟨hcC, hk⟩
    have h1 : (c : Q) ^ 2 ^ k = 1 := Subgroup.mem_bot.mp hbot
    exact ⟨k, by rw [orderOf_dvd_iff_pow_eq_one]; exact Subtype.ext (by simpa using h1)⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (fourFive_isSylowIn_of_le hT hTU).le_of_normal hCU hCnormal hC2

end CFSG.LocalAnalysis.WeakClosure81
