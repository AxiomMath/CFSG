module

public import CFSG.RankThree.PartOne.KF.D8Mod
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG.RankThree.PartOne.KFU

section Pair

variable {G : Type*} [Group G] {n : ℕ} [NeZero n] {s t : G}

theorem pair_conj (hs : s * s = 1) (ht : t * t = 1) : s * (s * t) * s = (s * t)⁻¹ := by
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [mul_inv_rev, hs', ht']
  calc s * (s * t) * s = (s * s) * t * s := by simp only [mul_assoc]
    _ = t * s := by rw [hs, one_mul]

@[expose] def pairAct (hs : s * s = 1) (ht : t * t = 1) (hst : (s * t) ^ n = 1) :
    DihedralGroup n →* G :=
  dihedralLift (s * t) s hst hs (pair_conj hs ht)

theorem pairAct_r (hs : s * s = 1) (ht : t * t = 1) (hst : (s * t) ^ n = 1) (i : ZMod n) :
    pairAct hs ht hst (DihedralGroup.r i) = (s * t) ^ i.val := rfl

theorem pairAct_sr (hs : s * s = 1) (ht : t * t = 1) (hst : (s * t) ^ n = 1) (i : ZMod n) :
    pairAct hs ht hst (DihedralGroup.sr i) = s * (s * t) ^ i.val := rfl

theorem pairAct_sr_zero (hs : s * s = 1) (ht : t * t = 1) (hst : (s * t) ^ n = 1) :
    pairAct hs ht hst (DihedralGroup.sr 0) = s := by
  rw [pairAct_sr, ZMod.val_zero, pow_zero, mul_one]

theorem pairAct_sr_one (h1 : (1 : ZMod n).val = 1) (hs : s * s = 1) (ht : t * t = 1)
    (hst : (s * t) ^ n = 1) : pairAct hs ht hst (DihedralGroup.sr 1) = t := by
  rw [pairAct_sr, h1, pow_one, ← mul_assoc, hs, one_mul]

theorem pairAct_injective (hs : s * s = 1) (ht : t * t = 1) (hst : (s * t) ^ n = 1)
    (hord : orderOf (s * t) = n) (hsn : s ∉ Subgroup.zpowers (s * t)) :
    Function.Injective (pairAct hs ht hst) := by
  rw [injective_iff_map_eq_one]
  rintro (i | i) h
  · rw [pairAct_r] at h
    have h1 : orderOf (s * t) ∣ i.val := orderOf_dvd_of_pow_eq_one h
    rw [hord] at h1
    have h2 : i.val = 0 := Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt i)
    have h3 : i = 0 := (ZMod.val_eq_zero i).mp h2
    rw [h3, DihedralGroup.r_zero]
  · exfalso
    rw [pairAct_sr] at h
    apply hsn
    have h1 : s = ((s * t) ^ i.val)⁻¹ := eq_inv_of_mul_eq_one_left h
    have h2 : ((s * t) ^ i.val)⁻¹ ∈ Subgroup.zpowers (s * t) :=
      Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
    rwa [← h1] at h2

theorem pairAct_mem_closure (hs : s * s = 1) (ht : t * t = 1) (hst : (s * t) ^ n = 1)
    (γ : DihedralGroup n) : pairAct hs ht hst γ ∈ Subgroup.closure ({s, t} : Set G) := by
  have hs_mem : s ∈ Subgroup.closure ({s, t} : Set G) := Subgroup.subset_closure (by simp)
  have ht_mem : t ∈ Subgroup.closure ({s, t} : Set G) := Subgroup.subset_closure (by simp)
  have hst_mem : s * t ∈ Subgroup.closure ({s, t} : Set G) := Subgroup.mul_mem _ hs_mem ht_mem
  rcases γ with i | i
  · rw [pairAct_r]
    exact Subgroup.pow_mem _ hst_mem _
  · rw [pairAct_sr]
    exact Subgroup.mul_mem _ hs_mem (Subgroup.pow_mem _ hst_mem _)

theorem exists_pairAct_of_mem_closure (h1 : (1 : ZMod n).val = 1) (hs : s * s = 1)
    (ht : t * t = 1) (hst : (s * t) ^ n = 1) {x : G} (hx : x ∈ Subgroup.closure ({s, t} : Set G)) :
    ∃ γ : DihedralGroup n, pairAct hs ht hst γ = x := by
  have hle : Subgroup.closure ({s, t} : Set G) ≤ (pairAct hs ht hst).range := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ⟨DihedralGroup.sr 0, pairAct_sr_zero hs ht hst⟩
    · exact ⟨DihedralGroup.sr 1, pairAct_sr_one h1 hs ht hst⟩
  exact hle hx

end Pair

theorem dih6_involution_cases (γ : DihedralGroup 6) (h2 : γ * γ = 1) (h1 : γ ≠ 1) :
    γ = DihedralGroup.r 3 ∨ ∃ i : ZMod 6, γ = DihedralGroup.sr i := by
  revert γ
  decide

theorem dih8_involution_cases (γ : DihedralGroup 8) (h2 : γ * γ = 1) (h1 : γ ≠ 1) :
    γ = DihedralGroup.r 4 ∨ ∃ i : ZMod 8, γ = DihedralGroup.sr i := by
  revert γ
  decide

end CFSG.RankThree.PartOne.KFOUT3
