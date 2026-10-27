module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3B3

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T CFSG.Open
open Fin.NatCast Fin.CommRing

namespace Sec8P3

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem exists_two_pow_mul : ∀ b : Fin 5, b ≠ 0 → ∃ j : ℕ, j < 4 ∧ 2 ^ j * (1 : Fin 5) = b := by
  decide

theorem winv_pow_smul_beta (F : FanTree Γ G) (h71c : Fan71c F L) {w : G} (hw : IsW1Elem D w)
    (j : ℕ) (i : Fin 5) : (w⁻¹) ^ j • D.beta i = D.beta (2 ^ j * i) := by
  induction j generalizing i with
  | zero => simp
  | succ j ih =>
    have h1 : w⁻¹ • D.beta i = D.beta (2 * i) :=
      isW1Elem_smul_vert D F h71c hw i (m := 1) (by norm_num)
    rw [pow_succ, mul_smul, h1, ih]
    congr 1
    ring

theorem stabilizer_le_closure_sup (F : FanTree Γ G) (h71c : Fan71c F L) {w : G}
    (hw : IsW1Elem D w) :
    MulAction.stabilizer G α ≤ Subgroup.closure ({D.x, w} : Set G) ⊔ nbrStab Γ G α := by
  intro g hg
  have hwα : w • α = α := by
    have := (Arc.mem_stab G).1 hw.1 0 (by norm_num)
    rwa [D.start] at this
  have hwβ : w • D.beta 0 = D.beta 0 := by
    have := (Arc.mem_stab G).1 hw.1 1 (by norm_num)
    exact this
  have hgα : g • α = α := MulAction.mem_stabilizer_iff.1 hg
  have hxα : D.x ∈ MulAction.stabilizer G α := D.x_mem_stabilizer F h71c
  have hx : D.x ∈ Subgroup.closure ({D.x, w} : Set G) := Subgroup.subset_closure (by simp)
  have hwc : w ∈ Subgroup.closure ({D.x, w} : Set G) := Subgroup.subset_closure (by simp)
  obtain ⟨a, ha⟩ := D.exists_beta_eq F h71c
    ((F.adj_smul g α (D.beta 0)).2 (D.adj_start_beta 0) |> fun h => by rwa [hgα] at h)
  have hxa : (D.x ^ a.val)⁻¹ • D.beta 0 = D.beta a := by
    have := D.x_pow_inv_smul_vert F h71c a.val 0 (m := 1) (by norm_num)
    rwa [zero_add, Fin.cast_val_eq_self] at this
  have hg1 : (D.x ^ a.val * g) • D.beta 0 = D.beta 0 := by
    rw [mul_smul, ← ha, ← hxa, smul_inv_smul]
  obtain ⟨b, hb⟩ := D.exists_beta_eq F h71c
    ((F.adj_smul (D.x ^ a.val * g) α (D.beta 1)).2 (D.adj_start_beta 1) |> fun h => by
      rwa [show (D.x ^ a.val * g) • α = α by
        rw [mul_smul, hgα]; exact MulAction.mem_stabilizer_iff.1 (pow_mem hxα a.val)] at h)
  have hne01 : D.beta 0 ≠ D.beta 1 := fun h => by
    have := D.beta_injective F h71c h
    exact absurd this (by decide)
  have hb0 : b ≠ 0 := by
    rintro rfl
    have : (D.x ^ a.val * g) • D.beta 1 = (D.x ^ a.val * g) • D.beta 0 := by
      rw [hg1]
      exact hb.symm
    exact hne01 (MulAction.injective _ this).symm
  obtain ⟨j, -, hj⟩ := exists_two_pow_mul b hb0
  have hwstab : w ∈ MulAction.stabilizer G α := MulAction.mem_stabilizer_iff.2 hwα
  have hwj : w ^ j • D.beta 0 = D.beta 0 :=
    MulAction.mem_stabilizer_iff.1 (pow_mem (MulAction.mem_stabilizer_iff.2 hwβ) j)
  have hg2 : (w ^ j * (D.x ^ a.val * g)) • D.beta 0 = D.beta 0 := by
    rw [mul_smul, hg1, hwj]
  have hg2' : (w ^ j * (D.x ^ a.val * g)) • D.beta 1 = D.beta 1 := by
    rw [mul_smul, ← hb, ← hj, ← winv_pow_smul_beta D F h71c hw j 1, ← mul_smul, inv_pow,
      mul_inv_cancel, one_smul]
  have hg2stab : w ^ j * (D.x ^ a.val * g) ∈ MulAction.stabilizer G α :=
    mul_mem (pow_mem hwstab j) (mul_mem (pow_mem hxα a.val) hg)
  have hK : w ^ j * (D.x ^ a.val * g) ∈ nbrStab Γ G α :=
    mem_nbrStab.2 fun c hc => F.frobenius_two α (D.beta 0) (D.beta 1) (D.adj_start_beta 0)
      (D.adj_start_beta 1) hne01 _ hg2stab hg2 hg2' c hc
  have hcl : ((D.x ^ a.val)⁻¹ * (w ^ j)⁻¹) ∈ Subgroup.closure ({D.x, w} : Set G) :=
    mul_mem (inv_mem (pow_mem hx a.val)) (inv_mem (pow_mem hwc j))
  have := Subgroup.mul_mem_sup hcl hK
  convert this using 1
  group

end Sec8P3

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan_8_6c (F : FanTree Γ G) (L : ZLab Γ G) (h71c : Fan71c F L) : Fan86c F L := by
  intro α D w hw
  refine ⟨le_antisymm (Sec8P3.stabilizer_le_closure_sup D F h71c hw) ?_,
    Sec8P3.nonempty_mulEquiv_sz_of_pair (D.orderOf_x F) hw.2.1 hw.2.2.1⟩
  refine sup_le ?_ (F.nbrStab_le_stabilizer α)
  rw [Subgroup.closure_le]
  intro g hg
  rcases hg with hg | hg
  · rw [hg]
    exact D.x_mem_stabilizer F h71c
  · have hg' : g = w := hg
    have := (Arc.mem_stab G).1 hw.1 0 (by norm_num)
    rw [D.start] at this
    rw [hg']
    exact MulAction.mem_stabilizer_iff.2 this

end CFSG.Quasithin.Fan86
