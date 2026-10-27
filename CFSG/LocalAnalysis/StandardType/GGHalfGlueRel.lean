module

public import CFSG.LocalAnalysis.StandardType.GGHalfGlue

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

private theorem map_conj {H : Type} [Group H] {M : Type} [Group M] (φ : M →* H) (s r : M) :
    φ s * φ r * (φ s)⁻¹ = φ (s * r * s⁻¹) := by
  rw [map_mul, map_mul, map_inv]

namespace GGHalfCtx

private theorem weylRep_conj_omegaBlock_inv_self {n : ℕ} (k : Fin n) :
    weylRep n F2 k * omegaBlock n k * (weylRep n F2 k)⁻¹ = (omegaBlock n k)⁻¹ := by
  rw [weylRep_eq_slPerm n k]
  exact slPerm_conj_omegaBlock_inv (n := n) (π := Equiv.swap k.castSucc k.succ)
    (k := k) (k' := k) (by rw [Equiv.swap_apply_left]) (by rw [Equiv.swap_apply_right])

private theorem weylRep_conj_omegaBlock_of_fixed {n : ℕ} (k j : Fin n)
    (h0 : Equiv.swap k.castSucc k.succ j.castSucc = j.castSucc)
    (h1 : Equiv.swap k.castSucc k.succ j.succ = j.succ) :
    weylRep n F2 k * omegaBlock n j * (weylRep n F2 k)⁻¹ = omegaBlock n j := by
  rw [weylRep_eq_slPerm n k]
  exact slPerm_conj_omegaBlock (n := n) (π := Equiv.swap k.castSucc k.succ)
    (k := j) (k' := j) h0 h1

private theorem fin_two_val (m : ℕ) : (2 : Fin (m + 1 + 1 + 1)).val = 2 := by
  change 2 % (m + 1 + 1 + 1) = 2
  exact Nat.mod_eq_of_lt (by omega)

private theorem fin_three_val (m : ℕ) (hm : 1 ≤ m) : (3 : Fin (m + 1 + 1 + 1)).val = 3 := by
  change 3 % (m + 1 + 1 + 1) = 3
  exact Nat.mod_eq_of_lt (by omega)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J K : Subgroup G} {m : ℕ} {y : G}
  {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
  (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂)

include h

theorem s0_x : sZero φ₁ * x * (sZero φ₁)⁻¹ = x := by
  obtain ⟨-, -, -, -, -, -, hxL, -, -, -⟩ := h.basic
  have hs : sZero φ₁ ∈ L := by
    rw [sZero, ← h.coords.range₁]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  rw [← hxL _ hs]
  group

theorem s0_u : sZero φ₁ * uElt φ₂ * (sZero φ₁)⁻¹ = uElt φ₂ := by
  have hm : 3 ≤ m := by have := h.nbr.2.2.1; omega
  rw [h.uElt_eq, sZero, map_conj]
  congr 1
  refine weylRep_conj_omegaBlock_of_fixed (n := m + 1 + 1)
    (⟨0, by omega⟩ : Fin (m + 1 + 1)) (⟨2, by omega⟩ : Fin (m + 1 + 1)) ?_ ?_
  · apply Equiv.swap_apply_of_ne_of_ne
    · apply Fin.ne_of_val_ne; simp only [Fin.val_castSucc, Fin.val_mk]; omega
    · apply Fin.ne_of_val_ne; simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_mk]; omega
  · apply Equiv.swap_apply_of_ne_of_ne
    · apply Fin.ne_of_val_ne; simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_mk]; omega
    · apply Fin.ne_of_val_ne; simp only [Fin.val_succ, Fin.val_mk]; omega

theorem s0_v : sZero φ₁ * vElt φ₁ * (sZero φ₁)⁻¹ = (vElt φ₁)⁻¹ := by
  rw [sZero, vElt, map_conj, ← map_inv]
  congr 1
  exact weylRep_conj_omegaBlock_inv_self (⟨0, by omega⟩ : Fin (m + 1 + 1))

theorem g_x : gElt φ₁ * x * (gElt φ₁)⁻¹ = x := by
  obtain ⟨-, -, -, -, -, -, hxL, -, -, -⟩ := h.basic
  have hg : gElt φ₁ ∈ L := by
    rw [gElt, ← h.coords.range₁]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  rw [← hxL _ hg]
  group

theorem g_v : gElt φ₁ * vElt φ₁ * (gElt φ₁)⁻¹ = uElt φ₂ := by
  have hm : 3 ≤ m := by have := h.nbr.2.2.1; omega
  rw [h.uElt_eq, gElt, vElt, map_conj]
  congr 1
  refine slPerm_conj_omegaBlock (n := m + 1 + 1) (π := sigmaPerm m)
    (k := (⟨0, by omega⟩ : Fin (m + 1 + 1))) (k' := (⟨2, by omega⟩ : Fin (m + 1 + 1))) ?_ ?_
  · have hx0 : ((⟨0, by omega⟩ : Fin (m + 1 + 1)).castSucc : Fin (m + 1 + 1 + 1)) =
        (0 : Fin (m + 1 + 1 + 1)) := rfl
    have hy2 : ((⟨2, by omega⟩ : Fin (m + 1 + 1)).castSucc : Fin (m + 1 + 1 + 1)) =
        (2 : Fin (m + 1 + 1 + 1)) := by
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.val_mk, fin_two_val]
    have hv0 : (0 : Fin (m + 1 + 1 + 1)).val = 0 := Fin.val_zero _
    have hv1 : (1 : Fin (m + 1 + 1 + 1)).val = 1 := Fin.val_one _
    have hv3 : (3 : Fin (m + 1 + 1 + 1)).val = 3 := fin_three_val m (by omega)
    rw [sigmaPerm, Equiv.Perm.mul_apply, hx0]
    rw [Equiv.swap_apply_of_ne_of_ne (a := (1 : Fin (m + 1 + 1 + 1))) (b := 3) (x := 0)
          (Fin.ne_of_val_ne (by rw [hv0, hv1]; omega))
          (Fin.ne_of_val_ne (by rw [hv0, hv3]; omega))]
    rw [Equiv.swap_apply_left]
    exact hy2.symm
  · have hx1 : ((⟨0, by omega⟩ : Fin (m + 1 + 1)).succ : Fin (m + 1 + 1 + 1)) =
        (1 : Fin (m + 1 + 1 + 1)) := rfl
    have hy3 : ((⟨2, by omega⟩ : Fin (m + 1 + 1)).succ : Fin (m + 1 + 1 + 1)) =
        (3 : Fin (m + 1 + 1 + 1)) := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_mk, fin_three_val m (by omega)]
    have hv0 : (0 : Fin (m + 1 + 1 + 1)).val = 0 := Fin.val_zero _
    have hv2 : (2 : Fin (m + 1 + 1 + 1)).val = 2 := fin_two_val m
    have hv3 : (3 : Fin (m + 1 + 1 + 1)).val = 3 := fin_three_val m (by omega)
    rw [sigmaPerm, Equiv.Perm.mul_apply, hx1]
    rw [Equiv.swap_apply_left]
    rw [Equiv.swap_apply_of_ne_of_ne (a := (0 : Fin (m + 1 + 1 + 1))) (b := 2) (x := 3)
          (Fin.ne_of_val_ne (by rw [hv3, hv0]; omega))
          (Fin.ne_of_val_ne (by rw [hv3, hv2]; omega))]
    exact hy3.symm

theorem g_u : gElt φ₁ * uElt φ₂ * (gElt φ₁)⁻¹ = vElt φ₁ := by
  have hm : 3 ≤ m := by have := h.nbr.2.2.1; omega
  rw [h.uElt_eq, gElt, vElt, map_conj]
  congr 1
  refine slPerm_conj_omegaBlock (n := m + 1 + 1) (π := sigmaPerm m)
    (k := (⟨2, by omega⟩ : Fin (m + 1 + 1))) (k' := (⟨0, by omega⟩ : Fin (m + 1 + 1))) ?_ ?_
  · have hx2 : ((⟨2, by omega⟩ : Fin (m + 1 + 1)).castSucc : Fin (m + 1 + 1 + 1)) =
        (2 : Fin (m + 1 + 1 + 1)) := by
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.val_mk, fin_two_val]
    have hy0 : ((⟨0, by omega⟩ : Fin (m + 1 + 1)).castSucc : Fin (m + 1 + 1 + 1)) =
        (0 : Fin (m + 1 + 1 + 1)) := rfl
    have hv0 : (0 : Fin (m + 1 + 1 + 1)).val = 0 := Fin.val_zero _
    have hv1 : (1 : Fin (m + 1 + 1 + 1)).val = 1 := Fin.val_one _
    have hv2 : (2 : Fin (m + 1 + 1 + 1)).val = 2 := fin_two_val m
    have hv3 : (3 : Fin (m + 1 + 1 + 1)).val = 3 := fin_three_val m (by omega)
    rw [sigmaPerm, Equiv.Perm.mul_apply, hx2]
    rw [Equiv.swap_apply_of_ne_of_ne (a := (1 : Fin (m + 1 + 1 + 1))) (b := 3) (x := 2)
          (Fin.ne_of_val_ne (by rw [hv2, hv1]; omega))
          (Fin.ne_of_val_ne (by rw [hv2, hv3]; omega))]
    rw [Equiv.swap_apply_right]
    exact hy0.symm
  · have hx3 : ((⟨2, by omega⟩ : Fin (m + 1 + 1)).succ : Fin (m + 1 + 1 + 1)) =
        (3 : Fin (m + 1 + 1 + 1)) := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_mk, fin_three_val m (by omega)]
    have hy1 : ((⟨0, by omega⟩ : Fin (m + 1 + 1)).succ : Fin (m + 1 + 1 + 1)) =
        (1 : Fin (m + 1 + 1 + 1)) := rfl
    have hv0 : (0 : Fin (m + 1 + 1 + 1)).val = 0 := Fin.val_zero _
    have hv1 : (1 : Fin (m + 1 + 1 + 1)).val = 1 := Fin.val_one _
    have hv2 : (2 : Fin (m + 1 + 1 + 1)).val = 2 := fin_two_val m
    rw [sigmaPerm, Equiv.Perm.mul_apply, hx3]
    rw [Equiv.swap_apply_right]
    rw [Equiv.swap_apply_of_ne_of_ne (a := (0 : Fin (m + 1 + 1 + 1))) (b := 2) (x := 1)
          (Fin.ne_of_val_ne (by rw [hv1, hv0]; omega))
          (Fin.ne_of_val_ne (by rw [hv1, hv2]; omega))]
    exact hy1.symm

theorem sk_y : endT₂ φ₂ * y * (endT₂ φ₂)⁻¹ = y := by
  obtain ⟨-, -, -, -, -, -, -, hyK, -, -⟩ := h.basic
  have hk : endT₂ φ₂ ∈ K := by
    rw [endT₂, ← h.coords.range₂]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  rw [← hyK _ hk]
  group

theorem sk_u : endT₂ φ₂ * uElt φ₂ * (endT₂ φ₂)⁻¹ = uElt φ₂ := by
  have hm : 3 ≤ m := by have := h.nbr.2.2.1; omega
  rw [endT₂, uElt, map_conj]
  congr 1
  refine weylRep_conj_omegaBlock_of_fixed (n := m + 1 + 1)
    (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)) (⟨0, by omega⟩ : Fin (m + 1 + 1)) ?_ ?_
  · apply Equiv.swap_apply_of_ne_of_ne
    · apply Fin.ne_of_val_ne; simp only [Fin.val_castSucc, Fin.val_mk]; omega
    · apply Fin.ne_of_val_ne; simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_mk]; omega
  · apply Equiv.swap_apply_of_ne_of_ne
    · apply Fin.ne_of_val_ne; simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_mk]; omega
    · apply Fin.ne_of_val_ne; simp only [Fin.val_succ, Fin.val_mk]; omega

theorem sk_w : endT₂ φ₂ * wElt φ₂ * (endT₂ φ₂)⁻¹ = (wElt φ₂)⁻¹ := by
  rw [endT₂, wElt, map_conj, ← map_inv]
  congr 1
  exact weylRep_conj_omegaBlock_inv_self (⟨m + 1, by omega⟩ : Fin (m + 1 + 1))

theorem h_y : hElt φ₂ * y * (hElt φ₂)⁻¹ = y := by
  obtain ⟨-, -, -, -, -, -, -, hyK, -, -⟩ := h.basic
  have hk : hElt φ₂ ∈ K := by
    rw [hElt, ← h.coords.range₂]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  rw [← hyK _ hk]
  group

theorem h_u : hElt φ₂ * uElt φ₂ * (hElt φ₂)⁻¹ = wElt φ₂ := by
  have hm : 3 ≤ m := by have := h.nbr.2.2.1; omega
  rw [hElt, uElt, wElt, map_conj]
  congr 1
  refine slPerm_conj_omegaBlock (n := m + 1 + 1) (π := tauPerm m)
    (k := (⟨0, by omega⟩ : Fin (m + 1 + 1)))
    (k' := (⟨m + 1, by omega⟩ : Fin (m + 1 + 1))) ?_ ?_
  · have hx0 : ((⟨0, by omega⟩ : Fin (m + 1 + 1)).castSucc : Fin (m + 1 + 1 + 1)) =
        (0 : Fin (m + 1 + 1 + 1)) := rfl
    have hlast : (Fin.last (m + 1)).castSucc =
        ((⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).castSucc : Fin (m + 1 + 1 + 1)) := by
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.val_last, Fin.val_mk]
    have hv0 : (0 : Fin (m + 1 + 1 + 1)).val = 0 := Fin.val_zero _
    have hv1 : (1 : Fin (m + 1 + 1 + 1)).val = 1 := Fin.val_one _
    rw [tauPerm, Equiv.Perm.mul_apply, hx0]
    rw [Equiv.swap_apply_of_ne_of_ne (a := Fin.last (m + 1 + 1)) (b := (1 : Fin (m + 1 + 1 + 1)))
          (x := 0)
          (Fin.ne_of_val_ne (by rw [hv0, Fin.val_last]; omega))
          (Fin.ne_of_val_ne (by rw [hv0, hv1]; omega))]
    rw [Equiv.swap_apply_right]
    exact hlast
  · have hx1 : ((⟨0, by omega⟩ : Fin (m + 1 + 1)).succ : Fin (m + 1 + 1 + 1)) =
        (1 : Fin (m + 1 + 1 + 1)) := rfl
    have hlast : (Fin.last (m + 1 + 1) : Fin (m + 1 + 1 + 1)) =
        ((⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).succ : Fin (m + 1 + 1 + 1)) := by
      apply Fin.ext
      simp only [Fin.val_last, Fin.val_succ, Fin.val_mk]
    have hv0 : (0 : Fin (m + 1 + 1 + 1)).val = 0 := Fin.val_zero _
    have hv1 : (1 : Fin (m + 1 + 1 + 1)).val = 1 := Fin.val_one _
    rw [tauPerm, Equiv.Perm.mul_apply, hx1]
    rw [Equiv.swap_apply_right]
    rw [Equiv.swap_apply_of_ne_of_ne (a := (Fin.last (m + 1)).castSucc) (b := (0 : Fin (m + 1 + 1 + 1)))
          (x := Fin.last (m + 1 + 1))
          (Fin.ne_of_val_ne (by simp only [Fin.val_last, Fin.val_castSucc, Fin.val_last]; omega))
          (Fin.ne_of_val_ne (by rw [Fin.val_last, hv0]; omega))]
    exact hlast

theorem h_w : hElt φ₂ * wElt φ₂ * (hElt φ₂)⁻¹ = uElt φ₂ := by
  have hm : 3 ≤ m := by have := h.nbr.2.2.1; omega
  rw [hElt, wElt, uElt, map_conj]
  congr 1
  refine slPerm_conj_omegaBlock (n := m + 1 + 1) (π := tauPerm m)
    (k := (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)))
    (k' := (⟨0, by omega⟩ : Fin (m + 1 + 1))) ?_ ?_
  · have hkc : ((⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).castSucc : Fin (m + 1 + 1 + 1)) =
        (Fin.last (m + 1)).castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.val_mk, Fin.val_castSucc, Fin.val_last]
    have hy0 : ((⟨0, by omega⟩ : Fin (m + 1 + 1)).castSucc : Fin (m + 1 + 1 + 1)) =
        (0 : Fin (m + 1 + 1 + 1)) := rfl
    have hv0 : (0 : Fin (m + 1 + 1 + 1)).val = 0 := Fin.val_zero _
    have hv1 : (1 : Fin (m + 1 + 1 + 1)).val = 1 := Fin.val_one _
    rw [tauPerm, Equiv.Perm.mul_apply, hkc]
    rw [Equiv.swap_apply_of_ne_of_ne (a := Fin.last (m + 1 + 1)) (b := (1 : Fin (m + 1 + 1 + 1)))
          (x := (Fin.last (m + 1)).castSucc)
          (Fin.ne_of_val_ne (by simp only [Fin.val_last, Fin.val_castSucc, Fin.val_last]; omega))
          (Fin.ne_of_val_ne (by simp only [Fin.val_last, Fin.val_castSucc, Fin.val_one]; omega))]
    rw [Equiv.swap_apply_left]
    exact hy0.symm
  · have hks : ((⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).succ : Fin (m + 1 + 1 + 1)) =
        (Fin.last (m + 1 + 1) : Fin (m + 1 + 1 + 1)) := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_mk, Fin.val_last]
    have hy1 : ((⟨0, by omega⟩ : Fin (m + 1 + 1)).succ : Fin (m + 1 + 1 + 1)) =
        (1 : Fin (m + 1 + 1 + 1)) := rfl
    have hv0 : (0 : Fin (m + 1 + 1 + 1)).val = 0 := Fin.val_zero _
    have hv1 : (1 : Fin (m + 1 + 1 + 1)).val = 1 := Fin.val_one _
    rw [tauPerm, Equiv.Perm.mul_apply, hks, Equiv.swap_apply_left]
    rw [Equiv.swap_apply_of_ne_of_ne (a := (Fin.last (m + 1)).castSucc) (b := (0 : Fin (m + 1 + 1 + 1)))
          (x := (1 : Fin (m + 1 + 1 + 1)))
          (Fin.ne_of_val_ne (by rw [hv1, Fin.val_castSucc, Fin.val_last]; omega))
          (Fin.ne_of_val_ne (by rw [hv1, hv0]; omega))]
    exact hy1.symm

theorem zSet_fix : ∀ z ∈ zSet φ₁,
    sZero φ₁ * z * (sZero φ₁)⁻¹ = z ∧ gElt φ₁ * z * (gElt φ₁)⁻¹ = z ∧
      endT₂ φ₂ * z * (endT₂ φ₂)⁻¹ = z ∧ hElt φ₂ * z * (hElt φ₂)⁻¹ = z := by
  intro z hz
  obtain ⟨k, -, hk4, rfl⟩ := hz
  have hm : 3 ≤ m := by have := h.nbr.2.2.1; omega
  have hk_le : k.val ≤ m + 1 := by have := k.isLt; omega
  have hk2 : 2 ≤ k.val := by omega
  have hv0 : (0 : Fin (m + 1 + 1 + 1)).val = 0 := Fin.val_zero _
  have hv1 : (1 : Fin (m + 1 + 1 + 1)).val = 1 := Fin.val_one _
  have hv2 : (2 : Fin (m + 1 + 1 + 1)).val = 2 := fin_two_val m
  have hv3 : (3 : Fin (m + 1 + 1 + 1)).val = 3 := fin_three_val m (by omega)
  have hz2 : φ₁ (omegaBlock (m + 1 + 1) k) =
      φ₂ (omegaBlock (m + 1 + 1) (⟨k.val - 2, by omega⟩ : Fin (m + 1 + 1))) := by
    have hk_eq : k = (⟨k.val - 2, by omega⟩ : Fin m).succ.succ := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_mk]
      omega
    have h1 : omegaBlock (m + 1 + 1) k =
        omegaBlock (m + 1 + 1) ((⟨k.val - 2, by omega⟩ : Fin m).succ.succ) :=
      congrArg (omegaBlock (m + 1 + 1)) hk_eq
    have hlow : omegaBlock (m + 1 + 1) k =
        slLower2Hom m (omegaBlock m (⟨k.val - 2, by omega⟩ : Fin m)) := by
      rw [h1, slLower2Hom_omegaBlock]
      rfl
    have hagree :=
      DFunLike.congr_fun h.coords.agree (omegaBlock m (⟨k.val - 2, by omega⟩ : Fin m))
    simp only [MonoidHom.comp_apply] at hagree
    rw [hlow, hagree, slUpper2Hom_omegaBlock]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sZero, map_conj]
    rw [h.coords.inj₁.eq_iff]
    refine weylRep_conj_omegaBlock_of_fixed (n := m + 1 + 1)
      (⟨0, by omega⟩ : Fin (m + 1 + 1)) k ?_ ?_
    · apply Equiv.swap_apply_of_ne_of_ne
      · apply Fin.ne_of_val_ne; simp only [Fin.val_castSucc, Fin.val_mk]; omega
      · apply Fin.ne_of_val_ne; simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_mk]; omega
    · apply Equiv.swap_apply_of_ne_of_ne
      · apply Fin.ne_of_val_ne; simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_mk]; omega
      · apply Fin.ne_of_val_ne; simp only [Fin.val_succ, Fin.val_mk]; omega
  · rw [gElt, map_conj]
    rw [h.coords.inj₁.eq_iff]
    refine slPerm_conj_omegaBlock (n := m + 1 + 1) (π := sigmaPerm m) (k := k) (k' := k) ?_ ?_
    · rw [sigmaPerm, Equiv.Perm.mul_apply]
      rw [Equiv.swap_apply_of_ne_of_ne (a := (1 : Fin (m + 1 + 1 + 1))) (b := 3) (x := k.castSucc)
            (Fin.ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_mk, hv1]; omega))
            (Fin.ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_mk, hv3]; omega))]
      exact Equiv.swap_apply_of_ne_of_ne (a := (0 : Fin (m + 1 + 1 + 1))) (b := 2) (x := k.castSucc)
        (Fin.ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_mk, hv0]; omega))
        (Fin.ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_mk, hv2]; omega))
    · rw [sigmaPerm, Equiv.Perm.mul_apply]
      rw [Equiv.swap_apply_of_ne_of_ne (a := (1 : Fin (m + 1 + 1 + 1))) (b := 3) (x := k.succ)
            (Fin.ne_of_val_ne (by rw [Fin.val_succ, Fin.val_mk, hv1]; omega))
            (Fin.ne_of_val_ne (by rw [Fin.val_succ, Fin.val_mk, hv3]; omega))]
      exact Equiv.swap_apply_of_ne_of_ne (a := (0 : Fin (m + 1 + 1 + 1))) (b := 2) (x := k.succ)
        (Fin.ne_of_val_ne (by rw [Fin.val_succ, Fin.val_mk, hv0]; omega))
        (Fin.ne_of_val_ne (by rw [Fin.val_succ, Fin.val_mk, hv2]; omega))
  · rw [hz2, endT₂, map_conj]
    rw [h.coords.inj₂.eq_iff]
    refine weylRep_conj_omegaBlock_of_fixed (n := m + 1 + 1)
      (⟨m + 1, by omega⟩ : Fin (m + 1 + 1))
      (⟨k.val - 2, by omega⟩ : Fin (m + 1 + 1)) ?_ ?_
    · apply Equiv.swap_apply_of_ne_of_ne
      · apply Fin.ne_of_val_ne; simp only [Fin.val_castSucc, Fin.val_mk]; omega
      · apply Fin.ne_of_val_ne; simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_mk]; omega
    · apply Equiv.swap_apply_of_ne_of_ne
      · apply Fin.ne_of_val_ne; simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_mk]; omega
      · apply Fin.ne_of_val_ne; simp only [Fin.val_succ, Fin.val_mk]; omega
  · rw [hz2, hElt, map_conj]
    rw [h.coords.inj₂.eq_iff]
    refine slPerm_conj_omegaBlock (n := m + 1 + 1) (π := tauPerm m)
      (k := (⟨k.val - 2, by omega⟩ : Fin (m + 1 + 1)))
      (k' := (⟨k.val - 2, by omega⟩ : Fin (m + 1 + 1))) ?_ ?_
    · rw [tauPerm, Equiv.Perm.mul_apply]
      rw [Equiv.swap_apply_of_ne_of_ne (a := Fin.last (m + 1 + 1)) (b := (1 : Fin (m + 1 + 1 + 1)))
            (x := (⟨k.val - 2, by omega⟩ : Fin (m + 1 + 1)).castSucc)
            (Fin.ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_mk, Fin.val_last]; omega))
            (Fin.ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_mk, Fin.val_one]; omega))]
      exact Equiv.swap_apply_of_ne_of_ne
        (a := (Fin.last (m + 1)).castSucc) (b := (0 : Fin (m + 1 + 1 + 1)))
        (x := (⟨k.val - 2, by omega⟩ : Fin (m + 1 + 1)).castSucc)
        (Fin.ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_mk, Fin.val_castSucc, Fin.val_last]; omega))
        (Fin.ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_mk, Fin.val_zero]; omega))
    · rw [tauPerm, Equiv.Perm.mul_apply]
      rw [Equiv.swap_apply_of_ne_of_ne (a := Fin.last (m + 1 + 1)) (b := (1 : Fin (m + 1 + 1 + 1)))
            (x := (⟨k.val - 2, by omega⟩ : Fin (m + 1 + 1)).succ)
            (Fin.ne_of_val_ne (by simp only [Fin.val_succ, Fin.val_mk, Fin.val_last]; omega))
            (Fin.ne_of_val_ne (by simp only [Fin.val_succ, Fin.val_mk, Fin.val_one]; omega))]
      exact Equiv.swap_apply_of_ne_of_ne
        (a := (Fin.last (m + 1)).castSucc) (b := (0 : Fin (m + 1 + 1 + 1)))
        (x := (⟨k.val - 2, by omega⟩ : Fin (m + 1 + 1)).succ)
        (Fin.ne_of_val_ne (by simp only [Fin.val_succ, Fin.val_mk, Fin.val_castSucc, Fin.val_last]; omega))
        (Fin.ne_of_val_ne (by simp only [Fin.val_succ, Fin.val_mk, Fin.val_zero]; omega))

end GGHalfCtx

end CFSG.StandardType

end
