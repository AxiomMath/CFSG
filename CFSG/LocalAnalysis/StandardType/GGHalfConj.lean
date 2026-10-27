module

public import CFSG.LocalAnalysis.StandardType.GGHalfZpowers
public import CFSG.LocalAnalysis.StandardType.GGHalfAux
public import CFSG.LocalAnalysis.StandardType.GGHalfSlOnLevi
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockPerm
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarPComp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

private theorem sigmaPerm_commute_slLower2 {m : ℕ} (hm : 1 ≤ m)
    {s : SpecialLinearGroup (Fin (m + 1)) F2}
    (hs : s ∈ slOn (m + 1) {j : Fin (m + 1) | 2 ≤ j.val}) :
    slPerm gf2_two (sigmaPerm m) * slLower2Hom m s =
      slLower2Hom m s * slPerm gf2_two (sigmaPerm m) := by
  have hmem : slLower2Hom m s ∈
      slOn (m + 1 + 1 + 1)
        ((fun i : Fin (m + 1) => i.succ.succ) '' {j : Fin (m + 1) | 2 ≤ j.val}) := by
    rw [← slLower2Hom_map_slOn]
    exact Subgroup.mem_map_of_mem (slLower2Hom m) hs
  refine commute_slPerm_slOn (N := m + 1 + 1 + 1) (π := sigmaPerm m) ?_ hmem
  rintro i ⟨j, hj, rfl⟩
  dsimp only
  have hj2 : 2 ≤ j.val := hj
  have hj4 : 4 ≤ (j.succ.succ : Fin (m + 1 + 1 + 1)).val := by
    rw [Fin.val_succ, Fin.val_succ]; omega
  apply sigmaPerm_apply_of_fixed m
  · intro hh
    have hh' := congrArg Fin.val hh
    rw [Fin.val_zero] at hh'
    omega
  · intro hh
    have hh' := congrArg Fin.val hh
    rw [Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt (show (1 : ℕ) < m + 1 + 1 + 1 by omega)] at hh'
    omega
  · intro hh
    have hh' := congrArg Fin.val hh
    rw [Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt (show (2 : ℕ) < m + 1 + 1 + 1 by omega)] at hh'
    omega
  · intro hh
    have hh' := congrArg Fin.val hh
    rw [Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt (show (3 : ℕ) < m + 1 + 1 + 1 by omega)] at hh'
    omega

private theorem tauPerm_commute_slUpper2 {m : ℕ} (hm : 1 ≤ m)
    {s : SpecialLinearGroup (Fin (m + 1)) F2}
    (hs : s ∈ slOn (m + 1) {j : Fin (m + 1) | 2 ≤ j.val}) :
    slPerm gf2_two (tauPerm m) * slUpper2Hom m s =
      slUpper2Hom m s * slPerm gf2_two (tauPerm m) := by
  have hmem : slUpper2Hom m s ∈
      slOn (m + 1 + 1 + 1)
        ((fun i : Fin (m + 1) => i.castSucc.castSucc) '' {j : Fin (m + 1) | 2 ≤ j.val}) := by
    rw [← slUpper2Hom_map_slOn]
    exact Subgroup.mem_map_of_mem (slUpper2Hom m) hs
  refine commute_slPerm_slOn (N := m + 1 + 1 + 1) (π := tauPerm m) ?_ hmem
  rintro i ⟨j, hj, rfl⟩
  dsimp only
  have hj2 : 2 ≤ j.val := hj
  have hjm : j.val ≤ m := by have := j.isLt; omega
  apply tauPerm_apply_of_fixed m
  · intro hh
    have hh' := congrArg Fin.val hh
    simp only [Fin.val_castSucc, Fin.val_zero] at hh'
    omega
  · intro hh
    have hh' := congrArg Fin.val hh
    simp only [Fin.val_castSucc, Fin.coe_ofNat_eq_mod,
      Nat.mod_eq_of_lt (show (1 : ℕ) < m + 1 + 1 + 1 by omega)] at hh'
    omega
  · intro hh
    have hh' := congrArg Fin.val hh
    simp only [Fin.val_castSucc, Fin.val_last] at hh'
    omega
  · intro hh
    have hh' := congrArg Fin.val hh
    simp only [Fin.val_castSucc, Fin.val_last] at hh'
    omega

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J K : Subgroup G} {m : ℕ} {y : G}
  {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
  (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂)

include h

theorem zpowers_conj_gElt_y :
    Subgroup.zpowers (gElt φ₁ * y * (gElt φ₁)⁻¹) = Subgroup.zpowers (uElt φ₂) := by
  have hm : 1 ≤ m := by have := h.nbr.2.2.1; omega
  have hconj : (MulAut.conj (gElt φ₁)).toMonoidHom
        (φ₁ (omegaBlock (m + 1 + 1) ⟨0, by omega⟩)) =
      φ₁ (omegaBlock (m + 1 + 1) ⟨2, by omega⟩) := by
    show (MulAut.conj (gElt φ₁)) (φ₁ (omegaBlock (m + 1 + 1) ⟨0, by omega⟩)) = _
    have h0 : sigmaPerm m (⟨0, by omega⟩ : Fin (m + 1 + 1)).castSucc =
        (⟨2, by omega⟩ : Fin (m + 1 + 1)).castSucc := by
      rw [show (⟨0, by omega⟩ : Fin (m + 1 + 1)).castSucc =
          (0 : Fin (m + 1 + 1 + 1)) from Fin.castSucc_zero, sigmaPerm_apply_zero m hm]
      exact Fin.ext (by simp [Fin.val_castSucc, Fin.val_mk, Fin.coe_ofNat_eq_mod,
        Nat.mod_eq_of_lt (show (2 : ℕ) < m + 1 + 1 + 1 by omega)])
    have h1 : sigmaPerm m (⟨0, by omega⟩ : Fin (m + 1 + 1)).succ =
        (⟨2, by omega⟩ : Fin (m + 1 + 1)).succ := by
      rw [show (⟨0, by omega⟩ : Fin (m + 1 + 1)).succ =
          (1 : Fin (m + 1 + 1 + 1)) from Fin.succ_zero_eq_one, sigmaPerm_apply_one m hm]
      exact Fin.ext (by simp [Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
        Nat.mod_eq_of_lt (show (3 : ℕ) < m + 1 + 1 + 1 by omega)])
    calc (MulAut.conj (gElt φ₁)) (φ₁ (omegaBlock (m + 1 + 1) ⟨0, by omega⟩))
        = gElt φ₁ * φ₁ (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) * (gElt φ₁)⁻¹ :=
          MulAut.conj_apply _ _
      _ = φ₁ (slPerm gf2_two (sigmaPerm m) * omegaBlock (m + 1 + 1) ⟨0, by omega⟩ *
            (slPerm gf2_two (sigmaPerm m))⁻¹) := by
          change φ₁ (slPerm gf2_two (sigmaPerm m)) *
              φ₁ (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) *
              (φ₁ (slPerm gf2_two (sigmaPerm m)))⁻¹ = _
          rw [← map_mul, ← map_inv, ← map_mul]
      _ = φ₁ (omegaBlock (m + 1 + 1) ⟨2, by omega⟩) := by
          rw [slPerm_conj_omegaBlock (n := m + 1 + 1) (sigmaPerm m) h0 h1]
  have hf : (MulAut.conj (gElt φ₁)).toMonoidHom y = gElt φ₁ * y * (gElt φ₁)⁻¹ := by
    simp [MulAut.conj_apply]
  rw [← hf, ← MonoidHom.map_zpowers (MulAut.conj (gElt φ₁)).toMonoidHom y, h.zpowers_y,
    MonoidHom.map_zpowers, hconj, ← h.uElt_eq]

theorem zpowers_conj_hElt_x :
    Subgroup.zpowers (hElt φ₂ * x * (hElt φ₂)⁻¹) = Subgroup.zpowers (uElt φ₂) := by
  have hm : 1 ≤ m := by have := h.nbr.2.2.1; omega
  have hconj : (MulAut.conj (hElt φ₂)).toMonoidHom
        (φ₂ (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩)) = uElt φ₂ := by
    show (MulAut.conj (hElt φ₂)) (φ₂ (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩)) = _
    have h0 : tauPerm m (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).castSucc =
        (⟨0, by omega⟩ : Fin (m + 1 + 1)).castSucc := by
      rw [show (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).castSucc =
          (Fin.last (m + 1)).castSucc from rfl, tauPerm_apply_lastCast m hm]
      exact Fin.castSucc_zero.symm
    have h1 : tauPerm m (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).succ =
        (⟨0, by omega⟩ : Fin (m + 1 + 1)).succ := by
      rw [show (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).succ =
          Fin.last (m + 1 + 1) from rfl, tauPerm_apply_lastSucc m hm]
      exact Fin.succ_zero_eq_one.symm
    calc (MulAut.conj (hElt φ₂)) (φ₂ (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩))
        = hElt φ₂ * φ₂ (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩) * (hElt φ₂)⁻¹ :=
          MulAut.conj_apply _ _
      _ = φ₂ (slPerm gf2_two (tauPerm m) * omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ *
            (slPerm gf2_two (tauPerm m))⁻¹) := by
          change φ₂ (slPerm gf2_two (tauPerm m)) *
              φ₂ (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩) *
              (φ₂ (slPerm gf2_two (tauPerm m)))⁻¹ = _
          rw [← map_mul, ← map_inv, ← map_mul]
      _ = uElt φ₂ := by
          rw [slPerm_conj_omegaBlock (n := m + 1 + 1) (tauPerm m) h0 h1]
          rfl
  have hf : (MulAut.conj (hElt φ₂)).toMonoidHom x = hElt φ₂ * x * (hElt φ₂)⁻¹ := by
    simp [MulAut.conj_apply]
  rw [← hf, ← MonoidHom.map_zpowers (MulAut.conj (hElt φ₂)).toMonoidHom x, h.zpowers_x,
    MonoidHom.map_zpowers, hconj]

theorem levi4_le_conj_g :
    (slOn (m + 1) {j : Fin (m + 1) | 2 ≤ j.val}).map (φ₁.comp (slLower2Hom m)) ≤
      K.map (MulAut.conj (gElt φ₁)).toMonoidHom := by
  have hm : 1 ≤ m := by have := h.nbr.2.2.1; omega
  rintro p ⟨s, hs, rfl⟩
  have hcommSL := sigmaPerm_commute_slLower2 (m := m) hm hs
  have hcommG : gElt φ₁ * φ₁ (slLower2Hom m s) = φ₁ (slLower2Hom m s) * gElt φ₁ := by
    calc gElt φ₁ * φ₁ (slLower2Hom m s)
        = φ₁ (slPerm gf2_two (sigmaPerm m)) * φ₁ (slLower2Hom m s) := by
          rw [show gElt φ₁ = φ₁ (slPerm gf2_two (sigmaPerm m)) from rfl]
      _ = φ₁ (slPerm gf2_two (sigmaPerm m) * slLower2Hom m s) :=
          (map_mul φ₁ (slPerm gf2_two (sigmaPerm m)) (slLower2Hom m s)).symm
      _ = φ₁ (slLower2Hom m s * slPerm gf2_two (sigmaPerm m)) := by rw [hcommSL]
      _ = φ₁ (slLower2Hom m s) * φ₁ (slPerm gf2_two (sigmaPerm m)) :=
          map_mul φ₁ (slLower2Hom m s) (slPerm gf2_two (sigmaPerm m))
      _ = φ₁ (slLower2Hom m s) * gElt φ₁ := by
          rw [show gElt φ₁ = φ₁ (slPerm gf2_two (sigmaPerm m)) from rfl]
  have hpK : φ₁ (slLower2Hom m s) ∈ K := by
    rw [show φ₁ (slLower2Hom m s) = φ₂ (slUpper2Hom m s) from
        DFunLike.congr_fun h.coords.agree s, ← h.coords.range₂]
    exact MonoidHom.mem_range.mpr ⟨slUpper2Hom m s, rfl⟩
  refine Subgroup.mem_map.mpr ⟨φ₁ (slLower2Hom m s), hpK, ?_⟩
  show (MulAut.conj (gElt φ₁)) (φ₁ (slLower2Hom m s)) = φ₁ (slLower2Hom m s)
  rw [MulAut.conj_apply, hcommG]
  group

theorem levi4_le_conj_h :
    (slOn (m + 1) {j : Fin (m + 1) | 2 ≤ j.val}).map (φ₁.comp (slLower2Hom m)) ≤
      L.map (MulAut.conj (hElt φ₂)).toMonoidHom := by
  have hm : 1 ≤ m := by have := h.nbr.2.2.1; omega
  rintro p ⟨s, hs, rfl⟩
  have hcommSL := tauPerm_commute_slUpper2 (m := m) hm hs
  have hcommG : hElt φ₂ * φ₂ (slUpper2Hom m s) = φ₂ (slUpper2Hom m s) * hElt φ₂ := by
    calc hElt φ₂ * φ₂ (slUpper2Hom m s)
        = φ₂ (slPerm gf2_two (tauPerm m)) * φ₂ (slUpper2Hom m s) := by
          rw [show hElt φ₂ = φ₂ (slPerm gf2_two (tauPerm m)) from rfl]
      _ = φ₂ (slPerm gf2_two (tauPerm m) * slUpper2Hom m s) :=
          (map_mul φ₂ (slPerm gf2_two (tauPerm m)) (slUpper2Hom m s)).symm
      _ = φ₂ (slUpper2Hom m s * slPerm gf2_two (tauPerm m)) := by rw [hcommSL]
      _ = φ₂ (slUpper2Hom m s) * φ₂ (slPerm gf2_two (tauPerm m)) :=
          map_mul φ₂ (slUpper2Hom m s) (slPerm gf2_two (tauPerm m))
      _ = φ₂ (slUpper2Hom m s) * hElt φ₂ := by
          rw [show hElt φ₂ = φ₂ (slPerm gf2_two (tauPerm m)) from rfl]
  have hp_eq : φ₁ (slLower2Hom m s) = φ₂ (slUpper2Hom m s) :=
    DFunLike.congr_fun h.coords.agree s
  have hcommG' : hElt φ₂ * φ₁ (slLower2Hom m s) = φ₁ (slLower2Hom m s) * hElt φ₂ := by
    rw [hp_eq]; exact hcommG
  have hpL : φ₁ (slLower2Hom m s) ∈ L := by
    rw [← h.coords.range₁]
    exact MonoidHom.mem_range.mpr ⟨slLower2Hom m s, rfl⟩
  refine Subgroup.mem_map.mpr ⟨φ₁ (slLower2Hom m s), hpL, ?_⟩
  show (MulAut.conj (hElt φ₂)) (φ₁ (slLower2Hom m s)) = φ₁ (slLower2Hom m s)
  rw [MulAut.conj_apply, hcommG']
  group

theorem conj_eq (hm : 4 ≤ m) :
    K.map (MulAut.conj (gElt φ₁)).toMonoidHom = L.map (MulAut.conj (hElt φ₂)).toMonoidHom := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Subgroup G :=
    (slOn (m + 1) {j : Fin (m + 1) | 2 ≤ j.val}).map (φ₁.comp (slLower2Hom m))
  have hzw : Subgroup.zpowers (gElt φ₁ * y * (gElt φ₁)⁻¹) =
      Subgroup.zpowers (hElt φ₂ * x * (hElt φ₂)⁻¹) := by
    rw [zpowers_conj_gElt_y h, zpowers_conj_hElt_x h]
  have hPa : P ≤ K.map (MulAut.conj (gElt φ₁)).toMonoidHom := levi4_le_conj_g h
  have hPb : P ≤ L.map (MulAut.conj (hElt φ₂)).toMonoidHom := levi4_le_conj_h h
  have hperf : P ≤ ⁅P, P⁆ := by
    have h0 : slOn (m + 1) {j : Fin (m + 1) | 2 ≤ j.val} ≤
        ⁅slOn (m + 1) {j : Fin (m + 1) | 2 ≤ j.val},
          slOn (m + 1) {j : Fin (m + 1) | 2 ≤ j.val}⁆ :=
      slOn_perfect ⟨⟨2, by omega⟩, ⟨3, by omega⟩, ⟨4, by omega⟩,
        by show (2 : ℕ) ≤ 2; norm_num,
        by show (2 : ℕ) ≤ 3; norm_num,
        by show (2 : ℕ) ≤ 4; norm_num,
        by intro hh; have := congrArg Fin.val hh; simp only [Fin.val_mk] at this; omega,
        by intro hh; have := congrArg Fin.val hh; simp only [Fin.val_mk] at this; omega,
        by intro hh; have := congrArg Fin.val hh; simp only [Fin.val_mk] at this; omega⟩
    have h1 := Subgroup.map_mono (f := φ₁.comp (slLower2Hom m)) h0
    rw [Subgroup.map_commutator] at h1
    exact h1
  have hg3 : φ₁ (slLower2Hom m (omegaBlock m ⟨2, by omega⟩)) ∈ P := by
    refine Subgroup.mem_map.mpr ⟨omegaBlock m ⟨2, by omega⟩, ?_, rfl⟩
    exact omegaBlock_mem_slOn (n := m) (k := ⟨2, by omega⟩)
      (by show (2 : ℕ) ≤ 2; norm_num) (by show (2 : ℕ) ≤ 3; norm_num)
  have hg3ne : φ₁ (slLower2Hom m (omegaBlock m ⟨2, by omega⟩)) ≠ 1 := by
    intro hh
    have h2 : slLower2Hom m (omegaBlock m ⟨2, by omega⟩) = 1 := by
      apply h.coords.inj₁
      rw [hh, map_one]
    have h3 : omegaBlock m ⟨2, by omega⟩ = 1 := by
      apply slLower2Hom_injective m
      rw [h2, map_one]
    exact omegaBlock_ne_one m ⟨2, by omega⟩ h3
  have hg3pow : φ₁ (slLower2Hom m (omegaBlock m ⟨2, by omega⟩)) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, omegaBlock_pow_three, map_one, map_one]
  exact eq_map_conj_of_pComponents (p := 3) (x := x) (y := y) (K := K) (L := L)
    (gElt φ₁) (hElt φ₂) h.pComponent_K h.pComponent_L hzw hPa hPb hperf hg3 hg3ne hg3pow

end GGHalfCtx

end CFSG.StandardType

end
