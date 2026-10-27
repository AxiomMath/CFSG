module

public import CFSG.LocalAnalysis.StandardType.GGHalfZpowers
public import CFSG.LocalAnalysis.StandardType.GGHalfSlOnLevi
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockPerm

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

private theorem commute_of_mem_zpowers {G : Type*} [Group G] {y k v : G}
    (hk : y * k = k * y) (hv : v ∈ Subgroup.zpowers y) : k * v = v * k := by
  have hy : y ∈ Subgroup.centralizer ({k} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hk.symm
  have hle : Subgroup.zpowers y ≤ Subgroup.centralizer ({k} : Set G) :=
    Subgroup.zpowers_le.mpr hy
  exact (Subgroup.mem_centralizer_iff.mp (hle hv)) k (Set.mem_singleton k)

private theorem fin_ne_ofNat_of_lt_val {n : ℕ} [NeZero n] {i : Fin n} {a k : ℕ}
    (hk : k < a) (hi : a ≤ i.val) : i ≠ Fin.ofNat n k := by
  intro hcon
  have hilt : i.val < n := i.isLt
  have hv : i.val = k := by
    rw [hcon, Fin.val_ofNat, Nat.mod_eq_of_lt (by omega : k < n)]
  omega

private theorem fin_ne_last_castSucc_of_val_le {m : ℕ} {i : Fin (m + 1 + 1 + 1)}
    (hi : i.val ≤ m) : i ≠ (Fin.last (m + 1)).castSucc := by
  intro hcon
  have hv : i.val = m + 1 := by rw [hcon, Fin.val_castSucc, Fin.val_last]
  omega

private theorem fin_ne_last_of_val_le {m : ℕ} {i : Fin (m + 1 + 1 + 1)}
    (hi : i.val ≤ m) : i ≠ Fin.last (m + 1 + 1) := by
  intro hcon
  have hv : i.val = m + 2 := by rw [hcon, Fin.val_last]
  omega

private theorem sigmaPerm_apply_of_val_ge_four {m : ℕ} {i : Fin (m + 1 + 1 + 1)}
    (hi : 4 ≤ i.val) : sigmaPerm m i = i :=
  sigmaPerm_apply_of_fixed m
    (fin_ne_ofNat_of_lt_val (n := m + 1 + 1 + 1) (a := 4) (k := 0) (by norm_num) hi)
    (fin_ne_ofNat_of_lt_val (n := m + 1 + 1 + 1) (a := 4) (k := 1) (by norm_num) hi)
    (fin_ne_ofNat_of_lt_val (n := m + 1 + 1 + 1) (a := 4) (k := 2) (by norm_num) hi)
    (fin_ne_ofNat_of_lt_val (n := m + 1 + 1 + 1) (a := 4) (k := 3) (by norm_num) hi)

private theorem tauPerm_apply_of_val_between {m : ℕ} {i : Fin (m + 1 + 1 + 1)}
    (hi2 : 2 ≤ i.val) (him : i.val ≤ m) : tauPerm m i = i :=
  tauPerm_apply_of_fixed m
    (fin_ne_ofNat_of_lt_val (n := m + 1 + 1 + 1) (a := 2) (k := 0) (by norm_num) hi2)
    (fin_ne_ofNat_of_lt_val (n := m + 1 + 1 + 1) (a := 2) (k := 1) (by norm_num) hi2)
    (fin_ne_last_castSucc_of_val_le him)
    (fin_ne_last_of_val_le him)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J K : Subgroup G} {m : ℕ} {y : G}
  {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
  (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂)

include h

theorem alpha_lower : ∀ s ∈ slOn (m + 1) {j : Fin (m + 1) | 2 ≤ j.val},
    gElt φ₁ * φ₂ (slUpper2Hom m s) * (gElt φ₁)⁻¹ =
      hElt φ₂ * φ₁ (slLower2Hom m s) * (hElt φ₂)⁻¹ := by
  intro s hs
  have hagree : φ₁ (slLower2Hom m s) = φ₂ (slUpper2Hom m s) := by
    simpa only [MonoidHom.comp_apply] using congrArg (fun f => f s) h.coords.agree
  have hLmem : slLower2Hom m s ∈ slOn (m + 1 + 1 + 1) {i : Fin (m + 1 + 1 + 1) | 4 ≤ i.val} := by
    have hsub : (fun i : Fin (m + 1) => i.succ.succ) '' {j : Fin (m + 1) | 2 ≤ j.val} ⊆
        {i : Fin (m + 1 + 1 + 1) | 4 ≤ i.val} := by
      rintro i ⟨j, hj, rfl⟩
      simp only [Set.mem_setOf_eq, Fin.val_succ] at hj ⊢
      omega
    have hmem : slLower2Hom m s ∈
        (slOn (m + 1) {j : Fin (m + 1) | 2 ≤ j.val}).map (slLower2Hom m) :=
      ⟨s, hs, rfl⟩
    rw [slLower2Hom_map_slOn m {j : Fin (m + 1) | 2 ≤ j.val}] at hmem
    exact slOn_mono hsub hmem
  have hUmem : slUpper2Hom m s ∈ slOn (m + 1 + 1 + 1)
      {i : Fin (m + 1 + 1 + 1) | 2 ≤ i.val ∧ i.val ≤ m} := by
    have hsub : (fun i : Fin (m + 1) => i.castSucc.castSucc) '' {j : Fin (m + 1) | 2 ≤ j.val} ⊆
        {i : Fin (m + 1 + 1 + 1) | 2 ≤ i.val ∧ i.val ≤ m} := by
      rintro i ⟨j, hj, rfl⟩
      simp only [Set.mem_setOf_eq, Fin.val_castSucc] at hj ⊢
      exact ⟨hj, by have := j.isLt; omega⟩
    have hmem : slUpper2Hom m s ∈
        (slOn (m + 1) {j : Fin (m + 1) | 2 ≤ j.val}).map (slUpper2Hom m) :=
      ⟨s, hs, rfl⟩
    rw [slUpper2Hom_map_slOn m {j : Fin (m + 1) | 2 ≤ j.val}] at hmem
    exact slOn_mono hsub hmem
  have hfixL : ∀ i ∈ {i : Fin (m + 1 + 1 + 1) | 4 ≤ i.val}, sigmaPerm m i = i :=
    fun i hi => sigmaPerm_apply_of_val_ge_four (by simpa only [Set.mem_setOf_eq] using hi)
  have hfixU : ∀ i ∈ {i : Fin (m + 1 + 1 + 1) | 2 ≤ i.val ∧ i.val ≤ m}, tauPerm m i = i :=
    fun i hi => tauPerm_apply_of_val_between hi.1 hi.2
  have hcommL : slPerm gf2_two (sigmaPerm m) * slLower2Hom m s =
      slLower2Hom m s * slPerm gf2_two (sigmaPerm m) :=
    commute_slPerm_slOn hfixL hLmem
  have hcommU : slPerm gf2_two (tauPerm m) * slUpper2Hom m s =
      slUpper2Hom m s * slPerm gf2_two (tauPerm m) :=
    commute_slPerm_slOn hfixU hUmem
  have hL : gElt φ₁ * φ₂ (slUpper2Hom m s) * (gElt φ₁)⁻¹ = φ₁ (slLower2Hom m s) := by
    rw [← hagree]
    have hg : gElt φ₁ * φ₁ (slLower2Hom m s) = φ₁ (slLower2Hom m s) * gElt φ₁ := by
      rw [gElt, ← map_mul, ← map_mul, hcommL]
    rw [hg, mul_assoc, mul_inv_cancel, mul_one]
  have hR : hElt φ₂ * φ₁ (slLower2Hom m s) * (hElt φ₂)⁻¹ = φ₁ (slLower2Hom m s) := by
    have hh : hElt φ₂ * φ₁ (slLower2Hom m s) = φ₁ (slLower2Hom m s) * hElt φ₂ := by
      rw [hagree, hElt, ← map_mul, ← map_mul, hcommU]
    rw [hh, mul_assoc, mul_inv_cancel, mul_one]
  rw [hL, hR]

theorem alpha_v :
    gElt φ₁ * φ₂ (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) * (gElt φ₁)⁻¹ =
      hElt φ₂ * φ₁ (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) * (hElt φ₂)⁻¹ := by
  have hm : 1 ≤ m := by have := h.nbr.2.2.1; omega
  obtain ⟨_, _, _, _, _, _, _, hKy, _, _⟩ := h.basic
  have h2c : ((⟨2, by omega⟩ : Fin (m + 1 + 1)).castSucc : Fin (m + 1 + 1 + 1)) = 2 := by
    apply Fin.ext
    rw [Fin.val_castSucc, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      Nat.mod_eq_of_lt (by omega : 2 < m + 1 + 1 + 1)]
  have h0c : ((⟨0, by omega⟩ : Fin (m + 1 + 1)).castSucc : Fin (m + 1 + 1 + 1)) = 0 := by
    apply Fin.ext
    rw [Fin.val_castSucc, Fin.val_mk, Fin.val_zero]
  have h3c : ((⟨2, by omega⟩ : Fin (m + 1 + 1)).succ : Fin (m + 1 + 1 + 1)) = 3 := by
    apply Fin.ext
    rw [Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      Nat.mod_eq_of_lt (by omega : 3 < m + 1 + 1 + 1)]
  have h1c : ((⟨0, by omega⟩ : Fin (m + 1 + 1)).succ : Fin (m + 1 + 1 + 1)) = 1 := by
    apply Fin.ext
    rw [Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      Nat.mod_eq_of_lt (by omega : 1 < m + 1 + 1 + 1)]
  have h0 : sigmaPerm m ((⟨2, by omega⟩ : Fin (m + 1 + 1)).castSucc) =
      (⟨0, by omega⟩ : Fin (m + 1 + 1)).castSucc := by
    rw [h2c, sigmaPerm_apply_two m hm, h0c]
  have h1 : sigmaPerm m ((⟨2, by omega⟩ : Fin (m + 1 + 1)).succ) =
      (⟨0, by omega⟩ : Fin (m + 1 + 1)).succ := by
    rw [h3c, sigmaPerm_apply_three m hm, h1c]
  have hL : gElt φ₁ * φ₂ (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) * (gElt φ₁)⁻¹ =
      φ₁ (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) := by
    have hu : φ₂ (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) =
        φ₁ (omegaBlock (m + 1 + 1) ⟨2, by omega⟩) := h.uElt_eq
    rw [hu, gElt, ← map_inv, ← map_mul, ← map_mul,
      slPerm_conj_omegaBlock (sigmaPerm m) h0 h1]
  have hR : hElt φ₂ * φ₁ (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) * (hElt φ₂)⁻¹ =
      φ₁ (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) := by
    have hv : φ₁ (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) ∈ Subgroup.zpowers y := by
      rw [h.zpowers_y]
      exact Subgroup.mem_zpowers _
    have hhK : hElt φ₂ ∈ K := by
      rw [← h.coords.range₂]
      exact ⟨slPerm gf2_two (tauPerm m), rfl⟩
    have hc := commute_of_mem_zpowers (hKy (hElt φ₂) hhK) hv
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  rw [hL, hR]

theorem alpha_w :
    gElt φ₁ * φ₂ (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩) * (gElt φ₁)⁻¹ =
      hElt φ₂ * φ₁ (omegaBlock (m + 1 + 1) ⟨2, by have := h.nbr.2.2.1; omega⟩) *
        (hElt φ₂)⁻¹ := by
  obtain ⟨_, _, _, _, _, _, hLx, _, _, _⟩ := h.basic
  have h0s : ((⟨0, by omega⟩ : Fin (m + 1 + 1)).castSucc : Fin (m + 1 + 1 + 1)) = 0 := by
    apply Fin.ext
    rw [Fin.val_castSucc, Fin.val_mk, Fin.val_zero]
  have h1s : ((⟨0, by omega⟩ : Fin (m + 1 + 1)).succ : Fin (m + 1 + 1 + 1)) = 1 := by
    apply Fin.ext
    rw [Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      Nat.mod_eq_of_lt (by omega : 1 < m + 1 + 1 + 1)]
  have h0 : tauPerm m ((⟨0, by omega⟩ : Fin (m + 1 + 1)).castSucc) =
      (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).castSucc := by
    rw [h0s, tauPerm_apply_zero m]
    apply Fin.ext
    rw [Fin.val_castSucc, Fin.val_last, Fin.val_castSucc, Fin.val_mk]
  have h1 : tauPerm m ((⟨0, by omega⟩ : Fin (m + 1 + 1)).succ) =
      (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).succ := by
    rw [h1s, tauPerm_apply_one m]
    apply Fin.ext
    rw [Fin.val_last, Fin.val_succ, Fin.val_mk]
  have hL : gElt φ₁ * φ₂ (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩) * (gElt φ₁)⁻¹ =
      φ₂ (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩) := by
    have hgL : gElt φ₁ ∈ L := by
      rw [← h.coords.range₁]
      exact ⟨slPerm gf2_two (sigmaPerm m), rfl⟩
    have hxL : x * gElt φ₁ = gElt φ₁ * x := hLx (gElt φ₁) hgL
    have hw : φ₂ (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩) ∈ Subgroup.zpowers x := by
      rw [h.zpowers_x]
      exact Subgroup.mem_zpowers _
    have hc := commute_of_mem_zpowers hxL hw
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  have hR : hElt φ₂ * φ₁ (omegaBlock (m + 1 + 1) ⟨2, by have := h.nbr.2.2.1; omega⟩) *
        (hElt φ₂)⁻¹ = φ₂ (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩) := by
    have hu : φ₁ (omegaBlock (m + 1 + 1) ⟨2, by have := h.nbr.2.2.1; omega⟩) =
        φ₂ (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) := h.uElt_eq.symm
    rw [hu, hElt, ← map_inv, ← map_mul, ← map_mul,
      slPerm_conj_omegaBlock (tauPerm m) h0 h1]
  rw [hL, hR]

end GGHalfCtx

end CFSG.StandardType

end
