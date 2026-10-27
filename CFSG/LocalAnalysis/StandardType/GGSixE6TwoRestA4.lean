module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestA4Elts
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestCentD

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint

private theorem e6a4_xr_a5Root_mem_lE
    {i j : Fin 6} (hij : i ≠ j) : xr (a5Root i j) ∈ lE := by
  rw [lE]
  exact E6Pilot.pinnedX_a5Root_mem_a5Levi hij 1

private theorem e6a4_cOmegaE_mem_lE
    (k : Fin 3) : cOmegaE k ∈ lE := by
  have h01 : blk k 0 ≠ blk k 1 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [blk, Fin.val_mk] at hv
    omega
  rw [cOmegaE]
  exact mul_mem (e6a4_xr_a5Root_mem_lE h01) (e6a4_xr_a5Root_mem_lE h01.symm)

private theorem e6a4_wOmegaE_mem_lE :
    wOmegaE ∈ lE := by
  rw [wOmegaE]
  exact mul_mem (mul_mem (e6a4_cOmegaE_mem_lE 0) (e6a4_cOmegaE_mem_lE 1))
    (e6a4_cOmegaE_mem_lE 2)

private theorem e6a4_commute_zE_wOmegaE :
    Commute zE wOmegaE := by
  have hmem : zE ∈ Subgroup.centralizer (lE : Set EC) :=
    centralizer_zE.2.2 (Subgroup.mem_zpowers zE)
  exact (Subgroup.mem_centralizer_iff.mp hmem wOmegaE e6a4_wOmegaE_mem_lE).symm

private theorem e6a4_exists_mul_of_mem_sup {G : Type*} [Group G] {H K : Subgroup G}
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {g : G} (hg : g ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, h * k = g := by
  let S : Subgroup G :=
    { carrier := {g | ∃ h ∈ H, ∃ k ∈ K, h * k = g}
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by rw [one_mul]⟩
      mul_mem' := by
        rintro _ _ ⟨h1, h1H, k1, k1K, rfl⟩ ⟨h2, h2H, k2, k2K, rfl⟩
        refine ⟨h1 * h2, H.mul_mem h1H h2H, k1 * k2, K.mul_mem k1K k2K, ?_⟩
        rw [show (h1 * k1) * (h2 * k2) = h1 * (k1 * h2) * k2 by group,
          ← hcomm h2 h2H k1 k1K,
          show h1 * (h2 * k1) * k2 = (h1 * h2) * (k1 * k2) by group]
      inv_mem' := by
        rintro _ ⟨h, hH, k, kK, rfl⟩
        exact ⟨h⁻¹, H.inv_mem hH, k⁻¹, K.inv_mem kK, by
          rw [mul_inv_rev, (hcomm h⁻¹ (H.inv_mem hH) k⁻¹ (K.inv_mem kK)).symm]⟩ }
  have hHS : H ≤ S := fun h hh => ⟨h, hh, 1, K.one_mem, by rw [mul_one]⟩
  have hKS : K ≤ S := fun k hk => ⟨1, H.one_mem, k, hk, by rw [one_mul]⟩
  exact (sup_le hHS hKS) hg

private theorem e6a4_zpow_normal_form
    (g : EC) (hg : g ∈ dE) :
    ∃ i j : ℤ, g = zE ^ i * wOmegaE ^ j := by
  have hle : dE ≤ Subgroup.zpowers zE ⊔ Subgroup.zpowers wOmegaE := by
    rw [dE, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers zE)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers wOmegaE)
  have hcomm : ∀ a ∈ Subgroup.zpowers zE, ∀ b ∈ Subgroup.zpowers wOmegaE,
      a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact Commute.zpow_zpow e6a4_commute_zE_wOmegaE m n
  obtain ⟨a, ha, b, hb, hab⟩ := e6a4_exists_mul_of_mem_sup hcomm (hle hg)
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact ⟨i, j, by rw [← hab, ← hi, ← hj]⟩

private theorem e6a4_wOmegaE_pow_three :
    wOmegaE ^ (3 : ℕ) = 1 := by
  have h := pow_orderOf_eq_one wOmegaE
  rwa [orderOf_wOmegaE] at h

private theorem e6a4_zE_sq_eq_inv :
    zE ^ 2 = zE⁻¹ := by
  have h : zE ^ 2 * zE = 1 := by
    rw [← pow_succ]
    exact zE_pow_three
  exact eq_inv_of_mul_eq_one_left h

private theorem e6a4_wOmegaE_sq_eq_inv :
    wOmegaE ^ 2 = wOmegaE⁻¹ := by
  have h : wOmegaE ^ 2 * wOmegaE = 1 := by
    rw [← pow_succ]
    exact e6a4_wOmegaE_pow_three
  exact eq_inv_of_mul_eq_one_left h

private theorem e6a4_inv_zE_sq_mul_w_pow
    (s : ℕ) (hs : s < 3) :
    (zE ^ 2 * wOmegaE ^ s)⁻¹ = zE * wOmegaE ^ ((3 - s) % 3) := by
  have hs' : s = 0 ∨ s = 1 ∨ s = 2 := by omega
  rcases hs' with rfl | rfl | rfl
  · rw [show (3 - 0) % 3 = 0 by norm_num]
    simp [e6a4_zE_sq_eq_inv]
  · rw [show (3 - 1) % 3 = 2 by norm_num, pow_one, e6a4_zE_sq_eq_inv, mul_inv_rev,
      inv_inv, e6a4_wOmegaE_sq_eq_inv]
    exact (e6a4_commute_zE_wOmegaE.inv_right).eq.symm
  · rw [show (3 - 2) % 3 = 1 by norm_num, pow_one, e6a4_wOmegaE_sq_eq_inv,
      e6a4_zE_sq_eq_inv, mul_inv_rev, inv_inv]
    exact e6a4_commute_zE_wOmegaE.symm

private theorem e6a4_conj_zE_w_pow
    (s : ℕ) (hs : s < 3) :
    ∃ h ∈ Subgroup.normalizer (jE : Set EC) ⊓ Subgroup.normalizer (rE : Set EC),
      h * zE * h⁻¹ = zE * wOmegaE ^ s := by
  have hnj : cE ∈ Subgroup.normalizer (jE : Set EC) :=
    Subgroup.centralizer_le_normalizer _ cE_mem_centralizer_jE
  have hnr : cE ∈ Subgroup.normalizer (rE : Set EC) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le rE_le_jE cE_mem_centralizer_jE)
  interval_cases s
  · exact ⟨1, by simp, by simp⟩
  · exact ⟨cE, ⟨hnj, hnr⟩, by simpa using cE_conj_zE⟩
  · refine ⟨phiE * cE, ⟨mul_mem phiE_facts.2.2.1 hnj, mul_mem phiE_facts.2.2.2 hnr⟩, ?_⟩
    have hphi_z : phiE * zE * phiE⁻¹ = zE := by
      have hmem : zE ∈ Subgroup.centralizer (lE : Set EC) :=
        centralizer_zE.2.2 (Subgroup.mem_zpowers zE)
      have hc : phiE * zE = zE * phiE :=
        Subgroup.mem_centralizer_iff.mp hmem phiE phiE_facts.1
      rw [hc]; group
    calc (phiE * cE) * zE * (phiE * cE)⁻¹
        = phiE * (cE * zE * cE⁻¹) * phiE⁻¹ := by group
      _ = phiE * (zE * wOmegaE) * phiE⁻¹ := by rw [cE_conj_zE]
      _ = (phiE * zE * phiE⁻¹) * (phiE * wOmegaE * phiE⁻¹) := by group
      _ = zE * wOmegaE⁻¹ := by rw [hphi_z, phiE_facts.2.1]
      _ = zE * wOmegaE ^ (2 : ℕ) := by rw [e6a4_wOmegaE_sq_eq_inv]

theorem exists_conj_zE_of_mem_dE
    (g : EC) (hg : g ∈ dE) (hgw : g ∉ Subgroup.zpowers wOmegaE) :
    ∃ h ∈ Subgroup.normalizer (jE : Set EC) ⊓ Subgroup.normalizer (rE : Set EC),
      h * zE * h⁻¹ = g ∨ h * zE * h⁻¹ = g⁻¹ := by
  obtain ⟨i, j, hgij⟩ := e6a4_zpow_normal_form g hg
  have hzi : zE ^ i = zE ^ (i % 3) := zpow_eq_zpow_emod' i zE_pow_three
  have hwj : wOmegaE ^ j = wOmegaE ^ (j % 3) := zpow_eq_zpow_emod' j e6a4_wOmegaE_pow_three
  have hir : i % 3 ≠ 0 := by
    intro h0
    apply hgw
    have h1 : zE ^ i = 1 := by rw [hzi, h0, zpow_zero]
    rw [hgij, h1, one_mul]
    exact Subgroup.mem_zpowers_iff.mpr ⟨j, rfl⟩
  have hir_split : i % 3 = 1 ∨ i % 3 = 2 := by
    have h1 : 0 ≤ i % 3 := Int.emod_nonneg i (by norm_num)
    have h2 : i % 3 < 3 := Int.emod_lt_of_pos i (by norm_num)
    omega
  have hwj_nat : wOmegaE ^ (j % 3) = wOmegaE ^ ((j % 3).toNat) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg j (by norm_num))]
  have hgnf : g = zE ^ (i % 3) * wOmegaE ^ ((j % 3).toNat) := by
    rw [hgij, hzi, hwj, hwj_nat]
  have hsn_lt : (j % 3).toNat < 3 :=
    (Int.toNat_lt_of_ne_zero (by norm_num : (3 : ℕ) ≠ 0)).2
      (Int.emod_lt_of_pos j (by norm_num))
  rcases hir_split with hi1 | hi2
  · obtain ⟨h, hh, hconj⟩ := e6a4_conj_zE_w_pow ((j % 3).toNat) hsn_lt
    refine ⟨h, hh, Or.inl ?_⟩
    rw [hconj, hgnf, hi1, zpow_one]
  · have hsn'_lt : (3 - (j % 3).toNat) % 3 < 3 := Nat.mod_lt _ (by norm_num)
    obtain ⟨h, hh, hconj⟩ := e6a4_conj_zE_w_pow ((3 - (j % 3).toNat) % 3) hsn'_lt
    refine ⟨h, hh, Or.inr ?_⟩
    have hg2 : g = zE ^ 2 * wOmegaE ^ ((j % 3).toNat) := by
      simpa [hi2] using hgnf
    calc h * zE * h⁻¹ = zE * wOmegaE ^ ((3 - (j % 3).toNat) % 3) := hconj
      _ = (zE ^ 2 * wOmegaE ^ ((j % 3).toNat))⁻¹ :=
            (e6a4_inv_zE_sq_mul_w_pow ((j % 3).toNat) hsn_lt).symm
      _ = g⁻¹ := congrArg Inv.inv hg2.symm

end CFSG.StandardType.GGSixE6Two
