module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestDefs
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestBasic
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoComponent
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoCent
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoJEq
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveCentralizes

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal.SpecialLinear

private theorem e6cd_omegaBlock_eq_transvections (n : ℕ) (k : Fin n) :
    omegaBlock n k =
      Matrix.SpecialLinearGroup.transvection
          ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne) (1 : F2) *
        Matrix.SpecialLinearGroup.transvection
          (((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm) (1 : F2) := by
  rw [omegaBlock, CFSG.LieType.Universal.SpecialLinear.weylRep]
  have hneg : (-1 : F2) = 1 := by rw [CharTwo.neg_eq]
  rw [hneg]
  set x : Matrix.SpecialLinearGroup (Fin (n + 1)) F2 :=
    Matrix.SpecialLinearGroup.transvection
      ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne) (1 : F2)
  set y : Matrix.SpecialLinearGroup (Fin (n + 1)) F2 :=
    Matrix.SpecialLinearGroup.transvection
      (((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm) (1 : F2)
  have hxx : x * x = 1 := by
    have h := Matrix.SpecialLinearGroup.transvection_mul_neg
      (hij := (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne) (b := (1 : F2))
    rw [hneg] at h
    exact h
  calc x * y * x * x = x * y * (x * x) := by group
    _ = x * y := by rw [hxx, mul_one]

private theorem e6cd_exists_mul_of_mem_sup {G : Type*} [Group G] {H K : Subgroup G}
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

private theorem e6cd_zeta5_eq_omegaBlocks :
    zeta5 = omegaBlock 5 0 * omegaBlock 5 2 * omegaBlock 5 4 := rfl

private theorem e6cd_wOmegaE_eq :
    wOmegaE = E6Pilot.slToAdjointE6 F2 zeta5 := by
  have hz0 : (Fin.castSucc (0 : Fin 5) : Fin 6) = blk 0 0 := by
    apply Fin.ext; simp [blk, Fin.castSucc]
  have hz1 : (Fin.succ (0 : Fin 5) : Fin 6) = blk 0 1 := by
    apply Fin.ext; simp [blk, Fin.succ]
  have hz0' : (Fin.castSucc (2 : Fin 5) : Fin 6) = blk 1 0 := by
    apply Fin.ext; simp [blk, Fin.castSucc]
  have hz1' : (Fin.succ (2 : Fin 5) : Fin 6) = blk 1 1 := by
    apply Fin.ext; simp [blk, Fin.succ]
  have hz0'' : (Fin.castSucc (4 : Fin 5) : Fin 6) = blk 2 0 := by
    apply Fin.ext; simp [blk, Fin.castSucc]
  have hz1'' : (Fin.succ (4 : Fin 5) : Fin 6) = blk 2 1 := by
    apply Fin.ext; simp [blk, Fin.succ]
  have h0 : cOmegaE 0 = E6Pilot.slToAdjointE6 F2 (omegaBlock 5 0) := by
    rw [cOmegaE, e6cd_omegaBlock_eq_transvections, map_mul,
      E6Pilot.slToAdjointE6_transvection, E6Pilot.slToAdjointE6_transvection, hz0, hz1]
    rfl
  have h1 : cOmegaE 1 = E6Pilot.slToAdjointE6 F2 (omegaBlock 5 2) := by
    rw [cOmegaE, e6cd_omegaBlock_eq_transvections, map_mul,
      E6Pilot.slToAdjointE6_transvection, E6Pilot.slToAdjointE6_transvection, hz0', hz1']
    rfl
  have h2 : cOmegaE 2 = E6Pilot.slToAdjointE6 F2 (omegaBlock 5 4) := by
    rw [cOmegaE, e6cd_omegaBlock_eq_transvections, map_mul,
      E6Pilot.slToAdjointE6_transvection, E6Pilot.slToAdjointE6_transvection, hz0'', hz1'']
    rfl
  rw [wOmegaE, h0, h1, h2, ← map_mul, ← map_mul, e6cd_zeta5_eq_omegaBlocks]

private theorem e6cd_omegaScalar_coe :
    (omegaScalar : Matrix (Fin 3) (Fin 3) F4) = Matrix.scalar (Fin 3) f4Omega := by
  rw [omegaScalar, Units.coe_map]
  rfl

private theorem e6cd_omegaScalar_eq_scalar :
    omegaScalar = Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 f4Omega f4Omega_ne_zero) := by
  rw [omegaScalar, Matrix.GeneralLinearGroup.scalar]

private theorem e6cd_zeta5_mem_sl3four : zeta5 ∈ sl3four := by
  rw [zeta5_eq, sl3four, resSL, MonoidHom.range_comp]
  refine Subgroup.mem_map.mpr ⟨omegaScalar, ?_, rfl⟩
  rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
  change Matrix.GeneralLinearGroup.det omegaScalar = 1
  rw [e6cd_omegaScalar_eq_scalar, Matrix.GeneralLinearGroup.det_scalar]
  ext
  simp [Units.val_mk0, f4Omega_pow_three]

private theorem e6cd_scalar_of_commute_transvections
    {A : Matrix (Fin 3) (Fin 3) F4}
    (h : ∀ i j : Fin 3, i ≠ j → A * (1 + Matrix.single i j (1 : F4)) =
      (1 + Matrix.single i j (1 : F4)) * A) :
    ∃ a : F4, A = Matrix.scalar (Fin 3) a := by
  have hmul : ∀ i j : Fin 3, i ≠ j →
      A * Matrix.single i j (1 : F4) = Matrix.single i j (1 : F4) * A := by
    intro i j hij
    have hh := h i j hij
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul] at hh
    exact add_left_cancel hh
  have key : ∀ i j : Fin 3, i ≠ j → A i i = A j j ∧ (∀ k, k ≠ i → A k i = 0) := by
    intro i j hij
    have h' := hmul i j hij
    constructor
    · have hL : (A * Matrix.single i j (1 : F4)) i j = A i i := by
        rw [Matrix.mul_apply, Finset.sum_eq_single i]
        · simp [Matrix.single_apply]
        · intro m _ hm; simp [Matrix.single_apply, hm, Ne.symm hm]
        · intro hi; exact absurd (Finset.mem_univ i) hi
      have hR : (Matrix.single i j (1 : F4) * A) i j = A j j := by
        rw [Matrix.mul_apply, Finset.sum_eq_single j]
        · simp [Matrix.single_apply]
        · intro m _ hm; simp [Matrix.single_apply, hm, Ne.symm hm]
        · intro hj; exact absurd (Finset.mem_univ j) hj
      have := congr_fun (congr_fun h' i) j
      rwa [hL, hR] at this
    · intro k hk
      have hL : (A * Matrix.single i j (1 : F4)) k j = A k i := by
        rw [Matrix.mul_apply, Finset.sum_eq_single i]
        · simp [Matrix.single_apply]
        · intro m _ hm; simp [Matrix.single_apply, hm, Ne.symm hm]
        · intro hi; exact absurd (Finset.mem_univ i) hi
      have hR : (Matrix.single i j (1 : F4) * A) k j = 0 := by
        rw [Matrix.mul_apply]
        apply Finset.sum_eq_zero
        intro m _
        have : Matrix.single i j (1 : F4) k m = 0 := by
          simp [Matrix.single_apply, hk, Ne.symm hk]
        rw [this, zero_mul]
      have := congr_fun (congr_fun h' k) j
      rwa [hL, hR] at this
  have hd : A 0 0 = A 1 1 := (key 0 1 (by decide)).1
  have hd' : A 1 1 = A 2 2 := (key 1 2 (by decide)).1
  have hz10 : A 1 0 = 0 := (key 0 1 (by decide)).2 1 (by decide)
  have hz20 : A 2 0 = 0 := (key 0 1 (by decide)).2 2 (by decide)
  have hz01 : A 0 1 = 0 := (key 1 2 (by decide)).2 0 (by decide)
  have hz21 : A 2 1 = 0 := (key 1 2 (by decide)).2 2 (by decide)
  have hz02 : A 0 2 = 0 := (key 2 0 (by decide)).2 0 (by decide)
  have hz12 : A 1 2 = 0 := (key 2 0 (by decide)).2 1 (by decide)
  refine ⟨A 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, hd, hd', hz10, hz20, hz01, hz21,
      hz02, hz12]

private theorem e6cd_commutant_sl3four (M : Matrix.SpecialLinearGroup (Fin 6) F2)
    (hM : ∀ s ∈ sl3four, M * s = s * M) : M ∈ Subgroup.zpowers zeta5 := by
  have hz : M * zeta5 = zeta5 * M := hM zeta5 e6cd_zeta5_mem_sl3four
  have hMrange : M ∈ (resGL 3).range := by
    rw [← centralizer_zeta5, Subgroup.mem_centralizer_singleton_iff]
    exact hz
  obtain ⟨g, rfl⟩ := hMrange
  have hAc : ∀ i j : Fin 3, i ≠ j →
      (g : Matrix (Fin 3) (Fin 3) F4) * (1 + Matrix.single i j (1 : F4)) =
      (1 + Matrix.single i j (1 : F4)) * (g : Matrix (Fin 3) (Fin 3) F4) := by
    intro i j hij
    have hs : resSL 3 (Matrix.SpecialLinearGroup.transvection hij (1 : F4)) ∈ sl3four :=
      ⟨_, rfl⟩
    have hh := hM _ hs
    apply resMat_injective 3
    have hh' := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 6) F2 =>
      (z : Matrix (Fin 6) (Fin 6) F2)) hh
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_resGL, coe_resSL,
      Matrix.SpecialLinearGroup.transvection_coe] at hh'
    rwa [← map_mul, ← map_mul] at hh'
  obtain ⟨a, ha⟩ := e6cd_scalar_of_commute_transvections hAc
  have ha_ne : a ≠ 0 := by
    intro h0
    have hg0 : (g : Matrix (Fin 3) (Fin 3) F4) = 0 := by
      rw [ha, h0, Matrix.scalar_apply, Matrix.diagonal_zero]
    have h1 : (1 : Matrix (Fin 3) (Fin 3) F4) = 0 := by
      calc (1 : Matrix (Fin 3) (Fin 3) F4) =
            (g : Matrix (Fin 3) (Fin 3) F4) * ↑g⁻¹ := by rw [Units.mul_inv]
        _ = 0 := by rw [hg0, zero_mul]
    exact one_ne_zero h1
  obtain ⟨k, hk⟩ : ∃ k : ℕ, a = f4Omega ^ k := by
    rcases f4_cases a with h0 | h1 | hω | hω2
    · exact absurd h0 ha_ne
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [hω, pow_one]⟩
    · exact ⟨2, by rw [hω2]⟩
  have hg_eq : g = omegaScalar ^ k := by
    apply Units.ext
    rw [ha, hk, Units.val_pow_eq_pow_val, e6cd_omegaScalar_coe]
    exact map_pow (Matrix.scalar (Fin 3)) f4Omega k
  refine Subgroup.mem_zpowers_iff.mpr ⟨(k : ℤ), ?_⟩
  rw [zpow_natCast, hg_eq, map_pow, ← zeta5_eq]

private theorem e6cd_zeta5_ne_one : zeta5 ≠ 1 := by
  intro h
  have hω1 : f4Omega ≠ 1 := by
    intro h1
    have h2 : (1 : F4) = 0 := by
      have hh := f4Omega_sq
      rw [h1] at hh
      simpa [CharTwo.add_self_eq_zero] using hh
    exact one_ne_zero h2
  have homega_ne : omegaScalar ≠ 1 := by
    intro h1
    apply hω1
    have hval := congrArg
      (fun u : Matrix.GeneralLinearGroup (Fin 3) F4 => (u : Matrix (Fin 3) (Fin 3) F4) 0 0) h1
    simpa [e6cd_omegaScalar_coe, Matrix.scalar_apply, Matrix.one_apply] using hval
  apply homega_ne
  apply resGL_injective 3
  rw [← zeta5_eq]
  simpa using h

private theorem e6cd_wOmegaE_mem_lE :
    wOmegaE ∈ lE := by
  rw [e6cd_wOmegaE_eq, lE, ← E6Pilot.range_slToAdjointE6]
  exact ⟨zeta5, rfl⟩

private theorem e6cd_wOmegaE_mem_centralizer_jE :
    wOmegaE ∈ Subgroup.centralizer (jE : Set EC) := by
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  rw [e6cd_wOmegaE_eq]
  rw [jE_eq] at hj
  obtain ⟨s, hs, rfl⟩ := hj
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subgroup.mem_centralizer_singleton_iff.mp (sl3four_le_centralizer hs)

private theorem e6cd_mem_zpowers_wOmegaE_of_mem_inf
    {l : EC}
    (hl : l ∈ lE ⊓ Subgroup.centralizer (jE : Set EC)) :
    l ∈ Subgroup.zpowers wOmegaE := by
  obtain ⟨hlL, hlc⟩ := hl
  rw [lE, ← E6Pilot.range_slToAdjointE6] at hlL
  obtain ⟨M, rfl⟩ := hlL
  have hM : ∀ s ∈ sl3four, M * s = s * M := by
    intro s hs
    have hs' : E6Pilot.slToAdjointE6 F2 s ∈ jE := by
      rw [jE_eq]
      exact Subgroup.mem_map_of_mem (E6Pilot.slToAdjointE6 F2) hs
    exact iota_injective (by
      rw [map_mul, map_mul]
      exact ((Subgroup.mem_centralizer_iff.mp hlc) _ hs').symm)
  have hMz : M ∈ Subgroup.zpowers zeta5 := e6cd_commutant_sl3four M hM
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hMz
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨k, ?_⟩
  rw [e6cd_wOmegaE_eq, ← map_zpow, hk]

private theorem e6cd_zE_mem_centralizer_jE :
    zE ∈ Subgroup.centralizer (jE : Set EC) := by
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  exact (Subgroup.mem_centralizer_iff.mp
    (centralizer_zE.2.2 (Subgroup.mem_zpowers zE))) j (jE_le_lE hj)

private theorem e6cd_wOmegaE_mem_centralizer_zE :
    wOmegaE ∈ Subgroup.centralizer ({zE} : Set EC) := by
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    ((Subgroup.mem_centralizer_iff.mp
      (centralizer_zE.2.2 (Subgroup.mem_zpowers zE))) wOmegaE e6cd_wOmegaE_mem_lE)

private theorem e6cd_omegaScalar_pow_three : omegaScalar ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, e6cd_omegaScalar_coe, ← map_pow, f4Omega_pow_three, map_one,
    Units.val_one]

private theorem e6cd_zeta5_pow_three : zeta5 ^ 3 = 1 := by
  rw [zeta5_eq, ← map_pow, e6cd_omegaScalar_pow_three, map_one]

theorem orderOf_wOmegaE :
    orderOf wOmegaE = 3 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [e6cd_wOmegaE_eq, ← map_pow, e6cd_zeta5_pow_three, map_one]
  · intro h
    apply e6cd_zeta5_ne_one
    have h' : E6Pilot.slToAdjointE6 F2 zeta5 = 1 := by
      rw [← e6cd_wOmegaE_eq]; exact h
    exact iota_injective (by rw [h', map_one])

theorem centralizer_zE_inf_centralizer_jE :
    Subgroup.centralizer ({zE} : Set EC) ⊓ Subgroup.centralizer (jE : Set EC) = dE := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgz, hgj⟩ := hg
    have hg' : g ∈ Subgroup.zpowers zE ⊔ lE := by
      rw [← centralizer_zE.1]; exact hgz
    have hcomm : ∀ h ∈ Subgroup.zpowers zE, ∀ k ∈ lE, h * k = k * h := by
      intro h hh k hk
      exact ((Subgroup.mem_centralizer_iff.mp (centralizer_zE.2.2 hh)) k hk).symm
    obtain ⟨a, ha, b, hb, hab⟩ := e6cd_exists_mul_of_mem_sup hcomm hg'
    have ha_cent : a ∈ Subgroup.centralizer (jE : Set EC) :=
      Subgroup.zpowers_le.mpr e6cd_zE_mem_centralizer_jE ha
    have hb_inf : b ∈ lE ⊓ Subgroup.centralizer (jE : Set EC) := by
      refine ⟨hb, ?_⟩
      have hb_eq : b = a⁻¹ * g := by rw [← hab]; group
      have hinv : a⁻¹ ∈ Subgroup.centralizer (jE : Set EC) := inv_mem ha_cent
      have hmul : a⁻¹ * g ∈ Subgroup.centralizer (jE : Set EC) := mul_mem hinv hgj
      rw [hb_eq]
      exact hmul
    have hbz : b ∈ Subgroup.zpowers wOmegaE := e6cd_mem_zpowers_wOmegaE_of_mem_inf hb_inf
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbz
    have hz_d : zE ∈ dE := Subgroup.subset_closure (by simp)
    have hw_d : wOmegaE ∈ dE := Subgroup.subset_closure (by simp)
    have ha_d : a ∈ dE := by rw [← hi]; exact Subgroup.zpow_mem dE hz_d i
    have hb_d : b ∈ dE := by rw [← hk]; exact Subgroup.zpow_mem dE hw_d k
    rw [← hab]
    exact dE.mul_mem ha_d hb_d
  · rw [dE, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, e6cd_zE_mem_centralizer_jE⟩
    · exact ⟨e6cd_wOmegaE_mem_centralizer_zE, e6cd_wOmegaE_mem_centralizer_jE⟩

end CFSG.StandardType.GGSixE6Two
