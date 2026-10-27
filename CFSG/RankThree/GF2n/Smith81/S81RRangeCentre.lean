module

public import CFSG.RankThree.GF2n.Smith81.S81NMask

open CFSG.RankThree.GF2n.Smith81.A5Cube

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

variable {K : Type*} [Field K]

open exteriorPower Matrix

private theorem m5p_rho_one : rho K (1 : GL (Fin 6) K) = 1 :=
  map_one (TauCeti.extPowerRep K 6 3)

private theorem m5p_rho_mul_apply (g h : GL (Fin 6) K) (ξ : Cube K) :
    rho K (g * h) ξ = rho K g (rho K h ξ) := by
  rw [rho, map_mul, Module.End.mul_apply]

private theorem m5p_rho_inv_cancel (c : GL (Fin 6) K) (η : Cube K) :
    rho K c⁻¹ (rho K c η) = η := by
  rw [← m5p_rho_mul_apply, inv_mul_cancel, m5p_rho_one, Module.End.one_apply]

private theorem m5p_rho_conj_apply (c x : GL (Fin 6) K) (η : Cube K) :
    rho K (c * x * c⁻¹) (rho K c η) = rho K c (rho K x η) := by
  rw [m5p_rho_mul_apply, m5p_rho_inv_cancel, m5p_rho_mul_apply]

private theorem m5p_rho_sub_one_conj (c x : GL (Fin 6) K) (η : Cube K) :
    rho K c ((rho K x - 1) η) = (rho K (c * x * c⁻¹) - 1) (rho K c η) := by
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, m5p_rho_conj_apply]

private theorem m5p_cfm_zero_of_range [CharP K 2] (i j : Fin 6) (hij : i ≠ j) (c : K)
    {η : Cube K} (hη : η ∈ LinearMap.range (rho K (transvGL K i j hij c) - 1))
    {m : ℕ} (hm : m < 64)
    (hsupp : ¬(m.testBit i.val = true ∧ m.testBit j.val = false)) :
    cfm K η m = 0 := by
  obtain ⟨ξ, rfl⟩ := LinearMap.mem_range.mp hη
  rw [LinearMap.sub_apply, Module.End.one_apply, cfm_sub,
    cfm_rho_transv i j hij c ξ m hm, if_neg hsupp]
  simp

private theorem m5p_three_masks : ∀ k : Fin 64, k.val.testBit 0 = true →
    k.val.testBit 1 = false → k.val.testBit 2 = false → (mset k.val).card = 3 →
    k.val = 25 ∨ k.val = 41 ∨ k.val = 49 := by
  decide +kernel

private theorem m5p_ι [CharP K 2] (a b c i j k : Fin 6) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hij : i < j) (hjk : j < k) (hI : ({i, j, k} : Finset (Fin 6)) = {a, b, c}) :
    ιMulti K 3 ![e K a, e K b, e K c] = ub K i j k hij hjk :=
  ι3_e_eq_cubeBasis hab hac hbc (tripleSet i j k hij.ne (hij.trans hjk).ne hjk.ne) hI

private theorem m5p_transvection_01 (α : K) :
    Matrix.transvection (0 : Fin 6) 1 α = 1 + vecMulVec (e K 0) (α • e K 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transvection, Matrix.single_apply, Matrix.one_apply, Matrix.vecMulVec, e,
      Pi.single_apply, Pi.smul_apply, smul_eq_mul]

private theorem m5p_transvection_02 (β : K) :
    Matrix.transvection (0 : Fin 6) 2 β = 1 + vecMulVec (e K 0) (β • e K 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transvection, Matrix.single_apply, Matrix.one_apply, Matrix.vecMulVec, e,
      Pi.single_apply, Pi.smul_apply, smul_eq_mul]

theorem pure_of_range_inf_range_std [CharP K 2] (α β : K) :
    ∀ ξ ∈ LinearMap.range (rho K (transvGL K 0 1 (by decide) α) - 1) ⊓
        LinearMap.range (rho K (transvGL K 0 2 (by decide) β) - 1), IsPure K ξ := by
  intro ξ hmem
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hmem
  have hzero : ∀ m : ℕ, m < 64 → m ≠ 25 → m ≠ 41 → m ≠ 49 → cfm K ξ m = 0 := by
    intro m hm h25 h41 h49
    by_cases hc : (mset m).card = 3
    · by_cases hA : m.testBit 0 = true ∧ m.testBit 1 = false
      · by_cases hB : m.testBit 0 = true ∧ m.testBit 2 = false
        · rcases m5p_three_masks ⟨m, hm⟩ hA.1 hA.2 hB.2 hc with h | h | h
          · exact absurd h h25
          · exact absurd h h41
          · exact absurd h h49
        · exact m5p_cfm_zero_of_range 0 2 (by decide) β h2 hm hB
      · exact m5p_cfm_zero_of_range 0 1 (by decide) α h1 hm hA
    · exact cf_of_card_ne _ hc
  have hdec : ξ = cfm K ξ 25 • ub K 0 3 4 (by decide) (by decide) +
      cfm K ξ 41 • ub K 0 3 5 (by decide) (by decide) +
      cfm K ξ 49 • ub K 0 4 5 (by decide) (by decide) := by
    refine cfm_ext fun m hm => ?_
    rw [cfm_add, cfm_add, cfm_smul, cfm_smul, cfm_smul,
      cfm_ub_mask 0 3 4 (by decide) (by decide) m hm,
      cfm_ub_mask 0 3 5 (by decide) (by decide) m hm,
      cfm_ub_mask 0 4 5 (by decide) (by decide) m hm]
    by_cases h25 : m = 25
    · subst h25; norm_num
    by_cases h41 : m = 41
    · subst h41; norm_num
    by_cases h49 : m = 49
    · subst h49; norm_num
    simp [hzero m hm h25 h41 h49, h25, h41, h49]
  obtain ⟨c1, c2, c3, hξ⟩ : ∃ c1 c2 c3 : K, ξ = c1 • ub K 0 3 4 (by decide) (by decide) +
      c2 • ub K 0 3 5 (by decide) (by decide) + c3 • ub K 0 4 5 (by decide) (by decide) :=
    ⟨_, _, _, hdec⟩
  have h034 : ιMulti K 3 ![e K 0, e K 3, e K 4] = ub K 0 3 4 (by decide) (by decide) :=
    m5p_ι 0 3 4 0 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h035 : ιMulti K 3 ![e K 0, e K 3, e K 5] = ub K 0 3 5 (by decide) (by decide) :=
    m5p_ι 0 3 5 0 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h045 : ιMulti K 3 ![e K 0, e K 4, e K 5] = ub K 0 4 5 (by decide) (by decide) :=
    m5p_ι 0 4 5 0 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h054 : ιMulti K 3 ![e K 0, e K 5, e K 4] = ub K 0 4 5 (by decide) (by decide) :=
    m5p_ι 0 5 4 0 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [hξ]
  by_cases hc1 : c1 = 0
  · refine ⟨![e K 0, c2 • e K 3 + c3 • e K 4, e K 5], ?_⟩
    rw [hc1, zero_smul, zero_add]
    simp only [ι3_add_snd, ι3_smul_snd]
    rw [h035, h045]
  · refine ⟨![e K 0, e K 3 + (c3 / c1) • e K 5, c1 • e K 4 + c2 • e K 5], ?_⟩
    simp only [ι3_add_snd, ι3_add_thd, ι3_smul_snd, ι3_smul_thd, ι3_eq_snd_thd, smul_zero,
      add_zero]
    rw [h034, h035, h054, smul_add, smul_smul, mul_div_cancel₀ c3 hc1]
    abel

theorem pure_of_range_inf_range_centre [CharP K 2] {x y : GL (Fin 6) K} {a f g : Fin 6 → K}
    (hxa : (x : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec a f)
    (hyb : (y : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec a g)
    (hframe : ∃ (c : Matrix (Fin 6) (Fin 6) K) (α β : K), c.det = 1 ∧ c *ᵥ a = e K 0 ∧
      f ᵥ* c⁻¹ = α • e K 1 ∧ g ᵥ* c⁻¹ = β • e K 2) :
    ∀ ξ ∈ LinearMap.range (rho K x - 1) ⊓ LinearMap.range (rho K y - 1), IsPure K ξ := by
  obtain ⟨c, α, β, hdet, hca, hf, hg⟩ := hframe
  obtain ⟨cG, hcG⟩ : ∃ cG : GL (Fin 6) K, (cG : Matrix (Fin 6) (Fin 6) K) = c :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero c (by rw [hdet]; exact one_ne_zero),
      Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _⟩
  have hcinv : ((cG⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = c⁻¹ := by
    rw [Matrix.coe_units_inv, hcG]
  have hcx : cG * x * cG⁻¹ = transvGL K 0 1 (by decide) α := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hxa, conj_one_add_vecMulVec, hcG, hcinv, hca, hf,
      transvGL_val, m5p_transvection_01]
  have hcy : cG * y * cG⁻¹ = transvGL K 0 2 (by decide) β := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hyb, conj_one_add_vecMulVec, hcG, hcinv, hca, hg,
      transvGL_val, m5p_transvection_02]
  intro ξ hmem
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hmem
  obtain ⟨η1, hη1⟩ := LinearMap.mem_range.mp h1
  obtain ⟨η2, hη2⟩ := LinearMap.mem_range.mp h2
  have hT1 : rho K cG ξ ∈ LinearMap.range (rho K (transvGL K 0 1 (by decide) α) - 1) := by
    refine LinearMap.mem_range.mpr ⟨rho K cG η1, ?_⟩
    rw [← hcx, ← m5p_rho_sub_one_conj, hη1]
  have hT2 : rho K cG ξ ∈ LinearMap.range (rho K (transvGL K 0 2 (by decide) β) - 1) := by
    refine LinearMap.mem_range.mpr ⟨rho K cG η2, ?_⟩
    rw [← hcy, ← m5p_rho_sub_one_conj, hη2]
  have hp := pure_of_range_inf_range_std α β (rho K cG ξ) (Submodule.mem_inf.mpr ⟨hT1, hT2⟩)
  have hq := hp.rho cG⁻¹
  rwa [m5p_rho_inv_cancel] at hq

end CFSG.RankThree.GF2n.Smith81.A5Cube
