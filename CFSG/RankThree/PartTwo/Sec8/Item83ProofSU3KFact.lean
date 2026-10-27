module

public import CFSG.RankThree.PartTwo.Sec8.Item83ProofDefs
public import CFSG.RankThree.PartTwo.KFacts.K71SU3AutFacts
public import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item83Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank (StatedSU)
open CFSG.Assembly.RankThreeEven (projSL)
open Matrix

section Swap

variable {K : Type} [Field K]

@[expose] def swap02 (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem swap02_mul_self : swap02 K * swap02 K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swap02, Matrix.mul_apply, Fin.sum_univ_three]

theorem swap02_mul_diagonal_mul_swap02 (a b : K) :
    swap02 K * diagonal ![a, b, b] * swap02 K = diagonal ![b, b, a] := by
  have h1 : ∀ x y z : K, diagonal ![x, y, z] = !![x, 0, 0; 0, y, 0; 0, 0, z] := by
    intro x y z
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [h1, h1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swap02, Matrix.mul_apply, Fin.sum_univ_three]

theorem conjTr_swap02 (σ : K ≃+* K) : conjTr σ (swap02 K) = swap02 K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swap02, conjTr]

end Swap

theorem map_centralizer_singleton {M : Type*} [Group M] (φ : MulAut M) (x : M) :
    (Subgroup.centralizer ({x} : Set M)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ x} : Set M) := by
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hz
    change φ z * φ x = φ x * φ z
    rw [← map_mul, ← map_mul, hz]
  · intro hy
    refine ⟨φ⁻¹ y, ?_, MulAut.apply_inv_self _ _ _⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    apply φ.injective
    rw [map_mul, map_mul, MulAut.apply_inv_self]
    exact hy

theorem kF83SUThree : KF83SUThree := by
  intro K _ _ n hn hK g hg3c hg3
  classical
  have hn1 : 1 ≤ n := hn.pos
  have h3n : Odd (3 * n) := Odd.mul (by decide) hn
  have hPi : PiField false 2 (3 * n) K := ⟨Nat.prime_two, by omega, hK⟩
  have hmod : ModThree false (2 ^ (3 * n)) := by
    have := three_dvd_two_pow_three_mul_add_one hn
    change 2 ^ (3 * n) % 3 = 2
    omega
  have := hPi.finite
  have : CharP K 2 := hPi.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h3 : (3 : K) ≠ 0 := by
    rw [show (3 : K) = 1 by linear_combination h2]
    exact one_ne_zero
  set hU := hPi.unitary
  set σ := CFSG.LieType.BorelTits.unitaryInvolution K 2 (3 * n)
  have hσ : IsUnitaryInvolution σ :=
    isUnitaryInvolution_unitaryInvolution (by rw [hPi.card]; rfl)
  have hq2 : 2 < 2 ^ (3 * n) := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq4 : 4 ≤ 2 ^ (3 * n) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨c₀, hc₀3, hgc₀⟩ := exists_scalar_of_conj_eq_one hU hq2 (z := g ^ 3) (by
    ext y
    rw [MulAut.conj_apply, MulAut.one_apply, (Subgroup.mem_center_iff.mp hg3c y).symm,
      mul_inv_cancel_right])
  have hc₀1 : c₀ ≠ 1 := by
    rintro rfl
    apply hg3
    apply Subtype.ext
    rw [hgc₀, map_one]
    rfl
  have hKc : Nat.card K = ((2 ^ n) ^ 3) ^ 2 := by rw [hK, ← pow_mul 2 n 3, mul_comm n 3]
  have hc₀q : c₀⁻¹ ^ (2 ^ n + 1) = 1 := by
    obtain ⟨k, hk⟩ : 3 ∣ 2 ^ n + 1 := by simpa using Odd.nat_add_dvd_pow_add_pow 2 1 hn
    rw [hk, inv_pow, pow_mul, hc₀3, one_pow, inv_one]
  obtain ⟨μ, hμq, hμ3⟩ := exists_cube_root_normOne hKc hc₀q
  have hQ3 : (2 ^ n) ^ 3 = 2 ^ (3 * n) := by rw [← pow_mul, mul_comm]
  rw [hQ3] at hμq
  obtain ⟨Gm, hGm⟩ : ∃ Gm : Matrix (Fin 3) (Fin 3) K,
      Gm = ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := ⟨_, rfl⟩
  have hGm3 : Gm ^ 3 = (c₀ : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    have h1 : (((g ^ 3 : StatedSU 3 (2 ^ (3 * n)) K) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = (c₀ : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      rw [hgc₀]
      simp [Matrix.smul_one_eq_diagonal]
    rw [← h1, hGm]
    simp
  have hdetG : Gm.det = 1 := by
    rw [hGm]
    exact ((mem_slPi_false hU).1 g.2).1
  have hGu : conjTr σ Gm * Gm = 1 := by
    rw [conjTr_unitaryInvolution_eq hPi, hGm]
    exact ((mem_slPi_false hU).1 g.2).2
  have hμ0 : (μ : K) ≠ 0 := μ.ne_zero
  have hμ3' : (μ : K) ^ 3 * (c₀ : K) = 1 := by
    rw [← Units.val_pow_eq_pow_val, hμ3, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hc₀1' : (c₀ : K) ≠ 1 := fun h1 => hc₀1 (Units.ext h1)
  have hμ3c : (μ : K) ^ 3 ≠ 1 := by
    intro h1
    rw [h1, one_mul] at hμ3'
    exact hc₀1' hμ3'
  have hv3 : ((μ : K) • Gm) ^ 3 = 1 := by
    rw [smul_pow, hGm3, smul_smul, hμ3', one_smul]
  have hvs : ∀ c : K, (μ : K) • Gm ≠ c • 1 := by
    intro c hc
    have hG : Gm = ((μ : K)⁻¹ * c) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      rw [← smul_smul, ← hc, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
    have hdet : ((μ : K)⁻¹ * c) ^ 3 = 1 := by
      have h1 := hdetG
      rw [hG, det_smul, det_one, mul_one, Fintype.card_fin] at h1
      exact h1
    apply hc₀1'
    have h1 := hGm3
    rw [hG, smul_pow, one_pow, hdet, one_smul] at h1
    have h2 := congrFun (congrFun h1 0) 0
    simpa using h2.symm
  obtain ⟨τ, hτ3, hτ1⟩ := exists_primitive_cube_root hPi
  have hτ0 : τ ≠ 0 := fun h0 => by rw [h0] at hτ3; norm_num at hτ3
  obtain ⟨P, j, hP, hform⟩ := exists_normal_form hτ3 hτ1 h3 hv3 hvs
  have hPdet : P.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det P).mp hP).ne_zero
  have hdetD : ∀ {D : Matrix (Fin 3) (Fin 3) K},
      (τ ^ (j : ℕ) • (μ : K) • Gm) * P = P * D → D.det = (μ : K) ^ 3 := by
    intro D hD
    have h1 := congrArg Matrix.det hD
    rw [det_mul, det_mul, det_smul, det_smul, hdetG, Fintype.card_fin, mul_one, ← pow_mul,
      mul_comm (j : ℕ) 3, pow_mul, hτ3, one_pow, one_mul] at h1
    exact mul_left_cancel₀ hPdet (h1.symm.trans (mul_comm _ _))
  obtain ⟨ρ, hρ3, hρ1, hD⟩ : ∃ ρ : K, ρ ^ 3 = 1 ∧ ρ ≠ 1 ∧
      (τ ^ (j : ℕ) • (μ : K) • Gm) * P = P * diagonal ![ρ, 1, 1] := by
    rcases hform with hD | hD | hD
    · exfalso
      have h1 := hdetD hD
      rw [det_diagonal, Fin.prod_univ_three] at h1
      change τ * τ ^ 2 * 1 = (μ : K) ^ 3 at h1
      apply hμ3c
      rw [← h1, mul_one, ← pow_succ', hτ3]
    · exact ⟨τ, hτ3, hτ1, hD⟩
    · refine ⟨τ ^ 2, by rw [← pow_mul, mul_comm, pow_mul, hτ3, one_pow], fun h1 => hτ1 ?_, hD⟩
      calc τ = τ ^ 2 * τ := by rw [h1, one_mul]
        _ = τ ^ 3 := by ring
        _ = 1 := hτ3
  have hτn : σ τ * τ = 1 := by
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← pow_succ]
    exact pow_succ_eq_one_of_modThree hmod hτ3
  have hρn : σ ρ * ρ = 1 := by
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← pow_succ]
    exact pow_succ_eq_one_of_modThree hmod hρ3
  have hμn : σ (μ : K) * (μ : K) = 1 := by
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← pow_succ, ← Units.val_pow_eq_pow_val,
      hμq, Units.val_one]
  have hconjTr_smul : ∀ (c : K) (M : Matrix (Fin 3) (Fin 3) K),
      conjTr σ (c • M) = σ c • conjTr σ M := by
    intro c M
    ext i k
    simp [conjTr]
  have hyu : conjTr σ (τ ^ (j : ℕ) • (μ : K) • Gm) * (τ ^ (j : ℕ) • (μ : K) • Gm) = 1 := by
    rw [hconjTr_smul, hconjTr_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_smul, hGu, smul_smul, smul_smul, smul_smul, map_pow,
      show σ τ ^ (j : ℕ) * σ (μ : K) * τ ^ (j : ℕ) * (μ : K) =
        (σ τ * τ) ^ (j : ℕ) * (σ (μ : K) * (μ : K)) by ring, hτn, hμn, one_pow, one_mul,
      one_smul]
  have hd : ∀ i, σ (![ρ, 1, 1] i) * ![ρ, 1, 1] i = 1 := by
    intro i
    fin_cases i
    · exact hρn
    · simp
    · simp
  have hdd : (![ρ, 1, 1] 0 ≠ ![ρ, 1, 1] 1 ∧ ![ρ, 1, 1] 0 ≠ ![ρ, 1, 1] 2 ∧
      ![ρ, 1, 1] 1 ≠ ![ρ, 1, 1] 2) ∨ (![ρ, 1, 1] 0 ≠ ![ρ, (1 : K), 1] 1 ∧
      ![ρ, 1, 1] 1 = ![ρ, (1 : K), 1] 2) := Or.inr ⟨hρ1, rfl⟩
  obtain ⟨P', hP'u, hyP'⟩ := exists_unitary_conj hσ hd hdd hyu hP hD
  have hτμ0 : τ ^ (j : ℕ) * (μ : K) ≠ 0 := mul_ne_zero (pow_ne_zero _ hτ0) hμ0
  obtain ⟨κ, hκ⟩ : ∃ κ : K, κ = (τ ^ (j : ℕ) * (μ : K))⁻¹ := ⟨_, rfl⟩
  have hκ0 : κ ≠ 0 := by rw [hκ]; exact inv_ne_zero hτμ0
  have hGy : Gm = κ • τ ^ (j : ℕ) • (μ : K) • Gm := by
    rw [smul_smul, smul_smul, mul_assoc, hκ, inv_mul_cancel₀ hτμ0, one_smul]
  have hGP' : Gm * P' = P' * diagonal ![κ * ρ, κ, κ] := by
    rw [hGy, Matrix.smul_mul, hyP', ← Matrix.mul_smul, ← diagonal_smul]
    congr 2
    ext i
    fin_cases i <;> simp
  have hGQ : Gm * (P' * swap02 K) = (P' * swap02 K) * diagonal ![κ, κ, κ * ρ] := by
    rw [← swap02_mul_diagonal_mul_swap02 (κ * ρ) κ, ← Matrix.mul_assoc, hGP']
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (swap02 K) (swap02 K), swap02_mul_self, Matrix.one_mul]
  have hQu : conjTr σ (P' * swap02 K) * (P' * swap02 K) = 1 := by
    rw [conjTr_mul, conjTr_swap02, Matrix.mul_assoc, ← Matrix.mul_assoc (conjTr σ P'), hP'u,
      Matrix.one_mul, swap02_mul_self]
  have hQunit : IsUnit (P' * swap02 K) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hQu)
  have hQiso : hQunit.unit ∈ unitaryIsom3 hU := by
    rw [mem_unitaryIsom3, IsUnit.unit_spec, ← conjTr_unitaryInvolution_eq hPi]
    exact hQu
  set φ : MulAut (StatedSU 3 (2 ^ (3 * n)) K) :=
    suConj hU (⟨hQunit.unit, hQiso⟩ : unitaryIsom3 hU)⁻¹ with hφ
  have hinv : ((hQunit.unit⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (P' * swap02 K) =
      1 := by
    have h1 := Units.inv_mul hQunit.unit
    rwa [IsUnit.unit_spec] at h1
  have ht : (((φ g : StatedSU 3 (2 ^ (3 * n)) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![κ, κ, κ * ρ] := by
    rw [hφ, coe_suConj, inv_inv]
    change ((hQunit.unit⁻¹ * (g : GL (Fin 3) K) * hQunit.unit : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = _
    rw [Units.val_mul, Units.val_mul, ← hGm, IsUnit.unit_spec, Matrix.mul_assoc, hGQ,
      ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  have hlm : κ ≠ κ * ρ := fun h1 => hρ1 (mul_left_cancel₀ hκ0 (by rw [mul_one]; exact h1.symm))
  obtain ⟨F₀, _, _, hF₀, ⟨ι⟩⟩ := exists_perfectResidual_suCentralizer_mulEquiv hU hq4 hlm ht
  obtain ⟨ι'⟩ := nonempty_sl2_mulEquiv_projSL hF₀
  have hC : Subgroup.centralizer ({φ g} : Set (StatedSU 3 (2 ^ (3 * n)) K)) =
      suCentralizer (2 ^ (3 * n)) ((φ g : StatedSU 3 (2 ^ (3 * n)) K) : GL (Fin 3) K) := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff, mem_suCentralizer]
    exact ⟨fun h1 => congrArg Subtype.val h1, fun h1 => Subtype.ext h1⟩
  have hmap : (inSubgroup perfectResidual (Subgroup.centralizer
      ({g} : Set (StatedSU 3 (2 ^ (3 * n)) K)))).map φ.toMonoidHom =
      inSubgroup perfectResidual
        (suCentralizer (2 ^ (3 * n)) ((φ g : StatedSU 3 (2 ^ (3 * n)) K) : GL (Fin 3) K)) := by
    rw [map_inSubgroup_perfectResidual, map_centralizer_singleton, hC]
  exact ⟨((inSubgroup perfectResidual (Subgroup.centralizer
    ({g} : Set (StatedSU 3 (2 ^ (3 * n)) K)))).equivMapOfInjective φ.toMonoidHom
      φ.injective).trans ((MulEquiv.subgroupCongr hmap).trans (ι.trans ι'))⟩

end CFSG.RankThree.PartTwo.Sec8.Item83Proof
