module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U34Unitary
public import CFSG.Quasithin.Background.HSU3
public import CFSG.Quasithin.Background.HStandardScalars
public import CFSG.Quasithin.Background.A3FactsClassical
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.LinearAlgebra.MatrixPlanes
public import CFSG.ClassicalGroups.Unitary.StatedSUFieldAut
public import CFSG.GroupTheory.SupCommute
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.InvolutionPair
public import CFSG.GroupTheory.PRankBound
public import CFSG.GroupTheory.PRankZeroOfPrimeNotDvd
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.SU3
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.Unitary
open scoped Matrix

variable {K : Type} [Field K]

theorem statedScalars_subgroupOf_statedSU_three_four_eq_bot (hK : Nat.card K = 16) :
    (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 4 K) = ⊥ := by
  have h := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two
    (by rw [hK]; norm_num : Nat.card K = (2 ^ 2) ^ 2) (n := 3) (by norm_num)).2.2
  exact Subgroup.card_eq_one.mp (by simpa using h)

noncomputable def statedProjStatedSUEquiv (hK : Nat.card K = 16) :
    StatedProj (StatedSU 3 4 K) ≃* StatedSU 3 4 K :=
  (QuotientGroup.quotientMulEquivOfEq
    (statedScalars_subgroupOf_statedSU_three_four_eq_bot hK)).trans QuotientGroup.quotientBot

theorem card_statedSU_three_four (hK : Nat.card K = 16) :
    Nat.card (StatedSU 3 4 K) = 62400 := by
  rw [← Nat.card_congr (statedProjStatedSUEquiv hK).toEquiv]
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (p := 2) (f := 2)
    (n := 3) Nat.prime_two (by norm_num) (by rw [hK]; norm_num) (by norm_num)
  norm_num at h
  exact h

abbrev natScalImage (K : Type) [Field K] : Subgroup (MulAut (StdMod (Fin 3) K)) :=
  natImage (StatedScalars (Fin 3) K)

theorem card_natScalImage (hK : Nat.card K = 16) :
    Nat.card (natScalImage K) = 15 := by
  rw [natScalImage, natImage_eq_map, Subgroup.card_map_of_injective matHom_injective]
  show Nat.card (StatedScalars (Fin 3) K) = 15
  rw [StatedScalars, ← Nat.card_congr (MonoidHom.ofInjective
    (CFSG.LinearAlgebra.generalLinearGroup_scalar_injective (ι := Fin 3) (R := K))).toEquiv,
    Nat.card_units, hK]

theorem card_natImage_statedSU_three_four (hK : Nat.card K = 16) :
    Nat.card (natImage (StatedSU 3 4 K)) = 62400 := by
  rw [natImage_eq_map, Subgroup.card_map_of_injective matHom_injective]
  exact card_statedSU_three_four hK

theorem natScalImage_inf_natImage_statedSU (hK : Nat.card K = 16) :
    natScalImage K ⊓ natImage (StatedSU 3 4 K) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hg1, hg2⟩
  rw [Subgroup.mem_bot]
  obtain ⟨γ, hγg⟩ := hg1
  obtain ⟨A, hA⟩ := γ
  obtain ⟨δ, hδg⟩ := hg2
  obtain ⟨B, hB⟩ := δ
  have hAB : A = B := matHom_injective (hγg.trans hδg.symm)
  subst hAB
  have hmem : (⟨A, hB⟩ : ↥(StatedSU 3 4 K)) ∈
      (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 4 K) := hA
  rw [statedScalars_subgroupOf_statedSU_three_four_eq_bot hK, Subgroup.mem_bot] at hmem
  have hA1 : A = 1 := congrArg Subtype.val hmem
  rw [← hγg]
  have hsub : (⟨A, hA⟩ : ↥(StatedScalars (Fin 3) K)) = 1 := Subtype.ext hA1
  rw [hsub, map_one]

def u34S13 : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
def u34M13 (ω : K) : Matrix (Fin 3) (Fin 3) K := !![ω, 0, ω ^ 2; 0, 1, 0; ω ^ 2, 0, ω]

theorem u34S13_det [CharP K 2] : (u34S13 (K := K)).det = 1 := by
  rw [u34S13, Matrix.det_fin_three]
  simp [CharTwo.neg_eq]

theorem u34S13_unitary : ((u34S13 (K := K)).map (· ^ 4))ᵀ * u34S13 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u34S13, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]

theorem u34S13_mul_self : u34S13 (K := K) * u34S13 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u34S13, Matrix.mul_apply, Fin.sum_univ_three]

theorem u34M13_det [CharP K 2] {ω : K} (hω3 : ω ^ 3 = 1) (hω2 : ω ^ 2 + ω + 1 = 0) :
    (u34M13 ω).det = 1 := by
  have hω4 : ω ^ 4 = ω := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, hω3, one_mul, pow_one]
  have hωsum : ω ^ 2 + ω = 1 := by
    have h : ω ^ 2 + ω = -1 := by linear_combination hω2
    simpa [CharTwo.neg_eq] using h
  rw [u34M13, Matrix.det_fin_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Matrix.of_apply, Matrix.cons_val']
  ring_nf
  rw [hω4, CharTwo.sub_eq_add]
  exact hωsum

theorem u34M13_map_pow {ω : K} (hω3 : ω ^ 3 = 1) :
    (u34M13 ω).map (· ^ 4) = u34M13 ω := by
  have hω4 : ω ^ 4 = ω := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, hω3, one_mul, pow_one]
  have hω2four : (ω ^ 2) ^ 4 = ω ^ 2 := by
    rw [← pow_mul, show 2 * 4 = 8 by norm_num,
      show (8 : ℕ) = 3 * 2 + 2 by norm_num, pow_add, pow_mul, hω3, one_pow, one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u34M13, hω4, hω2four]

theorem u34M13_transpose {ω : K} : (u34M13 ω)ᵀ = u34M13 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u34M13, Matrix.transpose_apply]

theorem u34M13_mul_self [CharP K 2] {ω : K} (hω3 : ω ^ 3 = 1) (hω2 : ω ^ 2 + ω + 1 = 0) :
    u34M13 ω * u34M13 ω = 1 := by
  have hω4 : ω ^ 4 = ω := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, hω3, one_mul, pow_one]
  have hωsum : ω ^ 2 + ω = 1 := by
    have h : ω ^ 2 + ω = -1 := by linear_combination hω2
    simpa [CharTwo.neg_eq] using h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u34M13, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring_nf
  all_goals
    first
    | rw [hω4]; exact hωsum
    | simp [CharTwo.two_eq_zero]
    | exact hωsum
    | rfl

theorem u34S13_comm_u34M13 {ω : K} :
    u34S13 (K := K) * u34M13 ω = u34M13 ω * u34S13 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u34S13, u34M13, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] noncomputable def u34S13GL [CharP K 2] : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero u34S13 (by rw [u34S13_det]; exact one_ne_zero)

@[expose] noncomputable def u34M13GL [CharP K 2] (ω : K) (hω3 : ω ^ 3 = 1)
    (hω2 : ω ^ 2 + ω + 1 = 0) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (u34M13 ω)
    (by rw [u34M13_det hω3 hω2]; exact one_ne_zero)

theorem u34S13GL_coe [CharP K 2] :
    ((u34S13GL (K := K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = u34S13 := rfl

theorem u34M13GL_coe [CharP K 2] {ω : K} (hω3 : ω ^ 3 = 1) (hω2 : ω ^ 2 + ω + 1 = 0) :
    ((u34M13GL ω hω3 hω2 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = u34M13 ω := rfl

theorem u34S13GL_mem [CharP K 2] : u34S13GL (K := K) ∈ StatedSU 3 4 K := by
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [u34S13GL_coe, u34S13_det]
  · rw [u34S13GL_coe, u34S13_unitary]

theorem u34M13GL_mem [CharP K 2] {ω : K} (hω3 : ω ^ 3 = 1)
    (hω2 : ω ^ 2 + ω + 1 = 0) : u34M13GL ω hω3 hω2 ∈ StatedSU 3 4 K := by
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [u34M13GL_coe, u34M13_det hω3 hω2]
  · rw [u34M13GL_coe, u34M13_map_pow hω3, u34M13_transpose, u34M13_mul_self hω3 hω2]

variable [Finite K]

theorem exists_scalar_mul_of_normalizes_statedSU (hK : Nat.card K = 16) {A : GL (Fin 3) K}
    (hnorm : ∀ l ∈ StatedSU 3 4 K, A * l * A⁻¹ ∈ StatedSU 3 4 K) :
    ∃ (c : Kˣ) (B : GL (Fin 3) K), B ∈ StatedSU 3 4 K ∧
      A = Matrix.GeneralLinearGroup.scalar (Fin 3) c * B := by
  have : CharP K 2 := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow
    (F := K) (n := 4) Nat.prime_two (by rw [hK]; norm_num)
  have hK' : Nat.card K = (2 ^ 2) ^ 2 := by rw [hK]; norm_num
  obtain ⟨μ, hμ⟩ := exists_gram_scalar (n := 2) (by norm_num) hK' hnorm
  set Am : Matrix (Fin 3) (Fin 3) K := (A : Matrix (Fin 3) (Fin 3) K) with hAm
  set d : K := Am.det with hd
  have hd0 : d ≠ 0 := by
    have h := (Matrix.GeneralLinearGroup.det A).ne_zero
    rw [Matrix.GeneralLinearGroup.val_det_apply, ← hd] at h
    exact h
  have hdet5 : d ^ 5 = μ ^ 3 := by
    have hdet := congrArg Matrix.det hμ
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_one,
      Fintype.card_fin, mul_one] at hdet
    have hconj : (conjM 2 Am).det = d ^ 4 := by
      have h := RingHom.map_det ((bar (K := K) 2 : K ≃+* K) : K →+* K) Am
      change (bar (K := K) 2) Am.det = (Am.map (bar 2)).det at h
      rw [bar_apply, show (2 : ℕ) ^ 2 = 4 by norm_num, ← hd] at h
      simpa [conjM] using h.symm
    rw [hconj] at hdet
    rwa [← pow_succ] at hdet
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num : 3 ≠ 0)] at hdet5
    exact pow_ne_zero 5 hd0 hdet5
  let μu : Kˣ := Units.mk0 μ hμ0
  let du : Kˣ := Matrix.GeneralLinearGroup.det A
  have hdu_val : (du : K) = d := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, ← hd]
  have hdet5u : du ^ 5 = μu ^ 3 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hdu_val]
    exact hdet5
  have hdu15 : du ^ 15 = 1 := by
    have h := pow_card_eq_one' (x := du)
    simpa [Nat.card_units, hK] using h
  have hμu15 : μu ^ 15 = 1 := by
    have h := pow_card_eq_one' (x := μu)
    simpa [Nat.card_units, hK] using h
  have hμu3 : μu ^ 3 = 1 := by
    have h1 : (μu ^ 3) ^ 3 = 1 := by
      rw [← hdet5u, ← pow_mul, show 5 * 3 = 15 by norm_num, hdu15]
    have h2 : (μu ^ 3) ^ 5 = 1 := by
      rw [← pow_mul, show 3 * 5 = 15 by norm_num, hμu15]
    have hord : orderOf (μu ^ 3) ∣ 1 := by
      simpa using Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr h1)
        (orderOf_dvd_iff_pow_eq_one.mpr h2)
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord)
  have hdu5 : du ^ 5 = 1 := by rw [hdet5u, hμu3]
  have hμ3 : μ ^ 3 = 1 := by
    have h := congrArg (fun u : Kˣ => (u : K)) hμu3
    simpa [μu, Units.val_pow_eq_pow_val] using h
  have hd5 : d ^ 5 = 1 := by
    have h := congrArg (fun u : Kˣ => (u : K)) hdu5
    simpa [du, hdu_val, Units.val_pow_eq_pow_val] using h
  let c : K := μ ^ 2 * d ^ 2
  have hc0 : c ≠ 0 := mul_ne_zero (pow_ne_zero 2 hμ0) (pow_ne_zero 2 hd0)
  have hc5 : c ^ 5 = μ := by
    have hμ10 : μ ^ 10 = μ := by
      calc μ ^ 10 = (μ ^ 3) ^ 3 * μ := by
            rw [show (10 : ℕ) = 3 * 3 + 1 by norm_num, pow_add, pow_mul, pow_one]
        _ = μ := by rw [hμ3]; simp
    have hd10 : d ^ 10 = 1 := by
      calc d ^ 10 = (d ^ 5) ^ 2 := by
            rw [show (10 : ℕ) = 5 * 2 by norm_num, pow_mul]
        _ = 1 := by rw [hd5, one_pow]
    dsimp [c]
    rw [mul_pow, show (μ ^ 2) ^ 5 = μ ^ 10 by rw [← pow_mul],
      show (d ^ 2) ^ 5 = d ^ 10 by rw [← pow_mul], hμ10, hd10, mul_one]
  have hc3 : c ^ 3 = d := by
    have hμ6 : μ ^ 6 = 1 := by
      calc μ ^ 6 = (μ ^ 3) ^ 2 := by
            rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul]
        _ = 1 := by rw [hμ3, one_pow]
    have hd6 : d ^ 6 = d := by
      calc d ^ 6 = d ^ 5 * d := by
            rw [show (6 : ℕ) = 5 + 1 by norm_num, pow_add, pow_one]
        _ = d := by rw [hd5, one_mul]
    dsimp [c]
    rw [mul_pow, show (μ ^ 2) ^ 3 = μ ^ 6 by rw [← pow_mul],
      show (d ^ 2) ^ 3 = d ^ 6 by rw [← pow_mul], hμ6, hd6, one_mul]
  let cu : Kˣ := Units.mk0 c hc0
  let B : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (c⁻¹ • Am) (by
    rw [Matrix.det_smul, Fintype.card_fin]
    exact mul_ne_zero (pow_ne_zero 3 (inv_ne_zero hc0)) hd0)
  have hBmat : (B : Matrix (Fin 3) (Fin 3) K) = c⁻¹ • Am :=
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _
  have hBdet : (B : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [hBmat, Matrix.det_smul, Fintype.card_fin, inv_pow, hc3]
    exact inv_mul_cancel₀ hd0
  have hbar : CFSG.LieType.BorelTits.unitaryInvolution K 2 2 = bar 2 := by
    ext x
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, bar_apply]
  have hBunit : ((B : Matrix (Fin 3) (Fin 3) K).map (bar 2))ᵀ *
      (B : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [hBmat]
    have hmap : (c⁻¹ • Am).map (bar 2) = (c⁻¹) ^ 4 • (Am.map (bar 2)) := by
      rw [Matrix.map_smul' (bar 2) c⁻¹ Am (fun a b => map_mul (bar 2) a b), bar_apply,
        show (2 : ℕ) ^ 2 = 4 by norm_num]
    rw [hmap, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have h1 : (c⁻¹) ^ 4 * c⁻¹ = (c ^ 5)⁻¹ := by
      rw [inv_pow, ← mul_inv_rev, show c * c ^ 4 = c ^ 5 by ring]
    have h2 : (c⁻¹) ^ 4 * c⁻¹ * μ = 1 := by
      rw [h1, hc5, inv_mul_cancel₀ hμ0]
    rw [show (Am.map (bar 2))ᵀ * Am = μ • 1 from hμ, smul_smul, h2, one_smul]
  have hBSU : B ∈ StatedSU 3 4 K := by
    have hSUid : StatedSU 3 4 K =
        CFSG.LieType.Universal.Unitary.SUid
          (CFSG.LieType.BorelTits.unitaryInvolution K 2 2) 3 := by
      simpa using (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU (p := 2) (f := 2)
        hK' 3).symm
    rw [hSUid, CFSG.LieType.Universal.Unitary.mem_SUid]
    refine ⟨hBdet, ?_⟩
    rw [hbar]
    exact hBunit
  refine ⟨cu, B, hBSU, ?_⟩
  apply Units.ext
  rw [Units.val_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
    Matrix.GeneralLinearGroup.coe_scalar]
  ext i j
  rw [Matrix.scalar_apply, Matrix.diagonal_mul]
  change (Am : Matrix (Fin 3) (Fin 3) K) i j = (↑cu : K) * (c⁻¹ * Am i j)
  rw [show (↑cu : K) = c from rfl, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]

theorem natNorm_statedSU_inf_linSub_eq (hK : Nat.card K = 16) :
    natNorm (StatedSU 3 4 K) ⊓ linSub = natScalImage K ⊔ natImage (StatedSU 3 4 K) := by
  refine le_antisymm ?_ (sup_le (le_inf (natImage_statedScalars_le_natNorm _)
    (natImage_le_linSub _)) (le_inf Subgroup.le_normalizer (natImage_le_linSub _)))
  intro g hg
  obtain ⟨hgN, hgL⟩ := hg
  obtain ⟨A, rfl⟩ := exists_matAut_of_mem_linSub hgL
  have hnorm : ∀ l ∈ StatedSU 3 4 K, A * l * A⁻¹ ∈ StatedSU 3 4 K := by
    intro l hl
    have hmem : natAut (StatedSU 3 4 K) ⟨l, hl⟩ ∈ natImage (StatedSU 3 4 K) := ⟨_, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp hgN (natAut (StatedSU 3 4 K) ⟨l, hl⟩)).mp hmem
    obtain ⟨l', hl'⟩ := h1
    have heq : matAut (A * l * A⁻¹) = natAut (StatedSU 3 4 K) l' := by
      calc matAut (A * l * A⁻¹) = matAut A * matAut l * (matAut A)⁻¹ := by
            change matHom (A * l * A⁻¹) = matHom A * matHom l * (matHom A)⁻¹
            rw [map_mul, map_mul, map_inv]
        _ = natAut (StatedSU 3 4 K) l' := hl'.symm
    have heq' : A * l * A⁻¹ = (l' : GL (Fin 3) K) := matHom_injective heq
    rw [heq']
    exact l'.2
  obtain ⟨c, B, hBSU, hAB⟩ := exists_scalar_mul_of_normalizes_statedSU hK hnorm
  rw [hAB]
  change matHom (Matrix.GeneralLinearGroup.scalar (Fin 3) c * B) ∈ _
  rw [map_mul]
  exact Subgroup.mul_mem_sup
    (show matHom (Matrix.GeneralLinearGroup.scalar (Fin 3) c) ∈ natScalImage K from
      ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 3) c, ⟨c, rfl⟩⟩, rfl⟩)
    (show matHom B ∈ natImage (StatedSU 3 4 K) from ⟨⟨B, hBSU⟩, rfl⟩)

theorem card_natNorm_statedSU_inf_linSub (hK : Nat.card K = 16) :
    Nat.card ↥(natNorm (StatedSU 3 4 K) ⊓ linSub) = 936000 := by
  rw [natNorm_statedSU_inf_linSub_eq hK, CFSG.card_sup_eq_mul_of_commute]
  · rw [card_natScalImage hK, card_natImage_statedSU_three_four hK]
  · exact fun a ha b hb => commute_of_mem_natImage_statedScalars ha hb
  · exact natScalImage_inf_natImage_statedSU hK

theorem card_natNorm_statedSU_three_four (hK : Nat.card K = 16) :
    Nat.card (natNorm (StatedSU 3 4 K)) = 2 ^ 8 * 3 ^ 2 * 5 ^ 3 * 13 := by
  have : CharP K 2 := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow
    (F := K) (n := 4) Nat.prime_two (by rw [hK]; norm_num)
  have hK' : Nat.card K = (2 ^ 2) ^ 2 := by rw [hK]; norm_num
  have hΓ : HasScalarCommutant (StatedSU 3 4 K) := hasScalarCommutant' (n := 2) (by norm_num) hK'
  have hrange : (fieldHom hΓ).range = ⊤ :=
    eq_top_iff.mpr fun σ _ => ⟨⟨fieldMap σ, fieldMap_mem_natNorm_statedSU σ⟩,
      (fieldHom_eq_iff hΓ _ σ).mpr (isSemilinear_fieldMap σ)⟩
  have hker : Nat.card (fieldHom hΓ).ker = 936000 := by
    have hker_eq : (fieldHom hΓ).ker = linSub.subgroupOf (natNorm (StatedSU 3 4 K)) := by
      ext g
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, fieldHom_eq_one_iff]
    rw [hker_eq]
    have hcard : Nat.card ↥(linSub.subgroupOf (natNorm (StatedSU 3 4 K))) =
        Nat.card ↥(natNorm (StatedSU 3 4 K) ⊓ linSub) := by
      refine Nat.card_congr
        { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
          invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
          left_inv := fun x => rfl
          right_inv := fun y => rfl }
    rw [hcard]
    exact card_natNorm_statedSU_inf_linSub hK
  have hcard := Subgroup.card_ker_mul_card_range (fieldHom hΓ)
  rw [hker, hrange, Subgroup.card_top, show Nat.card (K ≃+* K) = 4 from
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K
      (by rw [hK]; norm_num)).1] at hcard
  rw [← hcard]
  norm_num

theorem succ_le_pRank_natNorm_of_scalar (hK : Nat.card K = 16) {p k : ℕ} (hp : p.Prime)
    {E : Subgroup (StatedSU 3 4 K)} (hE : CFSG.Open.IsElemAbelian p E)
    (hEcard : Nat.card E = p ^ k) {ζ : Kˣ} (hζ : orderOf ζ = p) :
    k + 1 ≤ CFSG.Open.pRank p (natNorm (StatedSU 3 4 K)) := by
  have hCord : orderOf (matAut (Matrix.GeneralLinearGroup.scalar (Fin 3) ζ)) = p := by
    change orderOf (matHom (Matrix.GeneralLinearGroup.scalar (Fin 3) ζ)) = p
    rw [orderOf_injective matHom matHom_injective,
      orderOf_injective (Matrix.GeneralLinearGroup.scalar (Fin 3))
        CFSG.LinearAlgebra.generalLinearGroup_scalar_injective ζ, hζ]
  have hAle : E.map (matHom.comp (StatedSU 3 4 K).subtype) ≤ natImage (StatedSU 3 4 K) := by
    rintro _ ⟨x, -, rfl⟩
    exact ⟨⟨x, x.2⟩, rfl⟩
  have hCle : Subgroup.zpowers (matAut (Matrix.GeneralLinearGroup.scalar (Fin 3) ζ)) ≤
      natScalImage K :=
    Subgroup.zpowers_le.mpr ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 3) ζ, ζ, rfl⟩, rfl⟩
  have hcomm : ∀ a ∈ E.map (matHom.comp (StatedSU 3 4 K).subtype),
      ∀ b ∈ Subgroup.zpowers (matAut (Matrix.GeneralLinearGroup.scalar (Fin 3) ζ)),
        Commute a b := fun a ha b hb =>
    (commute_of_mem_natImage_statedScalars (hCle hb) (hAle ha)).symm
  have hdisj : E.map (matHom.comp (StatedSU 3 4 K).subtype) ⊓
      Subgroup.zpowers (matAut (Matrix.GeneralLinearGroup.scalar (Fin 3) ζ)) = ⊥ := by
    rw [eq_bot_iff, ← natScalImage_inf_natImage_statedSU hK]
    exact fun x hx => ⟨hCle hx.2, hAle hx.1⟩
  refine le_pRank hp (sup_le (hAle.trans Subgroup.le_normalizer)
    (hCle.trans (natImage_statedScalars_le_natNorm _)))
    (CFSG.Open.IsElemAbelian.sup_of_commute (hE.map _)
      (CFSG.Open.isElemAbelian_zpowers (orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hCord))) hcomm)
    ?_
  rw [CFSG.card_sup_eq_mul_of_commute _ _ hcomm hdisj, Nat.card_zpowers, hCord,
    Subgroup.card_map_of_injective (f := matHom.comp (StatedSU 3 4 K).subtype)
      (fun x y h => Subtype.ext (matHom_injective h)), hEcard, pow_succ]

theorem three_le_pRank_five_natNorm (hK : Nat.card K = 16) :
    3 ≤ CFSG.Open.pRank 5 (natNorm (StatedSU 3 4 K)) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hgord : orderOf g = 15 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  let ζu : Kˣ := g ^ 3
  have hζord : orderOf ζu = 5 := by
    rw [orderOf_pow, hgord]
    norm_num
  have hζ5 : ζu ^ 5 = 1 := by
    have h := pow_orderOf_eq_one ζu
    rwa [hζord] at h
  have hd0 : CFSG.SectionRank.ClassicalEven.torusDiag
      (CFSG.SectionRank.ClassicalEven.torusVec ζu (0 : Fin 3) 2) ∈ StatedSU 3 4 K :=
    CFSG.SectionRank.ClassicalEven.torusDiag_mem_SU (q := 4) (by norm_num)
      (CFSG.SectionRank.ClassicalEven.prod_torusVec ζu _ _)
      (by rw [CFSG.SectionRank.ClassicalEven.torusVec_pow, hζ5,
        CFSG.SectionRank.ClassicalEven.torusVec_one])
  have hd1 : CFSG.SectionRank.ClassicalEven.torusDiag
      (CFSG.SectionRank.ClassicalEven.torusVec ζu (1 : Fin 3) 2) ∈ StatedSU 3 4 K :=
    CFSG.SectionRank.ClassicalEven.torusDiag_mem_SU (q := 4) (by norm_num)
      (CFSG.SectionRank.ClassicalEven.prod_torusVec ζu _ _)
      (by rw [CFSG.SectionRank.ClassicalEven.torusVec_pow, hζ5,
        CFSG.SectionRank.ClassicalEven.torusVec_one])
  have hproj : 2 ≤ CFSG.Open.pRank 5
      (⊤ : Subgroup (StatedProj (StatedSU 3 4 K))) :=
    CFSG.Quasithin.A3Facts.two_le_pRank_torus_shared (H := StatedSU 3 4 K)
      (r := 5) (by norm_num) hζord (by decide) (by decide) (by decide) hd0 hd1
  have hrankSU : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup (StatedSU 3 4 K)) := by
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 5) (by norm_num)
      (statedProjStatedSUEquiv hK)]
    exact hproj
  obtain ⟨E, -, hEel, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 5) (by norm_num) (⊤ : Subgroup (StatedSU 3 4 K))
  have h := succ_le_pRank_natNorm_of_scalar hK Nat.prime_five hEel hEcard hζord
  omega

theorem two_le_pRank_three_natNorm (hK : Nat.card K = 16) :
    2 ≤ CFSG.Open.pRank 3 (natNorm (StatedSU 3 4 K)) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hgord : orderOf g = 15 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  have hωord : orderOf (g ^ 5) = 3 := by
    rw [orderOf_pow, hgord]
    norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := StatedSU 3 4 K) 3
    (by rw [card_statedSU_three_four hK]; norm_num)
  exact succ_le_pRank_natNorm_of_scalar hK Nat.prime_three (E := Subgroup.zpowers x)
    (CFSG.Open.isElemAbelian_zpowers (orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hx)))
    (by rw [Nat.card_zpowers, hx, pow_one]) hωord

theorem three_le_pRank_two_natNorm [CharP K 2] (hK : Nat.card K = 16) :
    3 ≤ CFSG.Open.pRank 2 (natNorm (StatedSU 3 4 K)) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hgord : orderOf g = 15 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  let ωu : Kˣ := g ^ 5
  have hωuord : orderOf ωu = 3 := by
    rw [orderOf_pow, hgord]
    norm_num
  let ω : K := (ωu : K)
  have hω3 : ω ^ 3 = 1 := by
    have h := pow_orderOf_eq_one ωu
    rw [hωuord] at h
    simpa [ω, Units.val_pow_eq_pow_val] using congrArg (fun u : Kˣ => (u : K)) h
  have hω0 : ω ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num : 3 ≠ 0)] at hω3
    exact zero_ne_one hω3
  have hωne : ω ≠ 1 := by
    intro h
    have h1 : ωu = 1 := Units.ext (by simpa [ω] using h)
    have h2 : orderOf ωu = 1 := by rw [h1, orderOf_one]
    rw [hωuord] at h2
    norm_num at h2
  have hω2 : ω ^ 2 + ω + 1 = 0 := by
    have h1 : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
      rw [show (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 by ring, hω3, sub_self]
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd (sub_eq_zero.mp h2) hωne
    · exact h2
  have hω4 : ω ^ 4 = ω := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, hω3, one_mul, pow_one]
  have hω2four : (ω ^ 2) ^ 4 = ω ^ 2 := by
    rw [← pow_mul, show 2 * 4 = 8 by norm_num,
      show (8 : ℕ) = 3 * 2 + 2 by norm_num, pow_add, pow_mul, hω3, one_pow, one_mul]
  let S13GL : GL (Fin 3) K := u34S13GL
  let M13GL : GL (Fin 3) K := u34M13GL ω hω3 hω2
  have hS13mem : S13GL ∈ StatedSU 3 4 K := u34S13GL_mem
  have hM13mem : M13GL ∈ StatedSU 3 4 K := u34M13GL_mem hω3 hω2
  let A : MulAut (StdMod (Fin 3) K) := matHom S13GL
  let B : MulAut (StdMod (Fin 3) K) := matHom M13GL
  let C : MulAut (StdMod (Fin 3) K) := fieldMap (ι := Fin 3) (bar (K := K) 2)
  have hS13sq : S13GL * S13GL = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change ((S13GL : Matrix (Fin 3) (Fin 3) K) * (S13GL : Matrix (Fin 3) (Fin 3) K)) i j =
      (1 : Matrix (Fin 3) (Fin 3) K) i j
    rw [show (S13GL : Matrix (Fin 3) (Fin 3) K) = u34S13 from rfl, u34S13_mul_self]
  have hM13sq : M13GL * M13GL = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change ((M13GL : Matrix (Fin 3) (Fin 3) K) * (M13GL : Matrix (Fin 3) (Fin 3) K)) i j =
      (1 : Matrix (Fin 3) (Fin 3) K) i j
    rw [show (M13GL : Matrix (Fin 3) (Fin 3) K) = u34M13 ω from rfl,
      u34M13_mul_self hω3 hω2]
  have hA2 : A ^ 2 = 1 := by
    change matHom S13GL ^ 2 = 1
    rw [pow_two, ← map_mul, hS13sq, map_one]
  have hB2 : B ^ 2 = 1 := by
    change matHom M13GL ^ 2 = 1
    rw [pow_two, ← map_mul, hM13sq, map_one]
  have hbar2ne : bar (K := K) 2 ≠ 1 := by
    intro h
    have h1 : (g : K) ^ 4 = (g : K) := by
      have := congrArg (fun σ : K ≃+* K => σ (g : K)) h
      simpa [bar_apply] using this
    have hg0 : (g : K) ≠ 0 := Units.ne_zero g
    have h2 : (g : K) ^ 3 = 1 := by
      have h4 : (g : K) ^ 4 = (g : K) ^ 3 * (g : K) := by ring
      have h5 : (g : K) ^ 3 * (g : K) = 1 * (g : K) := by rw [← h4, h1, one_mul]
      exact mul_right_cancel₀ hg0 h5
    have hdvd : orderOf (g : K) ∣ 3 := orderOf_dvd_of_pow_eq_one h2
    rw [orderOf_units] at hdvd
    rw [hgord] at hdvd
    norm_num at hdvd
  have hbb : ∀ x : K, bar (K := K) 2 (bar (K := K) 2 x) = x := by
    have : Fintype K := Fintype.ofFinite K
    intro x
    rw [bar_apply, bar_apply, ← pow_mul]
    have h := FiniteField.pow_card x
    rw [← Nat.card_eq_fintype_card, hK] at h
    simpa using h
  have hC2 : C ^ 2 = 1 := by
    change fieldMap (ι := Fin 3) (bar (K := K) 2) ^ 2 = 1
    refine toAddMap_injective fun v => ?_
    rw [pow_two, toAddMap_mul, toAddMap_fieldMap, toAddMap_fieldMap, toAddMap_one]
    exact funext fun i => hbb (v i)
  have hAB : A * B = B * A := by
    change matHom S13GL * matHom M13GL = matHom M13GL * matHom S13GL
    rw [← map_mul, ← map_mul]
    congr 1
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change ((S13GL : Matrix (Fin 3) (Fin 3) K) * (M13GL : Matrix (Fin 3) (Fin 3) K)) i j =
      ((M13GL : Matrix (Fin 3) (Fin 3) K) * (S13GL : Matrix (Fin 3) (Fin 3) K)) i j
    rw [show (S13GL : Matrix (Fin 3) (Fin 3) K) = u34S13 from rfl,
      show (M13GL : Matrix (Fin 3) (Fin 3) K) = u34M13 ω from rfl,
      u34S13_comm_u34M13]
  have hCmem : C ∈ natNorm (StatedSU 3 4 K) := fieldMap_mem_natNorm_statedSU (bar 2)
  have hAC : A * C = C * A := by
    have hconj : C * A * C⁻¹ = A := by
      change fieldMap (ι := Fin 3) (bar 2) * matHom S13GL *
        (fieldMap (ι := Fin 3) (bar 2))⁻¹ = matHom S13GL
      rw [matHom_apply, fieldMap_conj_matAut_eq_glAut]
      congr 1
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      change ((glAut (bar (K := K) 2) S13GL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j =
        (u34S13 : Matrix (Fin 3) (Fin 3) K) i j
      rw [coe_glAut]
      fin_cases i <;> fin_cases j <;>
        simp [S13GL, u34S13GL, u34S13, bar_apply, show (2 : ℕ) ^ 2 = 4 by norm_num]
    calc A * C = C * A * C⁻¹ * C := by rw [hconj]
      _ = C * A := by rw [mul_assoc, inv_mul_cancel, mul_one]
  have hBC : B * C = C * B := by
    have hconj : C * B * C⁻¹ = B := by
      change fieldMap (ι := Fin 3) (bar 2) * matHom M13GL *
        (fieldMap (ι := Fin 3) (bar 2))⁻¹ = matHom M13GL
      rw [matHom_apply, fieldMap_conj_matAut_eq_glAut]
      congr 1
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      change ((glAut (bar (K := K) 2) M13GL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j =
        (u34M13 ω : Matrix (Fin 3) (Fin 3) K) i j
      rw [coe_glAut]
      fin_cases i <;> fin_cases j <;>
        simp [M13GL, u34M13GL, u34M13, bar_apply, show (2 : ℕ) ^ 2 = 4 by norm_num,
          hω4, hω2four]
    calc B * C = C * B * C⁻¹ * C := by rw [hconj]
      _ = C * B := by rw [mul_assoc, inv_mul_cancel, mul_one]
  have hA1 : A ≠ 1 := by
    intro h
    have h1 : S13GL = 1 := by
      exact matHom_injective (by simpa [A] using h)
    have h2 : (u34S13 : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [← u34S13GL_coe]
      exact congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) h1
    have h3 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 2) h2
    simp [u34S13] at h3
  have hB1 : B ≠ 1 := by
    intro h
    have h1 : M13GL = 1 := by
      exact matHom_injective (by simpa [B] using h)
    have h2 : (u34M13 ω : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [← u34M13GL_coe hω3 hω2]
      exact congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) h1
    have h3 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 0) h2
    simp [u34M13] at h3
    exact hωne h3
  have hC1 : C ≠ 1 := by
    intro h
    apply hbar2ne
    ext x
    have h3 := congrArg (fun f : MulAut (StdMod (Fin 3) K) =>
      toAddMap f (fun _ => x) 0) h
    rw [toAddMap_fieldMap, toAddMap_one] at h3
    simpa using h3
  have hABne : A ≠ B := by
    intro h
    have h1 : S13GL = M13GL := matHom_injective (by simpa [A, B] using h)
    have h2 : (u34S13 : Matrix (Fin 3) (Fin 3) K) = u34M13 ω := by
      rw [← u34S13GL_coe, ← u34M13GL_coe hω3 hω2]
      exact congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) h1
    have h3 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 0) h2
    simp [u34S13, u34M13] at h3
    exact hω0 h3.symm
  let AB : Subgroup (MulAut (StdMod (Fin 3) K)) := Subgroup.closure ({A, B} : Set _)
  let CC : Subgroup (MulAut (StdMod (Fin 3) K)) := Subgroup.closure ({C} : Set _)
  have hABcard : Nat.card ↥AB = 4 := by
    exact CFSG.GroupTheory.card_closure_pair_eq_four (by simpa [pow_two] using hA2)
      (by simpa [pow_two] using hB2) hAB hA1 hB1 hABne
  have hCord : orderOf C = 2 := orderOf_eq_prime hC2 hC1
  have hCcard : Nat.card ↥CC = 2 := by
    change Nat.card ↥(Subgroup.closure ({C} : Set _)) = 2
    rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers, hCord]
  have hABnat : AB ≤ natImage (StatedSU 3 4 K) := by
    rw [show AB = Subgroup.closure ({A, B} : Set _) from rfl]
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨⟨S13GL, hS13mem⟩, matHom_apply S13GL⟩
    · exact ⟨⟨M13GL, hM13mem⟩, matHom_apply M13GL⟩
  have hABlin : AB ≤ linSub := hABnat.trans (natImage_le_linSub _)
  have hCnotlin : C ∉ linSub := by
    have hΓ : HasScalarCommutant (StatedSU 3 4 K) :=
      hasScalarCommutant' (n := 2) (by norm_num) (by rw [hK]; norm_num)
    have hCfield : fieldHom hΓ ⟨C, hCmem⟩ = bar (K := K) 2 :=
      (fieldHom_eq_iff hΓ ⟨C, hCmem⟩ (bar 2)).mpr (isSemilinear_fieldMap (bar 2))
    intro hlin
    have h1 : fieldHom hΓ ⟨C, hCmem⟩ = 1 := (fieldHom_eq_one_iff hΓ ⟨C, hCmem⟩).mpr hlin
    rw [hCfield] at h1
    exact hbar2ne h1
  have hdisj : AB ⊓ CC = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxAB, hxC⟩
    rw [Subgroup.mem_bot]
    by_contra hxne
    have hxC' : x ∈ Subgroup.zpowers C := by
      rw [Subgroup.zpowers_eq_closure]
      exact hxC
    have hdvd : orderOf x ∣ orderOf C := orderOf_dvd_of_mem_zpowers hxC'
    rw [hCord] at hdvd
    have hxord : orderOf x = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hxne
      · exact h1
    have hxle : Subgroup.zpowers x ≤ Subgroup.zpowers C := Subgroup.zpowers_le.mpr hxC'
    have hxCeq : Subgroup.zpowers x = Subgroup.zpowers C := by
      refine Subgroup.eq_of_le_of_card_ge hxle ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hxord, hCord]
    have hClin : C ∈ linSub := by
      have hCmem' : C ∈ Subgroup.zpowers C := Subgroup.mem_zpowers C
      rw [← hxCeq] at hCmem'
      exact hABlin (Subgroup.zpowers_le.mpr hxAB hCmem')
    exact hCnotlin hClin
  have hcommAB : ∀ a ∈ AB, ∀ b ∈ CC, Commute a b := by
    intro a ha b hb
    have ha' : a ∈ Subgroup.closure ({A, B} : Set _) := ha
    have hb' : b ∈ Subgroup.zpowers C := by
      change b ∈ Subgroup.closure ({C} : Set _) at hb
      rwa [Subgroup.zpowers_eq_closure]
    have hCa : Commute a C := by
      refine Subgroup.closure_induction ?_ ?_ ?_ ?_ ha'
      · intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · exact hAC
        · exact hBC
      · exact Commute.one_left C
      · intro x y _ _ hx hy
        exact hx.mul_left hy
      · intro x _ hx
        exact hx.inv_left
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb'
    rw [← hk]
    exact hCa.zpow_right k
  have hEel : CFSG.Open.IsElemAbelian 2 (AB ⊔ CC) :=
    CFSG.Open.IsElemAbelian.sup_of_commute
      (by
        rw [show AB = Subgroup.closure ({A, B} : Set _) from rfl]
        refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
        · intro x hx y hy
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
          rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
            simp [hAB, hA2, hB2, pow_two]
        · intro x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl <;> simp [hA2, hB2, pow_two])
      (by
        rw [show CC = Subgroup.closure ({C} : Set _) from rfl]
        refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
        · intro x hx y hy
          simp only [Set.mem_singleton_iff] at hx hy
          rw [hx, hy]
        · intro x hx
          simp only [Set.mem_singleton_iff] at hx
          rw [hx]
          exact hC2)
      hcommAB
  have hEcard : Nat.card ↥(AB ⊔ CC) = 8 := by
    rw [CFSG.card_sup_eq_mul_of_commute AB CC hcommAB hdisj, hABcard, hCcard]
  have hEle : AB ⊔ CC ≤ natNorm (StatedSU 3 4 K) := by
    refine sup_le ?_ ?_
    · exact hABnat.trans Subgroup.le_normalizer
    · rw [show CC = Subgroup.closure ({C} : Set _) from rfl]
      refine (Subgroup.closure_le _).mpr ?_
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hCmem
  have hcard8 : Nat.card ↥(AB ⊔ CC) = 2 ^ 3 := by
    rw [hEcard]; norm_num
  exact le_pRank Nat.prime_two hEle hEel hcard8

theorem k_U34NormalizerRanks_holds : K_U34NormalizerRanks := by
  intro K _ _ hK
  have : CharP K 2 := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow
    (F := K) (n := 4) Nat.prime_two (by rw [hK]; norm_num)
  have hN := card_natNorm_statedSU_three_four hK
  have htop (p : ℕ) (hp : 1 < p) : CFSG.pRank p (⊤ : Subgroup (natNorm (StatedSU 3 4 K))) =
      CFSG.Open.pRank p (natNorm (StatedSU 3 4 K)) := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp Subgroup.topEquiv,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  have h13 : 1 ≤ CFSG.Open.pRank 13 (natNorm (StatedSU 3 4 K)) := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact CFSG.one_le_pRank_of_dvd_card (by norm_num) (by rw [hN]; norm_num)
  refine ⟨hN, ?_, ?_, ?_, ?_⟩ <;> rw [htop _ (by norm_num)]
  · refine le_antisymm ?_ (three_le_pRank_two_natNorm hK)
    have h := CFSG.Quasithin.H.SU3.pRank_le (K := K) (n := 2) (by norm_num)
      (by rw [hK]; norm_num) (X := natNorm (StatedSU 3 4 K)) le_rfl
    simpa using h
  · exact le_antisymm (CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ Nat.prime_three
      (by rw [hN]; norm_num)) (two_le_pRank_three_natNorm hK)
  · exact le_antisymm (CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ Nat.prime_five
      (by rw [hN]; norm_num)) (three_le_pRank_five_natNorm hK)
  · exact le_antisymm (CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ (by norm_num)
      (by rw [hN]; norm_num)) h13

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
