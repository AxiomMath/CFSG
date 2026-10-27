module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res3ProofLinBlock
public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res3ProofLinArith
public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res3ProofHessU
import CFSG.Quasithin.EmptyFaithful.Insp9Cases11
import CFSG.RankThree.PartTwo.Sec19.Step1915WProofLie3K
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec14.Item14Res8ProofGenNine

public section

namespace CFSG.RankThree.PartTwo.Sec14

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.SeitzGeneration (heisC blockOneGL)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)

namespace L3PGLU27

open CFSG.RankThree.PartTwo.Sec14.L3PGLU

variable {K : Type} [Field K]

@[expose] def fourierBarMat (τ : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 1, 1; 1, τ ^ 2, τ; 1, τ, τ ^ 2]

section FourierLin

variable {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)

include hτ hτ1 in
theorem fourier_mul_bar : fourierMat τ * fourierBarMat τ =
    (3 : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
  have h0 := one_add_tau_add_sq hτ hτ1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fourierMat, fourierBarMat, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | ring1 | linear_combination h0 | linear_combination (-1 : K) * h0 |
      linear_combination (2 : K) * hτ | linear_combination (-2 : K) * hτ |
      linear_combination h0 + τ * hτ

include hτ hτ1 in
theorem bar_mul_fourier : fourierBarMat τ * fourierMat τ =
    (3 : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
  have h0 := one_add_tau_add_sq hτ hτ1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fourierMat, fourierBarMat, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | ring1 | linear_combination h0 | linear_combination (-1 : K) * h0 |
      linear_combination (2 : K) * hτ | linear_combination (-2 : K) * hτ |
      linear_combination h0 + τ * hτ

variable (h3 : (3 : K) ≠ 0)

@[expose] noncomputable def fourierGLlin : GL (Fin 3) K :=
  ⟨fourierMat τ, (3 : K)⁻¹ • fourierBarMat τ,
    by rw [Matrix.mul_smul, fourier_mul_bar hτ hτ1, smul_smul, inv_mul_cancel₀ h3, one_smul],
    by rw [Matrix.smul_mul, bar_mul_fourier hτ hτ1, smul_smul, inv_mul_cancel₀ h3, one_smul]⟩

theorem coe_fourierGLlin :
    ((fourierGLlin hτ hτ1 h3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = fourierMat τ :=
  rfl

theorem coe_fourierGLlin_inv :
    (((fourierGLlin hτ hτ1 h3)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (3 : K)⁻¹ • fourierBarMat τ :=
  rfl

include hτ hτ1 in
theorem fourierLin_conj_mulVec (x : K) :
    (!![0, 1, 0; 0, 0, 1; 1, 0, 0] * (fourierMat τ * diagonal ![x, 1, 1] *
      ((3 : K)⁻¹ • fourierBarMat τ))) *ᵥ ![0, 0, 1] =
      ![(x - 1) / 3, (x + 2) / 3, (x - 1) / 3] := by
  have h0 := one_add_tau_add_sq hτ hτ1
  have e : (!![0, 1, 0; 0, 0, 1; 1, 0, 0] * (fourierMat τ * diagonal ![x, 1, 1] *
      ((3 : K)⁻¹ • fourierBarMat τ))) *ᵥ ![0, 0, 1] =
      (3 : K)⁻¹ • ((!![0, 1, 0; 0, 0, 1; 1, 0, 0] * (fourierMat τ * diagonal ![x, 1, 1] *
        fourierBarMat τ)) *ᵥ ![0, 0, 1]) := by
    simp only [Matrix.mul_smul, Matrix.smul_mulVec]
  rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have e1 : fourierBarMat τ *ᵥ ![0, 0, 1] = ![1, τ, τ ^ 2] := by
    ext i
    fin_cases i <;> simp [fourierBarMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have e2 : diagonal ![x, 1, 1] *ᵥ ![1, τ, τ ^ 2] = ![x, τ, τ ^ 2] := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec_diagonal]
  have e3 : fourierMat τ *ᵥ ![x, τ, τ ^ 2] = ![x - 1, x - 1, x + 2] := by
    ext i
    fin_cases i <;> simp [fourierMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
      first | linear_combination h0 | linear_combination h0 + τ * hτ | linear_combination 2 * hτ
  have e4 : !![0, 1, 0; 0, 0, 1; 1, 0, 0] *ᵥ ![x - 1, x - 1, x + 2] = ![x - 1, x + 2, x - 1] := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  rw [e1, e2, e3, e4]
  ext i
  fin_cases i <;> simp [div_eq_inv_mul]

include hτ hτ1 in
theorem fourierLin_conj_vecMul (y : K) :
    ![0, 0, 1] ᵥ* (fourierMat τ * diagonal ![y, 1, 1] * ((3 : K)⁻¹ • fourierBarMat τ) *
      !![0, 0, 1; 1, 0, 0; 0, 1, 0]) = ![(y - 1) / 3, (y + 2) / 3, (y - 1) / 3] := by
  have h0 := one_add_tau_add_sq hτ hτ1
  have e : ![0, 0, 1] ᵥ* (fourierMat τ * diagonal ![y, 1, 1] * ((3 : K)⁻¹ • fourierBarMat τ) *
      !![0, 0, 1; 1, 0, 0; 0, 1, 0]) = (3 : K)⁻¹ • (![0, 0, 1] ᵥ* (fourierMat τ *
        diagonal ![y, 1, 1] * fourierBarMat τ * !![0, 0, 1; 1, 0, 0; 0, 1, 0])) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.vecMul_smul]
  rw [e, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
  have e1 : ![0, 0, 1] ᵥ* fourierMat τ = ![1, τ ^ 2, τ] := by
    ext i
    fin_cases i <;> simp [fourierMat, Matrix.vecMul, dotProduct, Fin.sum_univ_three]
  have e2 : ![1, τ ^ 2, τ] ᵥ* diagonal ![y, 1, 1] = ![y, τ ^ 2, τ] := by
    ext i
    fin_cases i <;> simp [Matrix.vecMul_diagonal]
  have e3 : ![y, τ ^ 2, τ] ᵥ* fourierBarMat τ = ![y - 1, y - 1, y + 2] := by
    ext i
    fin_cases i <;> simp [fourierBarMat, Matrix.vecMul, dotProduct, Fin.sum_univ_three] <;>
      first | linear_combination h0 | linear_combination h0 + τ * hτ | linear_combination 2 * hτ
  have e4 : ![y - 1, y - 1, y + 2] ᵥ* !![0, 0, 1; 1, 0, 0; 0, 1, 0] = ![y - 1, y + 2, y - 1] := by
    ext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three]
  rw [e1, e2, e3, e4]
  ext i
  fin_cases i <;> simp [div_eq_inv_mul]

end FourierLin

theorem exists_good_of_card₃ [DecidableEq K] (S : Finset K) (hS : 6 ≤ S.card) (a b b' : K) :
    ∃ x ∈ S, x ≠ a ∧ x ≠ b ∧ x ≠ b' ∧ x ^ 2 + 7 * x + 1 ≠ 0 := by
  classical
  set P : Polynomial K := Polynomial.C 1 * Polynomial.X ^ 2 + Polynomial.C 7 * Polynomial.X +
    Polynomial.C 1 with hP
  have hdeg : P.natDegree = 2 := Polynomial.natDegree_quadratic one_ne_zero
  have hP0 : P ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hdeg
    omega
  set B : Finset K := ({a, b, b'} : Finset K) ∪ P.roots.toFinset with hB
  have hBc : B.card ≤ 5 := by
    calc B.card ≤ ({a, b, b'} : Finset K).card + P.roots.toFinset.card := Finset.card_union_le _ _
      _ ≤ 3 + 2 := by
        gcongr
        · exact Finset.card_le_three
        · exact (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' P).trans hdeg.le)
  obtain ⟨x, hxS, hxB⟩ := Finset.exists_mem_notMem_of_card_lt_card (by omega : B.card < S.card)
  refine ⟨x, hxS, fun h => hxB ?_, fun h => hxB ?_, fun h => hxB ?_, fun h => hxB ?_⟩
  · rw [hB, Finset.mem_union]
    left
    simp [h]
  · rw [hB, Finset.mem_union]
    left
    simp [h]
  · rw [hB, Finset.mem_union]
    left
    simp [h]
  · rw [hB, Finset.mem_union, Multiset.mem_toFinset, Polynomial.mem_roots hP0]
    right
    simp [hP, Polynomial.IsRoot, h]

section HessL

variable {p f : ℕ} [Finite K] (hπ : true = false → UnitaryFieldData p f K)
  {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
  (hc : (cycThree : GL (Fin 3) K) ∈ glPi true 3 (p ^ f) K)
  (hd : diagTau hτ ∈ glPi true 3 (p ^ f) K)

omit [Finite K] in
theorem map_conj_cyc_le_lin {Y : Subgroup (projImage (slPi true 3 (p ^ f) K))}
    (hc2 : (cycThree : GL (Fin 3) K) ^ 2 ∈ glPi true 3 (p ^ f) K)
    (hY : Y.map (Res8Hess.conjM' hπ hc2).toMonoidHom ≤ Y) :
    Y.map (Res8Hess.conjM' hπ hc).toMonoidHom ≤ Y := by
  have h3 : ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) ^ 3 = 1 := by
    rw [← map_pow, cycThree_pow_three', map_one]
  rintro _ ⟨y, hy, rfl⟩
  have e : Res8Hess.conjM' hπ hc y =
      Res8Hess.conjM' hπ hc2 (Res8Hess.conjM' hπ hc2 y) := by
    apply Subtype.ext
    rw [Res8Hess.coe_conjM', Res8Hess.coe_conjM', Res8Hess.coe_conjM', map_pow]
    set m := ProjGenLinGroup.mk (cycThree : GL (Fin 3) K)
    have h4 : m ^ 2 * m ^ 2 = m := by
      rw [← pow_add, show 2 + 2 = 3 + 1 by norm_num, pow_succ, h3, one_mul]
    calc m * (y : ProjGenLinGroup (Fin 3) K) * m⁻¹
        = (m ^ 2 * m ^ 2) * (y : ProjGenLinGroup (Fin 3) K) * (m ^ 2 * m ^ 2)⁻¹ := by rw [h4]
      _ = m ^ 2 * (m ^ 2 * (y : ProjGenLinGroup (Fin 3) K) * (m ^ 2)⁻¹) * (m ^ 2)⁻¹ := by group
  change Res8Hess.conjM' hπ hc y ∈ Y
  rw [e]
  exact hY ⟨_, hY ⟨y, hy, rfl⟩, rfl⟩

include hτ1 in
theorem fourierGLlin_mem_normGU (h3 : (3 : K) ≠ 0) :
    fourierGLlin hτ hτ1 h3 ∈
      normGU hπ (sSup (invSet142 (Res8Hess.conjM' hπ hc) (Res8Hess.conjM' hπ hd))) := by
  set F := fourierGLlin hτ hτ1 h3 with hF
  have hFU : F ∈ glPi true 3 (p ^ f) K := mem_glPi_true _ _
  refine ⟨hFU, ?_⟩
  have hc2 : (cycThree : GL (Fin 3) K) ^ 2 ∈ glPi true 3 (p ^ f) K := pow_mem hc 2
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  set τu : Kˣ := Units.mk0 τ hτ0 with hτu
  have hyg : ProjGenLinGroup.mk (diagTau hτ * F) = ProjGenLinGroup.mk (F * cycThree) := by
    rw [ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨τu ^ 2, Units.ext ?_⟩
    rw [Units.val_mul, Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
      coe_fourierGLlin, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
      Matrix.mul_one, fourier_mul_cyc hτ, Units.val_pow_eq_pow_val, Units.val_mk0]
  have hsg : ProjGenLinGroup.mk ((cycThree : GL (Fin 3) K) ^ 2 * F) =
      ProjGenLinGroup.mk (F * diagTau hτ) := by
    rw [ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨τu, Units.ext ?_⟩
    have hc2i : (cycThree : GL (Fin 3) K) ^ 2 = cycThree⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, cycThree_pow_three']
    rw [hc2i, Units.val_mul, Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
      coe_fourierGLlin, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
      Matrix.mul_one, fourier_mul_diagTau hτ, Units.val_mk0]
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun X hX => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  have hX' := L3PGL.map_conjM'_mem_invSet142 hπ hd hc2 hc hd hFU hyg hsg hX
  exact le_sSup ⟨hX'.1, map_conj_cyc_le_lin hπ hc hc2 hX'.2.2, hX'.2.1⟩

include hτ1 in
theorem diagUnits_mem_normGU_lin {x : Kˣ}
    (hx : x ^ (3 * ordCompl[3] (Nat.card K - 1)) = 1) :
    diagUnits 1 1 x ∈
      normGU hπ (sSup (invSet142 (Res8Hess.conjM' hπ hc) (Res8Hess.conjM' hπ hd))) := by
  set N := sSup (invSet142 (Res8Hess.conjM' hπ hc) (Res8Hess.conjM' hπ hd)) with hN
  set Q := normGU hπ N with hQ
  set m := ordCompl[3] (Nat.card K - 1) with hm
  have hcm : ((cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = heisC 1 :=
    L3PGL.coe_cycThree_eq_heisC
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  set τu : Kˣ := Units.mk0 τ hτ0 with hτu
  have hτu' : (τu : K) = τ := rfl
  have hD₁ : diagUnits 1 τu 1 ∈ glPi true 3 (p ^ f) K := mem_glPi_true _ _
  have hcQ : (cycThree : GL (Fin 3) K) ∈ Q := cβ_mem_normGU hπ hτ hc hd
  have hE : diagUnits 1 1 τu ∈ Q := by
    rw [← conj_diagUnits_heisC hcm 1 τu 1]
    exact Q.mul_mem (Q.mul_mem hcQ (d₁_mem_normGU hπ hτ hc hd hcm hτu' hD₁)) (Q.inv_mem hcQ)
  have hm3 : Nat.Coprime m 3 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (Nat.not_dvd_ordCompl Nat.prime_three (by
        have : 1 < Nat.card K := Finite.one_lt_card
        omega)))
  obtain ⟨u, v, huv⟩ : IsCoprime ((3 : ℕ) : ℤ) (m : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr hm3.symm
  have hzpow : ∀ (y : Kˣ) (z : ℤ), y ^ (3 * m) = 1 → y ^ (z * 3 * m) = 1 := by
    intro y z hy
    rw [show z * 3 * (m : ℤ) = ((3 * m : ℕ) : ℤ) * z by push_cast; ring, _root_.zpow_mul,
      zpow_natCast, hy, _root_.one_zpow]
  have hsplit : x = x ^ (u * 3) * x ^ (v * m) := by
    rw [← _root_.zpow_add]
    push_cast at huv
    rw [huv, zpow_one]
  have h3 : diagUnits 1 1 (x ^ (v * m)) ∈ Q := by
    have hx3 : ((x ^ (v * m) : Kˣ) : K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← _root_.zpow_mul,
        show v * (m : ℤ) * ((3 : ℕ) : ℤ) = v * 3 * m by push_cast; ring,
        hzpow x v hx, Units.val_one]
    obtain ⟨k, hk⟩ := exists_pow_eq_of_cube hτ hτ1 hx3
    have hk' : x ^ (v * m) = τu ^ k :=
      Units.ext (by rw [hk, Units.val_pow_eq_pow_val, hτu'])
    rw [hk', show diagUnits (1 : Kˣ) 1 (τu ^ k) = diagUnits 1 1 τu ^ k by
      rw [diagUnits_pow, one_pow]]
    exact Q.pow_mem hE k
  set c := x ^ (u * 3) with hcdef
  have hcm' : c ^ m = 1 := by
    rw [hcdef, ← zpow_natCast, ← _root_.zpow_mul]
    exact hzpow x u hx
  set c' := c ^ u with hc'
  have hc'm : c' ^ m = 1 := by
    rw [hc', ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hcm',
      _root_.one_zpow]
  have hc'3 : c' ^ 3 = c := by
    have e : c' ^ 3 = c ^ (u * 3) := by
      rw [hc', ← zpow_natCast, ← _root_.zpow_mul]
      norm_num
    rw [e]
    have : c ^ (u * 3) = c ^ ((1 : ℤ) - v * m) := by
      congr 1
      push_cast at huv
      linarith
    rw [this, _root_.zpow_sub, zpow_one, show v * (m : ℤ) = ((m : ℕ) : ℤ) * v by ring,
      _root_.zpow_mul, zpow_natCast, hcm', _root_.one_zpow, inv_one, mul_one]
  have hmu : ∀ y : Kˣ, y ^ m = 1 → (y : K) ∈ L3PGL.muM K := fun y hy => by
    rw [L3PGL.mem_muM, ← Units.val_pow_eq_pow_val, ← hm, hy, Units.val_one]
  have hc'0 : (c' : K) ≠ 0 := c'.ne_zero
  have hdet : ((c'⁻¹ : Kˣ) : K) * ((c'⁻¹ : Kˣ) : K) * ((c' ^ 2 : Kˣ) : K) = 1 := by
    rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    field_simp
  set g := CFSG.LieType.SeitzGeneration.diagSL ((c'⁻¹ : Kˣ) : K) ((c'⁻¹ : Kˣ) : K)
    ((c' ^ 2 : Kˣ) : K) hdet with hg
  have hgM : g ∈ L3PGL.diagMuSL K :=
    ⟨_, _, _, hdet, hmu _ (by rw [inv_pow, hc'm, inv_one]), hmu _ (by rw [inv_pow, hc'm, inv_one]),
      hmu _ (by rw [← pow_mul, mul_comm, pow_mul, hc'm, one_pow]), rfl⟩
  have hgN : L3PGL.rhoSL (p ^ f) K g ∈ N :=
    le_sSup (L3PGL.diagMu_mem_invSet142 hπ hτ hc hd hcm) ⟨g, hgM, rfl⟩
  set w : slPi true 3 (p ^ f) K :=
    ⟨Matrix.SpecialLinearGroup.toGL g, (mem_slPi_true _).mpr g.2⟩ with hw
  have hwg : projOf (slPi true 3 (p ^ f) K) w = L3PGL.rhoSL (p ^ f) K g :=
    Subtype.ext (by rw [coe_projOf, L3PGL.coe_rhoSL])
  have hgQ : Matrix.SpecialLinearGroup.toGL g ∈ Q :=
    mem_normGU_of_projOf_mem hπ (x := w) (by rw [hwg]; exact hgN)
  have hc'q : (Matrix.GeneralLinearGroup.scalar (Fin 3) c') ∈ Q :=
    scalar_mem_normGU hπ (mem_glPi_true _ _)
  have hcdiag : diagUnits 1 1 c =
      Matrix.GeneralLinearGroup.scalar (Fin 3) c' * Matrix.SpecialLinearGroup.toGL g := by
    apply Units.ext
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, coe_diagUnits,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hg, ← hc'3]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CFSG.LieType.SeitzGeneration.diagSL, Matrix.scalar_apply]
    all_goals field_simp
  have h3' : diagUnits 1 1 c ∈ Q := by
    rw [hcdiag]
    exact Q.mul_mem hc'q hgQ
  rw [hsplit, show diagUnits (1 : Kˣ) 1 (c * x ^ (v * m)) =
    diagUnits 1 1 c * diagUnits 1 1 (x ^ (v * m)) by rw [diagUnits_mul, one_mul]]
  exact Q.mul_mem h3' h3

include hτ1 in
theorem hessL_top (hK : PiField true p f K) (h9 : p ^ f % 9 = 1) :
    sSup (invSet142 (Res8Hess.conjM' hπ hc) (Res8Hess.conjM' hπ hd)) = ⊤ := by
  classical
  have hfin := finite_pgl (K := K)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact p.Prime := ⟨hK.prime⟩
  have : CharP K p := hK.charP
  have hKq : Nat.card K = p ^ f := by rw [hK.card, piCard, Bool.cond_true]
  set N := sSup (invSet142 (Res8Hess.conjM' hπ hc) (Res8Hess.conjM' hπ hd)) with hN
  set ρ := projOf (slPi true 3 (p ^ f) K) with hρ
  set Q := normGU hπ N with hQ
  set m := ordCompl[3] (p ^ f - 1) with hm
  have hcm : ((cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = heisC 1 :=
    L3PGL.coe_cycThree_eq_heisC
  have hf0 : f ≠ 0 := by
    have := hK.one_le
    omega
  have hq2 : 2 ≤ p ^ f := hK.prime.two_le.trans (Nat.le_self_pow hf0 p)
  have hq4 : 4 ≤ p ^ f := by omega
  have hq : ModThree true (p ^ f) := by
    change p ^ f % 3 = 1
    omega
  obtain ⟨r, hr⟩ := nine_mul_mL_dvd hq2 h9
  obtain ⟨hm2, hsf⟩ := mL_facts hK.prime hf0 h9
  have h3 : (3 : K) ≠ 0 := hK.three_ne_zero hq
  have hcQ : (cycThree : GL (Fin 3) K) ∈ Q := cβ_mem_normGU hπ hτ hc hd
  have hdiag3 : ∀ x : Kˣ, x ^ (3 * m) = 1 → diagUnits 1 1 x ∈ Q := fun x hx =>
    diagUnits_mem_normGU_lin hπ hτ hτ1 hc hd (by rw [hKq]; exact hx)
  have hdiag1 : ∀ x : Kˣ, x ^ (3 * m) = 1 → diagUnits x 1 1 ∈ Q := by
    intro x hx
    rw [← conj_diagUnits_heisC hcm 1 1 x]
    exact Q.mul_mem (Q.mul_mem hcQ (hdiag3 x hx)) (Q.inv_mem hcQ)
  have hscal : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ Q := fun c =>
    scalar_mem_normGU hπ (mem_glPi_true _ _)
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hg₀o : orderOf g₀ = p ^ f - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg₀, Nat.card_units, hKq]
  have hr0 : r ≠ 0 := by
    rintro rfl
    omega
  set au : Kˣ := g₀ ^ r with hau
  have hou : orderOf au = 9 * m := by
    rw [hau, orderOf_pow_of_dvd hr0 (by rw [hg₀o, hr]; exact dvd_mul_left r _), hg₀o, hr,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hr0)]
  have hau9 : au ^ (9 * m) = 1 := by
    rw [← hou]
    exact pow_orderOf_eq_one au
  obtain ⟨a, hadef⟩ : ∃ a : K, (au : K) = a := ⟨_, rfl⟩
  have ha : orderOf a = 9 * m := by rw [← hadef, orderOf_units, hou]
  have ha0 : a ≠ 0 := by
    rw [← hadef]
    exact au.ne_zero
  set x : Kˣ := au⁻¹ ^ 3 with hxdef
  have hx : x ^ (3 * m) = 1 := by
    rw [hxdef, ← pow_mul, show 3 * (3 * m) = 9 * m by ring, inv_pow, hau9, inv_one]
  have hratio : orderOf (a⁻¹ ^ 2 / a) = 3 * m := by
    have e : a⁻¹ ^ 2 / a = (((au ^ 3)⁻¹ : Kˣ) : K) := by
      rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, hadef]
      field_simp
    rw [e, orderOf_units, orderOf_inv, orderOf_pow' _ (by norm_num), hou,
      Nat.gcd_eq_right (dvd_mul_of_dvd_left (by norm_num : 3 ∣ 9) _)]
    omega
  have hxa : (x : K) = a⁻¹ ^ 2 * a⁻¹ := by
    rw [hxdef, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hadef, pow_succ]
  have hH0 : ∃ g ∈ Q, (g : Matrix (Fin 3) (Fin 3) K) = diagonal ![a⁻¹ ^ 2, a, a] := by
    refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) au * diagUnits x 1 1,
      Q.mul_mem (hscal au) (hdiag1 x hx), ?_⟩
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, coe_diagUnits, hadef, hxa]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    all_goals field_simp
  have hH2 : ∃ g ∈ Q, (g : Matrix (Fin 3) (Fin 3) K) = diagonal ![a, a, a⁻¹ ^ 2] := by
    refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) au * diagUnits 1 1 x,
      Q.mul_mem (hscal au) (hdiag3 x hx), ?_⟩
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, coe_diagUnits, hadef, hxa]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    all_goals field_simp
  set F := fourierGLlin hτ hτ1 h3 with hF
  have hFQ : F ∈ Q := fourierGLlin_mem_normGU hπ hτ hτ1 hc hd h3
  set ζ : Kˣ := au ^ 3 with hζ
  have hζo : orderOf ζ = 3 * m := by
    rw [hζ, orderOf_pow' _ (by norm_num), hou,
      Nat.gcd_eq_right (dvd_mul_of_dvd_left (by norm_num : 3 ∣ 9) _)]
    omega
  set S : Finset K := (Finset.range (3 * m)).image (fun k => ((ζ ^ k : Kˣ) : K)) with hS
  have hScard : S.card = 3 * m := by
    rw [hS, Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    have hij' : ζ ^ i = ζ ^ j := Units.ext hij
    exact pow_injOn_Iio_orderOf (by rw [hζo]; exact Finset.mem_range.mp hi)
      (by rw [hζo]; exact Finset.mem_range.mp hj) hij'
  obtain ⟨x₀, hx₀S, hx₀1, hx₀2, hx₀2', hx₀7⟩ :=
    exists_good_of_card₃ S (by omega) 1 (-2) (-2)⁻¹
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx₀S
  set y : Kˣ := ζ ^ k with hy
  have hy3m : y ^ (3 * m) = 1 := by
    rw [hy, ← pow_mul, mul_comm, pow_mul, ← hζo, pow_orderOf_eq_one, one_pow]
  have hdinv : diagUnits y⁻¹ 1 1 = (diagUnits y 1 1)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, diagUnits_mul]
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_diagUnits]
  set z : GL (Fin 3) K := (cycThree : GL (Fin 3) K)⁻¹ * F * diagUnits y 1 1 * F⁻¹ with hz
  have hzQ : z ∈ Q :=
    Q.mul_mem (Q.mul_mem (Q.mul_mem (Q.inv_mem hcQ) hFQ) (hdiag1 y hy3m)) (Q.inv_mem hFQ)
  have hzm : (z : Matrix (Fin 3) (Fin 3) K) = !![0, 1, 0; 0, 0, 1; 1, 0, 0] *
      (fourierMat τ * diagonal ![(y : K), 1, 1] * ((3 : K)⁻¹ • fourierBarMat τ)) := by
    rw [hz, Units.val_mul, Units.val_mul, Units.val_mul, coe_fourierGLlin, coe_fourierGLlin_inv,
      coe_diagUnits]
    simp only [Matrix.mul_assoc, Units.val_one]
    rfl
  have hzi : z⁻¹ = F * diagUnits y⁻¹ 1 1 * F⁻¹ * cycThree := by
    rw [hz, hdinv]
    group
  have hzim : ((z⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      fourierMat τ * diagonal ![((y⁻¹ : Kˣ) : K), 1, 1] * ((3 : K)⁻¹ • fourierBarMat τ) *
        !![0, 0, 1; 1, 0, 0; 0, 1, 0] := by
    rw [hzi, Units.val_mul, Units.val_mul, Units.val_mul, coe_fourierGLlin, coe_fourierGLlin_inv,
      coe_diagUnits, coe_cycThree]
    simp only [Units.val_one]
  have hzw : (z : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1] =
      ![((y : K) - 1) / 3, ((y : K) + 2) / 3, ((y : K) - 1) / 3] := by
    rw [hzm]
    exact fourierLin_conj_mulVec hτ hτ1 (y : K)
  have hzr : ![0, 0, 1] ᵥ* ((z⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ![(((y⁻¹ : Kˣ) : K) - 1) / 3, (((y⁻¹ : Kˣ) : K) + 2) / 3,
        (((y⁻¹ : Kˣ) : K) - 1) / 3] := by
    rw [hzim]
    exact fourierLin_conj_vecMul hτ hτ1 _
  have hyi : ((y⁻¹ : Kˣ) : K) = (y : K)⁻¹ := Units.val_inv_eq_inv_val y
  have hy0 : (y : K) ≠ 0 := y.ne_zero
  have hy1' : (y : K) - 1 ≠ 0 := sub_ne_zero.mpr hx₀1
  have hy2' : (y : K) + 2 ≠ 0 := by
    intro h0
    exact hx₀2 (by linear_combination h0)
  have hyi1 : ((y⁻¹ : Kˣ) : K) - 1 ≠ 0 := by
    rw [hyi]
    intro h0
    apply hx₀1
    have h1 : (y : K)⁻¹ = 1 := by linear_combination h0
    rw [← inv_inv (y : K), h1, inv_one]
  have hyi2 : ((y⁻¹ : Kˣ) : K) + 2 ≠ 0 := by
    rw [hyi]
    intro h0
    apply hx₀2'
    have h1 : (y : K)⁻¹ = -2 := by linear_combination h0
    rw [← h1, inv_inv]
  have hrw2 : (((y⁻¹ : Kˣ) : K) - 1) / 3 * (((y : K) - 1) / 3) ≠ 1 := by
    rw [hyi]
    intro h1
    apply hx₀7
    field_simp at h1
    linear_combination -h1
  have hB := sl2_block_mem_of_generic_lin hKq hq4 ha0 (by rw [ha]; omega) (by rw [hratio]; omega)
    (by rw [hratio]; exact hsf) Q hH0 hH2 hzQ hzw hzr
    (div_ne_zero hy1' h3) (div_ne_zero hy2' h3) (div_ne_zero hy1' h3)
    (div_ne_zero hyi1 h3) (div_ne_zero hyi2 h3) (div_ne_zero hyi1 h3) hrw2
  have hSL := sl3_le_of_block Q hB (s := cycThree) coe_cycThree hcQ
  have hnorm : N.Normal := by
    refine ⟨fun n hn m' => ?_⟩
    obtain ⟨z', rfl⟩ := projOf_surjective _ m'
    have hzQ' : (z' : GL (Fin 3) K) ∈ Q := by
      have h1 := hSL ⟨((z' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
        (mem_slPi_true _).mp z'.2⟩
      have e : SpecialLinearGroup.toGL ⟨((z' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
          (mem_slPi_true _).mp z'.2⟩ = (z' : GL (Fin 3) K) := Units.ext rfl
      rwa [e] at h1
    have hmap := map_le_of_mem_normGU hπ (slPi_le_glPi hπ z'.2) hzQ'
    rw [conjM'_eq_conj hπ z'] at hmap
    exact hmap ⟨n, hn, rfl⟩
  have hsimple : IsSimpleGroup (projImage (slPi true 3 (p ^ f) K)) := by
    have hs := CFSG.Quasithin.Insp9.isSimpleGroup_statedProj_statedSL_three K
    exact (Sec4.Census.statedProjEquivProjImage
      (CFSG.Assembly.LowTwoRank.StatedSL 3 K)
      (P := projImage (slPi true 3 (p ^ f) K)) rfl).symm.isSimpleGroup
  set t : Kˣ := ζ ^ 3 with ht
  have hto : orderOf t = m := by
    rw [ht, orderOf_pow' _ (by norm_num), hζo, Nat.gcd_eq_right (dvd_mul_right 3 _)]
    omega
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hto
    omega
  have htm : t ^ m = 1 := by
    rw [← hto]
    exact pow_orderOf_eq_one t
  have hmu : ∀ s : Kˣ, s ^ m = 1 → (s : K) ∈ L3PGL.muM K := fun s hs => by
    rw [L3PGL.mem_muM, hKq, ← Units.val_pow_eq_pow_val, ← hm, hs, Units.val_one]
  have hdet1 : (t : K) * ((t⁻¹ : Kˣ) : K) * 1 = 1 := by
    rw [mul_one, Units.mul_inv]
  set g := CFSG.LieType.SeitzGeneration.diagSL (t : K) ((t⁻¹ : Kˣ) : K) 1 hdet1 with hg
  have hgM : g ∈ L3PGL.diagMuSL K :=
    ⟨_, _, _, hdet1, hmu t htm, hmu t⁻¹ (by rw [inv_pow, htm, inv_one]), L3PGL.one_mem_muM, rfl⟩
  have hgN : L3PGL.rhoSL (p ^ f) K g ∈ N :=
    le_sSup (L3PGL.diagMu_mem_invSet142 hπ hτ hc hd hcm) ⟨g, hgM, rfl⟩
  set w : slPi true 3 (p ^ f) K :=
    ⟨Matrix.SpecialLinearGroup.toGL g, (mem_slPi_true _).mpr g.2⟩ with hw
  have hwg : ρ w = L3PGL.rhoSL (p ^ f) K g :=
    Subtype.ext (by rw [coe_projOf, L3PGL.coe_rhoSL])
  have hwN : ρ w ∈ N := by
    rw [hwg]
    exact hgN
  have hw1 : ρ w ≠ 1 := by
    intro e
    rw [projOf_eq_one_iff] at e
    obtain ⟨s, hs⟩ := e
    have h00 : (s : K) = t :=
      congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hs
    have h22 : (s : K) = 1 :=
      congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 2 2) hs
    exact ht1 (Units.ext (by rw [← h00, h22, Units.val_one]))
  have := hnorm
  have := hsimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · exact absurd (hbot ▸ hwN : ρ w ∈ (⊥ : Subgroup _)) (by
      rw [Subgroup.mem_bot]
      exact hw1)
  · exact htop

end HessL

end L3PGLU27

open L3PGLU27 L3PGLU Res8Hess in
theorem ks142L3HessGenNineModel_linear (p f : ℕ) (K : Type)
    [Field K] (hK : PiField true p f K) (h9 : p ^ f % 9 = 1) (τ : K) (hτ : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) (dM cM : projImage (slPi true 3 (p ^ f) K))
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ))
    (hcM : (cM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (cycThree : GL (Fin 3) K)) :
    ⨆ (b : projImage (slPi true 3 (p ^ f) K)) (_ : b ∈ Subgroup.zpowers dM ⊔ Subgroup.zpowers cM)
      (_ : b ≠ 1), thetaC b = ⊤ := by
  have hπ : true = false → UnitaryFieldData p f K := fun h => by cases h
  have := hK.finite
  have hfin := finite_pgl (K := K)
  have hq : ModThree true (p ^ f) := by
    change p ^ f % 3 = 1
    omega
  have hcS : (cycThree : GL (Fin 3) K) ∈ slPi true 3 (p ^ f) K := cycThree_mem_slPi hπ
  have hdS : diagTau hτ ∈ slPi true 3 (p ^ f) K :=
    diagTau_mem_slPi hπ (fun h => by cases h) hτ
  have hc : (cycThree : GL (Fin 3) K) ∈ glPi true 3 (p ^ f) K := slPi_le_glPi hπ hcS
  have hd : diagTau hτ ∈ glPi true 3 (p ^ f) K := slPi_le_glPi hπ hdS
  have htop := hessL_top hπ hτ hτ1 hc hd hK h9
  obtain ⟨dM', cM', hdM', hcM', hdc, hdo, hco, hcd⟩ :=
    CFSG.RankThree.PartTwo.Sec19.Step1915WProof.exists_heisPair hK hq hτ hτ1
  have e1 : dM = dM' := Subtype.ext (hdM.trans hdM'.symm)
  have e2 : cM = cM' := Subtype.ext (hcM.trans hcM'.symm)
  subst e1 e2
  set ρ := projOf (slPi true 3 (p ^ f) K) with hρ
  have hρd : ρ ⟨diagTau hτ, hdS⟩ = dM := Subtype.ext (by rw [coe_projOf, hdM])
  have hρc : ρ ⟨cycThree, hcS⟩ = cM := Subtype.ext (by rw [coe_projOf, hcM])
  have hconjd : conjM' hπ hd = MulAut.conj dM := by
    rw [← hρd]
    exact conjM'_eq_conj hπ ⟨diagTau hτ, hdS⟩
  have hconjc : conjM' hπ hc = MulAut.conj cM := by
    rw [← hρc]
    exact conjM'_eq_conj hπ ⟨cycThree, hcS⟩
  rw [eq_top_iff, ← htop]
  refine sSup_le fun X hX => ?_
  obtain ⟨hX3, hXc, hXd⟩ := hX
  rw [hconjc] at hXc
  rw [hconjd] at hXd
  have hEY : Subgroup.zpowers dM ⊔ Subgroup.zpowers cM ≤
      Subgroup.normalizer (X : Set (projImage (slPi true 3 (p ^ f) K))) :=
    sup_le (Subgroup.zpowers_le.mpr (L3PGLU.mem_normalizer_of_map_le hXd))
      (Subgroup.zpowers_le.mpr (L3PGLU.mem_normalizer_of_map_le hXc))
  obtain ⟨b, hb, hb1, hXb⟩ :=
    L3PGL.hess_le_thetaC hτ hτ1 hK hq hdM hcM hdc hdo hco hcd hX3 hEY
  exact le_trans hXb (le_iSup₂_of_le b hb (le_iSup_of_le hb1 le_rfl))

theorem ks142L3HessGenNineModel_proof : KS142L3HessGenNineModel := by
  intro π p f K _ hK hq h9 h28 τ hτ hτ1 dM cM hdM hcM
  cases π
  · exact ks142L3HessGenNineModel_unitary p f K hK hq h9 h28 τ hτ hτ1 dM cM hdM hcM
  · have hq' : p ^ f % 3 = 1 := hq
    exact ks142L3HessGenNineModel_linear p f K hK (by omega) τ hτ hτ1 dM cM hdM hcM

end CFSG.RankThree.PartTwo.Sec14
