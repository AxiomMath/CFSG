module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3AutLin
import CFSG.GH74.GLS.IVK.L2.Fixed
import CFSG.RankThree.PartTwo.Sec12.ONanKS128Diag
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian

public section

namespace CFSG.RankThree.PartTwo.KFacts.KF163L3

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartTwo.Sec17.Proof17Res7
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec12.KS128Move (unitMap coe_unitMap frobGL_diagUnits frobGL_cycThree
  diagUnits_inv diagUnits_pow diagUnits_eq_iff diagUnits_comm scalar_eq_diagUnits)

variable {K : Type} [Field K]

private theorem toGL_map (σ : K ≃+* K) (g : SpecialLinearGroup (Fin 3) K) :
    SpecialLinearGroup.toGL (SpecialLinearGroup.map σ.toRingHom g) =
      frobGL σ (SpecialLinearGroup.toGL g) := by
  apply Units.ext
  rw [SpecialLinearGroup.coe_GL_coe_matrix, SpecialLinearGroup.map_apply_coe, coe_frobGL]
  rfl

private theorem det_coe_diagUnits (a b c : Kˣ) :
    ((diagUnits a b c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = (a : K) * b * c := by
  rw [coe_diagUnits, det_diagonal, Fin.prod_univ_three]
  simp

private theorem fieldAut_dSL (σ : K ≃+* K) {τ : K} (hτ : τ ^ 3 = 1) :
    fieldAut 3 K σ (proj 3 K (dSL hτ)) =
      proj 3 K (dSL (by rw [← map_pow, hτ, map_one] : (σ τ) ^ 3 = 1)) := by
  rw [fieldAut_proj]
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [toGL_map, toGL_dSL]
  apply Units.ext
  rw [coe_frobGL]
  change (diagTau hτ : Matrix (Fin 3) (Fin 3) K).map (σ : K → K) =
    (diagTau (by rw [← map_pow, hτ, map_one] : (σ τ) ^ 3 = 1) : Matrix (Fin 3) (Fin 3) K)
  rw [coe_diagTau, coe_diagTau]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

private theorem fieldAut_cSL (σ : K ≃+* K) :
    fieldAut 3 K σ (proj 3 K (cSL : SpecialLinearGroup (Fin 3) K)) = proj 3 K cSL := by
  rw [fieldAut_proj]
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [toGL_map, toGL_cSL, frobGL_cycThree]

private theorem dualAut_dSL {τ : K} (hτ : τ ^ 3 = 1) :
    dualAut 3 K (proj 3 K (dSL hτ)) = (proj 3 K (dSL hτ))⁻¹ := by
  rw [dualAut_proj, ← map_inv]
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [toGL_transpose_inv_dSL, map_inv, toGL_dSL]

private theorem dualAut_cSL :
    dualAut 3 K (proj 3 K (cSL : SpecialLinearGroup (Fin 3) K)) = proj 3 K cSL := by
  rw [dualAut_proj]
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [toGL_transpose_inv_cSL, toGL_cSL]

private theorem dualAut_y {ζ : Kˣ} {y : SpecialLinearGroup (Fin 3) K}
    (hy : SpecialLinearGroup.toGL y = diagUnits ζ ζ⁻¹ 1) :
    dualAut 3 K (proj 3 K y) = (proj 3 K y)⁻¹ := by
  rw [dualAut_proj, ← map_inv]
  have hd : ((y⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (diagUnits ζ⁻¹ ζ 1 : Matrix (Fin 3) (Fin 3) K) := by
    rw [← SpecialLinearGroup.coe_GL_coe_matrix, map_inv, hy, diagUnits_inv, inv_inv, inv_one]
  congr 1
  apply SpecialLinearGroup.toGL_injective
  apply Units.ext
  rw [SpecialLinearGroup.coe_GL_coe_matrix, SpecialLinearGroup.coe_transpose,
    SpecialLinearGroup.coe_GL_coe_matrix, hd, coe_diagUnits, diagonal_transpose]

private theorem toGL_map_y {σ : K ≃+* K} {ζ : Kˣ} {y : SpecialLinearGroup (Fin 3) K}
    (hy : SpecialLinearGroup.toGL y = diagUnits ζ ζ⁻¹ 1) :
    SpecialLinearGroup.toGL (SpecialLinearGroup.map σ.toRingHom y) =
      diagUnits (unitMap σ ζ) (unitMap σ ζ⁻¹) 1 := by
  rw [toGL_map, hy, frobGL_diagUnits, map_one (unitMap σ)]

private theorem dSL_eq_of_eq {τ τ' : K} (h : τ = τ') (hτ : τ ^ 3 = 1) (hτ' : τ' ^ 3 = 1) :
    dSL hτ = dSL hτ' := by
  apply Subtype.ext
  rw [show ((dSL hτ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    (diagTau hτ : Matrix (Fin 3) (Fin 3) K) from rfl,
    show ((dSL hτ' : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    (diagTau hτ' : Matrix (Fin 3) (Fin 3) K) from rfl,
    coe_diagTau, coe_diagTau, h]

private theorem eq_one_of_dSL_one {h : (1 : K) ^ 3 = 1} :
    (dSL h : SpecialLinearGroup (Fin 3) K) = 1 := by
  apply SpecialLinearGroup.toGL_injective
  rw [toGL_dSL, map_one]
  apply Units.ext
  rw [coe_diagTau, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem pow_two_cube {τ : K} (hτ : τ ^ 3 = 1) : (τ ^ 2) ^ 3 = 1 := by
  rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hτ, one_pow]

private theorem dSL_sq {τ : K} (hτ : τ ^ 3 = 1) {hτ' : (τ ^ 2) ^ 3 = 1} :
    (dSL hτ' : SpecialLinearGroup (Fin 3) K) = (dSL hτ)⁻¹ := by
  have hp : diagTau hτ ^ 2 = (diagTau hτ)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, show 2 + 1 = 3 from rfl, diagTau_pow_three hτ]
  apply SpecialLinearGroup.toGL_injective
  rw [toGL_dSL, map_inv, toGL_dSL, ← hp]
  apply Units.ext
  rw [coe_diagTau_pow, coe_diagTau]

private theorem dSL_ne_one {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    proj 3 K (dSL hτ) ≠ 1 := by
  intro h
  obtain ⟨c, -, hmat⟩ := mem_scalars.mp (proj_eq_one_iff.mp h)
  have hmat' : (diagTau hτ : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) (c : K) := hmat
  rw [coe_diagTau, Matrix.scalar_apply] at hmat'
  have h00 := congrFun (congrFun hmat' 0) 0
  have h22 := congrFun (congrFun hmat' 2) 2
  simp at h00 h22
  exact hτ1 (by rw [h00, h22])

private theorem fieldAut_dSL_trichotomy (σ : K ≃+* K) {τ : K} (hτ : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) :
    fieldAut 3 K σ (proj 3 K (dSL hτ)) = proj 3 K (dSL hτ) ∨
      fieldAut 3 K σ (proj 3 K (dSL hτ)) = (proj 3 K (dSL hτ))⁻¹ ∨
      fieldAut 3 K σ (proj 3 K (dSL hτ)) = 1 := by
  have hστ : (σ τ) ^ 3 = 1 := by rw [← map_pow, hτ, map_one]
  rw [fieldAut_dSL (σ := σ) (τ := τ) hτ]
  rcases eq_one_or_eq_tau_or_eq_tau_sq hτ hτ1 hστ with h | h | h
  · refine Or.inr (Or.inr ?_)
    rw [dSL_eq_of_eq h hστ (by norm_num : (1 : K) ^ 3 = 1), eq_one_of_dSL_one, map_one]
  · exact Or.inl (by rw [dSL_eq_of_eq h hστ hτ])
  · refine Or.inr (Or.inl ?_)
    rw [dSL_eq_of_eq h hστ (pow_two_cube hτ), dSL_sq hτ, map_inv]

private theorem cycThree_pow_mod (j : ℕ) :
    (cycThree : GL (Fin 3) K) ^ j = cycThree ^ (j % 3) := by
  conv_lhs => rw [← Nat.div_add_mod j 3]
  rw [pow_add, pow_mul, cycThree_pow_three, one_pow, one_mul]

private theorem cycThree_inv_pow_mod_aux (j : ℕ) :
    ((cycThree : GL (Fin 3) K)⁻¹) ^ j = (cycThree⁻¹) ^ (j % 3) := by
  have h : ((cycThree : GL (Fin 3) K)⁻¹) ^ 3 = 1 := by
    rw [inv_pow, cycThree_pow_three, inv_one]
  conv_lhs => rw [← Nat.div_add_mod j 3]
  rw [pow_add, pow_mul, h, one_pow, one_mul]

private theorem cycThree_inv_pow_mod (j : ℕ) :
    ((cycThree : GL (Fin 3) K) ^ j)⁻¹ = (cycThree⁻¹) ^ (j % 3) := by
  rw [← inv_pow, cycThree_inv_pow_mod_aux]

private theorem cycThree_sq : (cycThree : GL (Fin 3) K) ^ 2 = cycThree⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pow_succ, show 2 + 1 = 3 from rfl, cycThree_pow_three]

private theorem cycThree_inv_sq : ((cycThree : GL (Fin 3) K)⁻¹) ^ 2 = cycThree := by
  rw [inv_pow, cycThree_sq, inv_inv]

private theorem diagUnits_conj_self (a b c a' b' c' : Kˣ) :
    (diagUnits a b c : GL (Fin 3) K) * diagUnits a' b' c' * (diagUnits a b c)⁻¹ =
      diagUnits a' b' c' := by
  rw [diagUnits_comm a b c a' b' c', mul_assoc, mul_inv_cancel, mul_one]

private theorem eta_eq_zeta_or_cube {τ : K} (hτ : τ ^ 3 = 1) {ζ η u : Kˣ} {m j : ℕ}
    (h : diagTau hτ ^ m * cycThree ^ j * diagUnits η η⁻¹ 1 *
        (diagTau hτ ^ m * cycThree ^ j)⁻¹ =
          GeneralLinearGroup.scalar (Fin 3) u * diagUnits ζ ζ⁻¹ 1) :
    (η = ζ ∧ j % 3 = 0) ∨ ζ ^ 3 = 1 := by
  have hτ0 : τ ≠ 0 := tau_ne_zero hτ
  set T : Kˣ := Units.mk0 τ hτ0 with hT
  have hDm : diagTau hτ ^ m = diagUnits (T ^ m) ((T ^ 2) ^ m) 1 := by
    rw [diagTau_eq_diagUnits hτ hτ0, ← hT, diagUnits_pow, one_pow]
  have h1 : diagTau hτ ^ m * (cycThree ^ j * diagUnits η η⁻¹ 1 * (cycThree ^ j)⁻¹) *
      (diagTau hτ ^ m)⁻¹ = GeneralLinearGroup.scalar (Fin 3) u * diagUnits ζ ζ⁻¹ 1 := by
    have e : diagTau hτ ^ m * (cycThree ^ j * diagUnits η η⁻¹ 1 * (cycThree ^ j)⁻¹) *
        (diagTau hτ ^ m)⁻¹ = diagTau hτ ^ m * cycThree ^ j * diagUnits η η⁻¹ 1 *
          (diagTau hτ ^ m * cycThree ^ j)⁻¹ := by group
    rw [e, h]
  rw [cycThree_inv_pow_mod, cycThree_pow_mod] at h1
  rw [hDm, scalar_eq_diagUnits, diagUnits_mul] at h1
  have hj : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases hj with h3 | h3 | h3
  · rw [h3] at h1
    simp only [pow_zero, one_mul, inv_one, mul_one] at h1
    rw [diagUnits_conj_self, diagUnits_eq_iff] at h1
    obtain ⟨h1a, -, h1c⟩ := h1
    have hu : u = 1 := h1c.symm
    rw [hu, one_mul] at h1a
    exact Or.inl ⟨h1a, h3⟩
  · rw [h3] at h1
    simp only [pow_one, mul_one] at h1
    rw [cycThree_conj_diagUnits, diagUnits_conj_self, diagUnits_eq_iff] at h1
    obtain ⟨h1a, h1b, h1c⟩ := h1
    have hu : u = ζ⁻¹ := by
      calc u = u * ζ * ζ⁻¹ := by group
        _ = 1 * ζ⁻¹ := by rw [← h1a]
        _ = ζ⁻¹ := one_mul _
    have hη : η = ζ := by
      have h3' : u = η⁻¹ := h1c.symm
      exact inv_injective (h3'.symm.trans hu)
    right
    rw [hη, hu] at h1b
    have hsq : ζ ^ 2 = ζ⁻¹ := by
      have hmul : ζ * ζ = (ζ⁻¹ * ζ⁻¹) * ζ := congrArg (· * ζ) h1b
      calc ζ ^ 2 = ζ * ζ := pow_two ζ
        _ = (ζ⁻¹ * ζ⁻¹) * ζ := hmul
        _ = ζ⁻¹ := by rw [mul_assoc, inv_mul_cancel, mul_one]
    calc ζ ^ 3 = ζ ^ 2 * ζ := by rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ]
      _ = ζ⁻¹ * ζ := by rw [hsq]
      _ = 1 := inv_mul_cancel ζ
  · rw [h3] at h1
    simp only [mul_one] at h1
    rw [cycThree_sq, cycThree_inv_sq, cycThree_inv_conj_diagUnits, diagUnits_conj_self,
      diagUnits_eq_iff] at h1
    obtain ⟨h1a, h1b, h1c⟩ := h1
    have hu : u = ζ := by
      calc u = u * ζ⁻¹ * ζ := by group
        _ = 1 * ζ := by rw [← h1b]
        _ = ζ := one_mul _
    have hη : η = ζ := by rw [h1c, hu]
    right
    rw [hη, hu] at h1a
    calc ζ ^ 3 = ζ ^ 2 * ζ := by rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ]
      _ = (ζ * ζ) * ζ := by rw [pow_two]
      _ = ζ⁻¹ * ζ := by rw [← h1a]
      _ = 1 := inv_mul_cancel ζ

private theorem eta_eq_zeta_of_conj {τ : K} (hτ : τ ^ 3 = 1) {ζ η : Kˣ}
    {y z : SpecialLinearGroup (Fin 3) K} {m j : ℕ}
    (hy : SpecialLinearGroup.toGL y = diagUnits ζ ζ⁻¹ 1)
    (hz : SpecialLinearGroup.toGL z = diagUnits η η⁻¹ 1)
    (h : MulAut.conj ((proj 3 K (dSL hτ)) ^ m * (proj 3 K cSL) ^ j) (proj 3 K z) =
      proj 3 K y) :
    (η = ζ ∧ j % 3 = 0) ∨ ζ ^ 3 = 1 := by
  have h' : conjAut 3 K (SpecialLinearGroup.toGL ((dSL hτ) ^ m * cSL ^ j))
      (proj 3 K z) = proj 3 K y := by
    rw [conjAut_toGL, map_mul, map_pow, map_pow]
    exact h
  obtain ⟨u, hu⟩ := exists_scalar_of_conjAut_eq h'
  have hW : SpecialLinearGroup.toGL ((dSL hτ) ^ m * cSL ^ j) =
      diagTau hτ ^ m * cycThree ^ j := by
    rw [map_mul, map_pow, map_pow, toGL_dSL, toGL_cSL]
  rw [hW, hz, hy] at hu
  exact eta_eq_zeta_or_cube (hτ := hτ) (ζ := ζ) (η := η) (u := u) (m := m) (j := j) hu

private theorem sigma_zeta_and_mod_of_conj {τ : K} (hτ : τ ^ 3 = 1) {ζ : Kˣ}
    (hζ3 : ¬ ζ ^ 3 = 1) {σ : K ≃+* K} {ε : ℕ} (hε : ε ≤ 1)
    {y : SpecialLinearGroup (Fin 3) K} (hy : SpecialLinearGroup.toGL y = diagUnits ζ ζ⁻¹ 1)
    {m j : ℕ}
    (h : MulAut.conj ((proj 3 K (dSL hτ)) ^ m * (proj 3 K cSL) ^ j)
      ((fieldAut 3 K σ * dualAut 3 K ^ ε) (proj 3 K y)) = proj 3 K y) :
    (σ ζ = ζ ∨ σ ζ = ζ⁻¹) ∧ j % 3 = 0 := by
  have hε' : ε = 0 ∨ ε = 1 := by omega
  rcases hε' with rfl | rfl
  · set v : SpecialLinearGroup (Fin 3) K := SpecialLinearGroup.map σ.toRingHom y with hv
    have hvgl : SpecialLinearGroup.toGL v = diagUnits (unitMap σ ζ) ((unitMap σ ζ)⁻¹) 1 := by
      rw [hv, toGL_map_y hy, map_inv (unitMap σ) ζ]
    have hγ : (fieldAut 3 K σ * dualAut 3 K ^ 0) (proj 3 K y) = proj 3 K v := by
      rw [pow_zero, mul_one, hv]
      exact fieldAut_proj σ y
    rw [hγ] at h
    obtain ⟨hη, hj0⟩ := (eta_eq_zeta_of_conj hτ hy hvgl h).resolve_right hζ3
    refine ⟨Or.inl ?_, hj0⟩
    have h2 := congrArg (fun x : Kˣ => (x : K)) hη
    simpa [coe_unitMap] using h2
  · set v : SpecialLinearGroup (Fin 3) K := (SpecialLinearGroup.map σ.toRingHom y)⁻¹ with hv
    have hvgl : SpecialLinearGroup.toGL v = diagUnits (unitMap σ ζ)⁻¹ ((unitMap σ ζ)⁻¹)⁻¹ 1 := by
      rw [hv]
      have h1 : SpecialLinearGroup.toGL ((SpecialLinearGroup.map σ.toRingHom y)⁻¹) =
          (diagUnits (unitMap σ ζ) ((unitMap σ ζ)⁻¹) 1)⁻¹ := by
        rw [map_inv (SpecialLinearGroup.toGL) (SpecialLinearGroup.map σ.toRingHom y),
          toGL_map_y hy, map_inv (unitMap σ) ζ]
      rw [h1, diagUnits_inv, inv_one, inv_inv]
    have hγ : (fieldAut 3 K σ * dualAut 3 K ^ 1) (proj 3 K y) = proj 3 K v := by
      rw [pow_one, hv]
      exact (calc fieldAut 3 K σ (dualAut 3 K (proj 3 K y))
          = fieldAut 3 K σ (proj 3 K y⁻¹) := by rw [dualAut_y hy, map_inv (proj 3 K) y]
        _ = proj 3 K (SpecialLinearGroup.map σ.toRingHom y⁻¹) := fieldAut_proj σ y⁻¹
        _ = proj 3 K (SpecialLinearGroup.map σ.toRingHom y)⁻¹ :=
            congrArg (proj 3 K) (map_inv (SpecialLinearGroup.map σ.toRingHom) y))
    rw [hγ] at h
    obtain ⟨hη, hj0⟩ := (eta_eq_zeta_of_conj hτ hy hvgl h).resolve_right hζ3
    refine ⟨Or.inr ?_, hj0⟩
    have h2 : unitMap σ ζ = ζ⁻¹ := by
      calc unitMap σ ζ = ((unitMap σ ζ)⁻¹)⁻¹ := (inv_inv _).symm
        _ = ζ⁻¹ := by rw [hη]
    have h3 := congrArg (fun x : Kˣ => (x : K)) h2
    simpa [coe_unitMap] using h3

private theorem not_three_dvd_of_pow_mod {p f : ℕ} (hq : p ^ f % 3 = 1) (h9 : p ^ f % 9 ≠ 1) :
    ¬ 3 ∣ f := by
  rintro ⟨e, rfl⟩
  apply h9
  have hpow : p ^ (3 * e) = (p ^ e) ^ 3 := by
    rw [show 3 * e = e * 3 from by ring, pow_mul]
  rw [hpow] at hq ⊢
  set r := p ^ e with hr
  have hr3 : r % 3 = 1 := by
    have hlt : r % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have h : (r % 3) ^ 3 % 3 = 1 := by
      rw [← Nat.pow_mod]
      exact hq
    have h0 : r % 3 ≠ 0 := by
      intro h0
      rw [h0] at h
      norm_num at h
    have h2 : r % 3 ≠ 2 := by
      intro h2
      rw [h2] at h
      norm_num at h
    omega
  obtain ⟨k, hk⟩ : ∃ k, r = 3 * k + 1 := by
    have := Nat.div_add_mod r 3
    exact ⟨r / 3, by omega⟩
  rw [hk]
  have hcube : (3 * k + 1) ^ 3 = 9 * (k + 3 * k ^ 2 + 3 * k ^ 3) + 1 := by ring
  rw [hcube, Nat.add_comm, Nat.add_mul_mod_self_left]

private theorem two_pow_factorization_not_dvd {q r : ℕ} (hr : 3 ≤ r) (hro : r % 2 = 1)
    (hq : q = r ^ 2) :
    ¬ 2 ^ (q - 1).factorization 2 ∣ r - 1 ∧ ¬ 2 ^ (q - 1).factorization 2 ∣ r + 1 := by
  have hq1 : q - 1 = (r - 1) * (r + 1) := by
    rw [hq, mul_comm (r - 1) (r + 1), ← sq_tsub_sq r 1, one_pow]
  have hne1 : r - 1 ≠ 0 := by omega
  have hne2 : r + 1 ≠ 0 := by omega
  have hfac : (q - 1).factorization 2 =
      (r - 1).factorization 2 + (r + 1).factorization 2 := by
    rw [hq1, Nat.factorization_mul hne1 hne2]
    rfl
  have hd1 : 2 ∣ r - 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  have hd2 : 2 ∣ r + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  have hp1 : 1 ≤ (r - 1).factorization 2 :=
    (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hne1).mp hd1
  have hp2 : 1 ≤ (r + 1).factorization 2 :=
    (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hne2).mp hd2
  constructor
  · intro h
    have hle : (q - 1).factorization 2 ≤ (r - 1).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne1).mp h
    omega
  · intro h
    have hle : (q - 1).factorization 2 ≤ (r + 1).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne2).mp h
    omega

private theorem two_dvd_pow_sub_one {p f : ℕ} (hp2 : p ≠ 2) (hp : p.Prime) (hf : 1 ≤ f) :
    2 ∣ p ^ f - 1 := by
  have hpodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have hmod : p ^ f % 2 = 1 := by
    rw [Nat.pow_mod, hpodd]
    norm_num
  have hrepr : p ^ f = 2 * (p ^ f / 2) + 1 := by
    have := Nat.div_add_mod (p ^ f) 2
    omega
  refine ⟨p ^ f / 2, ?_⟩
  have h2 : 2 ≤ p ^ f := le_trans hp.two_le (by simpa using Nat.pow_le_pow_right hp.pos hf)
  omega

private theorem one_le_factorization_two {p f : ℕ} (hp2 : p ≠ 2) (hp : p.Prime) (hf : 1 ≤ f) :
    1 ≤ (p ^ f - 1).factorization 2 := by
  have h2 := two_dvd_pow_sub_one hp2 hp hf
  have hne : p ^ f - 1 ≠ 0 := by
    have : 2 ≤ p ^ f := le_trans hp.two_le (by simpa using Nat.pow_le_pow_right hp.pos hf)
    omega
  exact (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hne).mp h2

private theorem zeta_cube_ne_one {ζ : Kˣ} {a : ℕ} (ha : 1 ≤ a) (hζ : orderOf ζ = 2 ^ a) :
    ζ ^ 3 ≠ 1 := by
  intro h
  have h1 : orderOf ζ ∣ 3 := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf ζ ∣ 2 ^ a := by rw [← hζ]
  have hgcd : Nat.Coprime 3 (2 ^ a) := Nat.Coprime.pow_right a (by norm_num)
  have hone : orderOf ζ = 1 := by
    have h3 : orderOf ζ ∣ Nat.gcd 3 (2 ^ a) := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.gcd_eq_one hgcd] at h3
    exact Nat.dvd_one.mp h3
  rw [hζ] at hone
  have hgt : 1 < 2 ^ a := one_lt_pow' (by norm_num : 1 < (2 : ℕ)) (by omega : a ≠ 0)
  omega

private theorem zeta_pow_cases {σ : K ≃+* K} {ζ : K}
    (h : σ ζ = ζ ∨ σ ζ = ζ⁻¹) (n : ℕ) :
    (σ ^ n) ζ = ζ ∨ (σ ^ n) ζ = ζ⁻¹ := by
  induction n with
  | zero => left; simp
  | succ n ih =>
    rw [pow_succ]
    change (σ ^ n) (σ ζ) = ζ ∨ (σ ^ n) (σ ζ) = ζ⁻¹
    rcases ih with h1 | h1
    · rcases h with h2 | h2
      · left; rw [h2, h1]
      · right; rw [h2, map_inv₀, h1]
    · rcases h with h2 | h2
      · right; rw [h2, h1]
      · left; rw [h2, map_inv₀, h1, inv_inv]

private theorem false_of_sigma_ne_one [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) {σ : K ≃+* K} (hσ1 : σ ≠ 1) {ζ : Kˣ}
    (hζ : orderOf ζ = 2 ^ (p ^ f - 1).factorization 2)
    (hσζ : σ (ζ : K) = (ζ : K) ∨ σ (ζ : K) = ((ζ : K))⁻¹)
    {k : ℕ} (hσpow : σ ^ 2 ^ (k + 1) = 1) : False := by
  have hdvd : orderOf σ ∣ 2 ^ (k + 1) := orderOf_dvd_of_pow_eq_one hσpow
  obtain ⟨e, he, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hj
    exact hσ1 (orderOf_eq_one_iff.mp hj)
  set ρ : K ≃+* K := σ ^ 2 ^ (e - 1) with hρ
  have hρord : orderOf ρ = 2 := by
    have h2 : 2 ^ e = 2 * 2 ^ (e - 1) := by
      conv_lhs => rw [show e = e - 1 + 1 from by omega]
      rw [pow_succ']
    have h3 : 2 ^ e / 2 ^ (e - 1) = 2 := by
      rw [h2]
      exact Nat.mul_div_cancel 2 (by positivity)
    rw [hρ, orderOf_pow, hj, Nat.gcd_eq_right (Nat.pow_dvd_pow 2 (by omega))]
    exact h3
  have hρ1 : ρ ≠ 1 := by
    intro h
    have h1 : orderOf ρ = 1 := by rw [h, orderOf_one]
    omega
  have hρsq : ρ * ρ = 1 := by rw [← pow_two, ← hρord, pow_orderOf_eq_one]
  obtain ⟨hfe, hρpow⟩ := even_and_eq_pow_of_involution_prime hp hf hK hρ1 hρsq
  have hρζ : ρ (ζ : K) = (ζ : K) ∨ ρ (ζ : K) = ((ζ : K))⁻¹ := by
    rw [hρ]
    exact zeta_pow_cases hσζ (2 ^ (e - 1))
  obtain ⟨e2, hfe2⟩ : ∃ e2, f = 2 * e2 := by
    obtain ⟨e2, rfl⟩ := hfe
    exact ⟨e2, by ring⟩
  have he2 : 1 ≤ e2 := by
    rcases Nat.eq_zero_or_pos e2 with h | h
    · rw [hfe2, h] at hf
      omega
    · exact h
  have hdiv : f / 2 = e2 := by
    rw [hfe2]
    exact Nat.mul_div_right e2 (by norm_num)
  have hpe : p ^ f = (p ^ e2) ^ 2 := by
    rw [hfe2, show 2 * e2 = e2 * 2 from by ring, pow_mul]
  have hrodd : p ^ e2 % 2 = 1 := by
    rw [Nat.pow_mod]
    have hpodd : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · exact absurd h hp2
      · exact h
    rw [hpodd, one_pow]
    norm_num
  have hr3 : 3 ≤ p ^ e2 := by
    have hp3 : 3 ≤ p := by
      have h2 := hp.two_le
      omega
    exact le_trans hp3 (by simpa using Nat.pow_le_pow_right hp.pos he2)
  have hdvd' : 2 ^ (p ^ f - 1).factorization 2 ∣ p ^ e2 - 1 ∨
      2 ^ (p ^ f - 1).factorization 2 ∣ p ^ e2 + 1 := by
    rcases hρζ with hplus | hminus
    · left
      have hpζ : (ζ : K) ^ p ^ e2 = (ζ : K) := by
        have h1 : ρ (ζ : K) = (ζ : K) ^ p ^ (f / 2) := hρpow (ζ : K)
        rw [hdiv] at h1
        rw [← h1]
        exact hplus
      have hr1 : (ζ : K) ^ (p ^ e2 - 1) = 1 := by
        have hrge : 1 ≤ p ^ e2 := Nat.one_le_pow e2 p hp.pos
        have h2 : (ζ : K) ^ (p ^ e2 - 1) * (ζ : K) = 1 * (ζ : K) := by
          rw [← pow_succ, Nat.sub_add_cancel hrge, hpζ, one_mul]
        exact mul_right_cancel₀ ζ.ne_zero h2
      have hr1' : ζ ^ (p ^ e2 - 1) = 1 := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_one]
        exact hr1
      rw [← hζ]
      exact orderOf_dvd_of_pow_eq_one hr1'
    · right
      have hpζ : (ζ : K) ^ p ^ e2 = ((ζ : K))⁻¹ := by
        have h1 : ρ (ζ : K) = (ζ : K) ^ p ^ (f / 2) := hρpow (ζ : K)
        rw [hdiv] at h1
        rw [← h1]
        exact hminus
      have hr1 : (ζ : K) ^ (p ^ e2 + 1) = 1 := by
        rw [pow_succ, hpζ, inv_mul_cancel₀ ζ.ne_zero]
      have hr1' : ζ ^ (p ^ e2 + 1) = 1 := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_one]
        exact hr1
      rw [← hζ]
      exact orderOf_dvd_of_pow_eq_one hr1'
  rcases two_pow_factorization_not_dvd hr3 hrodd hpe with ⟨h1, h2⟩
  rcases hdvd' with h | h
  · exact h1 h
  · exact h2 h

private theorem exists_conjAut_eq_and_fix_dSL {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {A : GL (Fin 3) K} {γ : MulAut (projectiveSL 3 K)} {σ : K ≃+* K} {ε : ℕ}
    (hε : ε ≤ 1) (hγ : γ = fieldAut 3 K σ * dualAut 3 K ^ ε)
    (hd : (conjAut 3 K A * γ) (proj 3 K (dSL hτ)) = proj 3 K (dSL hτ))
    (hc : (conjAut 3 K A * γ) (proj 3 K cSL) = proj 3 K cSL) :
    γ (proj 3 K (dSL hτ)) = proj 3 K (dSL hτ) ∧
      ∃ m j : ℕ, conjAut 3 K A =
        MulAut.conj ((proj 3 K (dSL hτ)) ^ m * (proj 3 K cSL) ^ j) := by
  have hγc : γ (proj 3 K cSL) = proj 3 K cSL := by
    have h1 : (dualAut 3 K ^ ε) (proj 3 K cSL) = proj 3 K cSL := by
      have hε' : ε = 0 ∨ ε = 1 := by omega
      rcases hε' with rfl | rfl
      · rw [pow_zero]; rfl
      · rw [pow_one]; exact dualAut_cSL
    rw [hγ, MulAut.mul_apply, h1]
    exact fieldAut_cSL σ
  have hγd : γ (proj 3 K (dSL hτ)) = proj 3 K (dSL hτ) ∨
      γ (proj 3 K (dSL hτ)) = (proj 3 K (dSL hτ))⁻¹ ∨
      γ (proj 3 K (dSL hτ)) = 1 := by
    have hε' : ε = 0 ∨ ε = 1 := by omega
    rcases hε' with rfl | rfl
    · rw [hγ, pow_zero, mul_one]
      exact fieldAut_dSL_trichotomy σ hτ hτ1
    · have hinv : γ (proj 3 K (dSL hτ)) =
          (fieldAut 3 K σ (proj 3 K (dSL hτ)))⁻¹ := by
        have hstep : (fieldAut 3 K σ * dualAut 3 K) (proj 3 K (dSL hτ)) =
            fieldAut 3 K σ (dualAut 3 K (proj 3 K (dSL hτ))) := rfl
        rw [hγ, pow_one, hstep, dualAut_dSL hτ, map_inv]
      rw [hinv]
      rcases fieldAut_dSL_trichotomy σ hτ hτ1 with h | h | h
      · right; left; rw [h]
      · left; rw [h, inv_inv]
      · right; right; rw [h, inv_one]
  have hAd : conjAut 3 K A (γ (proj 3 K (dSL hτ))) = proj 3 K (dSL hτ) := by
    simpa only [MulAut.mul_apply] using hd
  have hAc : conjAut 3 K A (proj 3 K cSL) = proj 3 K cSL := by
    have h := hc
    rw [MulAut.mul_apply, hγc] at h
    exact h
  have hγd_eq : γ (proj 3 K (dSL hτ)) = proj 3 K (dSL hτ) := by
    rcases hγd with h1 | h1 | h1
    · exact h1
    · exfalso
      have h1' : γ (proj 3 K (dSL hτ)) = proj 3 K ((dSL hτ)⁻¹) := by rw [h1, ← map_inv]
      have hAd' : conjAut 3 K A (proj 3 K ((dSL hτ)⁻¹)) = proj 3 K (dSL hτ) := by
        rw [← h1']; exact hAd
      obtain ⟨u, hu⟩ := exists_scalar_of_conjAut_eq hAd'
      obtain ⟨v, hv⟩ := exists_scalar_of_conjAut_eq hAc
      rw [map_inv, toGL_dSL] at hu
      rw [toGL_cSL] at hv
      exact false_of_conj_inv_hessian hτ hτ1 hu hv
    · exfalso
      have h1' : (1 : projectiveSL 3 K) = proj 3 K (dSL hτ) := by
        rw [← hAd, h1, map_one]
      exact dSL_ne_one hτ hτ1 h1'.symm
  obtain ⟨m, j, hA⟩ : ∃ m j : ℕ, conjAut 3 K A =
      MulAut.conj ((proj 3 K (dSL hτ)) ^ m * (proj 3 K cSL) ^ j) := by
    have hAd' : conjAut 3 K A (proj 3 K (dSL hτ)) = proj 3 K (dSL hτ) := by
      simpa [hγd_eq] using hAd
    obtain ⟨u, hu⟩ := exists_scalar_of_conjAut_eq hAd'
    obtain ⟨v, hv⟩ := exists_scalar_of_conjAut_eq hAc
    rw [toGL_dSL] at hu
    rw [toGL_cSL] at hv
    obtain ⟨s, m, j, hAeq⟩ := exists_eq_of_conj_hessian hτ hτ1 hu hv
    exact ⟨m, j, by
      rw [hAeq, map_mul, map_mul, conjAut_scalar, one_mul, map_pow, map_pow, ← toGL_dSL hτ,
        ← toGL_cSL, conjAut_toGL, conjAut_toGL, map_mul, map_pow, map_pow]⟩
  exact ⟨hγd_eq, m, j, hA⟩

theorem eq_one_of_pow_two_projectiveSL {K : Type} [Field K] [Finite K] {p f : ℕ}
    [Fact p.Prime] (hK : Nat.card K = p ^ f) (hp2 : p ≠ 2) (hq : p ^ f % 3 = 1)
    (h9 : p ^ f % 9 ≠ 1) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {ζ : Kˣ}
    (hζ : orderOf ζ = 2 ^ (p ^ f - 1).factorization 2) {y : SpecialLinearGroup (Fin 3) K}
    (hy : SpecialLinearGroup.toGL y = diagUnits ζ ζ⁻¹ 1) (β : MulAut (projectiveSL 3 K))
    (hd : β (proj 3 K (dSL hτ)) = proj 3 K (dSL hτ)) (hc : β (proj 3 K cSL) = proj 3 K cSL)
    (hyβ : β (proj 3 K y) = proj 3 K y) {k : ℕ} (hk : β ^ 2 ^ k = 1) : β = 1 := by
  classical
  have hp : p.Prime := Fact.out
  have h2card : 2 ≤ Nat.card K := by
    haveI := Fintype.ofFinite K
    have h := Fintype.one_lt_card (α := K)
    rw [Nat.card_eq_fintype_card]
    omega
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · rw [h, pow_zero] at hK
      omega
    · exact h
  have h3f : ¬ 3 ∣ f := not_three_dvd_of_pow_mod hq h9
  obtain ⟨A, σ, ε, hε, hβ⟩ := (automorphism_generation (K := K) (n := 3) le_rfl).2 β
  set γ : MulAut (projectiveSL 3 K) := fieldAut 3 K σ * dualAut 3 K ^ ε with hγdef
  have hβ' : β = conjAut 3 K A * γ := by rw [hβ, hγdef, mul_assoc]
  have hd0 : (conjAut 3 K A * γ) (proj 3 K (dSL hτ)) = proj 3 K (dSL hτ) := by
    rw [← hβ']; exact hd
  have hc0 : (conjAut 3 K A * γ) (proj 3 K cSL) = proj 3 K cSL := by
    rw [← hβ']; exact hc
  obtain ⟨hγd_eq, m, j, hA⟩ := exists_conjAut_eq_and_fix_dSL hτ hτ1 hε hγdef hd0 hc0
  have hζa : 1 ≤ (p ^ f - 1).factorization 2 := one_le_factorization_two hp2 hp hf
  have hζ3 : ¬ ζ ^ 3 = 1 := zeta_cube_ne_one hζa hζ
  have hσζ : (σ ζ = ζ ∨ σ ζ = ζ⁻¹) ∧ j % 3 = 0 := by
    refine sigma_zeta_and_mod_of_conj (m := m) (j := j) hτ hζ3 hε hy ?_
    have h := hyβ
    rw [hβ', hA, MulAut.mul_apply] at h
    exact h
  obtain ⟨hσζ', hj0⟩ := hσζ
  have hcSLj : (cSL : SpecialLinearGroup (Fin 3) K) ^ j = 1 := by
    apply SpecialLinearGroup.toGL_injective
    rw [map_pow, toGL_cSL, cycThree_pow_mod, hj0, pow_zero, map_one]
  have hcj : (proj 3 K cSL) ^ j = 1 := by rw [← map_pow, hcSLj, map_one]
  have hβ'' : β = MulAut.conj ((proj 3 K (dSL hτ)) ^ m) * γ := by
    have e1 : MulAut.conj ((proj 3 K (dSL hτ)) ^ m * (proj 3 K cSL) ^ j) =
        MulAut.conj ((proj 3 K (dSL hτ)) ^ m) := by rw [map_mul, hcj, map_one, mul_one]
    rw [hβ', hA, e1]
  have hγb : γ ((proj 3 K (dSL hτ)) ^ m) = (proj 3 K (dSL hτ)) ^ m := by
    rw [map_pow, hγd_eq]
  have hcomm : Commute (MulAut.conj ((proj 3 K (dSL hτ)) ^ m)) γ := by
    show MulAut.conj ((proj 3 K (dSL hτ)) ^ m) * γ =
      γ * MulAut.conj ((proj 3 K (dSL hτ)) ^ m)
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hγb]
  have hδ2 : dualAut 3 K * dualAut 3 K = (1 : MulAut (projectiveSL 3 K)) := by
    obtain ⟨-, -, -, hdd, -, -⟩ := standard_automorphism_transport (n := 3) (K := K)
    exact hdd
  have hσf : σ ^ f = 1 := by
    obtain ⟨-, -, -, -, hcard, -⟩ :=
      finite_field_automorphism_fixed_field_cardinality hp hf hK
    haveI : Fintype (K ≃+* K) := Fintype.ofFinite _
    have h1 : orderOf σ ∣ Nat.card (K ≃+* K) := by
      rw [Nat.card_eq_fintype_card]
      exact orderOf_dvd_card
    rw [hcard] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hγ2 : γ ^ 2 = fieldAut 3 K (σ * σ) := by
    have hε' : ε = 0 ∨ ε = 1 := by omega
    rcases hε' with rfl | rfl
    · rw [hγdef, pow_zero, mul_one, pow_two]
      exact (map_mul (fieldAut 3 K) σ σ).symm
    · rw [hγdef, pow_one]
      calc (fieldAut 3 K σ * dualAut 3 K) ^ 2
          = fieldAut 3 K σ * (dualAut 3 K * fieldAut 3 K σ) * dualAut 3 K := by
              rw [pow_two]; group
        _ = fieldAut 3 K σ * (fieldAut 3 K σ * dualAut 3 K) * dualAut 3 K := by
            rw [dualAut_mul_fieldAut]
        _ = (fieldAut 3 K σ * fieldAut 3 K σ) * (dualAut 3 K * dualAut 3 K) := by group
        _ = fieldAut 3 K (σ * σ) := by rw [hδ2, mul_one, ← map_mul]
  have hγ2f : γ ^ (2 * f) = 1 := by
    have hss : (σ * σ) ^ f = 1 := by
      rw [← pow_two, ← pow_mul, show 2 * f = f * 2 from by ring, pow_mul, hσf, one_pow]
    rw [pow_mul, hγ2, ← map_pow, hss, map_one]
  have hdSL3 : ((proj 3 K (dSL hτ)) ^ 3) = 1 := by
    rw [← map_pow, show (dSL hτ : SpecialLinearGroup (Fin 3) K) ^ 3 = 1 from ?_, map_one]
    apply SpecialLinearGroup.toGL_injective
    rw [map_pow, toGL_dSL, diagTau_pow_three, map_one]
  have hconj3 : (MulAut.conj ((proj 3 K (dSL hτ)) ^ m)) ^ 3 = 1 := by
    rw [← map_pow, show ((proj 3 K (dSL hτ)) ^ m) ^ 3 = 1 from by
      rw [← pow_mul, show m * 3 = 3 * m from by ring, pow_mul, hdSL3, one_pow], map_one]
  have hγ3n : γ ^ (3 * 2 ^ k) = 1 := by
    have hβ3n : β ^ (3 * 2 ^ k) = 1 := by
      rw [show 3 * 2 ^ k = 2 ^ k * 3 from by ring, pow_mul, hk, one_pow]
    have hsplit : β ^ (3 * 2 ^ k) = (MulAut.conj ((proj 3 K (dSL hτ)) ^ m)) ^ (3 * 2 ^ k) *
        γ ^ (3 * 2 ^ k) := by
      rw [hβ'', hcomm.mul_pow]
    have hc3n : (MulAut.conj ((proj 3 K (dSL hτ)) ^ m)) ^ (3 * 2 ^ k) = 1 := by
      rw [pow_mul, hconj3, one_pow]
    rw [hsplit, hc3n, one_mul] at hβ3n
    exact hβ3n
  have hdvd1 : orderOf γ ∣ 2 * f := orderOf_dvd_of_pow_eq_one hγ2f
  have hdvd2 : orderOf γ ∣ 3 * 2 ^ k := orderOf_dvd_of_pow_eq_one hγ3n
  have h3d : ¬ 3 ∣ orderOf γ := by
    intro h
    have h32f : 3 ∣ 2 * f := h.trans hdvd1
    rcases (Nat.prime_three.dvd_mul).mp h32f with h2 | hf'
    · omega
    · exact h3f hf'
  have hcop : Nat.Coprime (orderOf γ) 3 :=
    ((Nat.prime_three.coprime_iff_not_dvd).mpr h3d).symm
  have hγn : γ ^ 2 ^ k = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one]
    exact hcop.dvd_of_dvd_mul_left hdvd2
  have hconjn : (MulAut.conj ((proj 3 K (dSL hτ)) ^ m)) ^ 2 ^ k = 1 := by
    have h := hk
    rw [hβ'', hcomm.mul_pow, hγn, mul_one] at h
    exact h
  have hconj1 : MulAut.conj ((proj 3 K (dSL hτ)) ^ m) = 1 := by
    have h1 : orderOf (MulAut.conj ((proj 3 K (dSL hτ)) ^ m)) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one hconjn
    have h2 : orderOf (MulAut.conj ((proj 3 K (dSL hτ)) ^ m)) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one hconj3
    have h3 : orderOf (MulAut.conj ((proj 3 K (dSL hτ)) ^ m)) = 1 := by
      have hgcd : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
      have := Nat.dvd_gcd h1 h2
      rwa [Nat.Coprime.gcd_eq_one hgcd, Nat.dvd_one] at this
    exact orderOf_eq_one_iff.mp h3
  have hβγ : β = γ := by rw [hβ'', hconj1, one_mul]
  have hγ2n : γ ^ (2 * 2 ^ k) = 1 := by
    rw [show 2 * 2 ^ k = 2 ^ k * 2 from by ring, pow_mul, hγn, one_pow]
  have hpow2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; ring
  have hσpow : σ ^ 2 ^ (k + 1) = 1 := by
    rw [hpow2]
    have h : fieldAut 3 K (σ ^ (2 * 2 ^ k)) = 1 := by
      have h1 : σ ^ (2 * 2 ^ k) = (σ * σ) ^ 2 ^ k := by rw [← pow_two, ← pow_mul]
      rw [h1, map_pow, ← hγ2, ← pow_mul, hγ2n]
    exact (eq_one_of_conjAut_mul_fieldAut_eq_one (K := K) (n := 3) le_rfl
      (1 : GL (Fin 3) K) (σ ^ (2 * 2 ^ k)) (by rw [map_one, one_mul]; exact h)).1
  have hγ1 : γ = 1 := by
    rcases Nat.eq_zero_or_pos (orderOf σ) with h | h
    · exact absurd h (orderOf_pos σ).ne'
    · by_cases hσ1 : σ = 1
      · have hγd'' : ((dualAut 3 K) ^ ε) (proj 3 K (dSL hτ)) = proj 3 K (dSL hτ) := by
          rw [hγdef, hσ1, map_one, one_mul] at hγd_eq
          exact hγd_eq
        have hε' : ε = 0 ∨ ε = 1 := by omega
        rcases hε' with rfl | rfl
        · rw [hγdef, hσ1, map_one, one_mul, pow_zero]
        · exfalso
          rw [pow_one, dualAut_dSL] at hγd''
          have h2 : proj 3 K (dSL hτ) * proj 3 K (dSL hτ) = 1 := by
            calc proj 3 K (dSL hτ) * proj 3 K (dSL hτ)
                = proj 3 K (dSL hτ) * (proj 3 K (dSL hτ))⁻¹ := by rw [hγd'']
              _ = 1 := mul_inv_cancel _
          have hord2 : orderOf (proj 3 K (dSL hτ)) ∣ 2 :=
            orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
          have hord3 : orderOf (proj 3 K (dSL hτ)) ∣ 3 :=
            orderOf_dvd_of_pow_eq_one hdSL3
          have h1 : orderOf (proj 3 K (dSL hτ)) = 1 := by
            have hg : Nat.Coprime 2 3 := by norm_num
            have := Nat.dvd_gcd hord2 hord3
            rwa [Nat.Coprime.gcd_eq_one hg, Nat.dvd_one] at this
          exact dSL_ne_one hτ hτ1 (orderOf_eq_one_iff.mp h1)
      · exfalso
        have hσζ'' : σ (ζ : K) = (ζ : K) ∨ σ (ζ : K) = ((ζ : K))⁻¹ := by
          rcases hσζ' with h | h
          · exact Or.inl h
          · exact Or.inr (by rw [← Units.val_inv_eq_inv_val]; exact h)
        exact false_of_sigma_ne_one hp hp2 hf hK hσ1 hζ hσζ'' hσpow
  rw [hβγ, hγ1]

theorem eq_one_of_pow_two_projImage_linear {p f : ℕ} {K : Type} [Field K]
    (hK : PiField true p f K) (hq : ModThree true (p ^ f)) (hp2 : p ≠ 2) (h9 : p ^ f % 9 ≠ 1)
    {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {ζ : Kˣ}
    (hζ : orderOf ζ = 2 ^ (p ^ f - 1).factorization 2)
    {dM cM yM : projImage (slPi true 3 (p ^ f) K)}
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ))
    (hcM : (cM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (cycThree : GL (Fin 3) K))
    (hyM : (yM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagUnits ζ ζ⁻¹ 1))
    (β : MulAut (projImage (slPi true 3 (p ^ f) K))) (hd : β dM = dM) (hc : β cM = cM)
    (hyβ : β yM = yM) {k : ℕ} (hk : β ^ 2 ^ k = 1) : β = 1 := by
  have hp : p.Prime := hK.prime
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite K := hK.finite
  have hcard : Nat.card K = p ^ f := by
    have := hK.card
    simpa [piCard] using this
  have hq' : p ^ f % 3 = 1 := by
    have := hq
    simpa [ModThree] using this
  have hdet : ((diagUnits ζ ζ⁻¹ 1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [det_coe_diagUnits]
    simp
  set ySL : SpecialLinearGroup (Fin 3) K :=
    ⟨((diagUnits ζ ζ⁻¹ 1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), hdet⟩ with hySL
  have hySL' : SpecialLinearGroup.toGL ySL = diagUnits ζ ζ⁻¹ 1 := Units.ext rfl
  set Φ : projectiveSL 3 K ≃* projImage (slPi true 3 (p ^ f) K) :=
    CFSG.RankThree.PartTwo.Sec17.Proof17Res7.linearModelEquiv (K := K) (p ^ f) with hΦ
  have hΦd : Φ (proj 3 K (dSL hτ)) = dM := Subtype.ext (by
    rw [hΦ, CFSG.RankThree.PartTwo.Sec17.Proof17Res7.coe_linearModelEquiv_proj,
      CFSG.RankThree.PartTwo.Sec17.Proof17Res7.toGL_dSL, hdM])
  have hΦc : Φ (proj 3 K cSL) = cM := Subtype.ext (by
    rw [hΦ, CFSG.RankThree.PartTwo.Sec17.Proof17Res7.coe_linearModelEquiv_proj,
      CFSG.RankThree.PartTwo.Sec17.Proof17Res7.toGL_cSL, hcM])
  have hΦy : Φ (proj 3 K ySL) = yM := Subtype.ext (by
    rw [hΦ, CFSG.RankThree.PartTwo.Sec17.Proof17Res7.coe_linearModelEquiv_proj, hySL', hyM])
  set β' : MulAut (projectiveSL 3 K) := (Φ.trans β).trans Φ.symm with hβ''
  have hd' : β' (proj 3 K (dSL hτ)) = proj 3 K (dSL hτ) := by
    rw [hβ'', MulEquiv.trans_apply, MulEquiv.trans_apply, hΦd, hd, ← hΦd,
      MulEquiv.symm_apply_apply]
  have hc' : β' (proj 3 K cSL) = proj 3 K cSL := by
    rw [hβ'', MulEquiv.trans_apply, MulEquiv.trans_apply, hΦc, hc, ← hΦc,
      MulEquiv.symm_apply_apply]
  have hy' : β' (proj 3 K ySL) = proj 3 K ySL := by
    rw [hβ'', MulEquiv.trans_apply, MulEquiv.trans_apply, hΦy, hyβ, ← hΦy,
      MulEquiv.symm_apply_apply]
  have hk' : β' ^ 2 ^ k = 1 := by
    have h1 : β' = (MulAut.congr Φ).symm β := rfl
    rw [h1, ← map_pow, hk, map_one]
  have hβ'1 : β' = 1 := eq_one_of_pow_two_projectiveSL hcard hp2 hq' h9 hτ hτ1 hζ hySL'
    β' hd' hc' hy' hk'
  have hfix : ∀ x : projectiveSL 3 K, Φ.symm (β (Φ x)) = x := by
    intro x
    have h := congrArg (fun f : MulAut (projectiveSL 3 K) => f x) hβ'1
    simpa [hβ'', MulEquiv.trans_apply] using h
  ext y
  obtain ⟨x, rfl⟩ := Φ.surjective y
  have h2 : β (Φ x) = Φ x := by
    have h3 := congrArg (fun z => Φ z) (hfix x)
    simpa using h3
  simpa using h2

end CFSG.RankThree.PartTwo.KFacts.KF163L3
