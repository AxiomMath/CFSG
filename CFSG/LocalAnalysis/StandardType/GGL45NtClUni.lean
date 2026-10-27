module

public import CFSG.LocalAnalysis.StandardType.GGL45NtClTransfer
public import CFSG.LocalAnalysis.StandardType.GGL45NtClRecipes
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeThree
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.RankThree.PartOne.S15K.CentralCover
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Monster.B.TwoA.Unitary.Semilinear

public section

namespace CFSG.HardMathSupport.C14Cl

open CFSG CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.ComponentInitial Matrix

theorem uniGroup_le_normalizer {K : Type} [Field K] {n : ℕ} {d : ℕ} (h : UnitaryFieldData 2 n K) :
    TableB.unitGroup (ι := Fin d) h.bar ≤
      Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K)) := by
  intro A hA
  refine TableBUE.gu_subset_normalizer h ⟨1, one_ne_zero, one_pow _, ?_⟩
  rw [one_smul]
  have hbar : ((A : Matrix (Fin d) (Fin d) K).map h.bar) =
      ((A : Matrix (Fin d) (Fin d) K).map (· ^ 2 ^ n)) := by
    ext i j
    rfl
  rw [← hbar]
  exact TableB.mem_unitGroup.mp hA

@[expose] noncomputable def uniConj {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData 2 n K) (d : ℕ) :
    ↥(TableB.unitGroup (ι := Fin d) h.bar) →*
      MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) :=
  (TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n))).comp
    (Subgroup.inclusion (uniGroup_le_normalizer h))

theorem uni_kappa {K : Type} [Field K] {n : ℕ} {d : ℕ} [Fintype K] [CharP K 2] {p : ℕ} (h : UnitaryFieldData 2 n K) (hp : p.Prime)
    (hd : 0 < d) (hpd : ¬ p ∣ d ∨ ¬ p ∣ 2 ^ n + 1)
    (g x : ↥(TableB.unitGroup (ι := Fin d) h.bar)) (hxp : x ^ p = 1) (κ : Kˣ)
    (hκ : (((g * x * g⁻¹ : ↥(TableB.unitGroup (ι := Fin d) h.bar)) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) = (κ : K) • ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) :
    κ = 1 := by
  classical
  have i0 : Fin d := ⟨0, hd⟩
  have hxU : (((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
      ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 :=
    TableB.mem_unitGroup.mp x.2
  rcases hpd with hpd | hpd
  ·
    refine lin_kappa hp hd (Or.inl hpd) (g : GL (Fin d) K) (x : GL (Fin d) K) κ ?_ ?_
    · simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hκ
    · have hh := congrArg (fun z : ↥(TableB.unitGroup (ι := Fin d) h.bar) =>
        (z : GL (Fin d) K)) hxp
      simpa [Subgroup.coe_pow] using hh
  ·
    have h1 : (((κ : K) • ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)).map h.bar)ᵀ *
        ((κ : K) • ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) = 1 := by
      rw [← hκ]
      exact TableB.mem_unitGroup.mp (g * x * g⁻¹).2
    have hbar_mul : h.bar (κ : K) * (κ : K) = 1 := by
      rw [TableB.transpose_map_smul, Matrix.smul_mul, Matrix.mul_smul, hxU,
        smul_smul] at h1
      have h2 := congrFun (congrFun h1 i0) i0
      simpa [Matrix.smul_apply, mul_one] using h2
    have hq1 : (κ : K) ^ (2 ^ n + 1) = 1 := by
      rw [UnitaryFieldData.bar_apply, ← pow_succ] at hbar_mul
      exact hbar_mul
    have hx_gl_p : (x : GL (Fin d) K) ^ p = 1 := by
      have hh := congrArg (fun z : ↥(TableB.unitGroup (ι := Fin d) h.bar) =>
        (z : GL (Fin d) K)) hxp
      simpa [Subgroup.coe_pow] using hh
    have hMxp : ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ^ p = 1 := by
      have hh := congrArg (fun y : GL (Fin d) K => (y : Matrix (Fin d) (Fin d) K)) hx_gl_p
      simpa [Units.val_pow_eq_pow_val] using hh
    have hconjp : (g * x * g⁻¹ : ↥(TableB.unitGroup (ι := Fin d) h.bar)) ^ p = 1 := by
      have hc : (g * x * g⁻¹ : ↥(TableB.unitGroup (ι := Fin d) h.bar)) =
          MulAut.conj g x := by rw [MulAut.conj_apply]
      rw [hc, ← map_pow, hxp, map_one]
    have hM'p : ((((g * x * g⁻¹ : ↥(TableB.unitGroup (ι := Fin d) h.bar)) : GL (Fin d) K)) :
        Matrix (Fin d) (Fin d) K) ^ p = 1 := by
      have hh : ((g * x * g⁻¹ : ↥(TableB.unitGroup (ι := Fin d) h.bar)) : GL (Fin d) K) ^ p = 1 := by
        have h2 := congrArg (fun z : ↥(TableB.unitGroup (ι := Fin d) h.bar) =>
          (z : GL (Fin d) K)) hconjp
        simpa [Subgroup.coe_pow] using h2
      have h3 := congrArg (fun y : GL (Fin d) K => (y : Matrix (Fin d) (Fin d) K)) hh
      rw [Units.val_pow_eq_pow_val] at h3
      exact h3
    have hκp : (κ : K) ^ p = 1 := by
      have h3 : ((((g * x * g⁻¹ : ↥(TableB.unitGroup (ι := Fin d) h.bar)) : GL (Fin d) K)) :
          Matrix (Fin d) (Fin d) K) ^ p =
          ((κ : K) ^ p) • (1 : Matrix (Fin d) (Fin d) K) := by
        rw [hκ, smul_pow, hMxp]
      rw [hM'p] at h3
      have h2 := congrFun (congrFun h3 i0) i0
      simpa [Matrix.smul_apply] using h2.symm
    have hcop : Nat.Coprime (2 ^ n + 1) p :=
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd).symm
    have hu1 : κ ^ (2 ^ n + 1) = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, hq1, Units.val_one])
    have hu2 : κ ^ p = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, hκp, Units.val_one])
    have hdvd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hu1) (orderOf_dvd_of_pow_eq_one hu2)
    rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
    exact hdvd

theorem uni_sl_adjust {K : Type} [Field K] {n : ℕ} {d : ℕ} [Fintype K] [CharP K 2] {p : ℕ} (h : UnitaryFieldData 2 n K) (hp : p.Prime)
    (hpd : ¬ p ∣ d ∨ ¬ p ∣ 2 ^ n + 1) (σ₀ : K ≃+* K)
    (y : ↥(TableB.unitGroup (ι := Fin d) h.bar)) (hy : y ^ p = 1)
    (hfix : ((y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ₀ =
      ((y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) :
    ∃ μ : Kˣ, σ₀ μ = μ ∧ μ ^ p = 1 ∧ (μ : K) ^ (2 ^ n + 1) = 1 ∧
      ((μ : K) • ((y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)).det = 1 := by
  classical
  have hYp : (y : GL (Fin d) K) ^ p = 1 := by
    have hh := congrArg (fun z : ↥(TableB.unitGroup (ι := Fin d) h.bar) =>
      (z : GL (Fin d) K)) hy
    simpa [Subgroup.coe_pow] using hh
  set M := ((y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) with hM
  set δ := M.det with hδ
  have hfixM : M.map σ₀ = M := by rw [hM]; exact hfix
  have hδ0 : δ ≠ 0 := by
    intro h0
    have h1 : δ * ((y⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).det = 1 := by
      rw [hδ, hM, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.det_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hδp : δ ^ p = 1 := by
    rw [hδ, hM, ← Matrix.det_pow, ← Units.val_pow_eq_pow_val, hYp, Units.val_one,
      Matrix.det_one]
  have hσδ : σ₀ δ = δ := by
    have hh := RingHom.map_det (σ₀ : K →+* K) M
    rw [hδ]
    exact hh.trans (congrArg Matrix.det hfixM)
  have hδq1 : δ ^ (2 ^ n + 1) = 1 := by
    have hbarδ : h.bar δ * δ = 1 := by
      have hbar_det : (M.map h.bar).det = h.bar M.det :=
        (RingHom.map_det h.bar M).symm
      have hdet := congrArg Matrix.det (TableB.mem_unitGroup.mp y.2)
      rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, ← hM] at hdet
      rw [hbar_det, ← hδ] at hdet
      exact hdet
    rw [UnitaryFieldData.bar_apply, ← pow_succ] at hbarδ
    exact hbarδ
  rcases hpd with hpd | hpd
  ·
    have hcop : Nat.Coprime d p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpd).symm
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
    set c := m * (p - 1) with hc
    have hp1 : 1 ≤ p := hp.one_lt.le
    have hcd : c * d + 1 = p * (d * m / p * (p - 1) + 1) := by
      have hdiv := Nat.div_add_mod (d * m) p
      rw [hm] at hdiv
      set t := d * m / p
      obtain ⟨p', hp'⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
      have e1 : c * d = (d * m) * p' := by simp only [hc, hp', Nat.add_sub_cancel]; ring
      rw [e1, ← hdiv, hp', Nat.add_sub_cancel]; ring
    refine ⟨Units.mk0 δ hδ0 ^ c, ?_, ?_, ?_, ?_⟩
    · simp only [Units.val_pow_eq_pow_val, Units.val_mk0, map_pow, hσδ]
    · apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_mk0, ← pow_mul,
        mul_comm, pow_mul, hδp, one_pow, Units.val_one]
    · rw [Units.val_pow_eq_pow_val, Units.val_mk0, ← pow_mul, mul_comm c (2 ^ n + 1),
        pow_mul, hδq1, one_pow]
    · rw [Matrix.det_smul, Fintype.card_fin, Units.val_pow_eq_pow_val, Units.val_mk0,
        ← pow_mul, ← hδ, ← pow_succ, hcd, pow_mul, hδp, one_pow]
  ·
    have hcop : Nat.Coprime p (2 ^ n + 1) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpd
    have hδ1 : δ = 1 := by
      have hdvd : orderOf δ ∣ Nat.gcd p (2 ^ n + 1) :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hδp) (orderOf_dvd_of_pow_eq_one hδq1)
      rw [hcop, Nat.dvd_one] at hdvd
      exact orderOf_eq_one_iff.mp hdvd
    refine ⟨1, by simp, by simp, by simp, ?_⟩
    rw [Units.val_one, one_smul, ← hδ]
    exact hδ1

theorem uni_commute_of_conj_commute {K : Type} [Field K] {n : ℕ} {d : ℕ} [Fintype K] [CharP K 2] {p : ℕ} (h : UnitaryFieldData 2 n K)
    (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime)
    (hpd : ¬ p ∣ d ∨ ¬ p ∣ 2 ^ n + 1) (E₀ : Subgroup ↥(TableB.unitGroup (ι := Fin d) h.bar))
    (hE : ∀ e ∈ E₀, e ^ p = 1) (g : ↥(TableB.unitGroup (ι := Fin d) h.bar))
    (hg : ∀ e ∈ E₀, uniConj h d g * uniConj h d e = uniConj h d e * uniConj h d g) :
    ∀ e ∈ E₀, g * e = e * g := by
  classical
  have hK : Nat.card K = (2 ^ n) ^ 2 := by
    rw [h.card, ← pow_mul, show 2 * n = n * 2 by omega]
  obtain ⟨p', hp', hp'q⟩ := Nat.exists_prime_and_dvd (n := 2 ^ n + 1) (by
    have : 0 < 2 ^ n := pow_pos (by norm_num) n
    omega)
  intro e he
  set M : ↥(TableB.unitGroup (ι := Fin d) h.bar) := g * e * g⁻¹ * e⁻¹ with hMdef
  have hconj : uniConj h d M = 1 := by
    rw [hMdef, map_mul, map_mul, map_mul, map_inv, map_inv, hg e he]
    group
  have hproj : TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n))
      ⟨(M : GL (Fin d) K), uniGroup_le_normalizer h M.2⟩ = 1 := by
    change uniConj h d M = 1
    exact hconj
  obtain ⟨κ, hκ⟩ := TableBUE.mem_scalars_of_projConj_eq_one h hK hd hdq hp' hp'q hproj
  have hMval : (M : GL (Fin d) K) =
      (g : GL (Fin d) K) * (e : GL (Fin d) K) * (g : GL (Fin d) K)⁻¹ *
        (e : GL (Fin d) K)⁻¹ := by
    rw [hMdef]
    simp [Subgroup.coe_mul, Subgroup.coe_inv]
  have hGL : ((g * e * g⁻¹ : ↥(TableB.unitGroup (ι := Fin d) h.bar)) : GL (Fin d) K) =
      Matrix.GeneralLinearGroup.scalar (Fin d) κ * (e : GL (Fin d) K) := by
    have h1 : ((g * e * g⁻¹ : ↥(TableB.unitGroup (ι := Fin d) h.bar)) : GL (Fin d) K) =
        (g : GL (Fin d) K) * (e : GL (Fin d) K) * (g : GL (Fin d) K)⁻¹ := by
      simp [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h1, hκ, hMval]
    group
  have hmat : (((g * e * g⁻¹ : ↥(TableB.unitGroup (ι := Fin d) h.bar)) : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) = (κ : K) •
        ((e : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    rw [hGL, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_eq_diagonal_mul]
  have hκ1 : κ = 1 := uni_kappa h hp (by omega) hpd g e (hE e he) κ hmat
  have heq : g * e * g⁻¹ = e := by
    apply Subtype.ext
    rw [hGL, hκ1]
    simp
  exact (mul_inv_eq_iff_eq_mul).mp heq

private noncomputable def cU5_sigmaGL {K : Type} [Field K] {d : ℕ} (σ₀ : K ≃+* K) : GL (Fin d) K ≃* GL (Fin d) K :=
  Units.mapEquiv (RingEquiv.mapMatrix (m := Fin d) σ₀).toMulEquiv

private lemma cU5_sigmaGL_coe {K : Type} [Field K] {d : ℕ} (σ₀ : K ≃+* K) (A : GL (Fin d) K) :
    ((cU5_sigmaGL (d := d) σ₀ A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (A : Matrix (Fin d) (Fin d) K).map σ₀ := by
  rw [cU5_sigmaGL, Units.coe_mapEquiv]
  rfl

private lemma cU5_sigmaGL_apply_symm {K : Type} [Field K] {d : ℕ} (σ₀ : K ≃+* K) (A : GL (Fin d) K) :
    cU5_sigmaGL (d := d) σ₀ (cU5_sigmaGL (d := d) σ₀⁻¹ A) = A := by
  apply Units.ext
  rw [cU5_sigmaGL_coe, cU5_sigmaGL_coe, Matrix.map_map]
  ext i j
  simp

private theorem cU5_bar_map {K : Type} [Field K] {n : ℕ} {d : ℕ} (h : UnitaryFieldData 2 n K) (M : Matrix (Fin d) (Fin d) K) :
    M.map (· ^ 2 ^ n) = M.map h.bar := by
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply, UnitaryFieldData.bar_apply]

private theorem cU5_mem_unitGroup_of_primeFormUnitary {K : Type} [Field K] {n : ℕ} {d : ℕ} (h : UnitaryFieldData 2 n K)
    {P : GL (Fin d) K} (hP : P ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K d)) :
    P ∈ TableB.unitGroup (ι := Fin d) h.bar := by
  rw [TableB.mem_unitGroup]
  rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary] at hP
  simpa [CFSG.RankThree.PartOne.KCUnitaryModel.idGram] using hP

private theorem cU5_exists_unitary_of_gu {K : Type} [Field K] {n : ℕ} {d : ℕ} [Fintype K] (h : UnitaryFieldData 2 n K)
    {M : GL (Fin d) K} (hM : M ∈ LargeEvenGUSet (Fin d) K (2 ^ n)) :
    ∃ u : Kˣ, GeneralLinearGroup.scalar (Fin d) u * M ∈
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K d) := by
  haveI : Finite K := Fintype.finite inferInstance
  obtain ⟨μ, hμ0, hμq, hμ⟩ := hM
  have hbar : h.bar μ = μ := by rw [UnitaryFieldData.bar_apply]; exact hμq
  have hK : Nat.card K = (2 ^ n) ^ 2 := by
    rw [h.card, show 2 ^ (2 * n) = (2 ^ n) ^ 2 by rw [← pow_mul, mul_comm]]
  obtain ⟨l, hl⟩ := TableB.exists_norm_eq (K := K) (q := 2 ^ n) (by simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) h.one_le) hK hμ0 hμq
  let u₀ : K := h.bar (l : K)
  have hu₀0 : u₀ ≠ 0 := by
    dsimp [u₀]
    exact (map_ne_zero h.bar).mpr (Units.ne_zero l)
  have hu₀ : h.bar u₀ * u₀ = μ := by
    dsimp [u₀]
    rw [UnitaryFieldData.bar_bar, h.bar_apply, ← pow_succ']
    exact hl
  refine ⟨(Units.mk0 u₀ hu₀0)⁻¹, ?_⟩
  rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary]
  rw [TableB.coe_scalar_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
  simp only [CFSG.RankThree.PartOne.KCUnitaryModel.idGram, Units.val_one, Matrix.mul_one]
  have hmap : (u₀⁻¹ • (M : Matrix (Fin d) (Fin d) K)).map h.bar =
      h.bar u₀⁻¹ • (M : Matrix (Fin d) (Fin d) K).map h.bar := by
    ext i j
    simp
  rw [hmap, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← cU5_bar_map h,
    hμ, smul_smul, map_inv₀]
  have hb0 : h.bar u₀ ≠ 0 := (map_ne_zero h.bar).mpr hu₀0
  have e : h.bar u₀⁻¹ * u₀⁻¹ * μ = 1 := by
    rw [map_inv₀, ← hu₀]
    field_simp
  rw [show (h.bar u₀)⁻¹ * u₀⁻¹ * μ = h.bar u₀⁻¹ * u₀⁻¹ * μ by rw [map_inv₀], e, one_smul]

private theorem cU5_mem_scalars_of_projConj_eq_one {K : Type} [Field K] {n : ℕ} {d : ℕ} [Fintype K] (h : UnitaryFieldData 2 n K)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2))
    {M : Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K))}
    (hM : TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n)) M = 1) :
    (M : GL (Fin d) K) ∈ LargeEvenScalars (Fin d) K := by
  haveI : Finite K := Fintype.finite inferInstance
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect (LargeEvenSUGroup (Fin d) K (2 ^ n)) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK hd hdq
  have hker : (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n))).ker ≤
      Subgroup.center (LargeEvenSUGroup (Fin d) K (2 ^ n)) :=
    TableBUE.ker_projMk_le_center
  have hcomm : ∀ g ∈ LargeEvenSUGroup (Fin d) K (2 ^ n),
      (M : GL (Fin d) K) * g = g * (M : GL (Fin d) K) := by
    intro g hg
    have key := CFSG.RankThree.PartOne.S15K.eq_of_perfect_of_map_eq
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n))) hker hperf
      ((LargeEvenSUGroup (Fin d) K (2 ^ n)).normalizerMonoidHom M).toMonoidHom
      (MonoidHom.id (LargeEvenSUGroup (Fin d) K (2 ^ n))) (fun u => by
        have h1 := congrArg (fun ψ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) =>
          ψ (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)) u)) hM
        exact h1) ⟨g, hg⟩
    have h2 := congrArg Subtype.val key
    change (M : GL (Fin d) K) * g * (M : GL (Fin d) K)⁻¹ = g at h2
    calc (M : GL (Fin d) K) * g = (M : GL (Fin d) K) * g * (M : GL (Fin d) K)⁻¹ *
          (M : GL (Fin d) K) := by group
      _ = g * (M : GL (Fin d) K) := by rw [h2]
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd
    (show 2 ^ n + 1 ≠ 1 by have : 0 < 2 ^ n := pow_pos (by norm_num) n; omega)
  exact TableBUE.mem_scalars_of_commute h hr hrd hcomm

private theorem cU5_scalar_eq_one {K : Type} [Field K] {n : ℕ} {d : ℕ} [Fintype K] {p : ℕ} (hp : p.Prime)
    (hpd : ¬ p ∣ d ∨ ¬ p ∣ 2 ^ n + 1) (κ : Kˣ)
    (hκd : (κ : K) ^ d = 1) (hκp : (κ : K) ^ p = 1) (hκq : (κ : K) ^ (2 ^ n + 1) = 1) :
    κ = 1 := by
  rcases hpd with h | h
  · have hcop : Nat.Coprime d p := ((Nat.Prime.coprime_iff_not_dvd hp).2 h).symm
    have hu1 : κ ^ d = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hκd, Units.val_one])
    have hu2 : κ ^ p = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hκp, Units.val_one])
    have h3 : orderOf κ ∣ 1 := by
      have h4 : orderOf κ ∣ Nat.gcd d p :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hu1) (orderOf_dvd_of_pow_eq_one hu2)
      rwa [hcop] at h4
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  · have hu1 : κ ^ (2 ^ n + 1) = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, hκq, Units.val_one])
    have hu2 : κ ^ p = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hκp, Units.val_one])
    have hcop' : Nat.Coprime p (2 ^ n + 1) := (hp.coprime_iff_not_dvd).mpr h
    have hcop : Nat.Coprime (2 ^ n + 1) p := Nat.coprime_comm.mp hcop'
    have h3 : orderOf κ ∣ 1 := by
      have h4 : orderOf κ ∣ Nat.gcd (2 ^ n + 1) p :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hu1) (orderOf_dvd_of_pow_eq_one hu2)
      rwa [hcop] at h4
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

private theorem cU5_sigmaGL_mem_unit {K : Type} [Field K] {n : ℕ} {d : ℕ} (h : UnitaryFieldData 2 n K) (σ₀ : K ≃+* K)
    (hσbar : ∀ c, σ₀ (h.bar c) = h.bar (σ₀ c)) {A : GL (Fin d) K}
    (hA : A ∈ TableB.unitGroup (ι := Fin d) h.bar) :
    cU5_sigmaGL (d := d) σ₀ A ∈ TableB.unitGroup (ι := Fin d) h.bar := by
  rw [TableB.mem_unitGroup] at hA ⊢
  rw [cU5_sigmaGL_coe]
  have hcomp : ((A : Matrix (Fin d) (Fin d) K).map σ₀).map h.bar =
      ((A : Matrix (Fin d) (Fin d) K).map h.bar).map σ₀ := by
    ext i j
    simp only [Matrix.map_apply]
    exact (hσbar _).symm
  rw [hcomp, ← Matrix.transpose_map, ← Matrix.map_mul, hA]
  simp

private noncomputable def cU5_sigmaU {K : Type} [Field K] {n : ℕ} {d : ℕ} (h : UnitaryFieldData 2 n K) (σ₀ : K ≃+* K)
    (hσbar : ∀ c, σ₀ (h.bar c) = h.bar (σ₀ c)) :
    ↥(TableB.unitGroup (ι := Fin d) h.bar) →* ↥(TableB.unitGroup (ι := Fin d) h.bar) where
  toFun A := ⟨cU5_sigmaGL (d := d) σ₀ A, cU5_sigmaGL_mem_unit h σ₀ hσbar A.2⟩
  map_one' := Subtype.ext (by
    simpa using map_one (cU5_sigmaGL (d := d) σ₀))
  map_mul' A B := Subtype.ext (by
    simpa using map_mul (cU5_sigmaGL (d := d) σ₀) (A : GL (Fin d) K) (B : GL (Fin d) K))

private theorem cU5_sigmaU_coe {K : Type} [Field K] {n : ℕ} {d : ℕ} (h : UnitaryFieldData 2 n K) (σ₀ : K ≃+* K)
    (hσbar : ∀ c, σ₀ (h.bar c) = h.bar (σ₀ c))
    (A : ↥(TableB.unitGroup (ι := Fin d) h.bar)) :
    ((cU5_sigmaU (n := n) (d := d) h σ₀ hσbar A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      ((A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ₀ :=
  cU5_sigmaGL_coe σ₀ (A : GL (Fin d) K)

private theorem cU5_sigmaGL_mem_SU {K : Type} [Field K] {n : ℕ} {d : ℕ} (h : UnitaryFieldData 2 n K) (σ₀ : K ≃+* K)
    (hσbar : ∀ c, σ₀ (h.bar c) = h.bar (σ₀ c)) {s : GL (Fin d) K}
    (hs : s ∈ LargeEvenSUGroup (Fin d) K (2 ^ n)) :
    cU5_sigmaGL (d := d) σ₀ s ∈ LargeEvenSUGroup (Fin d) K (2 ^ n) := by
  change s ∈ CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n K d at hs
  change cU5_sigmaGL (d := d) σ₀ s ∈ CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n K d
  rw [CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h] at hs ⊢
  constructor
  · rw [cU5_sigmaGL_coe]
    have hdet : ((s : Matrix (Fin d) (Fin d) K).map σ₀).det = σ₀ ((s : Matrix (Fin d) (Fin d) K).det) :=
      (RingHom.map_det (σ₀ : K →+* K) (s : Matrix (Fin d) (Fin d) K)).symm
    rw [hdet, hs.1, map_one]
  · rw [cU5_sigmaGL_coe]
    have hcomp : ((s : Matrix (Fin d) (Fin d) K).map σ₀).map h.bar =
        ((s : Matrix (Fin d) (Fin d) K).map h.bar).map σ₀ := by
      ext i j
      simp only [Matrix.map_apply]
      exact (hσbar _).symm
    rw [hcomp, ← Matrix.transpose_map, ← Matrix.map_mul, hs.2]
    simp

private theorem cU5_field_conj {K : Type} [Field K] {n : ℕ} {d : ℕ} [Fintype K] (h : UnitaryFieldData 2 n K) (σ₀ : K ≃+* K)
    (hσbar : ∀ c, σ₀ (h.bar c) = h.bar (σ₀ c))
    (hσbar_inv : ∀ c, σ₀⁻¹ (h.bar c) = h.bar (σ₀⁻¹ c))
    (f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))
    (hf : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (fun s s' => ((s' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ₀) f)
    (A : ↥(TableB.unitGroup (ι := Fin d) h.bar)) :
    f * uniConj h d A * f⁻¹ =
      uniConj h d (cU5_sigmaU (n := n) (d := d) h σ₀ hσbar A) := by
  classical
  apply MulEquiv.ext
  intro x
  obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective
    ((LargeEvenScalars (Fin d) K).subgroupOf
      (LargeEvenSUGroup (Fin d) K (2 ^ n))) x
  have hnormal : (A : GL (Fin d) K) ∈
      Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K)) :=
    uniGroup_le_normalizer h A.2
  rw [Subgroup.mem_normalizer_iff] at hnormal
  have hsinv_mem : (cU5_sigmaGL (d := d) σ₀⁻¹ (s : GL (Fin d) K)) ∈
      LargeEvenSUGroup (Fin d) K (2 ^ n) :=
    cU5_sigmaGL_mem_SU h σ₀⁻¹ hσbar_inv s.2
  have hconj1_mem : ((A : GL (Fin d) K) *
      (cU5_sigmaGL (d := d) σ₀⁻¹ (s : GL (Fin d) K)) * (A : GL (Fin d) K)⁻¹) ∈
      LargeEvenSUGroup (Fin d) K (2 ^ n) := (hnormal _).1 hsinv_mem
  have hsigmaA_unit : (cU5_sigmaGL (d := d) σ₀ (A : GL (Fin d) K)) ∈
      TableB.unitGroup (ι := Fin d) h.bar := cU5_sigmaGL_mem_unit h σ₀ hσbar A.2
  have hconj2_mem : ((cU5_sigmaGL (d := d) σ₀ (A : GL (Fin d) K)) *
      (s : GL (Fin d) K) * (cU5_sigmaGL (d := d) σ₀ (A : GL (Fin d) K))⁻¹) ∈
      LargeEvenSUGroup (Fin d) K (2 ^ n) := by
    have hN : (cU5_sigmaGL (d := d) σ₀ (A : GL (Fin d) K)) ∈
        Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K)) :=
      uniGroup_le_normalizer h (cU5_sigmaGL_mem_unit h σ₀ hσbar A.2)
    rw [Subgroup.mem_normalizer_iff] at hN
    exact (hN _).1 s.2
  have hfi : f⁻¹ (LargeEvenProjMk _ s) = LargeEvenProjMk _
      (⟨cU5_sigmaGL (d := d) σ₀⁻¹ (s : GL (Fin d) K), hsinv_mem⟩ :
        ↥(LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
    have h1 : f (LargeEvenProjMk _ (⟨cU5_sigmaGL (d := d) σ₀⁻¹ (s : GL (Fin d) K),
        hsinv_mem⟩ : ↥(LargeEvenSUGroup (Fin d) K (2 ^ n)))) =
        LargeEvenProjMk _ s := by
      apply hf
      rw [cU5_sigmaGL_coe, Matrix.map_map]
      ext i j
      simp
    simpa using (congrArg (fun z => f⁻¹ z) h1).symm
  rw [MulAut.mul_apply, MulAut.mul_apply, hfi]
  have hAconj : uniConj h d A (LargeEvenProjMk _ (⟨cU5_sigmaGL (d := d) σ₀⁻¹
      (s : GL (Fin d) K), hsinv_mem⟩ : ↥(LargeEvenSUGroup (Fin d) K (2 ^ n)))) =
      LargeEvenProjMk _ (⟨(A : GL (Fin d) K) * (cU5_sigmaGL (d := d) σ₀⁻¹
        (s : GL (Fin d) K)) * (A : GL (Fin d) K)⁻¹, hconj1_mem⟩ :
        ↥(LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
    exact TableB.projConj_mk (LargeEvenSUGroup (Fin d) K (2 ^ n))
      ((Subgroup.inclusion (uniGroup_le_normalizer h)) A)
      (⟨cU5_sigmaGL (d := d) σ₀⁻¹ (s : GL (Fin d) K), hsinv_mem⟩ :
        ↥(LargeEvenSUGroup (Fin d) K (2 ^ n)))
  rw [hAconj]
  have hstep : f (LargeEvenProjMk _ (⟨(A : GL (Fin d) K) * (cU5_sigmaGL (d := d) σ₀⁻¹
      (s : GL (Fin d) K)) * (A : GL (Fin d) K)⁻¹, hconj1_mem⟩ :
        ↥(LargeEvenSUGroup (Fin d) K (2 ^ n)))) =
      LargeEvenProjMk _ (⟨cU5_sigmaGL (d := d) σ₀ ((A : GL (Fin d) K) *
        (cU5_sigmaGL (d := d) σ₀⁻¹ (s : GL (Fin d) K)) * (A : GL (Fin d) K)⁻¹),
        cU5_sigmaGL_mem_SU h σ₀ hσbar hconj1_mem⟩ :
        ↥(LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
    apply hf
    rw [cU5_sigmaGL_coe]
  rw [hstep]
  have hAconj2 : uniConj h d (cU5_sigmaU (n := n) (d := d) h σ₀ hσbar A)
      (LargeEvenProjMk _ s) =
      LargeEvenProjMk _ (⟨(cU5_sigmaGL (d := d) σ₀ (A : GL (Fin d) K)) *
        (s : GL (Fin d) K) * (cU5_sigmaGL (d := d) σ₀ (A : GL (Fin d) K))⁻¹,
        hconj2_mem⟩ : ↥(LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
    exact TableB.projConj_mk (LargeEvenSUGroup (Fin d) K (2 ^ n))
      ((Subgroup.inclusion (uniGroup_le_normalizer h)) (cU5_sigmaU (n := n) (d := d) h σ₀ hσbar A))
      s
  rw [hAconj2]
  apply congrArg (LargeEvenProjMk _)
  apply Subtype.ext
  simp only [Subgroup.coe_mk]
  simp only [MulEquiv.map_mul, MulEquiv.map_inv, cU5_sigmaGL_apply_symm]

private theorem cU5_guSet_of_unitGroup {K : Type} [Field K] {n : ℕ} {d : ℕ} (h : UnitaryFieldData 2 n K) {M : GL (Fin d) K}
    (hM : M ∈ TableB.unitGroup (ι := Fin d) h.bar) :
    M ∈ LargeEvenGUSet (Fin d) K (2 ^ n) := by
  refine ⟨1, one_ne_zero, one_pow _, ?_⟩
  rw [one_smul, cU5_bar_map h]
  exact (TableB.mem_unitGroup).mp hM

private theorem cU5_scalar_mem_unit {K : Type} [Field K] {n : ℕ} {d : ℕ} (h : UnitaryFieldData 2 n K) {μ : Kˣ}
    (hμ : (μ : K) ^ (2 ^ n + 1) = 1) :
    GeneralLinearGroup.scalar (Fin d) μ ∈ TableB.unitGroup (ι := Fin d) h.bar := by
  rw [TableB.mem_unitGroup]
  have hmat : ((GeneralLinearGroup.scalar (Fin d) μ : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) = (μ : K) • 1 := by
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_eq_diagonal_mul, Matrix.mul_one]
  rw [hmat]
  have hmap : ((μ : K) • (1 : Matrix (Fin d) (Fin d) K)).map h.bar =
      h.bar (μ : K) • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [hmap, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h.bar_apply, mul_comm, ← pow_succ', hμ, one_smul, Matrix.transpose_one, Matrix.one_mul]
private theorem cU5_sigma_inv_comm_bar {K : Type} [Field K] {n : ℕ} [Fintype K] [CharP K 2] (h : UnitaryFieldData 2 n K)
    (σ₀ : K ≃+* K) :
    ∀ c, σ₀⁻¹ (h.bar c) = h.bar (σ₀⁻¹ c) := by
  obtain ⟨a, ha⟩ := exists_pow_two_of_ringEquiv σ₀⁻¹
  intro c
  rw [ha, h.bar_apply, ha, h.bar_apply, ← pow_mul, ← pow_mul, Nat.mul_comm]

private theorem cU5_lift_exists {K : Type} [Field K] {n : ℕ} {d : ℕ} [Fintype K] [CharP K 2] {p : ℕ}
    (h : UnitaryFieldData 2 n K) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2))
    (hp : p.Prime) (hp2 : p ≠ 2) (hpd : ¬ p ∣ d ∨ ¬ p ∣ 2 ^ n + 1)
    (σ₀ : K ≃+* K) (hσ₀ : orderOf σ₀ = p)
    (Ebar : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))))
    (hEab : IsElemAbelian p Ebar)
    (hEI : ∀ e ∈ Ebar, e ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n))) (LargeEvenGUSet (Fin d) K (2 ^ n)))
    (f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))
    (hf : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (fun s s' => ((s' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ₀) f)
    (hcomm : ∀ e ∈ Ebar, e * f = f * e)
    (ē : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) (hē : ē ∈ Ebar) :
    ∃ x : ↥(TableB.unitGroup (ι := Fin d) h.bar), uniConj h d x = ē ∧ x ^ p = 1 ∧
      (((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ₀ =
        ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) ∧
      (((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)).det = 1 := by
  classical
  have hK : Nat.card K = (2 ^ n) ^ 2 := by
    rw [h.card, show 2 ^ (2 * n) = (2 ^ n) ^ 2 by rw [← pow_mul, mul_comm]]
  have hKf : Fintype.card K = (2 ^ n) ^ 2 := by
    rw [← Nat.card_eq_fintype_card]; exact hK
  have hσbar : ∀ c, σ₀ (h.bar c) = h.bar (σ₀ c) := by
    obtain ⟨a, ha⟩ := exists_pow_two_of_ringEquiv σ₀
    intro c
    rw [ha, h.bar_apply, ha, h.bar_apply, ← pow_mul, ← pow_mul, Nat.mul_comm]
  have hσbar_inv : ∀ c, σ₀⁻¹ (h.bar c) = h.bar (σ₀⁻¹ c) :=
    cU5_sigma_inv_comm_bar h σ₀
  obtain ⟨A, hA, hAe⟩ := TableB.exists_eq_projConj
    (TableBUE.gu_subset_normalizer (d := d) h) (hEI ē hē)
  obtain ⟨u, huP⟩ := cU5_exists_unitary_of_gu h hA
  let A' : ↥(TableB.unitGroup (ι := Fin d) h.bar) :=
    ⟨GeneralLinearGroup.scalar (Fin d) u * A,
      cU5_mem_unitGroup_of_primeFormUnitary h huP⟩
  have hA'coe : ((A' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (u : K) • (A : Matrix (Fin d) (Fin d) K) := TableB.coe_scalar_mul u A
  have hA'e : uniConj h d A' = ē := by
    have hz : GeneralLinearGroup.scalar (Fin d) u ∈ LargeEvenScalars (Fin d) K := ⟨u, rfl⟩
    have hzN : GeneralLinearGroup.scalar (Fin d) u ∈
        Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K)) :=
      TableB.scalar_mem_normalizer _ hz
    have hprod : ((Subgroup.inclusion (uniGroup_le_normalizer h)) A' :
        Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K))) =
        ⟨GeneralLinearGroup.scalar (Fin d) u, hzN⟩ *
        ⟨A, TableBUE.gu_subset_normalizer (d := d) h hA⟩ := by
      apply Subtype.ext
      rfl
    calc uniConj h d A' = TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n))
          ((Subgroup.inclusion (uniGroup_le_normalizer h)) A') := rfl
      _ = TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n))
          (⟨GeneralLinearGroup.scalar (Fin d) u, hzN⟩ *
            ⟨A, TableBUE.gu_subset_normalizer (d := d) h hA⟩) := by rw [hprod]
      _ = TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n))
            ⟨A, TableBUE.gu_subset_normalizer (d := d) h hA⟩ := by
          rw [map_mul, TableB.projConj_of_scalar _ hz, one_mul]
      _ = ē := hAe.symm
  have hA'GU : (A' : GL (Fin d) K) ∈ LargeEvenGUSet (Fin d) K (2 ^ n) :=
    cU5_guSet_of_unitGroup h A'.2
  have hconj_pow : uniConj h d (A' ^ p) = 1 := by
    rw [map_pow, hA'e, hEab.2 ē hē]
  have hA'p_scalar : (((A' ^ p : ↥(TableB.unitGroup (ι := Fin d) h.bar)) :
      GL (Fin d) K) ∈ LargeEvenScalars (Fin d) K) :=
    cU5_mem_scalars_of_projConj_eq_one h hK hd hdq
      (M := (Subgroup.inclusion (uniGroup_le_normalizer h) (A' ^ p))) (by
        simpa [uniConj] using hconj_pow)
  obtain ⟨ν, hν⟩ := hA'p_scalar
  have hA'p_mat : (((A' ^ p : ↥(TableB.unitGroup (ι := Fin d) h.bar)) : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) = (ν : K) • 1 := by
    rw [← hν, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_eq_diagonal_mul, Matrix.mul_one]
  have hfield := cU5_field_conj (n := n) (d := d) h σ₀ hσbar hσbar_inv f hf A'
  have hcommf : f * uniConj h d A' * f⁻¹ = uniConj h d A' := by
    rw [hA'e]
    have h := (hcomm ē hē).symm
    calc f * ē * f⁻¹ = (ē * f) * f⁻¹ := by rw [h]
      _ = ē := by group
  have hc_eq : uniConj h d (cU5_sigmaU (n := n) (d := d) h σ₀ hσbar A') =
      uniConj h d A' := by
    rw [← hfield, hcommf]
  have hBker : TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n))
      ((Subgroup.inclusion (uniGroup_le_normalizer h))
        (cU5_sigmaU (n := n) (d := d) h σ₀ hσbar A' * A'⁻¹)) = 1 := by
    change uniConj h d (cU5_sigmaU (n := n) (d := d) h σ₀ hσbar A' * A'⁻¹) = 1
    rw [map_mul, map_inv, hc_eq, mul_inv_cancel]
  have hBscalar : (((cU5_sigmaU (n := n) (d := d) h σ₀ hσbar A' * A'⁻¹ :
      ↥(TableB.unitGroup (ι := Fin d) h.bar)) : GL (Fin d) K) ∈
      LargeEvenScalars (Fin d) K) :=
    cU5_mem_scalars_of_projConj_eq_one h hK hd hdq
      (M := (Subgroup.inclusion (uniGroup_le_normalizer h)
        (cU5_sigmaU (n := n) (d := d) h σ₀ hσbar A' * A'⁻¹))) hBker
  obtain ⟨lam, hlam⟩ := hBscalar
  have hsigma_eq : ((cU5_sigmaU (n := n) (d := d) h σ₀ hσbar A' :
      ↥(TableB.unitGroup (ι := Fin d) h.bar)) : GL (Fin d) K) =
      GeneralLinearGroup.scalar (Fin d) lam * (A' : GL (Fin d) K) := by
    have hBval : (((cU5_sigmaU (n := n) (d := d) h σ₀ hσbar A' * A'⁻¹ :
        ↥(TableB.unitGroup (ι := Fin d) h.bar)) : GL (Fin d) K)) =
        (cU5_sigmaU (n := n) (d := d) h σ₀ hσbar A' : GL (Fin d) K) * (A' : GL (Fin d) K)⁻¹ :=
      rfl
    calc (cU5_sigmaU (n := n) (d := d) h σ₀ hσbar A' : GL (Fin d) K) =
          ((cU5_sigmaU (n := n) (d := d) h σ₀ hσbar A' : GL (Fin d) K) *
            (A' : GL (Fin d) K)⁻¹) * (A' : GL (Fin d) K) := by group
      _ = (((cU5_sigmaU (n := n) (d := d) h σ₀ hσbar A' * A'⁻¹ :
          ↥(TableB.unitGroup (ι := Fin d) h.bar)) : GL (Fin d) K)) *
            (A' : GL (Fin d) K) := by rw [hBval]
      _ = GeneralLinearGroup.scalar (Fin d) lam * (A' : GL (Fin d) K) := by rw [hlam]
  have hx : ((A' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ₀ =
      (lam : K) • ((A' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    calc ((A' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ₀ =
          (((cU5_sigmaU (n := n) (d := d) h σ₀ hσbar A' :
            ↥(TableB.unitGroup (ι := Fin d) h.bar)) : GL (Fin d) K) :
            Matrix (Fin d) (Fin d) K) := (cU5_sigmaU_coe h σ₀ hσbar A').symm
      _ = ((GeneralLinearGroup.scalar (Fin d) lam * (A' : GL (Fin d) K) : GL (Fin d) K) :
            Matrix (Fin d) (Fin d) K) := by rw [hsigma_eq]
      _ = (lam : K) • ((A' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
          TableB.coe_scalar_mul lam (A' : GL (Fin d) K)
  obtain ⟨μ, hμfix, hμp, hμunit⟩ := uni_descent (q := 2 ^ n) hp hpd hKf σ₀ hσ₀
    (A' : GL (Fin d) K) hA'GU lam hx ν hA'p_mat
  let x₁ : ↥(TableB.unitGroup (ι := Fin d) h.bar) :=
    ⟨GeneralLinearGroup.scalar (Fin d) μ * (A' : GL (Fin d) K), by
      rw [TableB.mem_unitGroup, TableB.coe_scalar_mul, ← cU5_bar_map h]
      exact hμunit⟩
  have hx₁coe : ((x₁ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (μ : K) • ((A' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
    TableB.coe_scalar_mul μ (A' : GL (Fin d) K)
  have hx₁fix : ((x₁ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ₀ =
      ((x₁ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    rw [hx₁coe]
    simpa [Matrix.map_smul] using hμfix
  have hx₁p : x₁ ^ p = 1 := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one, Units.val_pow_eq_pow_val]
    rw [hx₁coe]
    exact hμp
  have hx₁e : uniConj h d x₁ = ē := by
    have hz : GeneralLinearGroup.scalar (Fin d) μ ∈ LargeEvenScalars (Fin d) K := ⟨μ, rfl⟩
    have hzN : GeneralLinearGroup.scalar (Fin d) μ ∈
        Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K)) :=
      TableB.scalar_mem_normalizer _ hz
    have hprod : ((Subgroup.inclusion (uniGroup_le_normalizer h)) x₁ :
        Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K))) =
        ⟨GeneralLinearGroup.scalar (Fin d) μ, hzN⟩ *
        ((Subgroup.inclusion (uniGroup_le_normalizer h)) A') := by
      apply Subtype.ext
      rfl
    calc uniConj h d x₁ = TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n))
          ((Subgroup.inclusion (uniGroup_le_normalizer h)) x₁) := rfl
      _ = TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n))
          (⟨GeneralLinearGroup.scalar (Fin d) μ, hzN⟩ *
            ((Subgroup.inclusion (uniGroup_le_normalizer h)) A')) := by rw [hprod]
      _ = TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n))
            ((Subgroup.inclusion (uniGroup_le_normalizer h)) A') := by
          rw [map_mul, TableB.projConj_of_scalar _ hz, one_mul]
      _ = ē := hA'e
  obtain ⟨μ₂, hσμ₂, hμ₂p, hμ₂q, hμ₂det⟩ :=
    uni_sl_adjust h hp hpd σ₀ x₁ hx₁p hx₁fix
  let x : ↥(TableB.unitGroup (ι := Fin d) h.bar) :=
    ⟨GeneralLinearGroup.scalar (Fin d) μ₂ * (x₁ : GL (Fin d) K),
      mul_mem (cU5_scalar_mem_unit h hμ₂q) x₁.2⟩
  have hxcoe : ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (μ₂ : K) • ((x₁ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
    TableB.coe_scalar_mul μ₂ (x₁ : GL (Fin d) K)
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  · have hz : GeneralLinearGroup.scalar (Fin d) μ₂ ∈ LargeEvenScalars (Fin d) K := ⟨μ₂, rfl⟩
    have hzN : GeneralLinearGroup.scalar (Fin d) μ₂ ∈
        Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K)) :=
      TableB.scalar_mem_normalizer _ hz
    have hprod : ((Subgroup.inclusion (uniGroup_le_normalizer h)) x :
        Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K))) =
        ⟨GeneralLinearGroup.scalar (Fin d) μ₂, hzN⟩ *
        ((Subgroup.inclusion (uniGroup_le_normalizer h)) x₁) := by
      apply Subtype.ext
      rfl
    calc uniConj h d x = TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n))
          ((Subgroup.inclusion (uniGroup_le_normalizer h)) x) := rfl
      _ = TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n))
          (⟨GeneralLinearGroup.scalar (Fin d) μ₂, hzN⟩ *
            ((Subgroup.inclusion (uniGroup_le_normalizer h)) x₁)) := by rw [hprod]
      _ = TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n))
            ((Subgroup.inclusion (uniGroup_le_normalizer h)) x₁) := by
          rw [map_mul, TableB.projConj_of_scalar _ hz, one_mul]
      _ = ē := hx₁e
  · apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one, Units.val_pow_eq_pow_val]
    rw [hxcoe, smul_pow]
    have hμ₂p' : (μ₂ : K) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, hμ₂p, Units.val_one]
    have hx₁p' : ((x₁ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, hx₁p, Subgroup.coe_one,
        Units.val_one]
    rw [hμ₂p', hx₁p', one_smul]
    rfl
  · rw [hxcoe]
    rw [Matrix.map_smul' σ₀ (μ₂ : K) ((x₁ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
      (map_mul σ₀), hσμ₂, hx₁fix]
  · rw [hxcoe]
    exact hμ₂det

private theorem cU5_lift_commute {K : Type} [Field K] {n : ℕ} {d : ℕ} [Fintype K] [CharP K 2] {p : ℕ}
    (h : UnitaryFieldData 2 n K) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2))
    (hp : p.Prime) (hpd : ¬ p ∣ d ∨ ¬ p ∣ 2 ^ n + 1)
    (Ebar : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))))
    (hEab : IsElemAbelian p Ebar)
    {x y : ↥(TableB.unitGroup (ι := Fin d) h.bar)}
    (hx : uniConj h d x ∈ Ebar) (hy : uniConj h d y ∈ Ebar)
    (hyp : y ^ p = 1) (hxp : x ^ p = 1) : x * y = y * x := by
  refine uni_commute_of_conj_commute h hd hdq hp hpd (Subgroup.zpowers y) ?_ x ?_
    y (Subgroup.mem_zpowers y)
  · rw [Subgroup.forall_mem_zpowers]
    intro m
    have hypz : y ^ (p : ℤ) = 1 := by rw [zpow_natCast, hyp]
    calc (y ^ m) ^ p = (y ^ m) ^ (p : ℤ) := by rw [zpow_natCast]
      _ = y ^ (m * (p : ℤ)) := by rw [_root_.zpow_mul]
      _ = y ^ ((p : ℤ) * m) := by rw [mul_comm]
      _ = (y ^ (p : ℤ)) ^ m := by rw [_root_.zpow_mul]
      _ = 1 := by rw [hypz, _root_.one_zpow]
  · rw [Subgroup.forall_mem_zpowers]
    intro m
    have hc : Commute (uniConj h d x) (uniConj h d y) := IsElemAbelian.comm hEab hx hy
    have hcomm := (hc.zpow_right m).eq
    rwa [map_zpow]

private theorem cU5_scalar_norm_of_mem {K : Type} [Field K] {n : ℕ} {d : ℕ} (h : UnitaryFieldData 2 n K) {c : Kˣ} (hd : 0 < d)
    (hc : GeneralLinearGroup.scalar (Fin d) c ∈ TableB.unitGroup (ι := Fin d) h.bar) :
    (c : K) ^ (2 ^ n + 1) = 1 := by
  have hcm : ((GeneralLinearGroup.scalar (Fin d) c : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) = (c : K) • 1 := by
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_eq_diagonal_mul, Matrix.mul_one]
  have hm := (TableB.mem_unitGroup).mp hc
  rw [hcm] at hm
  have hmap : ((c : K) • (1 : Matrix (Fin d) (Fin d) K)).map h.bar =
      h.bar (c : K) • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [hmap, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.transpose_one, Matrix.one_mul] at hm
  have h00 := congrArg (fun M : Matrix (Fin d) (Fin d) K =>
    M ⟨0, hd⟩ ⟨0, hd⟩) hm
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, mul_one] at h00
  rw [h.bar_apply, mul_comm, ← pow_succ'] at h00
  simpa using h00
theorem uni_E0_lift {K : Type} [Field K] {n : ℕ} {d : ℕ} [Fintype K] [CharP K 2] {p : ℕ} (h : UnitaryFieldData 2 n K) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpd : ¬ p ∣ d ∨ ¬ p ∣ 2 ^ n + 1) (σ₀ : K ≃+* K) (hσ₀ : orderOf σ₀ = p)
    (Ebar : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))))
    (hEab : IsElemAbelian p Ebar)
    (hEI : ∀ e ∈ Ebar, e ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n))) (LargeEvenGUSet (Fin d) K (2 ^ n)))
    (f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))
    (hf : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (fun s s' => ((s' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ₀) f)
    (hcomm : ∀ e ∈ Ebar, e * f = f * e) :
    ∃ E₀ : Subgroup ↥(TableB.unitGroup (ι := Fin d) h.bar), IsElemAbelian p E₀ ∧
      (∀ e ∈ E₀, ((e : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ₀ =
        ((e : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) ∧
      (∀ x ∈ E₀, ∀ y ∈ E₀, uniConj h d x = uniConj h d y → x = y) ∧
      ∀ e, e ∈ Ebar ↔ ∃ x ∈ E₀, uniConj h d x = e := by
  classical
  have hK : Nat.card K = (2 ^ n) ^ 2 := by
    rw [h.card, show 2 ^ (2 * n) = (2 ^ n) ^ 2 by rw [← pow_mul, mul_comm]]
  have hσbar : ∀ c, σ₀ (h.bar c) = h.bar (σ₀ c) := by
    obtain ⟨a, ha⟩ := exists_pow_two_of_ringEquiv σ₀
    intro c
    rw [ha, h.bar_apply, ha, h.bar_apply, ← pow_mul, ← pow_mul, Nat.mul_comm]
  let lift : Ebar → ↥(TableB.unitGroup (ι := Fin d) h.bar) := fun ē =>
    Classical.choose (cU5_lift_exists (n := n) (d := d) h hd hdq hp hp2 hpd σ₀ hσ₀
      Ebar hEab hEI f hf hcomm ē.1 ē.2)
  have hspec : ∀ ē : Ebar,
      uniConj h d (lift ē) = (ē : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) ∧
      (lift ē) ^ p = 1 ∧
      ((((lift ē : ↥(TableB.unitGroup (ι := Fin d) h.bar)) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K).map σ₀ =
        (((lift ē : ↥(TableB.unitGroup (ι := Fin d) h.bar)) : GL (Fin d) K) :
          Matrix (Fin d) (Fin d) K)) ∧
      ((((lift ē : ↥(TableB.unitGroup (ι := Fin d) h.bar)) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K)).det = 1 :=
    fun ē => Classical.choose_spec (cU5_lift_exists (n := n) (d := d) h hd hdq hp hp2 hpd
      σ₀ hσ₀ Ebar hEab hEI f hf hcomm ē.1 ē.2)
  let s : Set ↥(TableB.unitGroup (ι := Fin d) h.bar) := Set.range lift
  have hEab₀ : IsElemAbelian p (Subgroup.closure s) := by
    refine IsElemAbelian.closure_of_commute ?_ ?_
    · rintro a ⟨ē₁, rfl⟩ b ⟨ē₂, rfl⟩
      exact cU5_lift_commute h hd hdq hp hpd Ebar hEab
        (by rw [(hspec ē₁).1]; exact ē₁.2)
        (by rw [(hspec ē₂).1]; exact ē₂.2)
        (hspec ē₂).2.1 (hspec ē₁).2.1
    · rintro a ⟨ē, rfl⟩
      exact (hspec ē).2.1
  have hfixU : ∀ e ∈ Subgroup.closure s,
      cU5_sigmaU (n := n) (d := d) h σ₀ hσbar e = e := by
    intro e he
    induction he using Subgroup.closure_induction with
    | mem a ha =>
        obtain ⟨ē, rfl⟩ := ha
        apply Subtype.ext
        apply Units.ext
        exact (cU5_sigmaU_coe h σ₀ hσbar (lift ē)).trans (hspec ē).2.2.1
    | one => exact map_one _
    | mul a b ha hb iha ihb => rw [map_mul, iha, ihb]
    | inv a ha iha => rw [map_inv, iha]
  have hEfix : ∀ e ∈ Subgroup.closure s,
      (((e : ↥(TableB.unitGroup (ι := Fin d) h.bar)) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K).map σ₀ =
      (((e : ↥(TableB.unitGroup (ι := Fin d) h.bar)) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) := by
    intro e he
    rw [← cU5_sigmaU_coe h σ₀ hσbar e, hfixU e he]
  have hconj_mem : ∀ e ∈ Subgroup.closure s, uniConj h d e ∈ Ebar := by
    intro e he
    induction he using Subgroup.closure_induction with
    | mem a ha =>
        obtain ⟨ē, rfl⟩ := ha
        rw [(hspec ē).1]
        exact ē.2
    | one => rw [map_one]; exact Ebar.one_mem
    | mul a b ha hb iha ihb => rw [map_mul]; exact Ebar.mul_mem iha ihb
    | inv a ha iha => rw [map_inv]; exact Ebar.inv_mem iha
  have hdetu : ∀ y : GL (Fin d) K, ((y : Matrix (Fin d) (Fin d) K).det) *
      (((y⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).det) = 1 := fun y => by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hdet : ∀ e ∈ Subgroup.closure s,
      (((e : ↥(TableB.unitGroup (ι := Fin d) h.bar)) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K).det = 1 := by
    intro e he
    induction he using Subgroup.closure_induction with
    | mem a ha => obtain ⟨ē, rfl⟩ := ha; exact (hspec ē).2.2.2
    | one => rw [Subgroup.coe_one, Units.val_one, Matrix.det_one]
    | mul a b ha hb iha ihb =>
        rw [Subgroup.coe_mul, Units.val_mul, Matrix.det_mul, iha, ihb, one_mul]
    | inv a ha iha =>
        have h := hdetu ((a : ↥(TableB.unitGroup (ι := Fin d) h.bar)) : GL (Fin d) K)
        rw [iha, one_mul] at h
        simpa [Subgroup.coe_inv] using h
  have hinj : ∀ x ∈ Subgroup.closure s, ∀ y ∈ Subgroup.closure s,
      uniConj h d x = uniConj h d y → x = y := by
    intro x hx y hy hxy
    have h1 : uniConj h d (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have hscalar : (((x * y⁻¹ : ↥(TableB.unitGroup (ι := Fin d) h.bar)) : GL (Fin d) K) ∈
        LargeEvenScalars (Fin d) K) :=
      cU5_mem_scalars_of_projConj_eq_one h hK hd hdq
        (M := (Subgroup.inclusion (uniGroup_le_normalizer h) (x * y⁻¹))) (by
          simpa [uniConj] using h1)
    obtain ⟨c, hc⟩ := hscalar
    have hxyGL : (x : GL (Fin d) K) =
        GeneralLinearGroup.scalar (Fin d) c * (y : GL (Fin d) K) := by
      have h1' : (((x * y⁻¹ : ↥(TableB.unitGroup (ι := Fin d) h.bar)) : GL (Fin d) K)) =
          GeneralLinearGroup.scalar (Fin d) c := hc.symm
      calc (x : GL (Fin d) K) = ((x : GL (Fin d) K) * (y : GL (Fin d) K)⁻¹) *
            (y : GL (Fin d) K) := by group
        _ = (((x * y⁻¹ : ↥(TableB.unitGroup (ι := Fin d) h.bar)) : GL (Fin d) K)) *
              (y : GL (Fin d) K) := by rw [Subgroup.coe_mul, Subgroup.coe_inv]
        _ = GeneralLinearGroup.scalar (Fin d) c * (y : GL (Fin d) K) := by rw [h1']
    have hmat : (((x : ↥(TableB.unitGroup (ι := Fin d) h.bar)) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) =
        (c : K) • (((y : ↥(TableB.unitGroup (ι := Fin d) h.bar)) : GL (Fin d) K) :
          Matrix (Fin d) (Fin d) K) := by
      rw [hxyGL, TableB.coe_scalar_mul]
    have hcd : (c : K) ^ d = 1 := by
      have h := congrArg Matrix.det hmat
      rw [Matrix.det_smul, Fintype.card_fin, hdet x hx, hdet y hy, mul_one] at h
      exact h.symm
    have hcp : (c : K) ^ p = 1 := by
      have hcUmem : GeneralLinearGroup.scalar (Fin d) c ∈
          TableB.unitGroup (ι := Fin d) h.bar := by
        rw [hc]
        exact (x * y⁻¹).2
      have hcUp : (GeneralLinearGroup.scalar (Fin d) c) ^ p = 1 := by
        rw [hc]
        rw [← Subgroup.coe_pow, hEab₀.2 (x * y⁻¹)
          (Subgroup.mul_mem (Subgroup.closure s) hx (Subgroup.inv_mem (Subgroup.closure s) hy))]
        rfl
      have hsc : GeneralLinearGroup.scalar (Fin d) (c ^ p) = 1 := by
        rw [map_pow]; exact hcUp
      have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
      have h00 := congrArg (fun u : GL (Fin d) K =>
        ((u : Matrix (Fin d) (Fin d) K) ⟨0, hd0⟩ ⟨0, hd0⟩)) hsc
      rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h00
      simpa [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] using h00
    have hcq : (c : K) ^ (2 ^ n + 1) = 1 := by
      exact cU5_scalar_norm_of_mem h (lt_of_lt_of_le (by norm_num) hd)
        (by rw [hc]; exact (x * y⁻¹).2)
    have hc1 : c = 1 := cU5_scalar_eq_one hp hpd c hcd hcp hcq
    have hxy' : (x : GL (Fin d) K) = (y : GL (Fin d) K) := by
      rw [hxyGL, hc1, map_one, one_mul]
    exact Subtype.ext hxy'
  refine ⟨Subgroup.closure s, hEab₀, hEfix, hinj, ?_⟩
  intro e
  constructor
  · intro he
    refine ⟨lift ⟨e, he⟩, Subgroup.subset_closure ⟨⟨e, he⟩, rfl⟩, ?_⟩
    exact (hspec ⟨e, he⟩).1
  · rintro ⟨x, hx, rfl⟩
    exact hconj_mem x hx

private lemma cU6_scalar_mem_unitGroup {K : Type} [Field K] {n d : ℕ}
    (h : UnitaryFieldData 2 n K) {μ : Kˣ} (hμ : (μ : K) ^ (2 ^ n + 1) = 1) :
    GeneralLinearGroup.scalar (Fin d) μ ∈ TableB.unitGroup (ι := Fin d) h.bar := by
  rw [TableB.mem_unitGroup, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [UnitaryFieldData.bar_apply]
  simpa [pow_succ] using hμ

private lemma cU6_map_smul {K : Type} [Field K] {d : ℕ} (σ : K ≃+* K) (c : K)
    (M : Matrix (Fin d) (Fin d) K) : (c • M).map σ = σ c • M.map σ := by
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply]

theorem uni_sat_translate {K : Type} [Field K] {n : ℕ} {d : ℕ} [Fintype K] [CharP K 2] {p : ℕ} (h : UnitaryFieldData 2 n K) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime) (hpd : ¬ p ∣ d ∨ ¬ p ∣ 2 ^ n + 1) (σ₀ : K ≃+* K)
    (E₀ : Subgroup ↥(TableB.unitGroup (ι := Fin d) h.bar))
    (Ebar : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))))
    (hE₀ : ∀ e, e ∈ Ebar ↔ ∃ x ∈ E₀, uniConj h d x = e)
    (f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))
    (hf : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (fun s s' => ((s' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ₀) f)
    (hSatR : ∀ r : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)), r ^ p = 1 →
      (∀ e ∈ Ebar, e r = r) → f r = r → MulAut.conj r ∈ Ebar) :
    ∀ y : ↥(TableB.unitGroup (ι := Fin d) h.bar), (∀ e ∈ E₀, y * e = e * y) → y ^ p = 1 →
      ((y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ₀ =
        ((y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) →
      ((y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ∈
        spanE K (E₀.map (TableB.unitGroup (ι := Fin d) h.bar).subtype) := by
  classical
  haveI : Finite K := h.finite
  intro y hycomm hyp hyfix
  obtain ⟨μ, hσμ, hμp, hμK, hdet⟩ := uni_sl_adjust h hp hpd σ₀ y hyp hyfix
  have hσμ' : σ₀ (μ : K) = (μ : K) := hσμ
  have hμp' : (μ : K) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val μ p, hμp, Units.val_one]
  have hyp' : ((y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ^ p = 1 := by
    have h2 : (y : GL (Fin d) K) ^ p = 1 := by
      rw [← Subgroup.coe_pow, hyp]; rfl
    rw [← Units.val_pow_eq_pow_val (y : GL (Fin d) K) p, h2]
    rfl
  let zG : GL (Fin d) K := GeneralLinearGroup.scalar (Fin d) μ * (y : GL (Fin d) K)
  have hzmat : (zG : Matrix (Fin d) (Fin d) K) =
      (μ : K) • ((y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
    TableB.coe_scalar_mul μ (y : GL (Fin d) K)
  have hscalarU : GeneralLinearGroup.scalar (Fin d) μ ∈
      TableB.unitGroup (ι := Fin d) h.bar := cU6_scalar_mem_unitGroup h hμK
  have hzU : zG ∈ TableB.unitGroup (ι := Fin d) h.bar :=
    Subgroup.mul_mem _ hscalarU y.2
  have hdetZ : (zG : Matrix (Fin d) (Fin d) K).det = 1 := by
    rw [hzmat]; exact hdet
  have hzSU : zG ∈ LargeEvenSUGroup (Fin d) K (2 ^ n) := by
    change zG ∈ ClassicalGroups.UnitaryFlag.unitarySU 2 n K d
    rw [ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h]
    exact ⟨hdetZ, TableB.mem_unitGroup.mp hzU⟩
  let zU : ↥(TableB.unitGroup (ι := Fin d) h.bar) := ⟨zG, hzU⟩
  let zSU : ↥(LargeEvenSUGroup (Fin d) K (2 ^ n)) := ⟨zG, hzSU⟩
  let r : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) :=
    LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)) zSU
  have hzG_pow : zG ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hzmat, smul_pow, hμp', hyp', one_smul, Units.val_one]
  have hzSU_pow : zSU ^ p = 1 := by
    apply Subtype.ext
    change zG ^ p = 1
    exact hzG_pow
  have hr_pow : r ^ p = 1 := by
    rw [show r = LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)) zSU from rfl,
      ← map_pow, hzSU_pow, map_one]
  have hzfix : (zG : Matrix (Fin d) (Fin d) K).map σ₀ = zG := by
    rw [hzmat, cU6_map_smul, hσμ', hyfix, ← hzmat]
  have hfr : f r = r := hf zSU zSU hzfix.symm
  have hscalarScal : GeneralLinearGroup.scalar (Fin d) μ ∈ LargeEvenScalars (Fin d) K :=
    ⟨μ, rfl⟩
  have huniConj_scalar :
      uniConj h d ⟨GeneralLinearGroup.scalar (Fin d) μ, hscalarU⟩ = 1 := by
    change TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n))
      (Subgroup.inclusion (uniGroup_le_normalizer h)
        ⟨GeneralLinearGroup.scalar (Fin d) μ, hscalarU⟩) = 1
    rw [show Subgroup.inclusion (uniGroup_le_normalizer h)
          ⟨GeneralLinearGroup.scalar (Fin d) μ, hscalarU⟩ =
        ⟨GeneralLinearGroup.scalar (Fin d) μ,
          TableB.scalar_mem_normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n)) hscalarScal⟩
        from Subtype.ext rfl]
    exact TableB.projConj_of_scalar _ hscalarScal
  have huniConj_z : uniConj h d zU = MulAut.conj r := by
    change TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n))
      (Subgroup.inclusion (uniGroup_le_normalizer h) zU) = MulAut.conj r
    rw [show Subgroup.inclusion (uniGroup_le_normalizer h) zU =
        ⟨zG, Subgroup.le_normalizer hzSU⟩ from Subtype.ext rfl]
    exact TableB.projConj_of_mem _ zG hzSU
  have huniConj_y : uniConj h d y = MulAut.conj r := by
    have h1 : uniConj h d zU =
        uniConj h d ⟨GeneralLinearGroup.scalar (Fin d) μ, hscalarU⟩ * uniConj h d y := by
      rw [show zU = ⟨GeneralLinearGroup.scalar (Fin d) μ, hscalarU⟩ * y from Subtype.ext rfl,
        map_mul]
    rw [huniConj_scalar, one_mul] at h1
    rw [← h1, huniConj_z]
  have hfixE : ∀ e ∈ Ebar, e r = r := by
    intro e he
    obtain ⟨x, hxE, hxeq⟩ := (hE₀ e).mp he
    rw [← hxeq]
    have hA : ((LargeEvenSUGroup (Fin d) K (2 ^ n)).normalizerMonoidHom
        (Subgroup.inclusion (uniGroup_le_normalizer h) x)) zSU = zSU := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion]
      have hxs : (x : GL (Fin d) K) * GeneralLinearGroup.scalar (Fin d) μ =
          GeneralLinearGroup.scalar (Fin d) μ * (x : GL (Fin d) K) :=
        (GeneralLinearGroup.scalar_commute μ (x : GL (Fin d) K)).symm
      have hxy : (x : GL (Fin d) K) * (y : GL (Fin d) K) =
          (y : GL (Fin d) K) * (x : GL (Fin d) K) := by
        have h := congrArg
          (fun g : ↥(TableB.unitGroup (ι := Fin d) h.bar) => (g : GL (Fin d) K))
          (hycomm x hxE)
        rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
        exact h.symm
      have hcomm : (x : GL (Fin d) K) * zG = zG * (x : GL (Fin d) K) := by
        show (x : GL (Fin d) K) *
            (GeneralLinearGroup.scalar (Fin d) μ * (y : GL (Fin d) K)) =
          (GeneralLinearGroup.scalar (Fin d) μ * (y : GL (Fin d) K)) *
            (x : GL (Fin d) K)
        rw [← mul_assoc (x : GL (Fin d) K) (GeneralLinearGroup.scalar (Fin d) μ)
            (y : GL (Fin d) K), hxs,
          mul_assoc (GeneralLinearGroup.scalar (Fin d) μ) (x : GL (Fin d) K)
            (y : GL (Fin d) K), hxy, mul_assoc]
      calc (x : GL (Fin d) K) * zG * (x : GL (Fin d) K)⁻¹
          = zG * (x : GL (Fin d) K) * (x : GL (Fin d) K)⁻¹ := by rw [hcomm]
        _ = zG := by group
    change uniConj h d x (zSU : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) =
      (zSU : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
    rw [show uniConj h d x = TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n))
        (Subgroup.inclusion (uniGroup_le_normalizer h) x) from rfl,
      TableB.projConj_mk, hA]
  obtain ⟨x, hxE, hxeq⟩ :=
    (hE₀ (MulAut.conj r)).mp (hSatR r hr_pow hfixE hfr)
  have hyx1 : uniConj h d (y * x⁻¹) = 1 := by
    rw [map_mul, map_inv, huniConj_y, hxeq, mul_inv_cancel]
  let M : Subgroup.normalizer
      (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K)) :=
    Subgroup.inclusion (uniGroup_le_normalizer h) (y * x⁻¹)
  have hM1 : TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n)) M = 1 := by
    change uniConj h d (y * x⁻¹) = 1
    exact hyx1
  have hne : 2 ^ n + 1 ≠ 1 := by
    have hn1 : 1 ≤ n := h.one_le
    have hn : n ≠ 0 := by omega
    have := Nat.one_lt_two_pow hn
    omega
  obtain ⟨p', hp'prime, hp'div⟩ := Nat.exists_prime_and_dvd hne
  have hMscal : (M : GL (Fin d) K) ∈ LargeEvenScalars (Fin d) K :=
    TableBUE.mem_scalars_of_projConj_eq_one h h.card_eq_sq hd hdq hp'prime hp'div hM1
  have hMrange : (M : GL (Fin d) K) ∈ (GeneralLinearGroup.scalar (Fin d)).range := by
    rw [← largeEvenScalars_def]; exact hMscal
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hMrange
  have hMval : (M : GL (Fin d) K) = (y : GL (Fin d) K) * (x : GL (Fin d) K)⁻¹ := by
    rw [Subgroup.coe_inclusion, Subgroup.coe_mul, Subgroup.coe_inv]
  have hy_eq : (y : GL (Fin d) K) =
      GeneralLinearGroup.scalar (Fin d) c * (x : GL (Fin d) K) := by
    rw [hc, hMval]
    group
  have hyval : ((y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (c : K) • ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    rw [hy_eq, TableB.coe_scalar_mul]
  have hxspan : ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ∈
      spanE K (E₀.map (TableB.unitGroup (ι := Fin d) h.bar).subtype) :=
    Submodule.subset_span ⟨⟨(x : GL (Fin d) K), Subgroup.mem_map.mpr ⟨x, hxE, rfl⟩⟩, rfl⟩
  rw [hyval]
  exact Submodule.smul_mem _ (c : K) hxspan

end CFSG.HardMathSupport.C14Cl
