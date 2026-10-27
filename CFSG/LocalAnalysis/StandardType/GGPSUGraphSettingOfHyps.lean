module

public import CFSG.LocalAnalysis.StandardType.GGPSUGraphLayer0

public section

namespace CFSG.StandardType

open Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.BorelTits (unitaryInvolution)

private lemma psuC0_sigma_apply {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (h : UnitaryFieldData 2 f K) :
    (⇑(unitaryInvolution K 2 f) : K → K) = ⇑h.bar :=
  funext fun c => by
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, h.bar_apply]

private lemma psuC0_sigma_map {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (h : UnitaryFieldData 2 f K) (M : Matrix (Fin n) (Fin n) K) :
    M.map (unitaryInvolution K 2 f) = M.map h.bar :=
  Matrix.ext fun i j => by
    rw [Matrix.map_apply, Matrix.map_apply]
    exact congrFun (psuC0_sigma_apply h) (M i j)

private lemma psuC0_coe_scalar_mul {n : ℕ} {K : Type} [Field K] (c : Kˣ) (B : GL (Fin n) K) :
    ((GeneralLinearGroup.scalar (Fin n) c * B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (c : K) • (B : Matrix (Fin n) (Fin n) K) := by
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar]
  ext i j
  simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
    Finset.sum_ite_eq, Finset.sum_ite_eq']

private lemma psuC0_theta_mem {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (h : UnitaryFieldData 2 f K) (X : primeFormUnitary h (psuJ n K)) (x : AutPSU.XJ h n) :
    ((X : GL (Fin n) K) * glAut (unitaryInvolution K 2 f) (x : GL (Fin n) K) *
      (X : GL (Fin n) K)⁻¹) ∈ AutPSU.XJ h n := by
  exact conj_mem_gramSU h (psuJ n K) X.2
    (glAut_mem_gramSU h (AutPSU.isPrimeFormGram_gramJ (n := n)) (unitaryInvolution K 2 f) x.2)

private lemma psuC0_theta_eq {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (h : UnitaryFieldData 2 f K) (X : GL (Fin n) K) (x : GL (Fin n) K) :
    psuTheta h X (x : Matrix (Fin n) (Fin n) K) =
      (((X : GL (Fin n) K) * glAut (unitaryInvolution K 2 f) (x : GL (Fin n) K) *
        (X : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rw [psuTheta]
  simp only [Units.val_mul, coe_glAut]
  rw [psuC0_sigma_map h]

private lemma psuC0_scalar_mem_normOne {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hn : 1 ≤ n) {c : Kˣ}
    (hc : GeneralLinearGroup.scalar (Fin n) c ∈ AutPSU.XJ h n) :
    (⟨GeneralLinearGroup.scalar (Fin n) c, hc⟩ : AutPSU.XJ h n) ∈
      normOneScalars h (AutPSU.XJ h n) n := by
  rw [mem_normOneScalars]
  obtain ⟨hpu, hdet⟩ := (mem_gramSU_iff_unitary h).mp hc
  refine ⟨c, ?_, ?_, rfl⟩
  · exact norm_eq_one_of_scalar_mem_primeFormUnitary h hn (AutPSU.gramJ (K := K) n) hpu
  · have hd := hdet
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal] at hd
    refine Units.ext ?_
    simpa [Units.val_pow_eq_pow_val] using hd

private lemma psuC0_mk_eq_of_scalar_mul {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hn : 1 ≤ n) {x y : AutPSU.XJ h n} {c : Kˣ}
    (hc : GeneralLinearGroup.scalar (Fin n) c ∈ AutPSU.XJ h n)
    (hy : (y : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c * (x : GL (Fin n) K)) :
    (QuotientGroup.mk y : AutPSU.PJ h n) = QuotientGroup.mk x := by
  have hzN : (⟨GeneralLinearGroup.scalar (Fin n) c, hc⟩ : AutPSU.XJ h n) ∈
      normOneScalars h (AutPSU.XJ h n) n := psuC0_scalar_mem_normOne h hn hc
  have hz1 : (QuotientGroup.mk (⟨GeneralLinearGroup.scalar (Fin n) c, hc⟩ :
      AutPSU.XJ h n) : AutPSU.PJ h n) = 1 := (QuotientGroup.eq_one_iff _).mpr hzN
  have hy' : y = (⟨GeneralLinearGroup.scalar (Fin n) c, hc⟩ : AutPSU.XJ h n) * x :=
    Subtype.ext hy
  rw [hy', QuotientGroup.mk_mul, hz1, one_mul]

private lemma psuC0_alpha_mk {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (h : UnitaryFieldData 2 f K) (X : primeFormUnitary h (psuJ n K)) (g : AutPSU.XJ h n) :
    psuAlpha h (primeFormConjHom h (psuJ n K) X) (QuotientGroup.mk g : AutPSU.PJ h n) =
      QuotientGroup.mk (⟨(X : GL (Fin n) K) *
        glAut (unitaryInvolution K 2 f) (g : GL (Fin n) K) * (X : GL (Fin n) K)⁻¹,
        psuC0_theta_mem h X g⟩ : AutPSU.XJ h n) := by
  rw [psuAlpha, MulAut.mul_apply]
  change primeFormConjHom h (psuJ n K) X
    (primeFormFieldAut h (AutPSU.isPrimeFormGram_gramJ (n := n)) (unitaryInvolution K 2 f)
      (QuotientGroup.mk g : AutPSU.PJ h n)) = _
  rw [primeFormFieldAut_mk, primeFormConjHom_mk]
  rfl

private lemma psuC0_ker {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hn : 4 ≤ n) {A B : primeFormUnitary h (psuJ n K)}
    (hAB : primeFormConjHom h (psuJ n K) A = primeFormConjHom h (psuJ n K) B) :
    ∃ c : Kˣ, (A : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c * (B : GL (Fin n) K) := by
  have h1 : primeFormConjHom h (psuJ n K) (A * B⁻¹) = 1 := by
    rw [map_mul, map_inv, hAB, mul_inv_cancel]
  obtain ⟨c, -, hc⟩ := eq_scalar_of_primeFormConjHom_eq_one h
    (AutPSU.isPrimeFormGram_gramJ (n := n)) (by omega) h1
  refine ⟨c, ?_⟩
  have hc' : (A : GL (Fin n) K) * (B : GL (Fin n) K)⁻¹ =
      GeneralLinearGroup.scalar (Fin n) c := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hc
  calc (A : GL (Fin n) K)
      = (A : GL (Fin n) K) * (B : GL (Fin n) K)⁻¹ * (B : GL (Fin n) K) := by group
    _ = GeneralLinearGroup.scalar (Fin n) c * (B : GL (Fin n) K) := by rw [hc']

private lemma psuC0_Xsq {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (h : UnitaryFieldData 2 f K) (hn : 4 ≤ n) (X : primeFormUnitary h (psuJ n K))
    (hN : ∃ c : Kˣ, h.norm (c : K) = 1 ∧ (X : GL (Fin n) K) *
      glAut (unitaryInvolution K 2 f) (X : GL (Fin n) K) =
        GeneralLinearGroup.scalar (Fin n) c) :
    ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar = 1 := by
  obtain ⟨c, hcN, hc⟩ := hN
  set Am : Matrix (Fin n) (Fin n) K := ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAm
  have hc' : Am * Am.map h.bar = Matrix.scalar (Fin n) (c : K) := by
    have h1 := congrArg (fun t : GL (Fin n) K => (t : Matrix (Fin n) (Fin n) K)) hc
    simp only [Units.val_mul, coe_glAut, GeneralLinearGroup.coe_scalar] at h1
    rw [psuC0_sigma_map h] at h1
    rw [hAm]
    exact h1
  have hbarbar : (Am.map h.bar).map h.bar = Am := Matrix.ext fun i j => h.bar_bar _
  have h1 : Am.map h.bar * Am = Matrix.scalar (Fin n) (h.bar (c : K)) := by
    have h3 := congrArg (fun M : Matrix (Fin n) (Fin n) K => M.map h.bar) hc'
    simp only [Matrix.map_mul, hbarbar] at h3
    rw [h3, Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero h.bar)]
  have hAinv : ((X⁻¹ : primeFormUnitary h (psuJ n K)) : GL (Fin n) K) *
      (X : GL (Fin n) K) = 1 := by
    rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
  have hAinvm : (((X⁻¹ : primeFormUnitary h (psuJ n K)) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) * Am = 1 := by
    rw [hAm, ← Units.val_mul, hAinv, Units.val_one]
  have h2 : Am.map h.bar * Am = Matrix.scalar (Fin n) (c : K) := by
    calc Am.map h.bar * Am
        = (((X⁻¹ : primeFormUnitary h (psuJ n K)) : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K) * (Am * Am.map h.bar) * Am := by
          rw [← Matrix.mul_assoc, hAinvm, Matrix.one_mul]
      _ = Matrix.scalar (Fin n) (c : K) := by
          rw [hc', Matrix.mul_assoc,
            ((Matrix.scalar_commute (c : K) (fun r => Commute.all (c : K) r)) Am).eq,
            ← Matrix.mul_assoc, hAinvm, Matrix.one_mul]
  have hbarc : h.bar (c : K) = c := by
    have h3 := congrFun (congrFun (h1.symm.trans h2) ⟨0, by omega⟩) ⟨0, by omega⟩
    simpa using h3
  have hc1 : (c : K) = 1 := by
    refine eq_one_of_sq_eq_one ?_
    calc (c : K) ^ 2 = c * h.bar c := by rw [hbarc, sq]
      _ = 1 := hcN
  have hA : Am * Am.map h.bar = 1 := by rw [hc', hc1, map_one]
  exact hA

private lemma psuC0_odd {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hn : 4 ≤ n) (B : primeFormUnitary h (psuJ n K))
    (hodd : Odd (orderOf (primeFormConjHom h (psuJ n K) B))) :
    Odd (orderOf (B : GL (Fin n) K)) := by
  set m : ℕ := orderOf (primeFormConjHom h (psuJ n K) B) with hm
  have hcm : (primeFormConjHom h (psuJ n K) B) ^ m = 1 := pow_orderOf_eq_one _
  have hBm : primeFormConjHom h (psuJ n K) (B ^ m) = 1 := by
    rw [map_pow]
    exact hcm
  obtain ⟨c, hcN, hcGL⟩ := eq_scalar_of_primeFormConjHom_eq_one h
    (AutPSU.isPrimeFormGram_gramJ (n := n)) (by omega) hBm
  have hcGL' : (B : GL (Fin n) K) ^ m = GeneralLinearGroup.scalar (Fin n) c := by
    rw [← Subgroup.coe_pow]
    exact hcGL
  have hc1 : c ^ (2 ^ f + 1) = 1 := by
    refine Units.ext ?_
    have hdn := hcN
    rw [UnitaryFieldData.norm, h.bar_apply, ← pow_succ'] at hdn
    simpa [Units.val_pow_eq_pow_val] using hdn
  have hpow : (B : GL (Fin n) K) ^ (m * (2 ^ f + 1)) = 1 := by
    calc (B : GL (Fin n) K) ^ (m * (2 ^ f + 1))
        = ((B : GL (Fin n) K) ^ m) ^ (2 ^ f + 1) := by rw [pow_mul]
      _ = (GeneralLinearGroup.scalar (Fin n) c) ^ (2 ^ f + 1) := by rw [hcGL']
      _ = GeneralLinearGroup.scalar (Fin n) (c ^ (2 ^ f + 1)) := by rw [← map_pow]
      _ = 1 := by rw [hc1, map_one]
  have hoddprod : Odd (m * (2 ^ f + 1)) := by
    have hf : 1 ≤ f := h.one_le
    exact hodd.mul ((Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one)
  exact Odd.of_dvd_nat hoddprod (orderOf_dvd_of_pow_eq_one hpow)

private lemma psuC0_thetaB {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (h : UnitaryFieldData 2 f K) (hn : 4 ≤ n) (i β : MulAut (AutPSU.PJ h n))
    (X : primeFormUnitary h (psuJ n K)) (hX : i = primeFormConjHom h (psuJ n K) X)
    (B : primeFormUnitary h (psuJ n K)) (hB : β = primeFormConjHom h (psuJ n K) B)
    (hcomm : psuAlpha h i * β = β * psuAlpha h i) :
    ∃ c : Kˣ, psuTheta h X ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (c : K) • ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have hC := AutPSU.isPrimeFormGram_gramJ (K := K) (n := n)
  let σ := unitaryInvolution K 2 f
  let σB : primeFormUnitary h (psuJ n K) := primeFormFieldU h hC σ B
  let A : primeFormUnitary h (psuJ n K) := X * σB * X⁻¹
  have hAval : (A : GL (Fin n) K) = (X : GL (Fin n) K) * glAut σ (B : GL (Fin n) K) *
      (X : GL (Fin n) K)⁻¹ := rfl
  have hf : primeFormFieldHom h hC σ * primeFormConjHom h (psuJ n K) B *
      (primeFormFieldHom h hC σ)⁻¹ = primeFormConjHom h (psuJ n K) σB :=
    primeFormField_conj_eq h hC σ B
  have hαX : psuAlpha h i = primeFormConjHom h (psuJ n K) X * primeFormFieldHom h hC σ := by
    rw [hX, psuAlpha]
  have hconj : psuAlpha h i * β * (psuAlpha h i)⁻¹ = primeFormConjHom h (psuJ n K) A := by
    rw [hαX, hB]
    calc (primeFormConjHom h (psuJ n K) X * primeFormFieldHom h hC σ) *
          primeFormConjHom h (psuJ n K) B *
          (primeFormConjHom h (psuJ n K) X * primeFormFieldHom h hC σ)⁻¹
        = primeFormConjHom h (psuJ n K) X *
            (primeFormFieldHom h hC σ * primeFormConjHom h (psuJ n K) B *
              (primeFormFieldHom h hC σ)⁻¹) *
            (primeFormConjHom h (psuJ n K) X)⁻¹ := by group
      _ = primeFormConjHom h (psuJ n K) X * primeFormConjHom h (psuJ n K) σB *
            (primeFormConjHom h (psuJ n K) X)⁻¹ := by rw [hf]
      _ = primeFormConjHom h (psuJ n K) A := by
            rw [← map_inv, ← map_mul, ← map_mul]
  have hβeq : psuAlpha h i * β * (psuAlpha h i)⁻¹ = β := by
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hAB : primeFormConjHom h (psuJ n K) A = primeFormConjHom h (psuJ n K) B := by
    rw [← hconj, hβeq, hB]
  obtain ⟨c, hc⟩ := psuC0_ker h hn hAB
  refine ⟨c, ?_⟩
  rw [psuC0_theta_eq h (X : GL (Fin n) K) (B : GL (Fin n) K)]
  rw [← hAval, hc, psuC0_coe_scalar_mul]

private lemma psuC0_fix {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (h : UnitaryFieldData 2 f K) (hn : 4 ≤ n) (i β : MulAut (AutPSU.PJ h n))
    (X : primeFormUnitary h (psuJ n K)) (hX : i = primeFormConjHom h (psuJ n K) X)
    (B : primeFormUnitary h (psuJ n K)) (hB : β = primeFormConjHom h (psuJ n K) B)
    (hfix : ∀ g, β g = g → psuAlpha h i g = g) :
    ∀ x ∈ psuChat h (B : GL (Fin n) K), ∃ d : Kˣ,
      psuTheta h X ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (d : K) • ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  intro x hx
  obtain ⟨c, hc⟩ := hx
  have hcGL : (x : GL (Fin n) K) * (B : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) c * ((B : GL (Fin n) K) * (x : GL (Fin n) K)) := by
    refine Units.ext ?_
    rw [psuC0_coe_scalar_mul, Units.val_mul]
    exact hc
  have hBeq : (B : GL (Fin n) K) * (x : GL (Fin n) K) * (B : GL (Fin n) K)⁻¹ =
      GeneralLinearGroup.scalar (Fin n) c⁻¹ * (x : GL (Fin n) K) := by
    have h1 : (B : GL (Fin n) K) * (x : GL (Fin n) K) =
        GeneralLinearGroup.scalar (Fin n) c⁻¹ *
          ((x : GL (Fin n) K) * (B : GL (Fin n) K)) := by
      rw [hcGL, map_inv]
      group
    calc (B : GL (Fin n) K) * (x : GL (Fin n) K) * (B : GL (Fin n) K)⁻¹
        = (GeneralLinearGroup.scalar (Fin n) c⁻¹ *
            ((x : GL (Fin n) K) * (B : GL (Fin n) K))) * (B : GL (Fin n) K)⁻¹ := by rw [h1]
      _ = GeneralLinearGroup.scalar (Fin n) c⁻¹ * (x : GL (Fin n) K) := by group
  let y : AutPSU.XJ h n := ⟨(B : GL (Fin n) K) * (x : GL (Fin n) K) * (B : GL (Fin n) K)⁻¹,
    conj_mem_gramSU h (psuJ n K) B.2 x.2⟩
  have hyval : (y : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) c⁻¹ * (x : GL (Fin n) K) := hBeq
  have hscal_mem : GeneralLinearGroup.scalar (Fin n) c⁻¹ ∈ AutPSU.XJ h n := by
    have hyx : ((y * x⁻¹ : AutPSU.XJ h n) : GL (Fin n) K) =
        GeneralLinearGroup.scalar (Fin n) c⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hyval]
      group
    rw [← hyx]
    exact (y * x⁻¹ : AutPSU.XJ h n).2
  have hyx : (QuotientGroup.mk y : AutPSU.PJ h n) = QuotientGroup.mk x :=
    psuC0_mk_eq_of_scalar_mul h (by omega) hscal_mem hyval
  have hcb : primeFormConjHom h (psuJ n K) B (QuotientGroup.mk x : AutPSU.PJ h n) =
      QuotientGroup.mk x := by
    rw [primeFormConjHom_mk h (psuJ n K) B x]
    exact hyx
  have hαfix : psuAlpha h i (QuotientGroup.mk x : AutPSU.PJ h n) = QuotientGroup.mk x :=
    hfix _ (by rw [hB]; exact hcb)
  have hq : (QuotientGroup.mk (⟨(X : GL (Fin n) K) *
      glAut (unitaryInvolution K 2 f) (x : GL (Fin n) K) * (X : GL (Fin n) K)⁻¹,
      psuC0_theta_mem h X x⟩ : AutPSU.XJ h n) : AutPSU.PJ h n) = QuotientGroup.mk x := by
    rw [← psuC0_alpha_mk h X x, ← hX, hαfix]
  have hmem := QuotientGroup.eq.mp hq
  obtain ⟨d, -, -, hd⟩ := (mem_normOneScalars).mp hmem
  have h1 : (((X : GL (Fin n) K) * glAut (unitaryInvolution K 2 f) (x : GL (Fin n) K) *
      (X : GL (Fin n) K)⁻¹)⁻¹ * (x : GL (Fin n) K)) =
      GeneralLinearGroup.scalar (Fin n) d := by
    simpa only [Subgroup.coe_inv, Subgroup.coe_mul] using hd
  have h3 : (X : GL (Fin n) K) * glAut (unitaryInvolution K 2 f) (x : GL (Fin n) K) *
      (X : GL (Fin n) K)⁻¹ = GeneralLinearGroup.scalar (Fin n) d⁻¹ * (x : GL (Fin n) K) := by
    have h2 : (x : GL (Fin n) K) =
        ((X : GL (Fin n) K) * glAut (unitaryInvolution K 2 f) (x : GL (Fin n) K) *
          (X : GL (Fin n) K)⁻¹) * GeneralLinearGroup.scalar (Fin n) d := by
      rw [← h1]
      group
    calc (X : GL (Fin n) K) * glAut (unitaryInvolution K 2 f) (x : GL (Fin n) K) *
          (X : GL (Fin n) K)⁻¹
        = ((X : GL (Fin n) K) * glAut (unitaryInvolution K 2 f) (x : GL (Fin n) K) *
            (X : GL (Fin n) K)⁻¹) * GeneralLinearGroup.scalar (Fin n) d *
            (GeneralLinearGroup.scalar (Fin n) d)⁻¹ := by group
      _ = (x : GL (Fin n) K) * (GeneralLinearGroup.scalar (Fin n) d)⁻¹ := by rw [← h2]
      _ = GeneralLinearGroup.scalar (Fin n) d⁻¹ * (x : GL (Fin n) K) := by
            simpa [map_inv] using (commute_scalar d⁻¹ (x : GL (Fin n) K)).eq
  refine ⟨d⁻¹, ?_⟩
  rw [psuC0_theta_eq h (X : GL (Fin n) K) (x : GL (Fin n) K), h3, psuC0_coe_scalar_mul]

private lemma psuC0_not_all {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (h : UnitaryFieldData 2 f K) (hn : 4 ≤ n) (i : MulAut (AutPSU.PJ h n))
    (hi : i ∈ AutPSU.inndiag h) (X : primeFormUnitary h (psuJ n K))
    (hX : i = primeFormConjHom h (psuJ n K) X) :
    ∃ x : AutPSU.XJ h n, ∀ d : Kˣ,
      psuTheta h X ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠
        (d : K) • ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  by_contra hcon
  push Not at hcon
  have hα1 : psuAlpha h i = 1 := by
    apply MulEquiv.ext
    intro g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨d, hd⟩ := hcon x
    let θe : AutPSU.XJ h n := ⟨(X : GL (Fin n) K) *
      glAut (unitaryInvolution K 2 f) (x : GL (Fin n) K) * (X : GL (Fin n) K)⁻¹,
      psuC0_theta_mem h X x⟩
    have hθGL : (θe : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) d * (x : GL (Fin n) K) := by
      refine Units.ext ?_
      have h1 := hd
      rw [psuC0_theta_eq h (X : GL (Fin n) K) (x : GL (Fin n) K),
        ← psuC0_coe_scalar_mul d (x : GL (Fin n) K)] at h1
      exact h1
    have hscal_mem : GeneralLinearGroup.scalar (Fin n) d ∈ AutPSU.XJ h n := by
      have hz : ((θe * x⁻¹ : AutPSU.XJ h n) : GL (Fin n) K) =
          GeneralLinearGroup.scalar (Fin n) d := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hθGL]
        group
      rw [← hz]
      exact (θe * x⁻¹ : AutPSU.XJ h n).2
    have hmk : (QuotientGroup.mk θe : AutPSU.PJ h n) = QuotientGroup.mk x :=
      psuC0_mk_eq_of_scalar_mul h (by omega) hscal_mem hθGL
    rw [hX]
    show psuAlpha h (primeFormConjHom h (psuJ n K) X) (QuotientGroup.mk x : AutPSU.PJ h n) =
      QuotientGroup.mk x
    rw [psuC0_alpha_mk h X x]
    exact hmk
  have hC := AutPSU.isPrimeFormGram_gramJ (K := K) (n := n)
  have hf_inv : primeFormFieldHom h hC (unitaryInvolution K 2 f) = i⁻¹ := by
    have hif : i * primeFormFieldHom h hC (unitaryInvolution K 2 f) = 1 := by
      simpa only [psuAlpha] using hα1
    calc primeFormFieldHom h hC (unitaryInvolution K 2 f) = i⁻¹ * (i * primeFormFieldHom h hC
          (unitaryInvolution K 2 f)) := by group
      _ = i⁻¹ * 1 := by rw [hif]
      _ = i⁻¹ := by rw [mul_one]
  have hf_mem : primeFormFieldHom h hC (unitaryInvolution K 2 f) ∈ AutPSU.compl h :=
    ⟨unitaryInvolution K 2 f, rfl⟩
  have hf_bot : primeFormFieldHom h hC (unitaryInvolution K 2 f) ∈
      (⊥ : Subgroup (MulAut (AutPSU.PJ h n))) := by
    rw [← AutPSU.inndiag_inf_compl h hn]
    refine ⟨?_, hf_mem⟩
    have hfi : i⁻¹ ∈ AutPSU.inndiag h := inv_mem hi
    rwa [hf_inv]
  have hf1 : primeFormFieldHom h hC (unitaryInvolution K 2 f) = 1 := Subgroup.mem_bot.mp hf_bot
  have hσ1 : unitaryInvolution K 2 f = 1 := by
    have hF := primeFormFieldFactor_apply h hC (by omega) (AutPSU.not_three_of_four hn)
      (1 : primeFormUnitary h (psuJ n K)) (unitaryInvolution K 2 f)
    have hF' : primeFormFieldFactor h hC (by omega) (AutPSU.not_three_of_four hn)
        (primeFormFieldHom h hC (unitaryInvolution K 2 f)) = unitaryInvolution K 2 f := by
      simpa only [map_one, one_mul] using hF
    have h := congrArg (primeFormFieldFactor h hC (by omega)
      (AutPSU.not_three_of_four hn)) hf1
    rw [map_one, hF'] at h
    exact h
  obtain ⟨a, ha⟩ := h.exists_bar_ne
  exact ha (by
    rw [← psuC0_sigma_apply h]
    rw [hσ1]
    rfl)

theorem psuGraph_setting_of_hyps {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (h : UnitaryFieldData 2 f K) (hn : 4 ≤ n)
    (i β : MulAut (AutPSU.PJ h n)) (hi : i ∈ AutPSU.inndiag h) (hβ : β ∈ AutPSU.inndiag h)
    (hodd : Odd (orderOf β))
    (hα2 : psuAlpha h i * psuAlpha h i = 1) (hcomm : psuAlpha h i * β = β * psuAlpha h i)
    (hfix : ∀ g, β g = g → psuAlpha h i g = g) :
    ∃ (X : GL (Fin n) K) (B : primeFormUnitary h (psuJ n K)),
      β = primeFormConjHom h (psuJ n K) B ∧ PSUGraphSetting h n X (B : GL (Fin n) K) := by
  have hi_keep : i ∈ AutPSU.inndiag h := hi
  obtain ⟨X, hX⟩ := hi
  obtain ⟨B, hB⟩ := hβ
  have hC := AutPSU.isPrimeFormGram_gramJ (K := K) (n := n)
  have hpsi : psuAlpha h i = primeFormPsi h hC ⟨X, unitaryInvolution K 2 f⟩ := by
    rw [psuAlpha, ← hX, primeFormPsi_apply]
  have hα2psi : (primeFormPsi h hC ⟨X, unitaryInvolution K 2 f⟩) ^ 2 = 1 := by
    rw [sq, ← hpsi]
    exact hα2
  have hN : ∃ c : Kˣ, h.norm (c : K) = 1 ∧ (X : GL (Fin n) K) *
      glAut (unitaryInvolution K 2 f) (X : GL (Fin n) K) =
        GeneralLinearGroup.scalar (Fin n) c := by
    obtain ⟨-, c, hcN, hc⟩ := primeFormPsi_sq_eq_one h hC (by omega) hα2psi
    exact ⟨c, hcN, hc⟩
  have hXsq := psuC0_Xsq h hn X hN
  have hoddB : Odd (orderOf (B : GL (Fin n) K)) :=
    psuC0_odd h hn B (by rw [hB]; exact hodd)
  have hthetaB := psuC0_thetaB h hn i β X hX.symm B hB.symm hcomm
  have hfixfield := psuC0_fix h hn i β X hX.symm B hB.symm hfix
  have hnotall := psuC0_not_all h hn i hi_keep X hX.symm
  exact ⟨(X : GL (Fin n) K), B, hB.symm,
    ⟨hn, X.2, hXsq, B.2, hoddB, hthetaB, hfixfield, hnotall⟩⟩

end CFSG.StandardType
