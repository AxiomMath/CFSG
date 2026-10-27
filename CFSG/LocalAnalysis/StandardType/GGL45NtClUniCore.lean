module

public import CFSG.LocalAnalysis.StandardType.GGL45NtClUni
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUUnitary

public section

namespace CFSG.HardMathSupport.C14Cl

open CFSG CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.ComponentInitial Matrix

private theorem cUG1_graph {K : Type} [Field K] {n d : ℕ} (h : UnitaryFieldData 2 n K)
    (hd : 1 ≤ d) (σ : K ≃+* K) :
    LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (fun s s' => ((s' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ)
      ((MulAut.congr (InndiagSU.projEquiv h hd)).symm
        (UnitaryHigher.primeFormFieldHom h (UnitaryHigher.isPrimeFormGram_one (K := K) (n := d)) σ)) := by
  intro g g' hgg'
  rw [MulAut.congr_symm_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  change (InndiagSU.projEquiv h hd).symm (UnitaryHigher.primeFormFieldAut h (UnitaryHigher.isPrimeFormGram_one (K := K) (n := d)) σ
    (InndiagSU.projEquiv h hd (g : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))) =
      (g' : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
  rw [InndiagSU.projEquiv_mk, UnitaryHigher.primeFormFieldAut_mk, InndiagSU.projEquiv_symm_mk]
  congr 1
  apply Subtype.ext
  apply Units.ext
  change ((UnitaryHigher.glAut σ (g : GL (Fin d) K) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = _
  rw [UnitaryHigher.coe_glAut]
  exact hgg'.symm

theorem uni_fieldAut_orderOf {K : Type} [Field K] [Fintype K] [CharP K 2] {n d p : ℕ}
    (h : UnitaryFieldData 2 n K) (hd : 3 ≤ d) (hp : p.Prime) (hp2 : p ≠ 2)
    {f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n))))
    (hfp : orderOf f = p) :
    3 ≤ n ∧ ∃ σ₀ : K ≃+* K, orderOf σ₀ = p ∧
      LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (fun s s' => ((s' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
          ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ₀) f := by
  have hd1 : 1 ≤ d := by omega
  have hC1 := UnitaryHigher.isPrimeFormGram_one (K := K) (n := d)
  obtain ⟨σ', hσ'⟩ := RecipeFieldSU.congr_field_eq h hd1 hf
  have hgraph := cUG1_graph h hd1 σ'
  have hσpow : σ' ^ (2 * n) = 1 := by
    obtain ⟨a, ha⟩ := exists_pow_two_of_ringEquiv σ'
    have hiter : ∀ k (c : K), (σ' ^ k) c = c ^ 2 ^ (a * k) := by
      intro k
      induction k with
      | zero => intro c; simp
      | succ k ih =>
        intro c
        rw [pow_succ']
        change σ' ((σ' ^ k) c) = _
        rw [ih, map_pow, ha, ← pow_mul, ← pow_add, Nat.mul_succ, add_comm]
    ext c
    rw [hiter]
    show c ^ 2 ^ (a * (2 * n)) = c
    rw [show a * (2 * n) = (2 * n) * a by ring, pow_mul, ← h.card,
      Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_pow a c
  have hdvd1 : p ∣ orderOf σ' := by
    have h1 : orderOf (UnitaryHigher.primeFormFieldHom h hC1 σ') ∣ orderOf σ' :=
      orderOf_map_dvd _ σ'
    have h2 : orderOf (UnitaryHigher.primeFormFieldHom h hC1 σ') = p := by
      rw [← hσ', MulEquiv.orderOf_eq]
      exact hfp
    rw [h2] at h1
    exact h1
  have hpdvdn : p ∣ n := by
    have h2n : p ∣ 2 * n := hdvd1.trans (orderOf_dvd_of_pow_eq_one hσpow)
    have hp2' : ¬ p ∣ 2 := fun h =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
    exact (hp.dvd_mul).1 h2n |>.resolve_left hp2'
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hn3 : 3 ≤ n := by
    obtain ⟨k, hk⟩ := hpdvdn
    have hn1 : 1 ≤ n := h.one_le
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · rw [hk0, mul_zero] at hk
        omega
      · exact hk0
    rw [hk]
    calc 3 ≤ p := hp3
      _ ≤ p * k := Nat.le_mul_of_pos_right p (by omega)
  have hq : ¬(d = 3 ∧ 2 ^ n = 2) := by
    rintro ⟨-, h2n⟩
    have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    norm_num at h8
    omega
  have hord : orderOf σ' = p := by
    have hinj := RecipeFieldSpU.primeFormFieldHom_injective h hd hq
    have h1 : orderOf (UnitaryHigher.primeFormFieldHom h hC1 σ') = orderOf σ' :=
      orderOf_injective _ hinj σ'
    have h2 : orderOf (UnitaryHigher.primeFormFieldHom h hC1 σ') = p := by
      rw [← hσ', MulEquiv.orderOf_eq]
      exact hfp
    rw [← h1]
    exact h2
  have hfE : (MulAut.congr (InndiagSU.projEquiv h hd1)).symm (UnitaryHigher.primeFormFieldHom h hC1 σ') = f := by
    rw [← hσ', MulEquiv.symm_apply_apply]
  rw [hfE] at hgraph
  exact ⟨hn3, σ', hord, hgraph⟩

private noncomputable def cUG2_sigmaGL {K : Type} [Field K] {d : ℕ} (σ₀ : K ≃+* K) :
    GL (Fin d) K ≃* GL (Fin d) K :=
  Units.mapEquiv (RingEquiv.mapMatrix (m := Fin d) σ₀).toMulEquiv

private lemma cUG2_sigmaGL_coe {K : Type} [Field K] {d : ℕ} (σ₀ : K ≃+* K)
    (A : GL (Fin d) K) :
    ((cUG2_sigmaGL (d := d) σ₀ A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (A : Matrix (Fin d) (Fin d) K).map σ₀ := by
  rw [cUG2_sigmaGL, Units.coe_mapEquiv]
  rfl

private lemma cUG2_sigmaGL_apply_symm {K : Type} [Field K] {d : ℕ} (σ₀ : K ≃+* K)
    (A : GL (Fin d) K) :
    cUG2_sigmaGL (d := d) σ₀ (cUG2_sigmaGL (d := d) σ₀⁻¹ A) = A := by
  apply Units.ext
  rw [cUG2_sigmaGL_coe, cUG2_sigmaGL_coe, Matrix.map_map]
  ext i j
  simp

private theorem cUG2_sigmaGL_mem_unit {K : Type} [Field K] {n d : ℕ}
    (h : UnitaryFieldData 2 n K) (σ₀ : K ≃+* K)
    (hσbar : ∀ c, σ₀ (h.bar c) = h.bar (σ₀ c)) {A : GL (Fin d) K}
    (hA : A ∈ TableB.unitGroup (ι := Fin d) h.bar) :
    cUG2_sigmaGL (d := d) σ₀ A ∈ TableB.unitGroup (ι := Fin d) h.bar := by
  rw [TableB.mem_unitGroup] at hA ⊢
  rw [cUG2_sigmaGL_coe]
  have hcomp : ((A : Matrix (Fin d) (Fin d) K).map σ₀).map h.bar =
      ((A : Matrix (Fin d) (Fin d) K).map h.bar).map σ₀ := by
    ext i j
    simp only [Matrix.map_apply]
    exact (hσbar _).symm
  rw [hcomp, ← Matrix.transpose_map, ← Matrix.map_mul, hA]
  simp

private noncomputable def cUG2_sigmaU {K : Type} [Field K] {n d : ℕ}
    (h : UnitaryFieldData 2 n K) (σ₀ : K ≃+* K)
    (hσbar : ∀ c, σ₀ (h.bar c) = h.bar (σ₀ c)) :
    ↥(TableB.unitGroup (ι := Fin d) h.bar) →* ↥(TableB.unitGroup (ι := Fin d) h.bar) where
  toFun A := ⟨cUG2_sigmaGL (d := d) σ₀ A, cUG2_sigmaGL_mem_unit h σ₀ hσbar A.2⟩
  map_one' := Subtype.ext (by
    simpa using map_one (cUG2_sigmaGL (d := d) σ₀))
  map_mul' A B := Subtype.ext (by
    simpa using map_mul (cUG2_sigmaGL (d := d) σ₀) (A : GL (Fin d) K) (B : GL (Fin d) K))

private theorem cUG2_sigmaGL_mem_SU {K : Type} [Field K] {n d : ℕ}
    (h : UnitaryFieldData 2 n K) (σ₀ : K ≃+* K)
    (hσbar : ∀ c, σ₀ (h.bar c) = h.bar (σ₀ c)) {s : GL (Fin d) K}
    (hs : s ∈ LargeEvenSUGroup (Fin d) K (2 ^ n)) :
    cUG2_sigmaGL (d := d) σ₀ s ∈ LargeEvenSUGroup (Fin d) K (2 ^ n) := by
  change s ∈ CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n K d at hs
  change cUG2_sigmaGL (d := d) σ₀ s ∈ CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n K d
  rw [CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h] at hs ⊢
  constructor
  · rw [cUG2_sigmaGL_coe]
    have hdet : ((s : Matrix (Fin d) (Fin d) K).map σ₀).det =
        σ₀ ((s : Matrix (Fin d) (Fin d) K).det) :=
      (RingHom.map_det (σ₀ : K →+* K) (s : Matrix (Fin d) (Fin d) K)).symm
    rw [hdet, hs.1, map_one]
  · rw [cUG2_sigmaGL_coe]
    have hcomp : ((s : Matrix (Fin d) (Fin d) K).map σ₀).map h.bar =
        ((s : Matrix (Fin d) (Fin d) K).map h.bar).map σ₀ := by
      ext i j
      simp only [Matrix.map_apply]
      exact (hσbar _).symm
    rw [hcomp, ← Matrix.transpose_map, ← Matrix.map_mul, hs.2]
    simp

private theorem cUG2_field_conj {K : Type} [Field K] [Fintype K] {n d : ℕ}
    (h : UnitaryFieldData 2 n K) (σ₀ : K ≃+* K)
    (hσbar : ∀ c, σ₀ (h.bar c) = h.bar (σ₀ c))
    (hσbar_inv : ∀ c, σ₀⁻¹ (h.bar c) = h.bar (σ₀⁻¹ c))
    (f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))
    (hf : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (fun s s' => ((s' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ₀) f)
    (A : ↥(TableB.unitGroup (ι := Fin d) h.bar)) :
    f * uniConj h d A * f⁻¹ =
      uniConj h d (cUG2_sigmaU (n := n) (d := d) h σ₀ hσbar A) := by
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
  have hsinv_mem : (cUG2_sigmaGL (d := d) σ₀⁻¹ (s : GL (Fin d) K)) ∈
      LargeEvenSUGroup (Fin d) K (2 ^ n) :=
    cUG2_sigmaGL_mem_SU h σ₀⁻¹ hσbar_inv s.2
  have hconj1_mem : ((A : GL (Fin d) K) *
      (cUG2_sigmaGL (d := d) σ₀⁻¹ (s : GL (Fin d) K)) * (A : GL (Fin d) K)⁻¹) ∈
      LargeEvenSUGroup (Fin d) K (2 ^ n) := (hnormal _).1 hsinv_mem
  have hsigmaA_unit : (cUG2_sigmaGL (d := d) σ₀ (A : GL (Fin d) K)) ∈
      TableB.unitGroup (ι := Fin d) h.bar := cUG2_sigmaGL_mem_unit h σ₀ hσbar A.2
  have hconj2_mem : ((cUG2_sigmaGL (d := d) σ₀ (A : GL (Fin d) K)) *
      (s : GL (Fin d) K) * (cUG2_sigmaGL (d := d) σ₀ (A : GL (Fin d) K))⁻¹) ∈
      LargeEvenSUGroup (Fin d) K (2 ^ n) := by
    have hN : (cUG2_sigmaGL (d := d) σ₀ (A : GL (Fin d) K)) ∈
        Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K)) :=
      uniGroup_le_normalizer h (cUG2_sigmaGL_mem_unit h σ₀ hσbar A.2)
    rw [Subgroup.mem_normalizer_iff] at hN
    exact (hN _).1 s.2
  have hfi : f⁻¹ (LargeEvenProjMk _ s) = LargeEvenProjMk _
      (⟨cUG2_sigmaGL (d := d) σ₀⁻¹ (s : GL (Fin d) K), hsinv_mem⟩ :
        ↥(LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
    have h1 : f (LargeEvenProjMk _ (⟨cUG2_sigmaGL (d := d) σ₀⁻¹ (s : GL (Fin d) K),
        hsinv_mem⟩ : ↥(LargeEvenSUGroup (Fin d) K (2 ^ n)))) =
        LargeEvenProjMk _ s := by
      apply hf
      rw [cUG2_sigmaGL_coe, Matrix.map_map]
      ext i j
      simp
    simpa using (congrArg (fun z => f⁻¹ z) h1).symm
  rw [MulAut.mul_apply, MulAut.mul_apply, hfi]
  have hAconj : uniConj h d A (LargeEvenProjMk _ (⟨cUG2_sigmaGL (d := d) σ₀⁻¹
      (s : GL (Fin d) K), hsinv_mem⟩ : ↥(LargeEvenSUGroup (Fin d) K (2 ^ n)))) =
      LargeEvenProjMk _ (⟨(A : GL (Fin d) K) * (cUG2_sigmaGL (d := d) σ₀⁻¹
        (s : GL (Fin d) K)) * (A : GL (Fin d) K)⁻¹, hconj1_mem⟩ :
        ↥(LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
    exact TableB.projConj_mk (LargeEvenSUGroup (Fin d) K (2 ^ n))
      ((Subgroup.inclusion (uniGroup_le_normalizer h)) A)
      (⟨cUG2_sigmaGL (d := d) σ₀⁻¹ (s : GL (Fin d) K), hsinv_mem⟩ :
        ↥(LargeEvenSUGroup (Fin d) K (2 ^ n)))
  rw [hAconj]
  have hstep : f (LargeEvenProjMk _ (⟨(A : GL (Fin d) K) * (cUG2_sigmaGL (d := d) σ₀⁻¹
      (s : GL (Fin d) K)) * (A : GL (Fin d) K)⁻¹, hconj1_mem⟩ :
        ↥(LargeEvenSUGroup (Fin d) K (2 ^ n)))) =
      LargeEvenProjMk _ (⟨cUG2_sigmaGL (d := d) σ₀ ((A : GL (Fin d) K) *
        (cUG2_sigmaGL (d := d) σ₀⁻¹ (s : GL (Fin d) K)) * (A : GL (Fin d) K)⁻¹),
        cUG2_sigmaGL_mem_SU h σ₀ hσbar hconj1_mem⟩ :
        ↥(LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
    apply hf
    rw [cUG2_sigmaGL_coe]
  rw [hstep]
  have hAconj2 : uniConj h d (cUG2_sigmaU (n := n) (d := d) h σ₀ hσbar A)
      (LargeEvenProjMk _ s) =
      LargeEvenProjMk _ (⟨(cUG2_sigmaGL (d := d) σ₀ (A : GL (Fin d) K)) *
        (s : GL (Fin d) K) * (cUG2_sigmaGL (d := d) σ₀ (A : GL (Fin d) K))⁻¹,
        hconj2_mem⟩ : ↥(LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
    exact TableB.projConj_mk (LargeEvenSUGroup (Fin d) K (2 ^ n))
      ((Subgroup.inclusion (uniGroup_le_normalizer h)) (cUG2_sigmaU (n := n) (d := d) h σ₀ hσbar A))
      s
  rw [hAconj2]
  apply congrArg (LargeEvenProjMk _)
  apply Subtype.ext
  simp only [Subgroup.coe_mk]
  simp only [MulEquiv.map_mul, MulEquiv.map_inv, cUG2_sigmaGL_apply_symm]

private theorem cUG2_sigmaOn_eq_sigmaU {K : Type} [Field K] {n d : ℕ}
    (h : UnitaryFieldData 2 n K) (S : ClSetting K (Fin d))
    (hH : S.GoodGroup (TableB.unitGroup (ι := Fin d) h.bar))
    (hσbar : ∀ c, S.σ₀ (h.bar c) = h.bar (S.σ₀ c))
    (x : ↥(TableB.unitGroup (ι := Fin d) h.bar)) :
    S.sigmaOn hH x = cUG2_sigmaU (n := n) (d := d) h S.σ₀ hσbar x := by
  apply Subtype.ext
  apply Units.ext
  change ((S.σGL (x : GL (Fin d) K) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
    ((cUG2_sigmaGL (d := d) S.σ₀ (x : GL (Fin d) K) : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K)
  rw [cUG2_sigmaGL_coe]
  ext i j
  rfl

private theorem cUG2_sigma_inv_comm_bar {K : Type} [Field K] [Fintype K] [CharP K 2]
    {n : ℕ} (h : UnitaryFieldData 2 n K) (σ₀ : K ≃+* K) :
    ∀ c, σ₀⁻¹ (h.bar c) = h.bar (σ₀⁻¹ c) := by
  obtain ⟨a, ha⟩ := exists_pow_two_of_ringEquiv σ₀⁻¹
  intro c
  rw [ha, h.bar_apply, ha, h.bar_apply, ← pow_mul, ← pow_mul, Nat.mul_comm]

theorem uni_sigma_conj {K : Type} [Field K] [Fintype K] [CharP K 2] {n d : ℕ}
    (h : UnitaryFieldData 2 n K) (S : ClSetting K (Fin d)) (hτ : ∀ c : K, S.τ c = h.bar c)
    (hG : S.G = 1) (hH : S.GoodGroup (TableB.unitGroup (ι := Fin d) h.bar))
    (f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))
    (hf : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (fun s s' => ((s' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map S.σ₀) f)
    (x : ↥(TableB.unitGroup (ι := Fin d) h.bar)) :
    uniConj h d (S.sigmaOn hH x) = f * uniConj h d x * f⁻¹ := by
  have hσbar : ∀ c : K, S.σ₀ (h.bar c) = h.bar (S.σ₀ c) := fun c => by
    have hcomm := S.tau_sigma_comm c
    rw [hτ c, hτ (S.σ₀ c)] at hcomm
    exact hcomm
  have hσbar_inv : ∀ c : K, S.σ₀⁻¹ (h.bar c) = h.bar (S.σ₀⁻¹ c) :=
    cUG2_sigma_inv_comm_bar h S.σ₀
  rw [cUG2_sigmaOn_eq_sigmaU (n := n) (d := d) h S hH hσbar x]
  exact (cUG2_field_conj (n := n) (d := d) h S.σ₀ hσbar hσbar_inv f hf x).symm

private theorem cUG3_bar_map {K : Type} [Field K] {n d : ℕ} (h : UnitaryFieldData 2 n K)
    (M : Matrix (Fin d) (Fin d) K) :
    M.map (· ^ 2 ^ n) = M.map h.bar := by
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply, UnitaryFieldData.bar_apply]

private theorem cUG3_guSet_of_unitGroup {K : Type} [Field K] {n d : ℕ}
    (h : UnitaryFieldData 2 n K) {M : GL (Fin d) K}
    (hM : M ∈ TableB.unitGroup (ι := Fin d) h.bar) :
    M ∈ LargeEvenGUSet (Fin d) K (2 ^ n) := by
  refine ⟨1, one_ne_zero, one_pow _, ?_⟩
  rw [one_smul, cUG3_bar_map h]
  exact (TableB.mem_unitGroup).mp hM

private theorem cUG3_mem_unitGroup_of_primeFormUnitary {K : Type} [Field K] {n d : ℕ}
    (h : UnitaryFieldData 2 n K) {P : GL (Fin d) K}
    (hP : P ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K d)) :
    P ∈ TableB.unitGroup (ι := Fin d) h.bar := by
  rw [TableB.mem_unitGroup]
  rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary] at hP
  simpa [CFSG.RankThree.PartOne.KCUnitaryModel.idGram] using hP

private theorem cUG3_exists_unitary_of_gu {K : Type} [Field K] [Fintype K] [CharP K 2]
    {n d : ℕ} (h : UnitaryFieldData 2 n K)
    {M : GL (Fin d) K} (hM : M ∈ LargeEvenGUSet (Fin d) K (2 ^ n)) :
    ∃ u : Kˣ, GeneralLinearGroup.scalar (Fin d) u * M ∈
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K d) := by
  haveI : Finite K := Fintype.finite inferInstance
  obtain ⟨μ, hμ0, hμq, hμ⟩ := hM
  have hbar : h.bar μ = μ := by rw [UnitaryFieldData.bar_apply]; exact hμq
  have hK : Nat.card K = (2 ^ n) ^ 2 := by
    rw [h.card, show 2 ^ (2 * n) = (2 ^ n) ^ 2 by rw [← pow_mul, mul_comm]]
  obtain ⟨l, hl⟩ := TableB.exists_norm_eq (K := K) (q := 2 ^ n)
    (by simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) h.one_le) hK hμ0 hμq
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
  rw [hmap, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← cUG3_bar_map h,
    hμ, smul_smul, map_inv₀]
  have hb0 : h.bar u₀ ≠ 0 := (map_ne_zero h.bar).mpr hu₀0
  have e : h.bar u₀⁻¹ * u₀⁻¹ * μ = 1 := by
    rw [map_inv₀, ← hu₀]
    field_simp
  rw [show (h.bar u₀)⁻¹ * u₀⁻¹ * μ = h.bar u₀⁻¹ * u₀⁻¹ * μ by rw [map_inv₀], e, one_smul]

theorem uni_mem_conjImage_iff {K : Type} [Field K] [Fintype K] [CharP K 2] {n d : ℕ}
    (h : UnitaryFieldData 2 n K) (w : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) :
    w ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n)) ↔
      ∃ x : ↥(TableB.unitGroup (ι := Fin d) h.bar), uniConj h d x = w := by
  classical
  constructor
  · intro hw
    obtain ⟨A, hA, hwA⟩ :=
      TableB.exists_eq_projConj (TableBUE.gu_subset_normalizer (d := d) h) hw
    obtain ⟨u, huP⟩ := cUG3_exists_unitary_of_gu h hA
    let x : ↥(TableB.unitGroup (ι := Fin d) h.bar) :=
      ⟨GeneralLinearGroup.scalar (Fin d) u * (A : GL (Fin d) K),
        cUG3_mem_unitGroup_of_primeFormUnitary h huP⟩
    refine ⟨x, ?_⟩
    have hz : GeneralLinearGroup.scalar (Fin d) u ∈ LargeEvenScalars (Fin d) K := ⟨u, rfl⟩
    have hzN : GeneralLinearGroup.scalar (Fin d) u ∈
        Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K)) :=
      TableB.scalar_mem_normalizer _ hz
    have hprod : ((Subgroup.inclusion (uniGroup_le_normalizer h)) x :
        Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K))) =
        ⟨GeneralLinearGroup.scalar (Fin d) u, hzN⟩ *
        ⟨(A : GL (Fin d) K), TableBUE.gu_subset_normalizer (d := d) h hA⟩ := by
      apply Subtype.ext
      rfl
    calc uniConj h d x = TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n))
          ((Subgroup.inclusion (uniGroup_le_normalizer h)) x) := rfl
      _ = TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n))
          (⟨GeneralLinearGroup.scalar (Fin d) u, hzN⟩ *
            ⟨(A : GL (Fin d) K), TableBUE.gu_subset_normalizer (d := d) h hA⟩) := by rw [hprod]
      _ = TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n))
            ⟨(A : GL (Fin d) K), TableBUE.gu_subset_normalizer (d := d) h hA⟩ := by
          rw [map_mul, TableB.projConj_of_scalar _ hz, one_mul]
      _ = w := hwA.symm
  · rintro ⟨x, rfl⟩
    refine ⟨(x : GL (Fin d) K), cUG3_guSet_of_unitGroup h x.2, ?_⟩
    intro s s' hs
    have hxN : (x : GL (Fin d) K) ∈
        Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K)) :=
      uniGroup_le_normalizer h x.2
    have hmem : (x : GL (Fin d) K) * (s : GL (Fin d) K) * (x : GL (Fin d) K)⁻¹ ∈
        LargeEvenSUGroup (Fin d) K (2 ^ n) :=
      (Subgroup.mem_normalizer_iff.mp hxN (s : GL (Fin d) K)).mp s.2
    have hs' : s' = ⟨(x : GL (Fin d) K) * (s : GL (Fin d) K) * (x : GL (Fin d) K)⁻¹, hmem⟩ :=
      Subtype.ext hs
    rw [hs']
    change TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ n))
      (⟨(x : GL (Fin d) K), hxN⟩ :
        Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K)))
      (s : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) = _
    rw [TableB.projConj_mk]
    rfl

private lemma cUG4_isElemAbelian_map {G G' : Type*} [Group G] [Group G'] {p : ℕ}
    {E : Subgroup G} (hE : IsElemAbelian p E) (f : G →* G') (hf : Function.Injective f) :
    IsElemAbelian p (E.map f) := by
  haveI := hE.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨x, hx, hax⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨z, hz, hbz⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    change (a : G') * b = b * a
    rw [← hax, ← hbz, ← map_mul, ← map_mul]
    exact congrArg (fun w : E => f w) (mul_comm' (⟨x, hx⟩ : E) ⟨z, hz⟩)
  · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    rw [← map_pow, hE.2 x hx, map_one]

theorem ntCore_uni {K : Type} [Field K] [Fintype K] [CharP K 2] {d p q : ℕ} (hd : 3 ≤ d) (hp : p.Prime) (hp2 : p ≠ 2) (hpd : ¬ p ∣ d ∨ ¬ p ∣ q + 1)
    (hK : Fintype.card K = q ^ 2) :
    GGL45NtCore p (LargeEvenProj (LargeEvenSUGroup (Fin d) K q))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K q))
        (LargeEvenGUSet (Fin d) K q))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K q))) := by
  obtain ⟨n, hqn⟩ : ∃ n, q = 2 ^ n := by
    obtain ⟨m, -, hm⟩ := FiniteField.card K 2
    have hdvd : q ∣ 2 ^ (m : ℕ) := by
      rw [← hm, hK]
      exact dvd_pow_self q (by norm_num : 2 ≠ 0)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact ⟨k, hk⟩
  subst q
  have hn : 1 ≤ n := by
    rw [Nat.one_le_iff_ne_zero]
    intro hn0
    subst hn0
    have hc : 2 ≤ Fintype.card K := Fintype.one_lt_card
    rw [hK] at hc
    norm_num at hc
  have h : UnitaryFieldData 2 n K :=
    unitaryFieldData_of_card hn (by rw [Nat.card_eq_fintype_card]; exact hK)
  refine ntCore_of_conj p _ _ ?_ ?_ ?_
  ·
    intro x hx y hy
    rw [uni_mem_conjImage_iff h] at hx hy ⊢
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a * b⁻¹, by rw [map_mul, map_inv]⟩
  ·
    rw [uni_mem_conjImage_iff h]
    exact ⟨1, map_one _⟩
  ·
    intro _hsimp _hnab Ebar f hEab hcard hEI hfF hfo hcomm hSat
    obtain ⟨hn3, σ₀, hσ₀, hf⟩ := uni_fieldAut_orderOf h hd hp hp2 hfF hfo
    have hdq : (d, 2 ^ n) ≠ (3, 2) := by
      have h2n : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
      norm_num at h2n
      intro hh
      have h2 : 2 ^ n = 2 := congrArg Prod.snd hh
      omega
    obtain ⟨E₀, hE₀ab, hE₀fix, hE₀inj, hE₀Ebar⟩ :=
      uni_E0_lift h hd hdq hp hp2 hpd σ₀ hσ₀ Ebar hEab hEI f hf hcomm
    let τ : K ≃+* K := RingEquiv.ofBijective h.bar (Function.Involutive.bijective h.bar_bar)
    let U : Subgroup (GL (Fin d) K) := TableB.unitGroup (ι := Fin d) h.bar
    let S : ClSetting K (Fin d) :=
      { p := p
        hp := hp
        hp2 := hp2
        τ := τ
        hτ := fun c => h.bar_bar c
        G := 1
        hG := by rw [Matrix.det_one]; exact isUnit_one
        hGs := by simp [Matrix.map_one]
        σ₀ := σ₀
        hσ₀ := hσ₀
        hGσ := by simp [Matrix.map_one]
        E₀ := E₀.map U.subtype
        hE := cUG4_isElemAbelian_map hE₀ab U.subtype Subtype.val_injective
        hEU := by
          rintro e ⟨x, hx, rfl⟩
          have hxU := TableB.mem_unitGroup.mp x.2
          simpa [τ, formAdj] using hxU
        hEfix := by
          rintro e ⟨x, hx, rfl⟩
          exact hE₀fix x hx }
    have hτeq : ∀ c : K, S.τ c = h.bar c := fun c => RingEquiv.ofBijective_apply h.bar _ c
    have hG : S.G = 1 := rfl
    have hH : S.GoodGroup U := ClSetting.goodGroup_U S U fun g => by
      have hmap : ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map S.τ =
          ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar := by
        ext i j
        simp only [Matrix.map_apply]
        exact hτeq _
      have hUeq : S.adj (g : Matrix (Fin d) (Fin d) K) * (g : Matrix (Fin d) (Fin d) K) =
          (((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
            ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
        rw [ClSetting.adj, formAdj, show S.G = 1 from rfl, hmap]
        simp only [inv_one, Matrix.one_mul, Matrix.mul_one]
      rw [TableB.mem_unitGroup]
      constructor
      · intro hh; rwa [← hUeq] at hh
      · intro hh; rwa [hUeq] at hh
    have hEH : ∀ e ∈ S.E₀, e ∈ U := by
      rintro e ⟨x, _hx, rfl⟩
      exact x.2
    have hcardE0 : Nat.card E₀ = Nat.card Ebar := by
      let ψ : E₀ → Ebar := fun x => ⟨uniConj h d x, (hE₀Ebar _).mpr ⟨x, x.2, rfl⟩⟩
      have hψ : Function.Bijective ψ := by
        constructor
        · intro x y hxy
          exact Subtype.ext (hE₀inj x x.2 y y.2 (Subtype.ext_iff.mp hxy))
        · rintro ⟨e, he⟩
          obtain ⟨x, hx, hxe⟩ := (hE₀Ebar e).mp he
          exact ⟨⟨x, hx⟩, Subtype.ext hxe⟩
      exact Nat.card_congr (Equiv.ofBijective ψ hψ)
    have hcardS : S.p ^ 2 ≤ Nat.card S.E₀ := by
      change p ^ 2 ≤ Nat.card (E₀.map U.subtype)
      rw [Subgroup.card_map_of_injective (f := U.subtype) Subtype.val_injective, hcardE0]
      exact hcard
    have hSatS : S.Sat U := by
      intro y hyU hyCent hyp hyfix
      have hyfix' : ((y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ₀ =
          ((y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
        have hh := congrArg (fun z : GL (Fin d) K => (z : Matrix (Fin d) (Fin d) K)) hyfix
        simpa [ClSetting.σGL, ClSetting.σ, τ] using hh
      have hyp' : (⟨y, hyU⟩ : ↥U) ^ p = 1 := Subtype.ext hyp
      exact uni_sat_translate h hd hdq hp hpd σ₀ E₀ Ebar hE₀Ebar f hf hSat ⟨y, hyU⟩
        (fun e he => Subtype.ext (hyCent.2 (e : GL (Fin d) K) ⟨e, he, rfl⟩)) hyp' hyfix'
    have hsub : S.E₀.subgroupOf U = E₀ := by
      apply Subgroup.map_injective (f := U.subtype) Subtype.val_injective
      rw [Subgroup.subgroupOf_map_subtype]
      exact inf_of_le_left (Subgroup.map_subtype_le E₀)
    have hcl : ClCoreConcl p E₀ (S.sigmaOn hH) := by
      have hh := S.clCoreConcl hH hSatS hEH hcardS
      rwa [hsub] at hh
    have hα : ∀ g : ↥U, uniConj h d (S.sigmaOn hH g) = f * uniConj h d g * f⁻¹ :=
      fun g => uni_sigma_conj h S hτeq hG hH f hf g
    have hI : ∀ w ∈ LargeEvenMatConjImage
          (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
          (LargeEvenGUSet (Fin d) K (2 ^ n)), ∃ g : ↥U, uniConj h d g = w :=
      fun w hw => (uni_mem_conjImage_iff h w).mp hw
    have hIp : ∀ g : ↥U, (∃ k : ℕ, g ^ p ^ k = 1) →
        uniConj h d g ∈ LargeEvenMatConjImage
          (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
          (LargeEvenGUSet (Fin d) K (2 ^ n)) :=
      fun g _ => (uni_mem_conjImage_iff h (uniConj h d g)).mpr ⟨g, rfl⟩
    have hcomm' : ∀ g : ↥U, (∀ e ∈ E₀, uniConj h d g * uniConj h d e = uniConj h d e * uniConj h d g) →
        ∀ e ∈ E₀, g * e = e * g :=
      fun g hg => uni_commute_of_conj_commute h hd hdq hp hpd E₀ hE₀ab.2 g hg
    exact coreConcl_transfer hp _ Ebar f (uniConj h d) (S.sigmaOn hH) hα E₀ hE₀inj hE₀Ebar
      hI hIp hcomm' hcl

end CFSG.HardMathSupport.C14Cl
