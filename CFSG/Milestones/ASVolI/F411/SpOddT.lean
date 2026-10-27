module

public import CFSG.RankThree.PartOne.AUTSL.SpTwoAut

public section

namespace CFSG.ASVolI

open Matrix Subgroup CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne.AUTSL.SpTwo

variable {K : Type} [Field K]

abbrev burnsideF411_eTwo : Fin 2 ⊕ Fin 2 → K := Pi.single (Sum.inl 1) 1

noncomputable abbrev burnsideF411_dt (t : Kˣ) : StatedSp 2 K :=
  SymplecticTorusWeyl.torusHom ![t, 1]

theorem burnsideF411_spCoordImage_flag (σ : K ≃+* K) {i : ℕ} (hi : i ≤ 2) :
    spCoordImage σ (flag 2 K i) = flag 2 K i := by
  ext v
  rw [mem_spCoordImage, mem_flag_of_le hi, mem_flag_of_le hi, mem_isoFlag, mem_isoFlag]
  simp

theorem burnsideF411_eOne_mem_flag {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 2) :
    (eOne : Fin 2 ⊕ Fin 2 → K) ∈ flag 2 K i := by
  rw [mem_flag_of_le hi, mem_isoFlag]
  refine ⟨fun j => by simp, fun j hj => ?_⟩
  fin_cases j
  · simp at hj
    omega
  · simp

theorem burnsideF411_eTwo_mem_flag : (burnsideF411_eTwo : Fin 2 ⊕ Fin 2 → K) ∈ flag 2 K 2 := by
  rw [mem_flag_of_le le_rfl, mem_isoFlag]
  refine ⟨fun j => by simp, fun j hj => ?_⟩
  exact absurd hj (by have := j.isLt; omega)

theorem burnsideF411_inr_of_mem_flag_two {v : Fin 2 ⊕ Fin 2 → K} (hv : v ∈ flag 2 K 2) (j : Fin 2) :
    v (Sum.inr j) = 0 :=
  (mem_isoFlag.mp ((mem_flag_of_le le_rfl).mp hv)).1 j

theorem burnsideF411_mem_flag_one_of {v : Fin 2 ⊕ Fin 2 → K} (hv : v ∈ flag 2 K 2)
    (h1 : v (Sum.inl 1) = 0) : v ∈ flag 2 K 1 := by
  rw [mem_flag_of_le (by norm_num), mem_isoFlag]
  refine ⟨burnsideF411_inr_of_mem_flag_two hv, fun j hj => ?_⟩
  fin_cases j
  · simp at hj
  · exact h1

theorem burnsideF411_isTotallyIsotropic_flag {i : ℕ} (hi : i ≤ 2) :
    IsTotallyIsotropic (pairedSympForm K 2) (flag 2 K i) := by
  intro v hv w hw
  rw [mem_flag_of_le hi] at hv hw
  exact isTotallyIsotropic_isoFlag i v hv w hw

theorem burnsideF411_sp4_map_flag [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (A : gsp 2 K)
    (σ : K ≃+* K) {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 2)
    (h : (projStabilizer 2 K (flag 2 K i)).map (conjAut 2 K A * fieldAut 2 K σ).toMonoidHom =
      projStabilizer 2 K (flag 2 K i)) :
    (flag 2 K i).map (Matrix.mulVecLin ((A : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) = flag 2 K i := by
  rw [map_projStabilizer_conjAut_mul_fieldAut, burnsideF411_spCoordImage_flag σ hi] at h
  obtain ⟨-, -, hinj⟩ := maximal_parabolics (K := K) p (r := 2) (by norm_num)
  set M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := ((A : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hM
  have he1 : (eOne : Fin 2 ⊕ Fin 2 → K) ≠ 0 := by
    intro h0
    have := congrFun h0 (Sum.inl 0)
    simp at this
  refine hinj _ _ ?_ ?_ ?_ (burnsideF411_isTotallyIsotropic_flag hi) h
  · intro hbot
    have hmem : M *ᵥ eOne ∈ (flag 2 K i).map (Matrix.mulVecLin M) :=
      ⟨eOne, burnsideF411_eOne_mem_flag hi1 hi, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    apply he1
    have h2 : (((A : GL (Fin 2 ⊕ Fin 2) K)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ (M *ᵥ eOne) = eOne := by
      rw [Matrix.mulVec_mulVec, hM, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [← h2, hmem, Matrix.mulVec_zero]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hmul := multiplierUnit_spec A
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
      pairedSympForm_mulVec_of_formJ hmul x y, burnsideF411_isTotallyIsotropic_flag hi x hx y hy,
      mul_zero]
  · intro hbot
    have hmem := burnsideF411_eOne_mem_flag (K := K) hi1 hi
    rw [hbot, Submodule.mem_bot] at hmem
    exact he1 hmem

theorem burnsideF411_unip_mulVec_eOne {u : StatedSp 2 K} (hu : u ∈ unipotent 2 K) :
    mat u *ᵥ eOne = eOne := by
  obtain ⟨A, C, hA, -, hm⟩ := hu
  have h10 : A 1 0 = 0 := hA.1 (show (0 : Fin 2) < 1 by decide)
  change ((u : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ eOne = eOne
  rw [hm, Matrix.mulVec_single_one]
  funext x
  rcases x with i | i <;> fin_cases i <;>
    simp [blockMat, Matrix.col, hA.2 0, h10]

theorem burnsideF411_unip_mulVec_inl_one {u : StatedSp 2 K} (hu : u ∈ unipotent 2 K)
    {v : Fin 2 ⊕ Fin 2 → K} (hv : ∀ j, v (Sum.inr j) = 0) :
    (mat u *ᵥ v) (Sum.inl 1) = v (Sum.inl 1) := by
  obtain ⟨A, C, hA, -, hm⟩ := hu
  have h10 : A 1 0 = 0 := hA.1 (show (0 : Fin 2) < 1 by decide)
  have hr : (v ∘ Sum.inr : Fin 2 → K) = 0 := funext hv
  change (((u : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v)
    (Sum.inl 1) = v (Sum.inl 1)
  rw [hm, blockMat, fromBlocks_mulVec, hr]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h10, hA.2 1]

theorem burnsideF411_mat_dt (t : Kˣ) :
    mat (burnsideF411_dt t) =
      diagonal (Sum.elim (fun i => ((![t, 1] : Fin 2 → Kˣ) i : K))
        fun i => (((![t, 1] : Fin 2 → Kˣ) i)⁻¹ : Kˣ)) :=
  SymplecticTorusWeyl.coe_torusHom _

theorem burnsideF411_dt_mulVec_inl (t : Kˣ) (v : Fin 2 ⊕ Fin 2 → K) :
    (mat (burnsideF411_dt t) *ᵥ v) (Sum.inl 0) = t * v (Sum.inl 0) ∧
      (mat (burnsideF411_dt t) *ᵥ v) (Sum.inl 1) = v (Sum.inl 1) := by
  rw [burnsideF411_mat_dt]
  simp [mulVec_diagonal]

theorem burnsideF411_dt_mulVec_inr (t : Kˣ) {v : Fin 2 ⊕ Fin 2 → K}
    (hv : ∀ j, v (Sum.inr j) = 0) (j : Fin 2) : (mat (burnsideF411_dt t) *ᵥ v) (Sum.inr j) = 0 := by
  rw [burnsideF411_mat_dt]
  simp [mulVec_diagonal, hv j]

theorem burnsideF411_dt_mulVec_eOne (t : Kˣ) :
    mat (burnsideF411_dt t) *ᵥ eOne = (t : K) • (eOne : Fin 2 ⊕ Fin 2 → K) := by
  rw [burnsideF411_mat_dt]
  funext x
  rcases x with i | i <;> fin_cases i <;> simp [mulVec_diagonal]

theorem burnsideF411_dt_mulVec_eTwo (t : Kˣ) :
    mat (burnsideF411_dt t) *ᵥ burnsideF411_eTwo = (burnsideF411_eTwo : Fin 2 ⊕ Fin 2 → K) := by
  rw [burnsideF411_mat_dt]
  funext x
  rcases x with i | i <;> fin_cases i <;> simp [mulVec_diagonal]

theorem burnsideF411_fieldSp_dt (σ : K ≃+* K) (t : Kˣ) :
    fieldSp 2 K σ (burnsideF411_dt t) =
      burnsideF411_dt (Units.map σ.toRingHom.toMonoidHom t) := by
  apply SymplecticTorusWeyl.statedSp_ext
  rw [coe_fieldSp]
  change (mat (burnsideF411_dt t)).map σ = mat (burnsideF411_dt (Units.map σ.toRingHom.toMonoidHom t))
  rw [burnsideF411_mat_dt, burnsideF411_mat_dt, Matrix.diagonal_map (map_zero σ)]
  congr 1
  funext x
  rcases x with i | i <;> fin_cases i <;> simp

theorem burnsideF411_sp4_inner_of_torus [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (β : MulAut (StatedProj (StatedSp 2 K))) (k : ℕ)
    (hβ : β ^ (p ^ k) = 1)
    (h1 : (projStabilizer 2 K (flag 2 K 1)).map β.toMonoidHom = projStabilizer 2 K (flag 2 K 1))
    (h2 : (projStabilizer 2 K (flag 2 K 2)).map β.toMonoidHom = projStabilizer 2 K (flag 2 K 2))
    (hT : ∀ t : Kˣ, β (proj 2 K (burnsideF411_dt t)) * (proj 2 K (burnsideF411_dt t))⁻¹ ∈
      projUnipotent 2 K) :
    ∃ g, β = MulAut.conj g := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have h2K : (2 : K) ≠ 0 := by
    intro h0
    have h1' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff K p] at h1'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h1')
  obtain ⟨A, σ, rfl⟩ := (automorphism_generation_two h2K).2 β
  set M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := ((A : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hM
  have hA1 := burnsideF411_sp4_map_flag p A σ le_rfl (by norm_num) h1
  have hA2 := burnsideF411_sp4_map_flag p A σ (by norm_num) le_rfl h2
  rw [← hM] at hA1 hA2
  have hAe1 : M *ᵥ eOne ∈ flag 2 K 1 := by
    rw [← hA1]
    exact ⟨eOne, burnsideF411_eOne_mem_flag le_rfl (by norm_num), rfl⟩
  obtain ⟨α, hα⟩ := mem_flag_one.mp hAe1
  have hAe2 : M *ᵥ burnsideF411_eTwo ∈ flag 2 K 2 := by
    rw [← hA2]
    exact ⟨burnsideF411_eTwo, burnsideF411_eTwo_mem_flag, rfl⟩
  have hMinv : ∀ v, (((A : GL (Fin 2 ⊕ Fin 2) K)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ (M *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, hM, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  have hγ : (M *ᵥ burnsideF411_eTwo) (Sum.inl 1) ≠ 0 := by
    intro h0
    have hmem := burnsideF411_mem_flag_one_of hAe2 h0
    rw [← hA1] at hmem
    obtain ⟨w, hw, hwe⟩ := hmem
    have h3 : w = burnsideF411_eTwo := by
      have := congrArg (fun z => (((A : GL (Fin 2 ⊕ Fin 2) K)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ z) hwe
      simp only [Matrix.mulVecLin_apply] at this
      rwa [hMinv, hMinv] at this
    rw [h3] at hw
    have := (mem_isoFlag.mp ((mem_flag_of_le (by norm_num)).mp hw)).2 1 le_rfl
    simp at this
  have hα0 : α ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hα
    have := hMinv eOne
    rw [hα, Matrix.mulVec_zero] at this
    have := congrFun this (Sum.inl 0)
    simp at this
  have hσt : ∀ t : Kˣ, σ (t : K) = t := by
    intro t
    have hTt := hT t
    rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj, ← map_inv, ← map_mul] at hTt
    obtain ⟨u, hu, huX⟩ := hTt
    have huX' := (QuotientGroup.eq (s := spScalars 2 K)).mp huX
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp huX'
    set X := conjSp 2 K A (fieldSp 2 K σ (burnsideF411_dt t)) with hX
    have hXeq : ((X : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) = (u : GL (Fin 2 ⊕ Fin 2) K) *
        Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c *
          (burnsideF411_dt t : GL (Fin 2 ⊕ Fin 2) K) := by
      rw [hc, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv]
      group
    have hXv : ∀ w, mat X *ᵥ (M *ᵥ w) = M *ᵥ (mat (fieldSp 2 K σ (burnsideF411_dt t)) *ᵥ w) := by
      intro w
      have hcoe : mat X = M * mat (fieldSp 2 K σ (burnsideF411_dt t)) *
          (((A : GL (Fin 2 ⊕ Fin 2) K)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
        rw [hX, mat, coe_conjSp, Units.val_mul, Units.val_mul]
      rw [hcoe, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hMinv]
    have hXu : ∀ w, mat X *ᵥ w = (c : K) • (mat u *ᵥ (mat (burnsideF411_dt t) *ᵥ w)) := by
      intro w
      have : mat X = mat u * Matrix.scalar (Fin 2 ⊕ Fin 2) (c : K) * mat (burnsideF411_dt t) := by
        rw [mat, hXeq, Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
      have hs : ∀ v : Fin 2 ⊕ Fin 2 → K,
          Matrix.scalar (Fin 2 ⊕ Fin 2) (c : K) *ᵥ v = (c : K) • v := by
        intro v
        funext x
        rw [Matrix.scalar_apply, Matrix.mulVec_diagonal]
        rfl
      rw [this, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hs, Matrix.mulVec_smul]
    have hσd : mat (fieldSp 2 K σ (burnsideF411_dt t)) =
        mat (burnsideF411_dt (Units.map σ.toRingHom.toMonoidHom t)) := by
      rw [burnsideF411_fieldSp_dt]
    have e2 : M *ᵥ (mat (fieldSp 2 K σ (burnsideF411_dt t)) *ᵥ burnsideF411_eTwo) =
        (c : K) • (mat u *ᵥ (mat (burnsideF411_dt t) *ᵥ (M *ᵥ burnsideF411_eTwo))) :=
      (hXv _).symm.trans (hXu _)
    rw [hσd, burnsideF411_dt_mulVec_eTwo] at e2
    have e2' := congrFun e2 (Sum.inl 1)
    have hinr := burnsideF411_dt_mulVec_inr t (burnsideF411_inr_of_mem_flag_two hAe2)
    rw [Pi.smul_apply, smul_eq_mul, burnsideF411_unip_mulVec_inl_one hu hinr,
      (burnsideF411_dt_mulVec_inl t _).2] at e2'
    have hc1 : (c : K) = 1 := mul_right_cancel₀ hγ (by rw [one_mul]; exact e2'.symm)
    have e1 : M *ᵥ (mat (fieldSp 2 K σ (burnsideF411_dt t)) *ᵥ eOne) =
        (c : K) • (mat u *ᵥ (mat (burnsideF411_dt t) *ᵥ (M *ᵥ eOne))) :=
      (hXv _).symm.trans (hXu _)
    rw [hσd, burnsideF411_dt_mulVec_eOne, Matrix.mulVec_smul, hα, Matrix.mulVec_smul,
      burnsideF411_dt_mulVec_eOne, Matrix.mulVec_smul, Matrix.mulVec_smul,
      burnsideF411_unip_mulVec_eOne hu, hc1, one_smul, smul_smul] at e1
    have e1' := congrFun e1 (Sum.inl 0)
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one, Units.coe_map] at e1'
    have e1'' : σ (t : K) * α = α * t := e1'
    exact mul_right_cancel₀ hα0 (by rw [e1'']; ring)
  have hσ : σ = 1 := by
    refine RingEquiv.ext fun x => ?_
    by_cases hx : x = 0
    · rw [hx, map_zero, map_zero]
    · exact hσt (Units.mk0 x hx)
  rw [hσ, map_one, mul_one] at hβ ⊢
  have hD : conjAut 2 K A ∈ spLinearAutGroup 2 K := conjAut_mem_spLinearAutGroup A
  have hdvd := relIndex_inner_spLinearAutGroup_dvd (r := 2) hp hf hK
  set D := spLinearAutGroup 2 K with hDdef
  set I := CFSG.ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSp 2 K))
    with hI
  set x : D ⧸ I.subgroupOf D := QuotientGroup.mk (⟨conjAut 2 K A, hD⟩ : D) with hx
  have hxk : x ^ (p ^ k) = 1 := by
    rw [hx, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have : ((⟨conjAut 2 K A, hD⟩ ^ (p ^ k) : D) : MulAut (StatedProj (StatedSp 2 K))) = 1 := by
      rw [Subgroup.coe_pow, hβ]
    rw [this]
    exact I.one_mem
  have hcard2 : Nat.card (D ⧸ I.subgroupOf D) ∣ 2 := by
    have h1 : Nat.card (D ⧸ I.subgroupOf D) = I.relIndex D := (Subgroup.index_eq_card _).symm
    rw [h1]
    exact hdvd.trans (Nat.gcd_dvd_left 2 _)
  have hdvd1 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hxk
  have hdvd2 : orderOf x ∣ 2 := (orderOf_dvd_natCard x).trans hcard2
  have hcop : Nat.Coprime (p ^ k) 2 :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))
  have hx1 : x = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2)
  have hmem := (QuotientGroup.eq_one_iff (⟨conjAut 2 K A, hD⟩ : D)).mp hx1
  obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.mp hmem
  exact ⟨g, hg.symm⟩

end CFSG.ASVolI
