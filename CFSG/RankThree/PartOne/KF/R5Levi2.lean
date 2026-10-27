module

public import CFSG.RankThree.PartOne.KF.R6Levi

public section

namespace CFSG.RankThree.PartOne.KFU

open Matrix CFSG CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

@[expose] def blkB (σ : K ≃+* K) (X : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  !![X 0 0, X 0 1, 0, 0; X 1 0, X 1 1, 0, 0; 0, 0, σ (X 0 0), σ (X 0 1);
    0, 0, σ (X 1 0), σ (X 1 1)]

variable (σ : K ≃+* K)

theorem blkB_one : blkB σ (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkB]

theorem blkB_mul (X Y : Matrix (Fin 2) (Fin 2) K) : blkB σ (X * Y) = blkB σ X * blkB σ Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkB, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four]

theorem blkB_injective {X Y : Matrix (Fin 2) (Fin 2) K} (h : blkB σ X = blkB σ Y) : X = Y := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [blkB] using congrFun (congrFun h 0) 0
  · simpa [blkB] using congrFun (congrFun h 0) 1
  · simpa [blkB] using congrFun (congrFun h 1) 0
  · simpa [blkB] using congrFun (congrFun h 1) 1

theorem det_blkB (X : Matrix (Fin 2) (Fin 2) K) : (blkB σ X).det = X.det * σ X.det := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, blkB, Fin.succAbove]
  ring

theorem blkB_gram [CharP K 2] (hσσ : ∀ x, σ (σ x) = x) (X : Matrix (Fin 2) (Fin 2) K)
    (hX : X.det = 1) : conjTr σ (blkB σ X) * antidiag 4 * blkB σ X = antidiag 4 := by
  rw [Matrix.det_fin_two] at hX
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hXσ : σ (X 0 0) * σ (X 1 1) - σ (X 0 1) * σ (X 1 0) = 1 := by
    have := congrArg σ hX
    simpa [map_sub, map_mul] using this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkB, antidiag, conjTr, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply,
      Fin.rev, hσσ]
  all_goals first
    | linear_combination (σ (X 0 0) * σ (X 1 0)) * h2
    | linear_combination (σ (X 0 1) * σ (X 1 1)) * h2
    | linear_combination (X 0 0 * X 1 0) * h2
    | linear_combination (X 0 1 * X 1 1) * h2
    | linear_combination hXσ + (σ (X 0 1) * σ (X 1 0)) * h2
    | linear_combination hX + (X 0 1 * X 1 0) * h2

@[expose] noncomputable def blkBGL : SpecialLinearGroup (Fin 2) K →* GL (Fin 4) K where
  toFun A :=
    { val := blkB σ (A : Matrix (Fin 2) (Fin 2) K)
      inv := blkB σ ((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      val_inv := by
        rw [← blkB_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one, blkB_one]
      inv_val := by
        rw [← blkB_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one, blkB_one] }
  map_one' := by
    apply Units.ext
    simp [blkB_one]
  map_mul' A B := by
    apply Units.ext
    simp [blkB_mul]

@[expose] noncomputable def bB (ζ : Kˣ) (hζ : σ (ζ : K) = ζ) : ↥(SU σ 4) :=
  ⟨diagU (dvec4 ζ ζ), diagU_dvec4_mem_SU σ hζ hζ⟩

theorem coe_bB (ζ : Kˣ) (hζ : σ (ζ : K) = ζ) :
    ((bB σ ζ hζ : ↥(SU σ 4)) : GL (Fin 4) K) = diagU (dvec4 ζ ζ) := rfl

theorem centralizer_bB_facts {ζ : Kˣ} (hζ : σ (ζ : K) = ζ) (h2 : ζ ^ 2 ≠ 1) {g : ↥(SU σ 4)}
    (hg : g ∈ Subgroup.centralizer ({bB σ ζ hζ} : Set ↥(SU σ 4))) :
    gu g 0 2 = 0 ∧ gu g 0 3 = 0 ∧ gu g 1 2 = 0 ∧ gu g 1 3 = 0 ∧ gu g 2 0 = 0 ∧ gu g 2 1 = 0 ∧
      gu g 3 0 = 0 ∧ gu g 3 1 = 0 ∧
      σ (gu g 0 0) * gu g 3 2 + σ (gu g 1 0) * gu g 2 2 = 0 ∧
      σ (gu g 0 0) * gu g 3 3 + σ (gu g 1 0) * gu g 2 3 = 1 ∧
      σ (gu g 0 1) * gu g 3 2 + σ (gu g 1 1) * gu g 2 2 = 1 ∧
      σ (gu g 0 1) * gu g 3 3 + σ (gu g 1 1) * gu g 2 3 = 0 := by
  have hcomm : (g : GL (Fin 4) K) * diagU (dvec4 ζ ζ) = diagU (dvec4 ζ ζ) * (g : GL (Fin 4) K) :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hg)
  have hζ3 : ζ ≠ ζ⁻¹ := by
    intro h
    apply h2
    calc ζ ^ 2 = ζ * ζ := by rw [pow_two]
      _ = ζ * ζ⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel ζ
  have hne : ∀ i j : Fin 4, dvec4 ζ ζ i ≠ dvec4 ζ ζ j → gu g i j = 0 := fun i j h =>
    apply_eq_zero_of_commute_diagU hcomm h
  have e02 := hne 0 2 (by simpa [dvec4] using hζ3)
  have e03 := hne 0 3 (by simpa [dvec4] using hζ3)
  have e12 := hne 1 2 (by simpa [dvec4] using hζ3)
  have e13 := hne 1 3 (by simpa [dvec4] using hζ3)
  have e20 := hne 2 0 (by simpa [dvec4] using hζ3.symm)
  have e21 := hne 2 1 (by simpa [dvec4] using hζ3.symm)
  have e30 := hne 3 0 (by simpa [dvec4] using hζ3.symm)
  have e31 := hne 3 1 (by simpa [dvec4] using hζ3.symm)
  have hgram := (mem_SU.1 g.2).2
  have g03 := congrFun (congrFun hgram 0) 3
  have g02 := congrFun (congrFun hgram 0) 2
  have g12 := congrFun (congrFun hgram 1) 2
  have g13 := congrFun (congrFun hgram 1) 3
  simp [conjTr, Matrix.mul_apply, Fin.sum_univ_four, antidiag, Fin.rev,
    Matrix.transpose_apply] at g03 g02 g12 g13
  simp only [e02, e03, e12, e13, e20, e21, e30, e31, map_zero, mul_zero, add_zero, zero_add]
    at g03 g02 g12 g13
  refine ⟨e02, e03, e12, e13, e20, e21, e30, e31, ?_, ?_, ?_, ?_⟩
  · linear_combination g02
  · linear_combination g03
  · linear_combination g12
  · linear_combination g13

abbrev Xm4 {σ : K ≃+* K} (g : ↥(SU σ 4)) : Matrix (Fin 2) (Fin 2) K :=
  !![gu g 0 0, gu g 0 1; gu g 1 0, gu g 1 1]

@[expose] noncomputable def phiBSU {ζ : Kˣ} (hζ : σ (ζ : K) = ζ) (h2 : ζ ^ 2 ≠ 1) :
    ↥(Subgroup.centralizer ({bB σ ζ hζ} : Set ↥(SU σ 4))) →* Kˣ where
  toFun g :=
    Units.mk0 (Xm4 (g : ↥(SU σ 4))).det (fun h0 => by
      obtain ⟨-, -, -, -, -, -, -, -, i, ii, iii, -⟩ := centralizer_bB_facts σ hζ h2 g.2
      exact det_ne_zero_of_gram σ i ii iii (by simpa [Matrix.det_fin_two] using h0))
  map_one' := by
    apply Units.ext
    simp [Xm4, gu_one, Matrix.det_fin_two]
  map_mul' g h := by
    obtain ⟨e02, e03, e12, e13, -⟩ := centralizer_bB_facts σ hζ h2 g.2
    have hX : Xm4 ((g : ↥(SU σ 4)) * (h : ↥(SU σ 4))) = Xm4 (g : ↥(SU σ 4)) * Xm4 (h : ↥(SU σ 4)) := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [gu_mul, Matrix.mul_apply, Fin.sum_univ_four, e02, e03, e12, e13]
    apply Units.ext
    show (Xm4 ((g : ↥(SU σ 4)) * (h : ↥(SU σ 4)))).det =
      (Xm4 (g : ↥(SU σ 4))).det * (Xm4 (h : ↥(SU σ 4))).det
    rw [hX, Matrix.det_mul]

theorem phiBSU_apply {ζ : Kˣ} (hζ : σ (ζ : K) = ζ) (h2 : ζ ^ 2 ≠ 1)
    (g : ↥(Subgroup.centralizer ({bB σ ζ hζ} : Set ↥(SU σ 4)))) :
    ((phiBSU σ hζ h2 g : Kˣ) : K) = (Xm4 (g : ↥(SU σ 4))).det := rfl

variable [CharP K 2]

@[expose] noncomputable def suBlockB (hσσ : ∀ x, σ (σ x) = x) :
    SpecialLinearGroup (Fin 2) K →* ↥(SU σ 4) :=
  (blkBGL σ).codRestrict (SU σ 4) (fun A => by
    refine mem_SU.mpr ⟨?_, ?_⟩
    · show (blkB σ (A : Matrix (Fin 2) (Fin 2) K)).det = 1
      rw [det_blkB, A.2, map_one, one_mul]
    · exact blkB_gram σ hσσ _ A.2)

theorem coe_suBlockB (hσσ : ∀ x, σ (σ x) = x) (A : SpecialLinearGroup (Fin 2) K) :
    (((suBlockB σ hσσ A : ↥(SU σ 4)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      blkB σ (A : Matrix (Fin 2) (Fin 2) K) := rfl

theorem gu_suBlockB (hσσ : ∀ x, σ (σ x) = x) (A : SpecialLinearGroup (Fin 2) K) :
    gu (suBlockB σ hσσ A) = blkB σ (A : Matrix (Fin 2) (Fin 2) K) := rfl

theorem suBlockB_injective (hσσ : ∀ x, σ (σ x) = x) : Function.Injective (suBlockB σ hσσ) := by
  intro A B h
  apply Subtype.ext
  have h1 := congrArg (fun g : ↥(SU σ 4) => gu g) h
  simp only [gu_suBlockB] at h1
  exact blkB_injective σ h1

theorem suBlockB_mem_centralizer (hσσ : ∀ x, σ (σ x) = x) {ζ : Kˣ} (hζ : σ (ζ : K) = ζ)
    (A : SpecialLinearGroup (Fin 2) K) :
    suBlockB σ hσσ A ∈ Subgroup.centralizer ({bB σ ζ hζ} : Set ↥(SU σ 4)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_suBlockB, coe_bB, diagU_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkB, dvec4, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

theorem ker_phiBSU (hσσ : ∀ x, σ (σ x) = x) {ζ : Kˣ} (hζ : σ (ζ : K) = ζ) (h2 : ζ ^ 2 ≠ 1) :
    (phiBSU σ hζ h2).ker =
      (suBlockB σ hσσ).range.subgroupOf
        (Subgroup.centralizer ({bB σ ζ hζ} : Set ↥(SU σ 4))) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  obtain ⟨e02, e03, e12, e13, e20, e21, e30, e31, i, ii, iii, iv⟩ :=
    centralizer_bB_facts σ hζ h2 g.2
  constructor
  · intro h
    have hdet : (Xm4 (g : ↥(SU σ 4))).det = 1 := by
      have := congrArg (fun x : Kˣ => (x : K)) h
      rw [phiBSU_apply] at this
      simpa using this
    have hdet' := hdet
    rw [Matrix.det_fin_two_of] at hdet'
    obtain ⟨y00, y10, y11, y01⟩ := block_of_gram σ hdet' i ii iii iv
    have hgb : gu (g : ↥(SU σ 4)) = blkB σ (Xm4 (g : ↥(SU σ 4))) := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [blkB, Xm4, e02, e03, e12, e13, e20, e21, e30, e31, y00, y10, y11, y01,
          CharTwo.neg_eq]
    refine ⟨⟨Xm4 (g : ↥(SU σ 4)), hdet⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    exact hgb.symm
  · rintro ⟨A, hA⟩
    apply Units.ext
    rw [phiBSU_apply]
    have hX : Xm4 (g : ↥(SU σ 4)) = (A : Matrix (Fin 2) (Fin 2) K) := by
      rw [← hA]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [Xm4, gu_suBlockB, blkB]
    rw [hX]
    exact A.2

theorem perfectResidual_centralizer_bB [Finite K] (hσσ : ∀ x, σ (σ x) = x)
    (hK : 4 ≤ Nat.card K) {ζ : Kˣ} (hζ : σ (ζ : K) = ζ) (h2 : ζ ^ 2 ≠ 1) :
    inSubgroup perfectResidual (Subgroup.centralizer ({bB σ ζ hζ} : Set ↥(SU σ 4))) =
      (suBlockB σ hσσ).range := by
  have hq := CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (k := K) (m := 2) le_rfl hK
  have hperf : Group.IsPerfect ↥((suBlockB σ hσσ).range) := by
    have := hq.1
    exact Group.IsPerfect.ofSurjective
      (f := (MonoidHom.ofInjective (suBlockB_injective σ hσσ)).toMonoidHom)
      (MonoidHom.ofInjective (suBlockB_injective σ hσσ)).surjective
  exact inSubgroup_perfectResidual_eq_of_ker (by
    rintro _ ⟨A, rfl⟩
    exact suBlockB_mem_centralizer σ hσσ hζ A) hperf (phiBSU σ hζ h2) (ker_phiBSU σ hσσ hζ h2)

variable {σ}

@[expose] noncomputable def rhoB (σ : K ≃+* K) (hσσ : ∀ x, σ (σ x) = x) : Kˣ →* ↥(SU σ 4) :=
  (suBlockB σ hσσ).comp (diag2Hom K)

theorem rhoB_injective (hσσ : ∀ x, σ (σ x) = x) : Function.Injective (rhoB σ hσσ) :=
  (suBlockB_injective σ hσσ).comp (diag2Hom_injective K)

theorem coe_rhoB (hσσ : ∀ x, σ (σ x) = x) {a : Kˣ} (ha : σ (a : K) = a) :
    ((rhoB σ hσσ a : ↥(SU σ 4)) : GL (Fin 4) K) = diagU (dvec4 a a⁻¹) := by
  apply Units.ext
  show blkB σ (Matrix.diagonal fun i => ((![a, a⁻¹] i : Kˣ) : K)) = _
  rw [diagU_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkB, dvec4, ha, map_inv₀]

theorem rhoB_mem_range (hσσ : ∀ x, σ (σ x) = x) (a : Kˣ) :
    (rhoB σ hσσ a : ↥(SU σ 4)) ∈ (suBlockB σ hσσ).range :=
  ⟨diag2 a, rfl⟩

theorem rhoB_mem_torus5 (hσσ : ∀ x, σ (σ x) = x) {p : ℕ} {a : Kˣ} (ha : a ^ p = 1)
    (hσa : σ (a : K) = a) : (rhoB σ hσσ a : ↥(SU σ 4)) ∈ torus5 σ p :=
  mem_torus5_iff.2 ⟨a, a⁻¹, ha, by rw [inv_pow, ha, inv_one], coe_rhoB hσσ hσa⟩

theorem torus5_inf_rangeB_eq (hσσ : ∀ x, σ (σ x) = x) (p : ℕ)
    (hfix : ∀ u : Kˣ, u ^ p = 1 → σ (u : K) = u) :
    torus5 σ p ⊓ (suBlockB σ hσσ).range = (rootsOfUnity p K).map (rhoB σ hσσ) := by
  ext g
  constructor
  · rintro ⟨hgT, A, hA⟩
    obtain ⟨x, y, hx, hy, hxy⟩ := mem_torus5_iff.1 hgT
    have hmat : blkB σ (A : Matrix (Fin 2) (Fin 2) K) =
        Matrix.diagonal fun i => (dvec4 x y i : K) := by
      have h1 := congrArg (fun g : ↥(SU σ 4) => gu g) hA
      simp only [gu_suBlockB] at h1
      rw [h1]
      show ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = _
      rw [hxy, diagU_val]
    have a00 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 = x := by
      simpa [blkB, dvec4] using congrFun (congrFun hmat 0) 0
    have a11 : (A : Matrix (Fin 2) (Fin 2) K) 1 1 = y := by
      simpa [blkB, dvec4] using congrFun (congrFun hmat 1) 1
    have a01 : (A : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
      simpa [blkB, dvec4] using congrFun (congrFun hmat 0) 1
    have a10 : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
      simpa [blkB, dvec4] using congrFun (congrFun hmat 1) 0
    have hdet : (A : Matrix (Fin 2) (Fin 2) K).det = 1 := A.2
    rw [Matrix.det_fin_two, a00, a11, a01, a10, mul_zero, sub_zero] at hdet
    have hyx : y = x⁻¹ := by
      have : x * y = 1 := Units.ext hdet
      exact (eq_inv_of_mul_eq_one_right this)
    have hA' : A = diag2 x := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [diag2, a00, a11, a01, a10, hyx]
    refine ⟨x, (mem_rootsOfUnity p _).2 hx, ?_⟩
    show suBlockB σ hσσ (diag2 x) = g
    rw [← hA', hA]
  · rintro ⟨a, ha, rfl⟩
    exact ⟨rhoB_mem_torus5 hσσ ((mem_rootsOfUnity p _).1 ha)
      (hfix a ((mem_rootsOfUnity p _).1 ha)), rhoB_mem_range hσσ a⟩

theorem card_torus5_inf_rangeB (hσσ : ∀ x, σ (σ x) = x) {p : ℕ} (hp : 0 < p)
    (hfix : ∀ u : Kˣ, u ^ p = 1 → σ (u : K) = u) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    Nat.card ↥(torus5 σ p ⊓ (suBlockB σ hσσ).range) = p := by
  have : NeZero p := ⟨hp.ne'⟩
  obtain ⟨ζ, hζ⟩ := hζ
  rw [torus5_inf_rangeB_eq hσσ p hfix, Subgroup.card_map_of_injective (rhoB_injective hσσ)]
  exact IsPrimitiveRoot.card_rootsOfUnity (IsPrimitiveRoot.coe_units_iff.mpr hζ)

@[expose] noncomputable def rootUB (σ : K ≃+* K) (hσσ : ∀ x, σ (σ x) = x) : Subgroup ↥(SU σ 4) :=
  ((suBlockB σ hσσ).comp (tr2Hom K)).range

theorem mem_rootUB_iff (hσσ : ∀ x, σ (σ x) = x) {g : ↥(SU σ 4)} :
    g ∈ rootUB σ hσσ ↔ ∃ c : K, g = suBlockB σ hσσ (tr2 c) :=
  ⟨fun ⟨c, hc⟩ => ⟨Multiplicative.toAdd c, hc.symm⟩,
    fun ⟨c, hc⟩ => ⟨Multiplicative.ofAdd c, hc.symm⟩⟩

theorem suBlockB_tr2_mem_rootUB (hσσ : ∀ x, σ (σ x) = x) (c : K) :
    suBlockB σ hσσ (tr2 c) ∈ rootUB σ hσσ :=
  (mem_rootUB_iff hσσ).2 ⟨c, rfl⟩

theorem rootUB_le_range (hσσ : ∀ x, σ (σ x) = x) : rootUB σ hσσ ≤ (suBlockB σ hσσ).range := by
  intro g hg
  obtain ⟨c, rfl⟩ := (mem_rootUB_iff hσσ).1 hg
  exact ⟨tr2 c, rfl⟩

theorem isPGroup_rootUB (hσσ : ∀ x, σ (σ x) = x) : IsPGroup 2 ↥(rootUB σ hσσ) := by
  rw [IsPGroup.iff_orderOf]
  rintro ⟨g, hg⟩
  obtain ⟨c, rfl⟩ := (mem_rootUB_iff hσσ).1 hg
  have hsq : (suBlockB σ hσσ (tr2 c) : ↥(SU σ 4)) ^ 2 = 1 := by
    rw [pow_two, ← map_mul, tr2_mul, CharTwo.add_self_eq_zero, tr2_zero, map_one]
  have hdvd : orderOf (⟨suBlockB σ hσσ (tr2 c), hg⟩ : ↥(rootUB σ hσσ)) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa using hsq
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact ⟨0, by simpa using h⟩
  · exact ⟨1, by simpa using h⟩

theorem torus5_conj_rootUB (hσσ : ∀ x, σ (σ x) = x) {p : ℕ} {g : ↥(SU σ 4)}
    (hg : g ∈ torus5 σ p) : ∀ x ∈ rootUB σ hσσ, g * x * g⁻¹ ∈ rootUB σ hσσ := by
  intro x hx
  obtain ⟨c, rfl⟩ := (mem_rootUB_iff hσσ).1 hx
  obtain ⟨a, b, -, -, hab⟩ := mem_torus5_iff.1 hg
  obtain ⟨hσa, hσb⟩ := fix_of_diagU_mem_SU σ (hab ▸ g.2)
  have h : g * suBlockB σ hσσ (tr2 c) =
      suBlockB σ hσσ (tr2 ((a : K) * c * (b : K)⁻¹)) * g := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, coe_suBlockB, hab, diagU_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blkB, tr2, Matrix.transvection, dvec4, Matrix.mul_diagonal, Matrix.diagonal_mul,
        map_mul, map_inv₀, hσa, hσb]
    all_goals field_simp
  have : g * suBlockB σ hσσ (tr2 c) * g⁻¹ =
      suBlockB σ hσσ (tr2 ((a : K) * c * (b : K)⁻¹)) := by
    rw [h, mul_inv_cancel_right]
  rw [this]
  exact suBlockB_tr2_mem_rootUB hσσ _

theorem torus5_le_normalizer_rootUB (hσσ : ∀ x, σ (σ x) = x) {p : ℕ} :
    torus5 σ p ≤ Subgroup.normalizer (rootUB σ hσσ : Set ↥(SU σ 4)) := fun g hg =>
  mem_normalizer_of_conj_mem (torus5_conj_rootUB hσσ hg) (fun y hy => by
    have := torus5_conj_rootUB hσσ ((torus5 σ p).inv_mem hg) y hy
    simpa using this)

theorem suBlockB_tr2_one_not_commute_rhoB (hσσ : ∀ x, σ (σ x) = x) {a : Kˣ} (ha : a ≠ 1) :
    (suBlockB σ hσσ (tr2 (1 : K)) : ↥(SU σ 4)) * rhoB σ hσσ a ≠
      rhoB σ hσσ a * suBlockB σ hσσ (tr2 (1 : K)) := by
  intro h
  have h1 := congrArg (fun x : ↥(SU σ 4) => gu x 0 1) h
  simp only [gu_mul, rhoB, MonoidHom.comp_apply, diag2Hom_apply, gu_suBlockB] at h1
  simp [blkB, diag2, tr2, Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_four] at h1
  have h2 : (a⁻¹ : Kˣ) = a := Units.ext (by rw [Units.val_inv_eq_inv_val]; exact h1)
  exact ha (eq_one_of_inv_eq_self_two h2)

end CFSG.RankThree.PartOne.KFU
