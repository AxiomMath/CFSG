module

public import CFSG.RankThree.PartOne.KF.R5Levi

public section

namespace CFSG.RankThree.PartOne.KFU

open Matrix CFSG CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

@[expose] def dvec5 (a b : Kˣ) : Fin 5 → Kˣ := ![a, b, 1, b⁻¹, a⁻¹]

theorem d8Vec_five {p : ℕ} (v : D8Mod p K) :
    d8Vec 5 v = dvec5 ((v.1 : rootsOfUnity p K) : Kˣ) ((v.2 : rootsOfUnity p K) : Kˣ) := by
  funext i
  fin_cases i <;> simp [d8Vec, d8Cls, d8Ev, dvec5, Fin.rev]

@[expose] def blk6 (σ : K ≃+* K) (X : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 5) (Fin 5) K :=
  !![X 0 0, X 0 1, 0, 0, 0; X 1 0, X 1 1, 0, 0, 0; 0, 0, 1, 0, 0;
    0, 0, 0, σ (X 0 0), σ (X 0 1); 0, 0, 0, σ (X 1 0), σ (X 1 1)]

variable (σ : K ≃+* K)

theorem blk6_one : blk6 σ (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk6]

theorem blk6_mul (X Y : Matrix (Fin 2) (Fin 2) K) : blk6 σ (X * Y) = blk6 σ X * blk6 σ Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk6, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_five]

theorem blk6_injective {X Y : Matrix (Fin 2) (Fin 2) K} (h : blk6 σ X = blk6 σ Y) : X = Y := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [blk6] using congrFun (congrFun h 0) 0
  · simpa [blk6] using congrFun (congrFun h 0) 1
  · simpa [blk6] using congrFun (congrFun h 1) 0
  · simpa [blk6] using congrFun (congrFun h 1) 1

theorem det_blk6 (X : Matrix (Fin 2) (Fin 2) K) : (blk6 σ X).det = X.det * σ X.det := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, blk6, Fin.succAbove]
  ring

theorem blk6_gram [CharP K 2] (hσσ : ∀ x, σ (σ x) = x) (X : Matrix (Fin 2) (Fin 2) K)
    (hX : X.det = 1) : conjTr σ (blk6 σ X) * antidiag 5 * blk6 σ X = antidiag 5 := by
  rw [Matrix.det_fin_two] at hX
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hXσ : σ (X 0 0) * σ (X 1 1) - σ (X 0 1) * σ (X 1 0) = 1 := by
    have := congrArg σ hX
    simpa [map_sub, map_mul] using this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk6, antidiag, conjTr, Matrix.mul_apply, Fin.sum_univ_five, Matrix.transpose_apply,
      Fin.rev, hσσ]
  all_goals first
    | linear_combination (σ (X 0 0) * σ (X 1 0)) * h2
    | linear_combination (σ (X 0 1) * σ (X 1 1)) * h2
    | linear_combination (X 0 0 * X 1 0) * h2
    | linear_combination (X 0 1 * X 1 1) * h2
    | linear_combination hXσ + (σ (X 0 1) * σ (X 1 0)) * h2
    | linear_combination hX + (X 0 1 * X 1 0) * h2

@[expose] noncomputable def blk6GL : SpecialLinearGroup (Fin 2) K →* GL (Fin 5) K where
  toFun A :=
    { val := blk6 σ (A : Matrix (Fin 2) (Fin 2) K)
      inv := blk6 σ ((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      val_inv := by
        rw [← blk6_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one, blk6_one]
      inv_val := by
        rw [← blk6_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one, blk6_one] }
  map_one' := by
    apply Units.ext
    simp [blk6_one]
  map_mul' A B := by
    apply Units.ext
    simp [blk6_mul]

abbrev gu5 {σ : K ≃+* K} (g : ↥(SU σ 5)) : Matrix (Fin 5) (Fin 5) K :=
  ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)

theorem gu5_one : gu5 (1 : ↥(SU σ 5)) = 1 := rfl

theorem gu5_mul (g h : ↥(SU σ 5)) : gu5 (g * h) = gu5 g * gu5 h := rfl

theorem diagU_dvec5_mem_SU {a b : Kˣ} (ha : σ (a : K) = a) (hb : σ (b : K) = b) :
    (diagU (dvec5 a b) : GL (Fin 5) K) ∈ SU σ 5 := by
  refine mem_SU.mpr ⟨?_, diagU_gram σ (fun i => ?_)⟩
  · rw [det_diagU, ← Units.coe_prod]
    simp [Fin.prod_univ_five, dvec5]
  · fin_cases i <;> simp [dvec5, ha, hb, Fin.rev]

theorem fix_of_diagU_mem_SU5 {a b : Kˣ} (h : (diagU (dvec5 a b) : GL (Fin 5) K) ∈ SU σ 5) :
    σ (a : K) = a ∧ σ (b : K) = b := by
  have hg := (mem_SU.1 h).2
  have h04 := congrFun (congrFun hg 0) 4
  have h13 := congrFun (congrFun hg 1) 3
  simp [conjTr, diagU_val, Matrix.mul_apply, antidiag, Fin.rev, dvec5, Fin.sum_univ_five,
    Matrix.diagonal_apply] at h04 h13
  exact ⟨(mul_inv_eq_one₀ a.ne_zero).1 h04, (mul_inv_eq_one₀ b.ne_zero).1 h13⟩

@[expose] noncomputable def b6 (ζ : Kˣ) (hζ : σ (ζ : K) = ζ) : ↥(SU σ 5) :=
  ⟨diagU (dvec5 ζ ζ), diagU_dvec5_mem_SU σ hζ hζ⟩

theorem coe_b6 (ζ : Kˣ) (hζ : σ (ζ : K) = ζ) :
    ((b6 σ ζ hζ : ↥(SU σ 5)) : GL (Fin 5) K) = diagU (dvec5 ζ ζ) := rfl

theorem centralizer_b6_facts {ζ : Kˣ} (hζ : σ (ζ : K) = ζ) (h1 : ζ ≠ 1) (h2 : ζ ^ 2 ≠ 1)
    {g : ↥(SU σ 5)} (hg : g ∈ Subgroup.centralizer ({b6 σ ζ hζ} : Set ↥(SU σ 5))) :
    gu5 g 0 2 = 0 ∧ gu5 g 0 3 = 0 ∧ gu5 g 0 4 = 0 ∧ gu5 g 1 2 = 0 ∧ gu5 g 1 3 = 0 ∧
      gu5 g 1 4 = 0 ∧ gu5 g 2 0 = 0 ∧ gu5 g 2 1 = 0 ∧ gu5 g 2 3 = 0 ∧ gu5 g 2 4 = 0 ∧
      gu5 g 3 0 = 0 ∧ gu5 g 3 1 = 0 ∧ gu5 g 3 2 = 0 ∧ gu5 g 4 0 = 0 ∧ gu5 g 4 1 = 0 ∧
      gu5 g 4 2 = 0 ∧ σ (gu5 g 2 2) * gu5 g 2 2 = 1 ∧
      σ (gu5 g 0 0) * gu5 g 4 3 + σ (gu5 g 1 0) * gu5 g 3 3 = 0 ∧
      σ (gu5 g 0 0) * gu5 g 4 4 + σ (gu5 g 1 0) * gu5 g 3 4 = 1 ∧
      σ (gu5 g 0 1) * gu5 g 4 3 + σ (gu5 g 1 1) * gu5 g 3 3 = 1 ∧
      σ (gu5 g 0 1) * gu5 g 4 4 + σ (gu5 g 1 1) * gu5 g 3 4 = 0 := by
  have hcomm : (g : GL (Fin 5) K) * diagU (dvec5 ζ ζ) = diagU (dvec5 ζ ζ) * (g : GL (Fin 5) K) :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hg)
  have hζ1 : (1 : Kˣ) ≠ ζ := fun h => h1 h.symm
  have hζ2 : (1 : Kˣ) ≠ ζ⁻¹ := fun h => h1 (by simpa using h.symm)
  have hζ3 : ζ ≠ ζ⁻¹ := by
    intro h
    apply h2
    calc ζ ^ 2 = ζ * ζ := by rw [pow_two]
      _ = ζ * ζ⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel ζ
  have hne : ∀ i j : Fin 5, dvec5 ζ ζ i ≠ dvec5 ζ ζ j → gu5 g i j = 0 := fun i j h =>
    apply_eq_zero_of_commute_diagU hcomm h
  have e02 := hne 0 2 (by simpa [dvec5] using h1)
  have e03 := hne 0 3 (by simpa [dvec5] using hζ3)
  have e04 := hne 0 4 (by simpa [dvec5] using hζ3)
  have e12 := hne 1 2 (by simpa [dvec5] using h1)
  have e13 := hne 1 3 (by simpa [dvec5] using hζ3)
  have e14 := hne 1 4 (by simpa [dvec5] using hζ3)
  have e20 := hne 2 0 (by simpa [dvec5] using hζ1)
  have e21 := hne 2 1 (by simpa [dvec5] using hζ1)
  have e23 := hne 2 3 (by simpa [dvec5] using hζ2)
  have e24 := hne 2 4 (by simpa [dvec5] using hζ2)
  have e30 := hne 3 0 (by simpa [dvec5] using hζ3.symm)
  have e31 := hne 3 1 (by simpa [dvec5] using hζ3.symm)
  have e32 := hne 3 2 (by simpa [dvec5] using hζ2.symm)
  have e40 := hne 4 0 (by simpa [dvec5] using hζ3.symm)
  have e41 := hne 4 1 (by simpa [dvec5] using hζ3.symm)
  have e42 := hne 4 2 (by simpa [dvec5] using hζ2.symm)
  have hgram := (mem_SU.1 g.2).2
  have g22 := congrFun (congrFun hgram 2) 2
  have g03 := congrFun (congrFun hgram 0) 3
  have g04 := congrFun (congrFun hgram 0) 4
  have g13 := congrFun (congrFun hgram 1) 3
  have g14 := congrFun (congrFun hgram 1) 4
  simp [conjTr, Matrix.mul_apply, Fin.sum_univ_five, antidiag, Fin.rev,
    Matrix.transpose_apply] at g22 g03 g04 g13 g14
  simp only [e02, e03, e04, e12, e13, e14, e20, e21, e23, e24, e30, e31, e32, e40, e41, e42,
    map_zero, mul_zero, add_zero, zero_add] at g22 g03 g04 g13 g14
  refine ⟨e02, e03, e04, e12, e13, e14, e20, e21, e23, e24, e30, e31, e32, e40, e41, e42,
    ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination g22
  · linear_combination g03
  · linear_combination g04
  · linear_combination g13
  · linear_combination g14

theorem det_ne_zero_of_gram {a b c d y00 y01 y10 y11 : K}
    (i : σ a * y10 + σ c * y00 = 0) (ii : σ a * y11 + σ c * y01 = 1)
    (iii : σ b * y10 + σ d * y00 = 1) :
    a * d - b * c ≠ 0 := by
  intro h0
  have hΔ : σ a * σ d - σ b * σ c = 0 := by
    have := congrArg σ h0
    simpa [map_sub, map_mul] using this
  have key : (σ a * σ d - σ b * σ c) * (y00 * y11 - y01 * y10) = 1 := by
    linear_combination (-(σ b * y11 + σ d * y01)) * i + (σ a * y11 + σ c * y01) * iii + ii
  rw [hΔ, zero_mul] at key
  exact zero_ne_one key

theorem block_of_gram {a b c d y00 y01 y10 y11 : K}
    (hdet : a * d - b * c = 1)
    (i : σ a * y10 + σ c * y00 = 0) (ii : σ a * y11 + σ c * y01 = 1)
    (iii : σ b * y10 + σ d * y00 = 1) (iv : σ b * y11 + σ d * y01 = 0) :
    y00 = σ a ∧ y10 = -σ c ∧ y11 = σ d ∧ y01 = -σ b := by
  have hΔ : σ a * σ d - σ b * σ c = 1 := by
    have := congrArg σ hdet
    simpa [map_sub, map_mul] using this
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (-y00) * hΔ + σ a * iii - σ b * i
  · linear_combination (-y10) * hΔ + σ d * i - σ c * iii
  · linear_combination (-y11) * hΔ + σ d * ii - σ c * iv
  · linear_combination (-y01) * hΔ - σ b * ii + σ a * iv

abbrev Xm {σ : K ≃+* K} (g : ↥(SU σ 5)) : Matrix (Fin 2) (Fin 2) K :=
  !![gu5 g 0 0, gu5 g 0 1; gu5 g 1 0, gu5 g 1 1]

@[expose] noncomputable def phi6 {ζ : Kˣ} (hζ : σ (ζ : K) = ζ) (h1 : ζ ≠ 1) (h2 : ζ ^ 2 ≠ 1) :
    ↥(Subgroup.centralizer ({b6 σ ζ hζ} : Set ↥(SU σ 5))) →* Kˣ × Kˣ where
  toFun g :=
    (Units.mk0 (Xm (g : ↥(SU σ 5))).det (fun h0 => by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, i, ii, iii, -⟩ :=
        centralizer_b6_facts σ hζ h1 h2 g.2
      exact det_ne_zero_of_gram σ i ii iii (by simpa [Matrix.det_fin_two] using h0)),
     Units.mk0 (gu5 (g : ↥(SU σ 5)) 2 2) (fun h0 => by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hBB, -⟩ :=
        centralizer_b6_facts σ hζ h1 h2 g.2
      rw [h0, map_zero, zero_mul] at hBB
      exact zero_ne_one hBB))
  map_one' := by
    refine Prod.ext (Units.ext ?_) (Units.ext ?_)
    · simp [Xm, gu5_one, Matrix.det_fin_two]
    · simp [gu5_one]
  map_mul' g h := by
    obtain ⟨e02, e03, e04, e12, e13, e14, e20, e21, e23, e24, -⟩ :=
      centralizer_b6_facts σ hζ h1 h2 g.2
    have hX : Xm ((g : ↥(SU σ 5)) * (h : ↥(SU σ 5))) = Xm (g : ↥(SU σ 5)) * Xm (h : ↥(SU σ 5)) := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [gu5_mul, Matrix.mul_apply, Fin.sum_univ_five, e02, e03, e04, e12, e13, e14]
    refine Prod.ext (Units.ext ?_) (Units.ext ?_)
    · show (Xm ((g : ↥(SU σ 5)) * (h : ↥(SU σ 5)))).det =
        (Xm (g : ↥(SU σ 5))).det * (Xm (h : ↥(SU σ 5))).det
      rw [hX, Matrix.det_mul]
    · show gu5 ((g : ↥(SU σ 5)) * (h : ↥(SU σ 5))) 2 2 =
        gu5 (g : ↥(SU σ 5)) 2 2 * gu5 (h : ↥(SU σ 5)) 2 2
      simp [gu5_mul, Matrix.mul_apply, Fin.sum_univ_five, e20, e21, e23, e24]

theorem phi6_fst {ζ : Kˣ} (hζ : σ (ζ : K) = ζ) (h1 : ζ ≠ 1) (h2 : ζ ^ 2 ≠ 1)
    (g : ↥(Subgroup.centralizer ({b6 σ ζ hζ} : Set ↥(SU σ 5)))) :
    (((phi6 σ hζ h1 h2 g).1 : Kˣ) : K) = (Xm (g : ↥(SU σ 5))).det := rfl

theorem phi6_snd {ζ : Kˣ} (hζ : σ (ζ : K) = ζ) (h1 : ζ ≠ 1) (h2 : ζ ^ 2 ≠ 1)
    (g : ↥(Subgroup.centralizer ({b6 σ ζ hζ} : Set ↥(SU σ 5)))) :
    (((phi6 σ hζ h1 h2 g).2 : Kˣ) : K) = gu5 (g : ↥(SU σ 5)) 2 2 := rfl

variable [CharP K 2]

@[expose] noncomputable def suBlock6 (hσσ : ∀ x, σ (σ x) = x) :
    SpecialLinearGroup (Fin 2) K →* ↥(SU σ 5) :=
  (blk6GL σ).codRestrict (SU σ 5) (fun A => by
    refine mem_SU.mpr ⟨?_, ?_⟩
    · show (blk6 σ (A : Matrix (Fin 2) (Fin 2) K)).det = 1
      rw [det_blk6, A.2, map_one, one_mul]
    · exact blk6_gram σ hσσ _ A.2)

theorem coe_suBlock6 (hσσ : ∀ x, σ (σ x) = x) (A : SpecialLinearGroup (Fin 2) K) :
    (((suBlock6 σ hσσ A : ↥(SU σ 5)) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      blk6 σ (A : Matrix (Fin 2) (Fin 2) K) := rfl

theorem gu5_suBlock6 (hσσ : ∀ x, σ (σ x) = x) (A : SpecialLinearGroup (Fin 2) K) :
    gu5 (suBlock6 σ hσσ A) = blk6 σ (A : Matrix (Fin 2) (Fin 2) K) := rfl

theorem suBlock6_injective (hσσ : ∀ x, σ (σ x) = x) : Function.Injective (suBlock6 σ hσσ) := by
  intro A B h
  apply Subtype.ext
  have h1 := congrArg (fun g : ↥(SU σ 5) => gu5 g) h
  simp only [gu5_suBlock6] at h1
  exact blk6_injective σ h1

theorem suBlock6_mem_centralizer (hσσ : ∀ x, σ (σ x) = x) {ζ : Kˣ} (hζ : σ (ζ : K) = ζ)
    (A : SpecialLinearGroup (Fin 2) K) :
    suBlock6 σ hσσ A ∈ Subgroup.centralizer ({b6 σ ζ hζ} : Set ↥(SU σ 5)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_suBlock6, coe_b6, diagU_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk6, dvec5, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

theorem ker_phi6 (hσσ : ∀ x, σ (σ x) = x) {ζ : Kˣ} (hζ : σ (ζ : K) = ζ) (h1 : ζ ≠ 1)
    (h2 : ζ ^ 2 ≠ 1) :
    (phi6 σ hζ h1 h2).ker =
      (suBlock6 σ hσσ).range.subgroupOf
        (Subgroup.centralizer ({b6 σ ζ hζ} : Set ↥(SU σ 5))) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  obtain ⟨e02, e03, e04, e12, e13, e14, e20, e21, e23, e24, e30, e31, e32, e40, e41, e42, hBB,
    i, ii, iii, iv⟩ := centralizer_b6_facts σ hζ h1 h2 g.2
  constructor
  · intro h
    have hdet : (Xm (g : ↥(SU σ 5))).det = 1 := by
      have := congrArg (fun x : Kˣ × Kˣ => ((x.1 : Kˣ) : K)) h
      rw [phi6_fst] at this
      simpa using this
    have hu : gu5 (g : ↥(SU σ 5)) 2 2 = 1 := by
      have := congrArg (fun x : Kˣ × Kˣ => ((x.2 : Kˣ) : K)) h
      rw [phi6_snd] at this
      simpa using this
    have hdet' := hdet
    rw [Matrix.det_fin_two_of] at hdet'
    obtain ⟨y00, y10, y11, y01⟩ := block_of_gram σ hdet' i ii iii iv
    have hgb : gu5 (g : ↥(SU σ 5)) = blk6 σ (Xm (g : ↥(SU σ 5))) := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [blk6, Xm, e02, e03, e04, e12, e13, e14, e20, e21, e23, e24, e30, e31, e32, e40, e41,
          e42, hu, y00, y10, y11, y01, CharTwo.neg_eq]
    refine ⟨⟨Xm (g : ↥(SU σ 5)), hdet⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    exact hgb.symm
  · rintro ⟨A, hA⟩
    refine Prod.ext (Units.ext ?_) (Units.ext ?_)
    · rw [phi6_fst]
      have hX : Xm (g : ↥(SU σ 5)) = (A : Matrix (Fin 2) (Fin 2) K) := by
        rw [← hA]
        ext a b
        fin_cases a <;> fin_cases b <;> simp [Xm, gu5_suBlock6, blk6]
      rw [hX]
      exact A.2
    · rw [phi6_snd]
      rw [← hA]
      simp [gu5_suBlock6, blk6]

theorem perfectResidual_centralizer_b6 [Finite K] (hσσ : ∀ x, σ (σ x) = x)
    (hK : 4 ≤ Nat.card K) {ζ : Kˣ} (hζ : σ (ζ : K) = ζ) (h1 : ζ ≠ 1) (h2 : ζ ^ 2 ≠ 1) :
    inSubgroup perfectResidual (Subgroup.centralizer ({b6 σ ζ hζ} : Set ↥(SU σ 5))) =
      (suBlock6 σ hσσ).range := by
  have hq := CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (k := K) (m := 2) le_rfl hK
  have hperf : Group.IsPerfect ↥((suBlock6 σ hσσ).range) := by
    have := hq.1
    exact Group.IsPerfect.ofSurjective
      (f := (MonoidHom.ofInjective (suBlock6_injective σ hσσ)).toMonoidHom)
      (MonoidHom.ofInjective (suBlock6_injective σ hσσ)).surjective
  exact inSubgroup_perfectResidual_eq_of_ker (by
    rintro _ ⟨A, rfl⟩
    exact suBlock6_mem_centralizer σ hσσ hζ A) hperf (phi6 σ hζ h1 h2) (ker_phi6 σ hσσ hζ h1 h2)

theorem isQuasisimple_perfectResidual_centralizer_b6 [Finite K] (hσσ : ∀ x, σ (σ x) = x)
    (hK : 4 ≤ Nat.card K) {ζ : Kˣ} (hζ : σ (ζ : K) = ζ) (h1 : ζ ≠ 1) (h2 : ζ ^ 2 ≠ 1) :
    IsQuasisimple ↥(inSubgroup perfectResidual
      (Subgroup.centralizer ({b6 σ ζ hζ} : Set ↥(SU σ 5)))) := by
  rw [perfectResidual_centralizer_b6 σ hσσ hK hζ h1 h2]
  exact isQuasisimple_of_mulEquiv (MonoidHom.ofInjective (suBlock6_injective σ hσσ))
    (CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (k := K) (m := 2) le_rfl hK)

theorem card_center_range_suBlock6 (hσσ : ∀ x, σ (σ x) = x) :
    Nat.card (Subgroup.center ↥((suBlock6 σ hσσ).range)) = 1 := by
  rw [← card_center_mulEquiv (MonoidHom.ofInjective (suBlock6_injective σ hσσ))]
  exact card_center_SL_two

variable {σ}

@[expose] noncomputable def torus6 (σ : K ≃+* K) (p : ℕ) : Subgroup ↥(SU σ 5) :=
  (d8Tor p K 5).subgroupOf (SU σ 5)

omit [CharP K 2] in
theorem mem_torus6_iff {p : ℕ} {g : ↥(SU σ 5)} :
    g ∈ torus6 σ p ↔ ∃ a b : Kˣ, a ^ p = 1 ∧ b ^ p = 1 ∧
      ((g : GL (Fin 5) K)) = diagU (dvec5 a b) := by
  rw [torus6, Subgroup.mem_subgroupOf, mem_d8Tor_iff]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨(v.1 : rootsOfUnity p K), (v.2 : rootsOfUnity p K),
      (mem_rootsOfUnity p _).1 v.1.2, (mem_rootsOfUnity p _).1 v.2.2, ?_⟩
    rw [← hv, d8Vec_five]
  · rintro ⟨a, b, ha, hb, h⟩
    refine ⟨(⟨a, (mem_rootsOfUnity p _).2 ha⟩, ⟨b, (mem_rootsOfUnity p _).2 hb⟩), ?_⟩
    rw [h, d8Vec_five]

omit [CharP K 2] in
theorem torus6_pow_eq_one {p : ℕ} {g : ↥(SU σ 5)} (hg : g ∈ torus6 σ p) : g ^ p = 1 := by
  obtain ⟨a, b, ha, hb, hab⟩ := mem_torus6_iff.1 hg
  apply Subtype.ext
  show ((g : GL (Fin 5) K)) ^ p = 1
  rw [hab, diagU_pow]
  have : dvec5 a b ^ p = 1 := by
    funext i
    fin_cases i <;> simp [dvec5, inv_pow, ha, hb]
  rw [this, diagU_one]

omit [CharP K 2] in
theorem b6_mem_torus6 {p : ℕ} {ζ : Kˣ} (hζ : σ (ζ : K) = ζ) (hp : ζ ^ p = 1) :
    b6 σ ζ hζ ∈ torus6 σ p :=
  mem_torus6_iff.2 ⟨ζ, ζ, hp, hp, rfl⟩

@[expose] noncomputable def rho6 (σ : K ≃+* K) (hσσ : ∀ x, σ (σ x) = x) : Kˣ →* ↥(SU σ 5) :=
  (suBlock6 σ hσσ).comp (diag2Hom K)

theorem rho6_injective (hσσ : ∀ x, σ (σ x) = x) : Function.Injective (rho6 σ hσσ) :=
  (suBlock6_injective σ hσσ).comp (diag2Hom_injective K)

theorem coe_rho6 (hσσ : ∀ x, σ (σ x) = x) {a : Kˣ} (ha : σ (a : K) = a) :
    ((rho6 σ hσσ a : ↥(SU σ 5)) : GL (Fin 5) K) = diagU (dvec5 a a⁻¹) := by
  apply Units.ext
  show blk6 σ (Matrix.diagonal fun i => ((![a, a⁻¹] i : Kˣ) : K)) = _
  rw [diagU_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk6, dvec5, ha, map_inv₀]

theorem rho6_mem_range (hσσ : ∀ x, σ (σ x) = x) (a : Kˣ) :
    (rho6 σ hσσ a : ↥(SU σ 5)) ∈ (suBlock6 σ hσσ).range :=
  ⟨diag2 a, rfl⟩

theorem rho6_mem_torus6 (hσσ : ∀ x, σ (σ x) = x) {p : ℕ} {a : Kˣ} (ha : a ^ p = 1)
    (hσa : σ (a : K) = a) : (rho6 σ hσσ a : ↥(SU σ 5)) ∈ torus6 σ p :=
  mem_torus6_iff.2 ⟨a, a⁻¹, ha, by rw [inv_pow, ha, inv_one], coe_rho6 hσσ hσa⟩

theorem torus6_inf_range_eq (hσσ : ∀ x, σ (σ x) = x) (p : ℕ)
    (hfix : ∀ u : Kˣ, u ^ p = 1 → σ (u : K) = u) :
    torus6 σ p ⊓ (suBlock6 σ hσσ).range = (rootsOfUnity p K).map (rho6 σ hσσ) := by
  ext g
  constructor
  · rintro ⟨hgT, A, hA⟩
    obtain ⟨x, y, hx, hy, hxy⟩ := mem_torus6_iff.1 hgT
    have hmat : blk6 σ (A : Matrix (Fin 2) (Fin 2) K) =
        Matrix.diagonal fun i => (dvec5 x y i : K) := by
      have h1 := congrArg (fun g : ↥(SU σ 5) => gu5 g) hA
      simp only [gu5_suBlock6] at h1
      rw [h1]
      show ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = _
      rw [hxy, diagU_val]
    have a00 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 = x := by
      simpa [blk6, dvec5] using congrFun (congrFun hmat 0) 0
    have a11 : (A : Matrix (Fin 2) (Fin 2) K) 1 1 = y := by
      simpa [blk6, dvec5] using congrFun (congrFun hmat 1) 1
    have a01 : (A : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
      simpa [blk6, dvec5] using congrFun (congrFun hmat 0) 1
    have a10 : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
      simpa [blk6, dvec5] using congrFun (congrFun hmat 1) 0
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
    show suBlock6 σ hσσ (diag2 x) = g
    rw [← hA', hA]
  · rintro ⟨a, ha, rfl⟩
    exact ⟨rho6_mem_torus6 hσσ ((mem_rootsOfUnity p _).1 ha)
      (hfix a ((mem_rootsOfUnity p _).1 ha)), rho6_mem_range hσσ a⟩

theorem card_torus6_inf_range (hσσ : ∀ x, σ (σ x) = x) {p : ℕ} (hp : 0 < p)
    (hfix : ∀ u : Kˣ, u ^ p = 1 → σ (u : K) = u) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    Nat.card ↥(torus6 σ p ⊓ (suBlock6 σ hσσ).range) = p := by
  have : NeZero p := ⟨hp.ne'⟩
  obtain ⟨ζ, hζ⟩ := hζ
  rw [torus6_inf_range_eq hσσ p hfix, Subgroup.card_map_of_injective (rho6_injective hσσ)]
  exact IsPrimitiveRoot.card_rootsOfUnity (IsPrimitiveRoot.coe_units_iff.mpr hζ)

@[expose] noncomputable def rootU6 (σ : K ≃+* K) (hσσ : ∀ x, σ (σ x) = x) :
    Subgroup ↥(SU σ 5) :=
  ((suBlock6 σ hσσ).comp (tr2Hom K)).range

theorem mem_rootU6_iff (hσσ : ∀ x, σ (σ x) = x) {g : ↥(SU σ 5)} :
    g ∈ rootU6 σ hσσ ↔ ∃ c : K, g = suBlock6 σ hσσ (tr2 c) :=
  ⟨fun ⟨c, hc⟩ => ⟨Multiplicative.toAdd c, hc.symm⟩,
    fun ⟨c, hc⟩ => ⟨Multiplicative.ofAdd c, hc.symm⟩⟩

theorem suBlock6_tr2_mem_rootU6 (hσσ : ∀ x, σ (σ x) = x) (c : K) :
    suBlock6 σ hσσ (tr2 c) ∈ rootU6 σ hσσ :=
  (mem_rootU6_iff hσσ).2 ⟨c, rfl⟩

theorem rootU6_le_range (hσσ : ∀ x, σ (σ x) = x) : rootU6 σ hσσ ≤ (suBlock6 σ hσσ).range := by
  intro g hg
  obtain ⟨c, rfl⟩ := (mem_rootU6_iff hσσ).1 hg
  exact ⟨tr2 c, rfl⟩

theorem isPGroup_rootU6 (hσσ : ∀ x, σ (σ x) = x) : IsPGroup 2 ↥(rootU6 σ hσσ) := by
  rw [IsPGroup.iff_orderOf]
  rintro ⟨g, hg⟩
  obtain ⟨c, rfl⟩ := (mem_rootU6_iff hσσ).1 hg
  have hsq : (suBlock6 σ hσσ (tr2 c) : ↥(SU σ 5)) ^ 2 = 1 := by
    rw [pow_two, ← map_mul, tr2_mul, CharTwo.add_self_eq_zero, tr2_zero, map_one]
  have hdvd : orderOf (⟨suBlock6 σ hσσ (tr2 c), hg⟩ : ↥(rootU6 σ hσσ)) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa using hsq
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact ⟨0, by simpa using h⟩
  · exact ⟨1, by simpa using h⟩

theorem torus6_conj_rootU6 (hσσ : ∀ x, σ (σ x) = x) {p : ℕ} {g : ↥(SU σ 5)}
    (hg : g ∈ torus6 σ p) : ∀ x ∈ rootU6 σ hσσ, g * x * g⁻¹ ∈ rootU6 σ hσσ := by
  intro x hx
  obtain ⟨c, rfl⟩ := (mem_rootU6_iff hσσ).1 hx
  obtain ⟨a, b, -, -, hab⟩ := mem_torus6_iff.1 hg
  obtain ⟨hσa, hσb⟩ := fix_of_diagU_mem_SU5 σ (hab ▸ g.2)
  have h : g * suBlock6 σ hσσ (tr2 c) =
      suBlock6 σ hσσ (tr2 ((a : K) * c * (b : K)⁻¹)) * g := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, coe_suBlock6, hab, diagU_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blk6, tr2, Matrix.transvection, dvec5, Matrix.mul_diagonal, Matrix.diagonal_mul,
        map_mul, map_inv₀, hσa, hσb]
    all_goals field_simp
  have : g * suBlock6 σ hσσ (tr2 c) * g⁻¹ =
      suBlock6 σ hσσ (tr2 ((a : K) * c * (b : K)⁻¹)) := by
    rw [h, mul_inv_cancel_right]
  rw [this]
  exact suBlock6_tr2_mem_rootU6 hσσ _

theorem torus6_le_normalizer_rootU6 (hσσ : ∀ x, σ (σ x) = x) {p : ℕ} :
    torus6 σ p ≤ Subgroup.normalizer (rootU6 σ hσσ : Set ↥(SU σ 5)) := fun g hg =>
  mem_normalizer_of_conj_mem (torus6_conj_rootU6 hσσ hg) (fun y hy => by
    have := torus6_conj_rootU6 hσσ ((torus6 σ p).inv_mem hg) y hy
    simpa using this)

theorem suBlock6_tr2_one_not_commute_rho6 (hσσ : ∀ x, σ (σ x) = x) {a : Kˣ} (ha : a ≠ 1) :
    (suBlock6 σ hσσ (tr2 (1 : K)) : ↥(SU σ 5)) * rho6 σ hσσ a ≠
      rho6 σ hσσ a * suBlock6 σ hσσ (tr2 (1 : K)) := by
  intro h
  have h1 := congrArg (fun x : ↥(SU σ 5) => gu5 x 0 1) h
  simp only [gu5_mul, rho6, MonoidHom.comp_apply, diag2Hom_apply, gu5_suBlock6] at h1
  simp [blk6, diag2, tr2, Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_five] at h1
  have h2 : (a⁻¹ : Kˣ) = a := Units.ext (by rw [Units.val_inv_eq_inv_val]; exact h1)
  exact ha (eq_one_of_inv_eq_self_two h2)

end CFSG.RankThree.PartOne.KFU
