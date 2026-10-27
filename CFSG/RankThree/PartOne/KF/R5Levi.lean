module

public import CFSG.RankThree.PartOne.KF.R7Levi

public section

namespace CFSG.RankThree.PartOne.KFU

open Matrix CFSG CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

@[expose] def fixF (σ : K ≃+* K) : Subfield K := σ.toRingHom.eqLocusField (RingHom.id K)

theorem mem_fixF {σ : K ≃+* K} {c : K} : c ∈ fixF σ ↔ σ c = c := Iff.rfl

@[expose] noncomputable def blkGL : SpecialLinearGroup (Fin 2) K →* GL (Fin 4) K where
  toFun A :=
    { val := blk22 (A : Matrix (Fin 2) (Fin 2) K)
      inv := blk22 ((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      val_inv := by
        rw [← blk22_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one, blk22_one]
      inv_val := by
        rw [← blk22_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one, blk22_one] }
  map_one' := by
    apply Units.ext
    simp [blk22_one]
  map_mul' A B := by
    apply Units.ext
    simp [blk22_mul]

theorem map_blk (φ : K → K) (h0 : φ 0 = 0) (h1 : φ 1 = 1) (X : Matrix (Fin 2) (Fin 2) K) :
    (blk22 X).map φ = blk22 (X.map φ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk22, h0, h1]

variable (σ : K ≃+* K)

@[expose] noncomputable def liftSL :
    SpecialLinearGroup (Fin 2) (fixF σ) →* SpecialLinearGroup (Fin 2) K :=
  SpecialLinearGroup.map (fixF σ).subtype

theorem coe_liftSL (A : SpecialLinearGroup (Fin 2) (fixF σ)) (i j : Fin 2) :
    ((liftSL σ A : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j =
      ((A : Matrix (Fin 2) (Fin 2) (fixF σ)) i j : K) := rfl

theorem liftSL_injective : Function.Injective (liftSL σ) := by
  intro A B h
  apply Subtype.ext
  ext i j
  have := congrArg (fun X : SpecialLinearGroup (Fin 2) K =>
    (X : Matrix (Fin 2) (Fin 2) K) i j) h
  exact this

abbrev gu {σ : K ≃+* K} (g : ↥(SU σ 4)) : Matrix (Fin 4) (Fin 4) K :=
  ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)

theorem gu_one : gu (1 : ↥(SU σ 4)) = 1 := rfl

theorem gu_mul (g h : ↥(SU σ 4)) : gu (g * h) = gu g * gu h := rfl

theorem diagU_dvec4_mem_SU {a b : Kˣ} (ha : σ (a : K) = a) (hb : σ (b : K) = b) :
    (diagU (dvec4 a b) : GL (Fin 4) K) ∈ SU σ 4 := by
  refine mem_SU.mpr ⟨?_, diagU_gram σ (fun i => ?_)⟩
  · rw [det_diagU, ← Units.coe_prod]
    simp [Fin.prod_univ_four, dvec4]
  · fin_cases i <;> simp [dvec4, ha, hb, Fin.rev]

theorem fix_of_diagU_mem_SU {a b : Kˣ} (h : (diagU (dvec4 a b) : GL (Fin 4) K) ∈ SU σ 4) :
    σ (a : K) = a ∧ σ (b : K) = b := by
  have hg := (mem_SU.1 h).2
  have h03 := congrFun (congrFun hg 0) 3
  have h12 := congrFun (congrFun hg 1) 2
  simp [conjTr, diagU_val, Matrix.mul_apply, antidiag, Fin.rev, dvec4, Fin.sum_univ_four,
    Matrix.diagonal_apply] at h03 h12
  exact ⟨(mul_inv_eq_one₀ a.ne_zero).1 h03, (mul_inv_eq_one₀ b.ne_zero).1 h12⟩

@[expose] noncomputable def b5 (ζ : Kˣ) (hζ : σ (ζ : K) = ζ) : ↥(SU σ 4) :=
  ⟨diagU (dvec4 1 ζ), diagU_dvec4_mem_SU σ (by simp) hζ⟩

theorem coe_b5 (ζ : Kˣ) (hζ : σ (ζ : K) = ζ) :
    ((b5 σ ζ hζ : ↥(SU σ 4)) : GL (Fin 4) K) = diagU (dvec4 1 ζ) := rfl

theorem centralizer_b5_facts {ζ : Kˣ} (hζ : σ (ζ : K) = ζ) (h1 : ζ ≠ 1) (h2 : ζ ^ 2 ≠ 1)
    {g : ↥(SU σ 4)} (hg : g ∈ Subgroup.centralizer ({b5 σ ζ hζ} : Set ↥(SU σ 4))) :
    gu g 0 1 = 0 ∧ gu g 0 2 = 0 ∧ gu g 3 1 = 0 ∧ gu g 3 2 = 0 ∧ gu g 1 0 = 0 ∧ gu g 2 0 = 0 ∧
      gu g 1 3 = 0 ∧ gu g 2 3 = 0 ∧ gu g 1 2 = 0 ∧ gu g 2 1 = 0 ∧
      σ (gu g 1 1) * gu g 2 2 = 1 ∧
      σ (gu g 0 0) * gu g 3 0 + σ (gu g 3 0) * gu g 0 0 = 0 ∧
      σ (gu g 0 0) * gu g 3 3 + σ (gu g 3 0) * gu g 0 3 = 1 ∧
      σ (gu g 0 3) * gu g 3 0 + σ (gu g 3 3) * gu g 0 0 = 1 ∧
      σ (gu g 0 3) * gu g 3 3 + σ (gu g 3 3) * gu g 0 3 = 0 := by
  have hcomm : (g : GL (Fin 4) K) * diagU (dvec4 1 ζ) = diagU (dvec4 1 ζ) * (g : GL (Fin 4) K) :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hg)
  have hζ1 : (1 : Kˣ) ≠ ζ := fun h => h1 h.symm
  have hζ2 : (1 : Kˣ) ≠ ζ⁻¹ := fun h => h1 (by simpa using h.symm)
  have hζ3 : ζ ≠ ζ⁻¹ := by
    intro h
    apply h2
    calc ζ ^ 2 = ζ * ζ := by rw [pow_two]
      _ = ζ * ζ⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel ζ
  have e01 := apply_eq_zero_of_commute_diagU hcomm (i := 0) (j := 1) (by simpa [dvec4] using hζ1)
  have e02 := apply_eq_zero_of_commute_diagU hcomm (i := 0) (j := 2) (by simpa [dvec4] using hζ2)
  have e31 := apply_eq_zero_of_commute_diagU hcomm (i := 3) (j := 1) (by simpa [dvec4] using hζ1)
  have e32 := apply_eq_zero_of_commute_diagU hcomm (i := 3) (j := 2) (by simpa [dvec4] using hζ2)
  have e10 := apply_eq_zero_of_commute_diagU hcomm (i := 1) (j := 0)
    (by simpa [dvec4] using hζ1.symm)
  have e20 := apply_eq_zero_of_commute_diagU hcomm (i := 2) (j := 0)
    (by simpa [dvec4] using hζ2.symm)
  have e13 := apply_eq_zero_of_commute_diagU hcomm (i := 1) (j := 3)
    (by simpa [dvec4] using hζ1.symm)
  have e23 := apply_eq_zero_of_commute_diagU hcomm (i := 2) (j := 3)
    (by simpa [dvec4] using hζ2.symm)
  have e12 := apply_eq_zero_of_commute_diagU hcomm (i := 1) (j := 2) (by simpa [dvec4] using hζ3)
  have e21 := apply_eq_zero_of_commute_diagU hcomm (i := 2) (j := 1)
    (by simpa [dvec4] using hζ3.symm)
  have hgram := (mem_SU.1 g.2).2
  have g11 := congrFun (congrFun hgram 1) 2
  have g00 := congrFun (congrFun hgram 0) 0
  have g03 := congrFun (congrFun hgram 0) 3
  have g30 := congrFun (congrFun hgram 3) 0
  have g33 := congrFun (congrFun hgram 3) 3
  simp [conjTr, Matrix.mul_apply, Fin.sum_univ_four, antidiag, Fin.rev,
    Matrix.transpose_apply] at g11 g00 g03 g30 g33
  simp only [e10, e12, e13, e20, e21, e23, e01, e02, e31, e32, map_zero, mul_zero,
    add_zero, zero_add] at g11 g00 g03 g30 g33
  refine ⟨e01, e02, e31, e32, e10, e20, e13, e23, e12, e21, g11, ?_, ?_, ?_, ?_⟩
  · linear_combination g00
  · linear_combination g03
  · linear_combination g30
  · linear_combination g33

@[expose] noncomputable def phi5 {ζ : Kˣ} (hζ : σ (ζ : K) = ζ) (h1 : ζ ≠ 1) (h2 : ζ ^ 2 ≠ 1) :
    ↥(Subgroup.centralizer ({b5 σ ζ hζ} : Set ↥(SU σ 4))) →* Kˣ where
  toFun g := Units.mk0 (gu (g : ↥(SU σ 4)) 1 1) (fun h0 => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h11, -⟩ := centralizer_b5_facts σ hζ h1 h2 g.2
    rw [h0, map_zero, zero_mul] at h11
    exact zero_ne_one h11)
  map_one' := by
    apply Units.ext
    simp [gu_one]
  map_mul' g h := by
    apply Units.ext
    obtain ⟨-, -, -, -, h10, -, h13, -, h12, -, -, -⟩ := centralizer_b5_facts σ hζ h1 h2 g.2
    simp [Subgroup.coe_mul, gu_mul, Matrix.mul_apply, Fin.sum_univ_four, h10, h12, h13]

theorem phi5_apply {ζ : Kˣ} (hζ : σ (ζ : K) = ζ) (h1 : ζ ≠ 1) (h2 : ζ ^ 2 ≠ 1)
    (g : ↥(Subgroup.centralizer ({b5 σ ζ hζ} : Set ↥(SU σ 4)))) :
    ((phi5 σ hζ h1 h2 g : Kˣ) : K) = gu (g : ↥(SU σ 4)) 1 1 := rfl

@[expose] noncomputable def upU : (fixF σ)ˣ →* Kˣ := Units.map (fixF σ).subtype.toMonoidHom

theorem coe_upU (a : (fixF σ)ˣ) : ((upU σ a : Kˣ) : K) = ((a : fixF σ) : K) := rfl

theorem upU_injective : Function.Injective (upU σ) := by
  intro a b h
  apply Units.ext
  apply Subtype.val_injective
  exact congrArg (fun x : Kˣ => (x : K)) h

theorem σ_upU (a : (fixF σ)ˣ) : σ ((upU σ a : Kˣ) : K) = (upU σ a : Kˣ) := (a : fixF σ).2

@[expose] noncomputable def tr2Hom (k : Type) [Field k] :
    Multiplicative k →* SpecialLinearGroup (Fin 2) k where
  toFun c := tr2 (Multiplicative.toAdd c)
  map_one' := tr2_zero
  map_mul' _ _ := (tr2_mul _ _).symm

@[expose] noncomputable def diag2Hom (k : Type) [Field k] : kˣ →* SpecialLinearGroup (Fin 2) k where
  toFun := diag2
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diag2]
  map_mul' a b := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diag2, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem diag2Hom_apply {k : Type} [Field k] (a : kˣ) : diag2Hom k a = diag2 a := rfl

theorem liftSL_diag2 (a : (fixF σ)ˣ) :
    ((liftSL σ (diag2 a) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal ![((a : fixF σ) : K), (((a⁻¹ : (fixF σ)ˣ) : fixF σ) : K)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rw [coe_liftSL] <;> simp [diag2]

theorem liftSL_tr2 (c : fixF σ) :
    ((liftSL σ (tr2 c) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![1, (c : K); 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rw [coe_liftSL] <;> simp [tr2, Matrix.transvection]

theorem diag2Hom_injective (k : Type) [Field k] : Function.Injective (diag2Hom k) := by
  intro a b h
  have := congrArg (fun A : SpecialLinearGroup (Fin 2) k => (A : Matrix (Fin 2) (Fin 2) k) 0 0) h
  apply Units.ext
  simpa [diag2Hom, diag2] using this

theorem eq_one_of_inv_eq_self_two {k : Type} [Field k] [CharP k 2] {a : kˣ} (h : a⁻¹ = a) : a = 1 := by
  have h3 : a * a = 1 := by
    calc a * a = a * a⁻¹ := by rw [h]
      _ = 1 := mul_inv_cancel a
  have h4 : ((a : k) - 1) ^ 2 = 0 := by
    have : ((a : k) - 1) ^ 2 = (a : k) * a - 2 * a + 1 := by ring
    rw [this, ← Units.val_mul, h3, CharTwo.two_eq_zero, zero_mul, sub_zero, Units.val_one]
    exact CharTwo.add_self_eq_zero 1
  exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h4))

section CharTwo

variable [CharP K 2]

instance fixF_charP : CharP (fixF σ) 2 := inferInstance

theorem blk_conjTr_gram (X : Matrix (Fin 2) (Fin 2) K)
    (hX : X.det = 1) (hfix : ∀ i j, σ (X i j) = X i j) :
    conjTr σ (blk22 X) * antidiag 4 * blk22 X = antidiag 4 := by
  have hmap : X.map σ = X := by
    ext i j
    exact hfix i j
  have : conjTr σ (blk22 X) = (blk22 X)ᵀ := by
    rw [conjTr, map_blk σ (map_zero σ) (map_one σ), hmap]
  rw [this]
  exact blk22_gram X hX

@[expose] noncomputable def suBlock : SpecialLinearGroup (Fin 2) (fixF σ) →* ↥(SU σ 4) :=
  (blkGL.comp (liftSL σ)).codRestrict (SU σ 4) (fun A => by
    refine mem_SU.mpr ⟨?_, ?_⟩
    · show (blk22 ((liftSL σ A : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).det = 1
      rw [det_blk22]
      exact (liftSL σ A).2
    · show conjTr σ (blk22 ((liftSL σ A : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K)) * antidiag 4 *
          blk22 ((liftSL σ A : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
            antidiag 4
      exact blk_conjTr_gram σ _ (liftSL σ A).2 (fun i j => (A i j).2))

theorem coe_suBlock (A : SpecialLinearGroup (Fin 2) (fixF σ)) :
    (((suBlock σ A : ↥(SU σ 4)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      blk22 ((liftSL σ A : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem gu_suBlock (A : SpecialLinearGroup (Fin 2) (fixF σ)) :
    gu (suBlock σ A) =
      blk22 ((liftSL σ A : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem suBlock_injective : Function.Injective (suBlock σ) := by
  intro A B h
  apply liftSL_injective σ
  apply Subtype.ext
  have h1 := congrArg (fun g : ↥(SU σ 4) => gu g) h
  simp only [gu_suBlock] at h1
  exact blk22_injective h1

theorem suBlock_mem_centralizer {ζ : Kˣ} (hζ : σ (ζ : K) = ζ)
    (A : SpecialLinearGroup (Fin 2) (fixF σ)) :
    suBlock σ A ∈ Subgroup.centralizer ({b5 σ ζ hζ} : Set ↥(SU σ 4)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_suBlock, coe_b5, diagU_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk22, dvec4, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem ker_phi5 {ζ : Kˣ} (hζ : σ (ζ : K) = ζ) (h1 : ζ ≠ 1) (h2 : ζ ^ 2 ≠ 1) :
    (phi5 σ hζ h1 h2).ker =
      (suBlock σ).range.subgroupOf
        (Subgroup.centralizer ({b5 σ ζ hζ} : Set ↥(SU σ 4))) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  obtain ⟨e01, e02, e31, e32, e10, e20, e13, e23, e12, e21, h11, E00, E03, E30, E33⟩ :=
    centralizer_b5_facts σ hζ h1 h2 g.2
  constructor
  · intro h
    have h11' : gu (g : ↥(SU σ 4)) 1 1 = 1 := by
      have := congrArg (fun x : Kˣ => (x : K)) h
      rw [phi5_apply] at this
      simpa using this
    have h22 : gu (g : ↥(SU σ 4)) 2 2 = 1 := by
      rw [h11', map_one, one_mul] at h11
      exact h11
    have hgb : gu (g : ↥(SU σ 4)) = blk22 !![gu (g : ↥(SU σ 4)) 0 0, gu (g : ↥(SU σ 4)) 0 3;
        gu (g : ↥(SU σ 4)) 3 0, gu (g : ↥(SU σ 4)) 3 3] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [blk22, e01, e02, e31, e32, e10, e20, e13, e23, e12, e21, h11', h22]
    have hdet : (!![gu (g : ↥(SU σ 4)) 0 0, gu (g : ↥(SU σ 4)) 0 3;
        gu (g : ↥(SU σ 4)) 3 0, gu (g : ↥(SU σ 4)) 3 3] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
      have hd : (gu (g : ↥(SU σ 4))).det = 1 := (mem_SU.1 (g : ↥(SU σ 4)).2).1
      rw [hgb, det_blk22] at hd
      exact hd
    rw [Matrix.det_fin_two_of] at hdet
    set a := gu (g : ↥(SU σ 4)) 0 0 with ha_def
    set b := gu (g : ↥(SU σ 4)) 0 3 with hb_def
    set c := gu (g : ↥(SU σ 4)) 3 0 with hc_def
    set d := gu (g : ↥(SU σ 4)) 3 3 with hd_def
    have ha : σ a = a := by linear_combination (-σ a) * hdet + a * E03 - b * E00
    have hd' : σ d = d := by linear_combination (-σ d) * hdet + d * E30 - c * E33
    have hb : σ b = b := by
      have : σ b = -b := by linear_combination a * E33 - b * E30 - σ b * hdet
      rw [this, CharTwo.neg_eq]
    have hc : σ c = c := by
      have : σ c = -c := by linear_combination d * E00 - c * E03 - σ c * hdet
      rw [this, CharTwo.neg_eq]
    refine ⟨⟨!![⟨a, mem_fixF.2 ha⟩, ⟨b, mem_fixF.2 hb⟩; ⟨c, mem_fixF.2 hc⟩,
      ⟨d, mem_fixF.2 hd'⟩], ?_⟩, ?_⟩
    · apply Subtype.ext
      simpa [Matrix.det_fin_two_of] using hdet
    · apply Subtype.ext
      apply Units.ext
      show blk22 _ = gu (g : ↥(SU σ 4))
      rw [hgb]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
  · rintro ⟨A, hA⟩
    apply Units.ext
    rw [phi5_apply]
    have : gu (g : ↥(SU σ 4)) 1 1 = gu (suBlock σ A) 1 1 := by rw [hA]
    rw [this]
    show blk22 _ 1 1 = ((1 : Kˣ) : K)
    simp [blk22]

theorem perfectResidual_centralizer_b5 [Finite K] (hK : 4 ≤ Nat.card (fixF σ)) {ζ : Kˣ}
    (hζ : σ (ζ : K) = ζ) (h1 : ζ ≠ 1) (h2 : ζ ^ 2 ≠ 1) :
    inSubgroup perfectResidual (Subgroup.centralizer ({b5 σ ζ hζ} : Set ↥(SU σ 4))) =
      (suBlock σ).range := by
  have hq := CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (k := fixF σ) (m := 2)
    le_rfl hK
  have hperf : Group.IsPerfect ↥((suBlock σ).range) := by
    have := hq.1
    exact Group.IsPerfect.ofSurjective
      (f := (MonoidHom.ofInjective (suBlock_injective σ)).toMonoidHom)
      (MonoidHom.ofInjective (suBlock_injective σ)).surjective
  exact inSubgroup_perfectResidual_eq_of_ker (by
    rintro _ ⟨A, rfl⟩
    exact suBlock_mem_centralizer σ hζ A) hperf (phi5 σ hζ h1 h2) (ker_phi5 σ hζ h1 h2)

theorem isQuasisimple_perfectResidual_centralizer_b5 [Finite K] (hK : 4 ≤ Nat.card (fixF σ))
    {ζ : Kˣ} (hζ : σ (ζ : K) = ζ) (h1 : ζ ≠ 1) (h2 : ζ ^ 2 ≠ 1) :
    IsQuasisimple ↥(inSubgroup perfectResidual
      (Subgroup.centralizer ({b5 σ ζ hζ} : Set ↥(SU σ 4)))) := by
  rw [perfectResidual_centralizer_b5 σ hK hζ h1 h2]
  exact isQuasisimple_of_mulEquiv (MonoidHom.ofInjective (suBlock_injective σ))
    (CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (k := fixF σ) (m := 2) le_rfl hK)

theorem card_center_range_suBlock :
    Nat.card (Subgroup.center ↥((suBlock σ).range)) = 1 := by
  rw [← card_center_mulEquiv (MonoidHom.ofInjective (suBlock_injective σ))]
  exact card_center_SL_two

variable {σ}

@[expose] noncomputable def torus5 (σ : K ≃+* K) (p : ℕ) : Subgroup ↥(SU σ 4) :=
  (d8Tor p K 4).subgroupOf (SU σ 4)

omit [CharP K 2] in
theorem mem_torus5_iff {p : ℕ} {g : ↥(SU σ 4)} :
    g ∈ torus5 σ p ↔ ∃ a b : Kˣ, a ^ p = 1 ∧ b ^ p = 1 ∧
      ((g : GL (Fin 4) K)) = diagU (dvec4 a b) := by
  rw [torus5, Subgroup.mem_subgroupOf, mem_d8Tor_iff]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨(v.1 : rootsOfUnity p K), (v.2 : rootsOfUnity p K),
      (mem_rootsOfUnity p _).1 v.1.2, (mem_rootsOfUnity p _).1 v.2.2, ?_⟩
    rw [← hv, d8Vec_four]
  · rintro ⟨a, b, ha, hb, h⟩
    refine ⟨(⟨a, (mem_rootsOfUnity p _).2 ha⟩, ⟨b, (mem_rootsOfUnity p _).2 hb⟩), ?_⟩
    rw [h, d8Vec_four]

omit [CharP K 2] in
theorem torus5_pow_eq_one {p : ℕ} {g : ↥(SU σ 4)} (hg : g ∈ torus5 σ p) : g ^ p = 1 := by
  obtain ⟨a, b, ha, hb, hab⟩ := mem_torus5_iff.1 hg
  apply Subtype.ext
  show ((g : GL (Fin 4) K)) ^ p = 1
  rw [hab, diagU_pow]
  have : dvec4 a b ^ p = 1 := by
    funext i
    fin_cases i <;> simp [dvec4, inv_pow, ha, hb]
  rw [this, diagU_one]

omit [CharP K 2] in
theorem b5_mem_torus5 {p : ℕ} {ζ : Kˣ} (hζ : σ (ζ : K) = ζ) (hp : ζ ^ p = 1) :
    b5 σ ζ hζ ∈ torus5 σ p :=
  mem_torus5_iff.2 ⟨1, ζ, one_pow p, hp, rfl⟩

@[expose] noncomputable def rho5 (σ : K ≃+* K) : (fixF σ)ˣ →* ↥(SU σ 4) :=
  (suBlock σ).comp (diag2Hom (fixF σ))

theorem rho5_injective : Function.Injective (rho5 σ) :=
  (suBlock_injective σ).comp (diag2Hom_injective _)

theorem coe_rho5 (a : (fixF σ)ˣ) :
    ((rho5 σ a : ↥(SU σ 4)) : GL (Fin 4) K) = diagU (dvec4 (upU σ a) 1) := by
  have h : (((rho5 σ a : ↥(SU σ 4)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      blk22 ((liftSL σ (diag2 a) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := rfl
  apply Units.ext
  rw [h, liftSL_diag2, diagU_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk22, dvec4, upU]

theorem gu_rho5 (a : (fixF σ)ˣ) :
    gu (rho5 σ a) = Matrix.diagonal fun i => (dvec4 (upU σ a) 1 i : K) := by
  show (((rho5 σ a : ↥(SU σ 4)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = _
  rw [coe_rho5, diagU_val]

theorem rho5_mem_range (a : (fixF σ)ˣ) : (rho5 σ a : ↥(SU σ 4)) ∈ (suBlock σ).range :=
  ⟨diag2 a, rfl⟩

theorem rho5_mem_torus5 {p : ℕ} {a : (fixF σ)ˣ} (ha : a ^ p = 1) :
    (rho5 σ a : ↥(SU σ 4)) ∈ torus5 σ p :=
  mem_torus5_iff.2 ⟨upU σ a, 1, by rw [← map_pow, ha, map_one], one_pow p, coe_rho5 a⟩

theorem torus5_inf_range_eq (p : ℕ) :
    torus5 σ p ⊓ (suBlock σ).range = (rootsOfUnity p (fixF σ)).map (rho5 σ) := by
  ext g
  constructor
  · rintro ⟨hgT, A, hA⟩
    obtain ⟨a, b, ha, hb, hab⟩ := mem_torus5_iff.1 hgT
    obtain ⟨hσa, -⟩ := fix_of_diagU_mem_SU σ (hab ▸ g.2)
    have h11 : gu g 1 1 = 1 := by
      rw [← hA]
      show blk22 _ 1 1 = 1
      simp [blk22]
    have hb1 : b = 1 := by
      have h' : gu g 1 1 = (b : K) := by
        show ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 1 = _
        rw [hab, diagU_val]
        simp [dvec4]
      exact Units.ext (by rw [← h', h11]; rfl)
    let a' : (fixF σ)ˣ := Units.mk0 ⟨a, mem_fixF.2 hσa⟩ (fun h => a.ne_zero (congrArg Subtype.val h))
    have ha' : upU σ a' = a := Units.ext rfl
    have hapow : a' ^ p = 1 := by
      apply upU_injective σ
      rw [map_pow, ha', ha, map_one]
    refine ⟨a', (mem_rootsOfUnity p _).2 hapow, ?_⟩
    apply Subtype.ext
    rw [coe_rho5, ha', hab, hb1]
  · rintro ⟨a, ha, rfl⟩
    exact ⟨rho5_mem_torus5 ((mem_rootsOfUnity p _).1 ha), rho5_mem_range a⟩

theorem card_torus5_inf_range {p : ℕ} (hp : 0 < p)
    (hζ : ∃ ζ : (fixF σ)ˣ, IsPrimitiveRoot ζ p) :
    Nat.card ↥(torus5 σ p ⊓ (suBlock σ).range) = p := by
  have : NeZero p := ⟨hp.ne'⟩
  obtain ⟨ζ, hζ⟩ := hζ
  rw [torus5_inf_range_eq, Subgroup.card_map_of_injective rho5_injective]
  exact IsPrimitiveRoot.card_rootsOfUnity (IsPrimitiveRoot.coe_units_iff.mpr hζ)

@[expose] noncomputable def rootU5 (σ : K ≃+* K) : Subgroup ↥(SU σ 4) :=
  ((suBlock σ).comp (tr2Hom (fixF σ))).range

theorem mem_rootU5_iff {g : ↥(SU σ 4)} : g ∈ rootU5 σ ↔ ∃ c : fixF σ, g = suBlock σ (tr2 c) :=
  ⟨fun ⟨c, hc⟩ => ⟨Multiplicative.toAdd c, hc.symm⟩,
    fun ⟨c, hc⟩ => ⟨Multiplicative.ofAdd c, hc.symm⟩⟩

theorem suBlock_tr2_mem_rootU5 (c : fixF σ) : suBlock σ (tr2 c) ∈ rootU5 σ :=
  (mem_rootU5_iff).2 ⟨c, rfl⟩

theorem rootU5_le_range : rootU5 σ ≤ (suBlock σ).range := by
  intro g hg
  obtain ⟨c, rfl⟩ := (mem_rootU5_iff).1 hg
  exact ⟨tr2 c, rfl⟩

theorem isPGroup_rootU5 : IsPGroup 2 ↥(rootU5 σ) := by
  rw [IsPGroup.iff_orderOf]
  rintro ⟨g, hg⟩
  obtain ⟨c, rfl⟩ := (mem_rootU5_iff).1 hg
  have hsq : (suBlock σ (tr2 c) : ↥(SU σ 4)) ^ 2 = 1 := by
    rw [pow_two, ← map_mul, tr2_mul, CharTwo.add_self_eq_zero, tr2_zero, map_one]
  have hdvd : orderOf (⟨suBlock σ (tr2 c), hg⟩ : ↥(rootU5 σ)) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa using hsq
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact ⟨0, by simpa using h⟩
  · exact ⟨1, by simpa using h⟩

theorem torus5_conj_rootU5 {p : ℕ} {g : ↥(SU σ 4)} (hg : g ∈ torus5 σ p) :
    ∀ x ∈ rootU5 σ, g * x * g⁻¹ ∈ rootU5 σ := by
  intro x hx
  obtain ⟨c, rfl⟩ := (mem_rootU5_iff).1 hx
  obtain ⟨a, b, -, -, hab⟩ := mem_torus5_iff.1 hg
  obtain ⟨hσa, -⟩ := fix_of_diagU_mem_SU σ (hab ▸ g.2)
  let a' : fixF σ := ⟨a, mem_fixF.2 hσa⟩
  have h : g * suBlock σ (tr2 c) = suBlock σ (tr2 (a' * c * a')) * g := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, coe_suBlock, hab, diagU_val, liftSL_tr2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blk22, dvec4, a', Matrix.mul_diagonal, Matrix.diagonal_mul]
  have : g * suBlock σ (tr2 c) * g⁻¹ = suBlock σ (tr2 (a' * c * a')) := by
    rw [h, mul_inv_cancel_right]
  rw [this]
  exact suBlock_tr2_mem_rootU5 _

theorem torus5_le_normalizer_rootU5 {p : ℕ} :
    torus5 σ p ≤ Subgroup.normalizer (rootU5 σ : Set ↥(SU σ 4)) := fun g hg =>
  mem_normalizer_of_conj_mem (torus5_conj_rootU5 hg) (fun y hy => by
    have := torus5_conj_rootU5 ((torus5 σ p).inv_mem hg) y hy
    simpa using this)

theorem suBlock_tr2_one_not_commute_rho5 {a : (fixF σ)ˣ} (ha : a ≠ 1) :
    (suBlock σ (tr2 (1 : fixF σ)) : ↥(SU σ 4)) * rho5 σ a ≠
      rho5 σ a * suBlock σ (tr2 (1 : fixF σ)) := by
  intro h
  have h1 := congrArg (fun x : ↥(SU σ 4) => gu x 0 3) h
  have e00 : gu (suBlock σ (tr2 (1 : fixF σ))) 0 0 = 1 := by
    rw [gu_suBlock, liftSL_tr2]
    simp [blk22]
  have e01 : gu (suBlock σ (tr2 (1 : fixF σ))) 0 1 = 0 := by
    rw [gu_suBlock, liftSL_tr2]
    simp [blk22]
  have e02 : gu (suBlock σ (tr2 (1 : fixF σ))) 0 2 = 0 := by
    rw [gu_suBlock, liftSL_tr2]
    simp [blk22]
  have e03 : gu (suBlock σ (tr2 (1 : fixF σ))) 0 3 = 1 := by
    rw [gu_suBlock, liftSL_tr2]
    simp [blk22]
  simp [gu_mul, gu_rho5, Matrix.mul_apply, Fin.sum_univ_four, dvec4, e00, e01, e02, e03] at h1
  have h2 : (a⁻¹ : (fixF σ)ˣ) = a := by
    apply upU_injective σ
    apply Units.ext
    rw [map_inv, Units.val_inv_eq_inv_val]
    exact h1
  exact ha (eq_one_of_inv_eq_self_two h2)

end CharTwo

end CFSG.RankThree.PartOne.KFU
