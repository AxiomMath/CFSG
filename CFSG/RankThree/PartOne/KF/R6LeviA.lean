module

public import CFSG.RankThree.PartOne.KF.R6Levi
public import CFSG.RankThree.PartOne.KFOUT3.KtySUSmall
public import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.RankThree.PartOne.KFU

open Matrix CFSG CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits

variable {K : Type} [Field K]

@[expose] def eSum5 : Fin 3 ⊕ Fin 2 ≃ Fin 5 where
  toFun := Sum.elim ![0, 2, 4] ![1, 3]
  invFun := ![Sum.inl 0, Sum.inr 0, Sum.inl 1, Sum.inr 1, Sum.inl 2]
  left_inv := by decide
  right_inv := by decide

@[expose] def embBlock35 (a : Matrix (Fin 3) (Fin 3) K) (b : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 5) (Fin 5) K :=
  (Matrix.fromBlocks a 0 0 b).submatrix eSum5.symm eSum5.symm

@[expose] def embMat35 (h : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 5) (Fin 5) K :=
  embBlock35 h 1

theorem embMat35_apply (h : Matrix (Fin 3) (Fin 3) K) (i j : Fin 5) :
    embMat35 h i j = Matrix.fromBlocks h 0 0 1 (eSum5.symm i) (eSum5.symm j) := rfl

@[simp] theorem eSum5_symm_zero : eSum5.symm 0 = Sum.inl 0 := rfl
@[simp] theorem eSum5_symm_one : eSum5.symm 1 = Sum.inr 0 := rfl
@[simp] theorem eSum5_symm_two : eSum5.symm 2 = Sum.inl 1 := rfl
@[simp] theorem eSum5_symm_three : eSum5.symm 3 = Sum.inr 1 := rfl
@[simp] theorem eSum5_symm_four : eSum5.symm 4 = Sum.inl 2 := rfl

theorem embBlock35_mul (a a' : Matrix (Fin 3) (Fin 3) K) (b b' : Matrix (Fin 2) (Fin 2) K) :
    embBlock35 a b * embBlock35 a' b' = embBlock35 (a * a') (b * b') := by
  unfold embBlock35
  rw [Matrix.submatrix_mul_equiv _ _ eSum5.symm eSum5.symm eSum5.symm, Matrix.fromBlocks_multiply]
  simp

theorem embMat35_mul (h h' : Matrix (Fin 3) (Fin 3) K) : embMat35 (h * h') = embMat35 h * embMat35 h' := by
  unfold embMat35
  rw [embBlock35_mul, mul_one]

theorem embMat35_one : embMat35 (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  unfold embMat35 embBlock35
  rw [Matrix.fromBlocks_one]
  exact Matrix.submatrix_one_equiv eSum5.symm

theorem det_embBlock35 (a : Matrix (Fin 3) (Fin 3) K) (b : Matrix (Fin 2) (Fin 2) K) :
    (embBlock35 a b).det = a.det * b.det := by
  unfold embBlock35
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]

theorem det_embMat35 (h : Matrix (Fin 3) (Fin 3) K) : (embMat35 h).det = h.det := by
  unfold embMat35
  rw [det_embBlock35, Matrix.det_one, mul_one]

theorem conjTr_embBlock35 (σ : K ≃+* K) (a : Matrix (Fin 3) (Fin 3) K) (b : Matrix (Fin 2) (Fin 2) K) :
    conjTr σ (embBlock35 a b) = embBlock35 (conjTr σ a) (conjTr σ b) := by
  unfold conjTr embBlock35
  rw [← Matrix.submatrix_map, Matrix.transpose_submatrix, Matrix.fromBlocks_map,
    Matrix.fromBlocks_transpose]
  simp

theorem conjTr_embMat35 (σ : K ≃+* K) (h : Matrix (Fin 3) (Fin 3) K) :
    conjTr σ (embMat35 h) = embBlock35 (conjTr σ h) 1 := by
  unfold embMat35
  rw [conjTr_embBlock35]
  congr 1
  unfold conjTr
  rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]

theorem antidiag_five : (antidiag 5 : Matrix (Fin 5) (Fin 5) K) =
    embBlock35 (antidiag 3 : Matrix (Fin 3) (Fin 3) K) (antidiag 2 : Matrix (Fin 2) (Fin 2) K) := by
  unfold embBlock35
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antidiag, eSum5, Fin.rev]

theorem embMat35_gram (σ : K ≃+* K) {h : Matrix (Fin 3) (Fin 3) K}
    (hg : conjTr σ h * antidiag 3 * h = antidiag 3) :
    conjTr σ (embMat35 h) * antidiag 5 * embMat35 h = antidiag 5 := by
  rw [conjTr_embMat35, antidiag_five]
  unfold embMat35
  rw [embBlock35_mul, embBlock35_mul, hg, one_mul, mul_one]

theorem embMat35_injective : Function.Injective (embMat35 : Matrix (Fin 3) (Fin 3) K → _) := by
  intro h h' H
  ext a b
  have := congrFun (congrFun H (eSum5 (Sum.inl a))) (eSum5 (Sum.inl b))
  simpa [embMat35, embBlock35] using this

@[expose] noncomputable def embGL35 : GL (Fin 3) K →* GL (Fin 5) K where
  toFun g :=
    { val := embMat35 (g : Matrix (Fin 3) (Fin 3) K)
      inv := embMat35 ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      val_inv := by rw [← embMat35_mul, Units.mul_inv, embMat35_one]
      inv_val := by rw [← embMat35_mul, Units.inv_mul, embMat35_one] }
  map_one' := by
    apply Units.ext
    simp [embMat35_one]
  map_mul' g h := by
    apply Units.ext
    simp [embMat35_mul]

variable (σ : K ≃+* K)

@[expose] noncomputable def su3Emb : ↥(SU σ 3) →* ↥(SU σ 5) :=
  (embGL35.comp (SU σ 3).subtype).codRestrict (SU σ 5) (fun g => by
    obtain ⟨hdet, hgram⟩ := mem_SU.1 g.2
    refine mem_SU.mpr ⟨?_, ?_⟩
    · show (embMat35 ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).det = 1
      rw [det_embMat35]
      exact hdet
    · show conjTr σ (embMat35 ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) * antidiag 5 *
        embMat35 ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = antidiag 5
      exact embMat35_gram σ hgram)

theorem gu5_su3Emb (g : ↥(SU σ 3)) :
    gu5 (su3Emb σ g) = embMat35 ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := rfl

theorem su3Emb_injective : Function.Injective (su3Emb σ) := by
  intro g g' H
  apply Subtype.ext
  apply Units.ext
  apply embMat35_injective
  have := congrArg (fun x : ↥(SU σ 5) => gu5 x) H
  simpa only [gu5_su3Emb] using this

@[expose] noncomputable def bA6 (ζ : Kˣ) (hζ : σ (ζ : K) = ζ) : ↥(SU σ 5) :=
  ⟨diagU (dvec5 1 ζ), diagU_dvec5_mem_SU σ (by simp) hζ⟩

theorem coe_bA6 (ζ : Kˣ) (hζ : σ (ζ : K) = ζ) :
    ((bA6 σ ζ hζ : ↥(SU σ 5)) : GL (Fin 5) K) = diagU (dvec5 1 ζ) := rfl

theorem centralizer_bA6_facts {ζ : Kˣ} (hζ : σ (ζ : K) = ζ) (h1 : ζ ≠ 1) (h2 : ζ ^ 2 ≠ 1)
    {g : ↥(SU σ 5)} (hg : g ∈ Subgroup.centralizer ({bA6 σ ζ hζ} : Set ↥(SU σ 5))) :
    gu5 g 0 1 = 0 ∧ gu5 g 0 3 = 0 ∧ gu5 g 1 0 = 0 ∧ gu5 g 1 2 = 0 ∧ gu5 g 1 3 = 0 ∧
      gu5 g 1 4 = 0 ∧ gu5 g 2 1 = 0 ∧ gu5 g 2 3 = 0 ∧ gu5 g 3 0 = 0 ∧ gu5 g 3 1 = 0 ∧
      gu5 g 3 2 = 0 ∧ gu5 g 3 4 = 0 ∧ gu5 g 4 1 = 0 ∧ gu5 g 4 3 = 0 ∧
      σ (gu5 g 1 1) * gu5 g 3 3 = 1 := by
  have hcomm : (g : GL (Fin 5) K) * diagU (dvec5 1 ζ) = diagU (dvec5 1 ζ) * (g : GL (Fin 5) K) :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hg)
  have hζ1 : (1 : Kˣ) ≠ ζ := fun h => h1 h.symm
  have hζ2 : (1 : Kˣ) ≠ ζ⁻¹ := fun h => h1 (by simpa using h.symm)
  have hζ3 : ζ ≠ ζ⁻¹ := by
    intro h
    apply h2
    calc ζ ^ 2 = ζ * ζ := by rw [pow_two]
      _ = ζ * ζ⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel ζ
  have hne : ∀ i j : Fin 5, dvec5 1 ζ i ≠ dvec5 1 ζ j → gu5 g i j = 0 := fun i j h =>
    apply_eq_zero_of_commute_diagU hcomm h
  have e01 := hne 0 1 (by simpa [dvec5] using hζ1)
  have e03 := hne 0 3 (by simpa [dvec5] using hζ2)
  have e10 := hne 1 0 (by simpa [dvec5] using hζ1.symm)
  have e12 := hne 1 2 (by simpa [dvec5] using hζ1.symm)
  have e13 := hne 1 3 (by simpa [dvec5] using hζ3)
  have e14 := hne 1 4 (by simpa [dvec5] using hζ1.symm)
  have e21 := hne 2 1 (by simpa [dvec5] using hζ1)
  have e23 := hne 2 3 (by simpa [dvec5] using hζ2)
  have e30 := hne 3 0 (by simpa [dvec5] using hζ2.symm)
  have e31 := hne 3 1 (by simpa [dvec5] using hζ3.symm)
  have e32 := hne 3 2 (by simpa [dvec5] using hζ2.symm)
  have e34 := hne 3 4 (by simpa [dvec5] using hζ2.symm)
  have e41 := hne 4 1 (by simpa [dvec5] using hζ1)
  have e43 := hne 4 3 (by simpa [dvec5] using hζ2)
  have hgram := (mem_SU.1 g.2).2
  have g13 := congrFun (congrFun hgram 1) 3
  simp [conjTr, Matrix.mul_apply, Fin.sum_univ_five, antidiag, Fin.rev,
    Matrix.transpose_apply] at g13
  simp only [e01, e21, e31, e41, map_zero, zero_mul, add_zero, zero_add] at g13
  exact ⟨e01, e03, e10, e12, e13, e14, e21, e23, e30, e31, e32, e34, e41, e43, g13⟩

@[expose] noncomputable def phiA6 {ζ : Kˣ} (hζ : σ (ζ : K) = ζ) (h1 : ζ ≠ 1) (h2 : ζ ^ 2 ≠ 1) :
    ↥(Subgroup.centralizer ({bA6 σ ζ hζ} : Set ↥(SU σ 5))) →* Kˣ where
  toFun g :=
    Units.mk0 (gu5 (g : ↥(SU σ 5)) 1 1) (fun h0 => by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hgram⟩ :=
        centralizer_bA6_facts σ hζ h1 h2 g.2
      rw [h0, map_zero, zero_mul] at hgram
      exact zero_ne_one hgram)
  map_one' := Units.ext (by simp [gu5_one])
  map_mul' g h := by
    obtain ⟨-, -, e10, e12, e13, e14, -⟩ := centralizer_bA6_facts σ hζ h1 h2 g.2
    apply Units.ext
    show gu5 ((g : ↥(SU σ 5)) * (h : ↥(SU σ 5))) 1 1 =
      gu5 (g : ↥(SU σ 5)) 1 1 * gu5 (h : ↥(SU σ 5)) 1 1
    simp [gu5_mul, Matrix.mul_apply, Fin.sum_univ_five, e10, e12, e13, e14]

theorem phiA6_coe {ζ : Kˣ} (hζ : σ (ζ : K) = ζ) (h1 : ζ ≠ 1) (h2 : ζ ^ 2 ≠ 1)
    (g : ↥(Subgroup.centralizer ({bA6 σ ζ hζ} : Set ↥(SU σ 5)))) :
    (((phiA6 σ hζ h1 h2 g : Kˣ)) : K) = gu5 (g : ↥(SU σ 5)) 1 1 := rfl

@[expose] noncomputable def mkSU3 (h : Matrix (Fin 3) (Fin 3) K) (hdet : h.det = 1)
    (hg : conjTr σ h * antidiag 3 * h = antidiag 3) : ↥(SU σ 3) :=
  ⟨Matrix.GeneralLinearGroup.mk'' h (by rw [hdet]; exact isUnit_one), mem_SU.mpr ⟨hdet, hg⟩⟩

theorem embMat35_comm_diag (ζ : Kˣ) (h : Matrix (Fin 3) (Fin 3) K) :
    embMat35 h * Matrix.diagonal (fun i => ((dvec5 1 ζ i : Kˣ) : K)) =
      Matrix.diagonal (fun i => ((dvec5 1 ζ i : Kˣ) : K)) * embMat35 h := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [embMat35_apply, dvec5, mul_comm]

theorem su3Emb_mem_centralizer {ζ : Kˣ} (hζ : σ (ζ : K) = ζ) (u : ↥(SU σ 3)) :
    su3Emb σ u ∈ Subgroup.centralizer ({bA6 σ ζ hζ} : Set ↥(SU σ 5)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_bA6, diagU_val]
  exact embMat35_comm_diag ζ ((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

open CFSG.RankThree.PartOne.KFOUT3 in
theorem ker_phiA6 {ζ : Kˣ} (hζ : σ (ζ : K) = ζ) (h1 : ζ ≠ 1) (h2 : ζ ^ 2 ≠ 1) :
    (phiA6 σ hζ h1 h2).ker =
      (su3Emb σ).range.subgroupOf (Subgroup.centralizer ({bA6 σ ζ hζ} : Set ↥(SU σ 5))) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  obtain ⟨e01, e03, e10, e12, e13, e14, e21, e23, e30, e31, e32, e34, e41, e43, hgr⟩ :=
    centralizer_bA6_facts σ hζ h1 h2 g.2
  constructor
  · intro h
    have hu : gu5 (g : ↥(SU σ 5)) 1 1 = 1 := by
      have := congrArg (fun x : Kˣ => ((x : Kˣ) : K)) h
      rw [phiA6_coe] at this
      simpa using this
    have hv : gu5 (g : ↥(SU σ 5)) 3 3 = 1 := by
      rw [hu, map_one, one_mul] at hgr
      exact hgr
    set m : Matrix (Fin 3) (Fin 3) K :=
      (gu5 (g : ↥(SU σ 5))).submatrix ![0, 2, 4] ![0, 2, 4] with hm
    have hm_apply : ∀ a b : Fin 3, m a b = gu5 (g : ↥(SU σ 5)) ((![0, 2, 4] : Fin 3 → Fin 5) a)
        ((![0, 2, 4] : Fin 3 → Fin 5) b) := fun a b => rfl
    have hgb : gu5 (g : ↥(SU σ 5)) = embMat35 m := by
      ext a b
      rw [embMat35_apply]
      fin_cases a <;> fin_cases b <;>
        simp [hm_apply, e01, e03, e10, e12, e13, e14, e21, e23, e30, e31, e32, e34,
          e41, e43, hu, hv]
    have hdet : m.det = 1 := by
      have h0 := (mem_SU.1 (g : ↥(SU σ 5)).2).1
      rw [show (((g : ↥(SU σ 5)) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = embMat35 m from hgb,
        det_embMat35] at h0
      exact h0
    have hcol : ∀ (a : Fin 3) (l : Fin 5), l ∉ Set.range (![0, 2, 4] : Fin 3 → Fin 5) →
        gu5 (g : ↥(SU σ 5)) l ((![0, 2, 4] : Fin 3 → Fin 5) a) = 0 := by
      intro a l hl
      have key : ∀ l : Fin 5, (∃ a : Fin 3, (![0, 2, 4] : Fin 3 → Fin 5) a = l) ∨ l = 1 ∨ l = 3 := by
        decide
      rcases key l with ⟨a', ha'⟩ | rfl | rfl
      · exact absurd ⟨a', ha'⟩ hl
      · fin_cases a <;> simp [e10, e12, e14]
      · fin_cases a <;> simp [e30, e32, e34]
    have hgm : conjTr σ m * antidiag 3 * m = antidiag 3 := by
      have := gram_block σ (![0, 2, 4] : Fin 3 → Fin 5) eig_inj_five eig_rev_five
        (m := gu5 (g : ↥(SU σ 5))) (fun a l hl => hcol a l hl) (mem_SU.1 (g : ↥(SU σ 5)).2).2
      simpa [hm] using this
    refine ⟨mkSU3 σ m hdet hgm, ?_⟩
    apply Subtype.ext
    apply Units.ext
    exact hgb.symm
  · rintro ⟨u, hu⟩
    apply Units.ext
    rw [phiA6_coe, ← hu]
    show embMat35 _ 1 1 = _
    simp [embMat35_apply]

section Perfect

variable [Finite K] [CharP K 2] {f : ℕ}

theorem three_pair_ne {f : ℕ} (hf : 2 ≤ f) : ((3 : ℕ), 2 ^ f) ≠ (3, 2) := by
  intro h
  have h2 : 2 ^ f = 2 ^ 1 := congrArg Prod.snd h
  have := Nat.pow_right_injective (le_refl 2) h2
  omega

theorem isQuasisimple_SU_three (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) :
    IsQuasisimple ↥(SU (unitaryInvolution K 2 f) 3) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isQuasisimple_SU hK le_rfl (three_pair_ne hf)

theorem perfectResidual_centralizer_bA6 (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 f (ζ : K) = ζ) (h1 : ζ ≠ 1) (h2 : ζ ^ 2 ≠ 1) :
    inSubgroup perfectResidual (Subgroup.centralizer
      ({bA6 (unitaryInvolution K 2 f) ζ hζ} : Set ↥(SU (unitaryInvolution K 2 f) 5))) =
      (su3Emb (unitaryInvolution K 2 f)).range := by
  have hq := isQuasisimple_SU_three hK hf
  have hperf : Group.IsPerfect ↥((su3Emb (unitaryInvolution K 2 f)).range) := by
    have := hq.1
    exact Group.IsPerfect.ofSurjective
      (f := (MonoidHom.ofInjective (su3Emb_injective (unitaryInvolution K 2 f))).toMonoidHom)
      (MonoidHom.ofInjective (su3Emb_injective (unitaryInvolution K 2 f))).surjective
  exact inSubgroup_perfectResidual_eq_of_ker (by
    rintro _ ⟨u, rfl⟩
    exact su3Emb_mem_centralizer _ hζ u) hperf (phiA6 _ hζ h1 h2) (ker_phiA6 _ hζ h1 h2)

theorem isQuasisimple_perfectResidual_centralizer_bA6 (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f)
    {ζ : Kˣ} (hζ : unitaryInvolution K 2 f (ζ : K) = ζ) (h1 : ζ ≠ 1) (h2 : ζ ^ 2 ≠ 1) :
    IsQuasisimple ↥(inSubgroup perfectResidual (Subgroup.centralizer
      ({bA6 (unitaryInvolution K 2 f) ζ hζ} : Set ↥(SU (unitaryInvolution K 2 f) 5)))) := by
  rw [perfectResidual_centralizer_bA6 hK hf hζ h1 h2]
  exact isQuasisimple_of_mulEquiv (MonoidHom.ofInjective (su3Emb_injective _))
    (isQuasisimple_SU_three hK hf)

theorem card_center_SU_three (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) :
    Nat.card (Subgroup.center ↥(SU (unitaryInvolution K 2 f) 3)) = Nat.gcd 3 (2 ^ f + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [card_center_mulEquiv (equivStatedSU hK 3),
    (isQuasisimple_statedSU_of_card hK (n := 3) le_rfl (three_pair_ne hf)).2]
  exact (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (n := 3) (by norm_num)).2.2

theorem not_dvd_card_center_range_su3Emb (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) {p : ℕ}
    (hp3 : 3 < p) :
    ¬ p ∣ Nat.card (Subgroup.center ↥((su3Emb (unitaryInvolution K 2 f)).range)) := by
  rw [← card_center_mulEquiv (MonoidHom.ofInjective (su3Emb_injective (unitaryInvolution K 2 f))),
    card_center_SU_three hK hf]
  intro h
  have h3 : p ∣ 3 := h.trans (Nat.gcd_dvd_left 3 _)
  have := Nat.le_of_dvd (by norm_num) h3
  omega

theorem statedModel_SU_three (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) :
    StatedClassicalModel (↥(SU (unitaryInvolution K 2 f) 3) ⧸
      Subgroup.center ↥(SU (unitaryInvolution K 2 f) 3)) .PSU 3 2 f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact statedClassicalModel_center_quotient ⟨Nat.prime_two, by omega, le_rfl, three_pair_ne hf⟩ hK

end Perfect

section Torus

variable {σ} {p : ℕ}

theorem diagU_three_mem_SU {a : Kˣ} (ha : σ (a : K) = a) :
    (diagU (![a, 1, a⁻¹] : Fin 3 → Kˣ) : GL (Fin 3) K) ∈ SU σ 3 := by
  refine mem_SU.mpr ⟨?_, diagU_gram σ (fun i => ?_)⟩
  · rw [det_diagU, ← Units.coe_prod]
    simp [Fin.prod_univ_three]
  · fin_cases i <;> simp [ha, Fin.rev, map_inv₀]

@[expose] noncomputable def rhoSU3 (hfix : ∀ u : Kˣ, u ^ p = 1 → σ (u : K) = u) :
    ↥(rootsOfUnity p K) →* ↥(SU σ 5) where
  toFun u :=
    ⟨diagU (dvec5 (u : Kˣ) 1),
      diagU_dvec5_mem_SU σ (hfix _ ((mem_rootsOfUnity p _).1 u.2)) (by simp)⟩
  map_one' := by
    apply Subtype.ext
    have : dvec5 ((1 : ↥(rootsOfUnity p K)) : Kˣ) 1 = 1 := by
      funext i
      fin_cases i <;> simp [dvec5]
    show diagU (dvec5 ((1 : ↥(rootsOfUnity p K)) : Kˣ) 1) = 1
    rw [this, diagU_one]
  map_mul' u v := by
    apply Subtype.ext
    show diagU (dvec5 ((u * v : ↥(rootsOfUnity p K)) : Kˣ) 1) =
      diagU (dvec5 (u : Kˣ) 1) * diagU (dvec5 (v : Kˣ) 1)
    rw [diagU_mul]
    congr 1
    funext i
    fin_cases i <;> simp [dvec5, Pi.mul_apply, mul_comm]

theorem rhoSU3_injective (hfix : ∀ u : Kˣ, u ^ p = 1 → σ (u : K) = u) :
    Function.Injective (rhoSU3 (σ := σ) (p := p) hfix) := by
  intro u v h
  have h1 := congrArg (fun g : ↥(SU σ 5) => gu5 g 0 0) h
  simp [rhoSU3, gu5, diagU_val, dvec5] at h1
  exact Subtype.ext (Units.ext h1)

theorem torus6_inf_range_su3_eq (hfix : ∀ u : Kˣ, u ^ p = 1 → σ (u : K) = u) :
    torus6 σ p ⊓ (su3Emb σ).range = (rhoSU3 hfix).range := by
  ext g
  constructor
  · rintro ⟨hgT, u, hu⟩
    obtain ⟨a, b, ha, hb, hab⟩ := mem_torus6_iff.1 hgT
    have hb1 : b = 1 := by
      have h1 : gu5 g 1 1 = (b : K) := by
        show ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 1 1 = _
        rw [hab]
        simp [diagU_val, dvec5]
      have h2 : gu5 g 1 1 = 1 := by
        rw [← hu]
        show embMat35 _ 1 1 = 1
        simp [embMat35_apply]
      exact Units.ext (by rw [← h1, h2]; rfl)
    subst hb1
    refine ⟨⟨a, (mem_rootsOfUnity p _).2 ha⟩, ?_⟩
    apply Subtype.ext
    exact hab.symm
  · rintro ⟨u, rfl⟩
    have hu : (u : Kˣ) ^ p = 1 := (mem_rootsOfUnity p _).1 u.2
    refine ⟨mem_torus6_iff.2 ⟨u, 1, hu, one_pow p, rfl⟩, ?_⟩
    refine ⟨⟨diagU (![(u : Kˣ), 1, (u : Kˣ)⁻¹] : Fin 3 → Kˣ),
      diagU_three_mem_SU (hfix _ hu)⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    show embMat35 (Matrix.diagonal fun i => ((![(u : Kˣ), 1, (u : Kˣ)⁻¹] i : Kˣ) : K)) =
      Matrix.diagonal fun i => ((dvec5 (u : Kˣ) 1 i : Kˣ) : K)
    ext i j
    rw [embMat35_apply]
    fin_cases i <;> fin_cases j <;> simp [dvec5]

theorem card_torus6_inf_range_su3 (hp : 0 < p) (hfix : ∀ u : Kˣ, u ^ p = 1 → σ (u : K) = u)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    Nat.card ↥(torus6 σ p ⊓ (su3Emb σ).range) = p := by
  have : NeZero p := ⟨hp.ne'⟩
  obtain ⟨ζ, hζ⟩ := hζ
  rw [torus6_inf_range_su3_eq hfix,
    Nat.card_congr (MonoidHom.ofInjective (rhoSU3_injective hfix)).toEquiv.symm]
  exact IsPrimitiveRoot.card_rootsOfUnity (IsPrimitiveRoot.coe_units_iff.mpr hζ)

end Torus

end CFSG.RankThree.PartOne.KFU
