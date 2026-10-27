module

public import CFSG.Quasithin.EmptyFaithful.A38c17Defs
public import CFSG.LieType.Universal.Unitary.Comparison

public section

namespace CFSG.Quasithin.A38c17

open Matrix CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank

section General

variable {F : Type*} [Field F]

@[expose] def blockDiag3 (A : Matrix (Fin 2) (Fin 2) F) (d : F) : Matrix (Fin 3) (Fin 3) F :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, d]

theorem blockDiag3_mul (A B : Matrix (Fin 2) (Fin 2) F) (d e : F) :
    blockDiag3 A d * blockDiag3 B e = blockDiag3 (A * B) (d * e) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockDiag3, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem blockDiag3_one : blockDiag3 (1 : Matrix (Fin 2) (Fin 2) F) 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockDiag3]

theorem det_blockDiag3 (A : Matrix (Fin 2) (Fin 2) F) (d : F) :
    (blockDiag3 A d).det = A.det * d := by
  simp [blockDiag3, Matrix.det_fin_three, Matrix.det_fin_two]
  ring

theorem conjTr_blockDiag3 {σ : F ≃+* F} (A : Matrix (Fin 2) (Fin 2) F) (d : F) :
    conjTr σ (blockDiag3 A d) = blockDiag3 (conjTr σ A) (σ d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockDiag3, conjTr]

theorem blockDiag3_inj {A B : Matrix (Fin 2) (Fin 2) F} {d e : F}
    (h : blockDiag3 A d = blockDiag3 B e) : A = B ∧ d = e := by
  have h' := fun i j => congrFun (congrFun h i) j
  refine ⟨?_, by simpa [blockDiag3] using h' 2 2⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [blockDiag3] using h' 0 0
  · simpa [blockDiag3] using h' 0 1
  · simpa [blockDiag3] using h' 1 0
  · simpa [blockDiag3] using h' 1 1

@[expose] def gram3 (c : F) : Matrix (Fin 3) (Fin 3) F := blockDiag3 (antidiag 2) c

theorem gram3_eq (c : F) : gram3 c = !![0, 1, 0; 1, 0, 0; 0, 0, c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gram3, blockDiag3, antidiag]

theorem det_gram3 (c : F) : (gram3 c).det = -c := by
  simp [gram3_eq, Matrix.det_fin_three]

@[expose] noncomputable def levi3Hom :
    Matrix (Fin 2) (Fin 2) F →* Matrix (Fin 3) (Fin 3) F where
  toFun A := blockDiag3 A (A.det)⁻¹
  map_one' := by simp [blockDiag3_one]
  map_mul' A B := by rw [blockDiag3_mul, det_mul, mul_inv]

theorem levi3Hom_apply (A : Matrix (Fin 2) (Fin 2) F) :
    levi3Hom A = blockDiag3 A (A.det)⁻¹ := rfl

variable {σ : F ≃+* F}

theorem levi3_det_conjTr {n : ℕ} (A : Matrix (Fin n) (Fin n) F) :
    (conjTr σ A).det = σ A.det := by
  rw [conjTr, Matrix.det_transpose]
  exact (RingHom.map_det (σ : F →+* F) A).symm

theorem levi3_norm_det {A : Matrix (Fin 2) (Fin 2) F}
    (hA : conjTr σ A * antidiag 2 * A = antidiag 2) : σ A.det * A.det = 1 := by
  have h := congrArg Matrix.det hA
  rw [det_mul, det_mul, levi3_det_conjTr] at h
  apply mul_left_cancel₀ (det_antidiag_ne_zero (F := F) 2)
  linear_combination h

theorem levi3_conjTr_gram3 (c : F) {A : Matrix (Fin 2) (Fin 2) F}
    (hA : conjTr σ A * antidiag 2 * A = antidiag 2) :
    conjTr σ (levi3Hom A) * gram3 c * levi3Hom A = gram3 c := by
  have hn := levi3_norm_det hA
  have ha : A.det ≠ 0 := right_ne_zero_of_mul_eq_one hn
  have hsa : σ A.det ≠ 0 := left_ne_zero_of_mul_eq_one hn
  rw [levi3Hom_apply, gram3, conjTr_blockDiag3, blockDiag3_mul, blockDiag3_mul, hA]
  congr 1
  rw [map_inv₀]
  field_simp
  linear_combination (-c) * hn

theorem det_ne_zero_of_gram3 {c : F} (hc : c ≠ 0) {Q : Matrix (Fin 3) (Fin 3) F}
    (hQ : conjTr σ Q * Q = gram3 c) : Q.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det hQ
  rw [det_mul, levi3_det_conjTr, h, mul_zero, det_gram3] at this
  exact hc (neg_eq_zero.mp this.symm)

theorem levi3_conjTr_inv_gram3 {c : F} {Q Qi : Matrix (Fin 3) (Fin 3) F} (hQQi : Q * Qi = 1)
    (hQ : conjTr σ Q * Q = gram3 c) : conjTr σ Qi * gram3 c * Qi = 1 := by
  have e : conjTr σ Qi * (conjTr σ Q * Q) * Qi = conjTr σ (Q * Qi) * (Q * Qi) := by
    simp only [conjTr_mul, Matrix.mul_assoc]
  rw [← hQ, e, hQQi, conjTr_one, Matrix.mul_one]

theorem levi3_conj_mem {c : F} {Q Qi : Matrix (Fin 3) (Fin 3) F} (hQQi : Q * Qi = 1)
    (hQ : conjTr σ Q * Q = gram3 c) {A : Matrix (Fin 2) (Fin 2) F}
    (hA : conjTr σ A * antidiag 2 * A = antidiag 2) :
    (Q * levi3Hom A * Qi).det = 1 ∧
      conjTr σ (Q * levi3Hom A * Qi) * (Q * levi3Hom A * Qi) = 1 := by
  have hn := levi3_norm_det hA
  have ha : A.det ≠ 0 := right_ne_zero_of_mul_eq_one hn
  constructor
  · have h1 : Q.det * Qi.det = 1 := by rw [← det_mul, hQQi, det_one]
    rw [det_mul, det_mul, levi3Hom_apply, det_blockDiag3, mul_inv_cancel₀ ha, mul_one, h1]
  · have e : conjTr σ (Q * levi3Hom A * Qi) * (Q * levi3Hom A * Qi) =
        conjTr σ Qi * (conjTr σ (levi3Hom A) * (conjTr σ Q * Q) * levi3Hom A) * Qi := by
      simp only [conjTr_mul, Matrix.mul_assoc]
    rw [e, hQ, levi3_conjTr_gram3 c hA, levi3_conjTr_inv_gram3 hQQi hQ]

theorem levi3_mulVec_single_two (M : Matrix (Fin 3) (Fin 3) F) (i : Fin 3) :
    (M *ᵥ (Pi.single 2 1 : Fin 3 → F)) i = M i 2 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem levi3_exists_of_fix {c : F} (hc : c ≠ 0) {Q Qi : Matrix (Fin 3) (Fin 3) F}
    (hQQi : Q * Qi = 1) (hQiQ : Qi * Q = 1) (hQ : conjTr σ Q * Q = gram3 c)
    {g : Matrix (Fin 3) (Fin 3) F} (hgdet : g.det = 1) (hg : conjTr σ g * g = 1) {d : F}
    (hgv : g *ᵥ (Q *ᵥ Pi.single 2 1) = d • (Q *ᵥ Pi.single 2 1)) :
    ∃ A : Matrix (Fin 2) (Fin 2) F, conjTr σ A * antidiag 2 * A = antidiag 2 ∧
      g = Q * levi3Hom A * Qi := by
  obtain ⟨g', hg'⟩ : ∃ g' : Matrix (Fin 3) (Fin 3) F, g' = Qi * g * Q := ⟨_, rfl⟩
  have hdet' : g'.det = 1 := by
    rw [hg', det_mul, det_mul, hgdet, mul_one, ← det_mul, hQiQ, det_one]
  have h3 : g' *ᵥ (Pi.single 2 1 : Fin 3 → F) = d • (Pi.single 2 1 : Fin 3 → F) := by
    rw [hg', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hgv, Matrix.mulVec_smul,
      Matrix.mulVec_mulVec, hQiQ, Matrix.one_mulVec]
  have e02 : g' 0 2 = 0 := by
    have := congrFun h3 0
    rw [levi3_mulVec_single_two] at this
    simpa using this
  have e12 : g' 1 2 = 0 := by
    have := congrFun h3 1
    rw [levi3_mulVec_single_two] at this
    simpa using this
  have e22 : g' 2 2 = d := by
    have := congrFun h3 2
    rw [levi3_mulVec_single_two] at this
    simpa using this
  have hrel : conjTr σ g' * gram3 c * g' = gram3 c := by
    have e1 : conjTr σ g' * gram3 c * g' =
        conjTr σ Q * (conjTr σ g * (conjTr σ Qi * gram3 c * Qi) * g) * Q := by
      simp only [hg', conjTr_mul, Matrix.mul_assoc]
    rw [e1, levi3_conjTr_inv_gram3 hQQi hQ, Matrix.mul_one, hg, Matrix.mul_one, hQ]
  have hd : d ≠ 0 := by
    intro hd0
    rw [Matrix.det_fin_three, e02, e12, e22, hd0] at hdet'
    simp at hdet'
  have e20 : g' 2 0 = 0 := by
    have h := congrFun (congrFun hrel 2) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, conjTr, gram3_eq, e02, e12, e22] at h
    rcases h with (h | h) | h
    · exact absurd h hd
    · exact absurd h hc
    · exact h
  have e21 : g' 2 1 = 0 := by
    have h := congrFun (congrFun hrel 2) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, conjTr, gram3_eq, e02, e12, e22] at h
    rcases h with (h | h) | h
    · exact absurd h hd
    · exact absurd h hc
    · exact h
  have hgb : g' = blockDiag3 !![g' 0 0, g' 0 1; g' 1 0, g' 1 1] d := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blockDiag3, e02, e12, e22, e20, e21]
  set A : Matrix (Fin 2) (Fin 2) F := !![g' 0 0, g' 0 1; g' 1 0, g' 1 1]
  have hAJ : conjTr σ A * antidiag 2 * A = antidiag 2 := by
    rw [hgb, gram3, conjTr_blockDiag3, blockDiag3_mul, blockDiag3_mul] at hrel
    exact (blockDiag3_inj hrel).1
  have hdA : A.det * d = 1 := by rw [← det_blockDiag3, ← hgb, hdet']
  refine ⟨A, hAJ, ?_⟩
  have hdA' : d = A.det⁻¹ := eq_inv_of_mul_eq_one_right hdA
  calc g = (Q * Qi) * g * (Q * Qi) := by rw [hQQi, Matrix.one_mul, Matrix.mul_one]
    _ = Q * g' * Qi := by rw [hg']; simp only [Matrix.mul_assoc]
    _ = Q * levi3Hom A * Qi := by rw [hgb, hdA', levi3Hom_apply]

theorem levi_embedding_of_frame {c : F} (hc : c ≠ 0) {Q : Matrix (Fin 3) (Fin 3) F}
    (hQ : conjTr σ Q * Q = gram3 c) :
    ∃ ι : ↥(GU σ 2) →* ↥(SUid σ 3), Function.Injective ι ∧
      ∀ (g : ↥(SUid σ 3)) (d : F),
        ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (Q *ᵥ Pi.single 2 1) =
          d • (Q *ᵥ Pi.single 2 1) → g ∈ ι.range := by
  have hQdet := det_ne_zero_of_gram3 hc hQ
  set P : GL (Fin 3) F := Matrix.GeneralLinearGroup.mkOfDetNeZero Q hQdet
  have hPval : (P : Matrix (Fin 3) (Fin 3) F) = Q := rfl
  have hQQi : Q * ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← hPval, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQiQ : ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * Q = 1 := by
    rw [← hPval, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  let φ : GL (Fin 2) F →* GL (Fin 3) F := (MulAut.conj P).toMonoidHom.comp (Units.map levi3Hom)
  have hφ : ∀ A : GL (Fin 2) F, ((φ A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Q * levi3Hom (A : Matrix (Fin 2) (Fin 2) F) *
        ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    intro A
    rw [show (φ A : GL (Fin 3) F) = P * Units.map levi3Hom A * P⁻¹ from rfl, Units.val_mul,
      Units.val_mul]
    rfl
  have hmem : ∀ A : ↥(GU σ 2), φ (A : GL (Fin 2) F) ∈ SUid σ 3 := by
    intro A
    rw [mem_SUid, hφ]
    exact levi3_conj_mem hQQi hQ (mem_GU.mp A.2)
  refine ⟨(φ.comp (GU σ 2).subtype).codRestrict (SUid σ 3) hmem, ?_, ?_⟩
  · intro A B h
    have h1 : φ (A : GL (Fin 2) F) = φ (B : GL (Fin 2) F) := congrArg Subtype.val h
    have h2 := (MulAut.conj P).injective h1
    have h3 : levi3Hom ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        levi3Hom ((B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := congrArg Units.val h2
    exact Subtype.ext (Units.ext (blockDiag3_inj h3).1)
  · intro g d hgd
    have hg := g.2
    rw [mem_SUid] at hg
    obtain ⟨A0, hA0, hgA⟩ := levi3_exists_of_fix hc hQQi hQiQ hQ hg.1 hg.2 hgd
    have hdetA0 : A0.det ≠ 0 := right_ne_zero_of_mul_eq_one (levi3_norm_det hA0)
    let A : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero A0 hdetA0
    have hAmem : A ∈ GU σ 2 := mem_GU.mpr hA0
    refine ⟨⟨A, hAmem⟩, Subtype.ext (Units.ext ?_)⟩
    show ((φ A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = _
    rw [hφ]
    exact hgA.symm

end General

section StatedSU

open CFSG.LieType.BorelTits

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] [CharP K p]

theorem su3_levi_embedding_of_frame (hK : Nat.card K = p ^ 2) (M : Subgroup ↥(StatedSU 3 p K))
    {v : Fin 3 → K}
    (hvM : ∀ g ∈ M, ∃ c : K, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = c • v)
    {c : K} (hc : c ≠ 0) (Q : Matrix (Fin 3) (Fin 3) K) (hQv : ∀ i, Q i 2 = v i)
    (hQ : CFSG.LieType.Universal.Unitary.conjTr (unitaryInvolution K p 1) Q * Q =
      !![0, 1, 0; 1, 0, 0; 0, 0, c]) :
    ∃ ι : ↥(GU (unitaryInvolution K p 1) 2) →* ↥(StatedSU 3 p K),
      Function.Injective ι ∧ M ≤ ι.range := by
  have hK' : Nat.card K = (p ^ 1) ^ 2 := by rw [pow_one]; exact hK
  have hS : SUid (unitaryInvolution K p 1) 3 = StatedSU 3 p K := by
    have := SUid_eq_statedSU hK' 3
    rwa [pow_one] at this
  obtain ⟨ι, hι, hrange⟩ := levi_embedding_of_frame (σ := unitaryInvolution K p 1) hc
    (Q := Q) (by rw [gram3_eq]; exact hQ)
  refine ⟨(Subgroup.inclusion hS.le).comp ι, (Subgroup.inclusion_injective hS.le).comp hι, ?_⟩
  intro g hg
  obtain ⟨d, hd⟩ := hvM g hg
  have hQe : Q *ᵥ (Pi.single 2 1 : Fin 3 → K) = v := by
    funext i
    rw [levi3_mulVec_single_two, hQv]
  have hgS : (g : GL (Fin 3) K) ∈ SUid (unitaryInvolution K p 1) 3 := by
    rw [hS]
    exact g.2
  obtain ⟨A, hA⟩ := hrange ⟨g, hgS⟩ d (by rw [hQe]; exact hd)
  refine ⟨A, Subtype.ext ?_⟩
  have h1 : ((ι A : ↥(SUid (unitaryInvolution K p 1) 3)) : GL (Fin 3) K) = (g : GL (Fin 3) K) :=
    congrArg Subtype.val hA
  exact h1

end StatedSU

end CFSG.Quasithin.A38c17
