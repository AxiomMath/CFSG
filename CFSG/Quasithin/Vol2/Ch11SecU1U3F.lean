module

public import CFSG.Quasithin.Vol2.Ch11SecU1U3E

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.U3

open CFSG.Quasithin.E2P.Asc80 CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical
open CFSG.Quasithin.A312U3 (uniData exists_su2_equiv)
open CFSG.GH74.GLS.IVK.Proofs2 CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F]

omit [Fact p.Prime] [Finite F] in
theorem piU_eq_one_of_matU_eq_scalar {g : SU3F p F} {c : F}
    (hg : matU g = Matrix.scalar (Fin 3) c) : piU p F g = 1 := by
  have h1 : matU g * matU g⁻¹ = 1 := by rw [← matU_mul, mul_inv_cancel, matU_one]
  have h00 := congrFun (congrFun h1 0) 0
  rw [hg] at h00
  simp [Matrix.scalar_apply] at h00
  have hc0 : c ≠ 0 := left_ne_zero_of_mul_eq_one h00
  rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf, StatedScalars,
    MonoidHom.mem_range]
  refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
  simpa [Matrix.GeneralLinearGroup.coe_scalar, matU] using hg.symm

omit [Finite F] in
theorem blk_eq_scalar_of_piU_eq_one (hF : Nat.card F = p ^ 2) {M : ↥(GU2Stated (p ^ 1) F)}
    (h : piU p F (Lemma41aU3.blkU (uniData hF) M) = 1) :
    ∃ ζ : F, ((M : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) ζ ∧
      (((M : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det)⁻¹ = ζ := by
  obtain ⟨c, -, hc⟩ := exists_scalar_of_mem_ker hF (MonoidHom.mem_ker.mpr h)
  rw [matU_blkU hF] at hc
  refine ⟨c, ?_, ?_⟩
  · ext i j
    have := congrFun (congrFun hc i.castSucc) j.castSucc
    fin_cases i <;> fin_cases j <;> simpa [Lemma41aL3.blkMat, Matrix.scalar_apply] using this
  · simpa [Lemma41aL3.blkMat, Matrix.scalar_apply] using congrFun (congrFun hc 2) 2

omit [Finite F] in
theorem pow_succ_eq_one_of_scalar (hF : Nat.card F = p ^ 2) {M : ↥(GU2Stated (p ^ 1) F)} {ζ : F}
    (hM : ((M : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) ζ) :
    ζ ^ (p + 1) = 1 := by
  have h := (Lemma41aU3.mem_GU2Stated_iff (uniData hF)).mp M.2
  rw [hM] at h
  have h00 := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply] at h00
  rw [(uniData hF).bar_apply, pow_one] at h00
  rw [pow_succ]
  exact h00

theorem exists_eq_piU_ofSU2 (hF : Nat.card F = p ^ 2) {s : PSU3F p F} (hs : s ∈ leviSL hF) :
    ∃ S : ↥(StatedSU 2 (p ^ 1) F), s = piU p F (ofSU2 hF S) := by
  obtain ⟨y, rfl⟩ := hs
  exact ⟨_, rfl⟩

theorem scalar_of_piU_mem_centralizer_leviSL (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2)
    {N : ↥(GU2Stated (p ^ 1) F)}
    (hc : piU p F (Lemma41aU3.blkU (uniData hF) N) ∈
      Subgroup.centralizer (leviSL hF : Set (PSU3F p F))) :
    ∃ μ : F, ((N : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) μ := by
  have h2 := two_ne_zero_u hp2 hF
  obtain ⟨c₁, d₁, hQ⟩ := exists_quatPair_su2 hp2 hF
  have hQ' := hQ.map (StatedSU 2 (p ^ 1) F).subtype (StatedSU 2 (p ^ 1) F).subtype_injective
  obtain ⟨hC, hD, hDC⟩ := quat_relations h2 (det_of_mem_su2 hF c₁) hQ'
  have hNc : ∀ e : ↥(StatedSU 2 (p ^ 1) F), (N : GL (Fin 2) F).1 * (e : GL (Fin 2) F).1 =
      (e : GL (Fin 2) F).1 * (N : GL (Fin 2) F).1 := by
    intro e
    have h1 := Subgroup.mem_centralizer_iff.mp hc _ (piU_ofSU2_mem_leviSL hF e)
    have h2' := commute_of_piU_commute hF (A := Subgroup.inclusion su2_le_gu2 e) (B := N) h1
    have := congrArg
      (fun g : ↥(GU2Stated (p ^ 1) F) => ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) h2'
    simpa [Units.val_mul] using this.symm
  exact scalar_of_commute_quat h2 hC hD hDC (hNc c₁) (hNc d₁)

omit [Fact p.Prime] [Finite F] in
theorem sq_cases {S : Matrix (Fin 2) (Fin 2) F} (hdet : S.det = 1) {μ ξ : F} (hμ : μ ≠ 0)
    (hS : (μ • S) * (μ • S) = Matrix.scalar (Fin 2) ξ) (hξ : ξ * μ ^ 4 = 1) :
    μ ^ 6 = -1 ∨ (μ ^ 6 = 1 ∧ (S = 1 ∨ S = -1)) := by
  have e00 := congrFun (congrFun hS 0) 0
  have e01 := congrFun (congrFun hS 0) 1
  have e10 := congrFun (congrFun hS 1) 0
  have e11 := congrFun (congrFun hS 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply] at e00 e01 e10 e11
  rw [Matrix.det_fin_two] at hdet
  have hμ2 : μ ^ 2 ≠ 0 := pow_ne_zero 2 hμ
  by_cases had : S 0 0 + S 1 1 = 0
  · left
    linear_combination -hξ - μ ^ 4 * e00 + μ ^ 6 * S 0 0 * had - μ ^ 6 * hdet
  · right
    have hb : S 0 1 = 0 := by
      have : μ ^ 2 * (S 0 1 * (S 0 0 + S 1 1)) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hμ2)).resolve_right had
    have hc : S 1 0 = 0 := by
      have : μ ^ 2 * (S 1 0 * (S 0 0 + S 1 1)) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hμ2)).resolve_right had
    have hda : S 1 1 = S 0 0 := by
      have : μ ^ 2 * ((S 0 0 - S 1 1) * (S 0 0 + S 1 1)) = 0 := by linear_combination e00 - e11
      have := (mul_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hμ2)).resolve_right had
      linear_combination -this
    have ha : (S 0 0 - 1) * (S 0 0 + 1) = 0 := by
      linear_combination hdet - S 0 0 * hda + S 1 0 * hb
    refine ⟨by linear_combination hξ + μ ^ 4 * e00 - μ ^ 6 * hdet + μ ^ 6 * S 0 0 * hda -
      2 * μ ^ 6 * S 1 0 * hb, ?_⟩
    have hS1 : S = Matrix.scalar (Fin 2) (S 0 0) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hc, hda, Matrix.scalar_apply]
    rcases mul_eq_zero.mp ha with h | h
    · left
      rw [hS1, show S 0 0 = 1 by linear_combination h, map_one]
    · right
      rw [hS1, show S 0 0 = -1 by linear_combination h, map_neg, map_one]

omit [Finite F] in
theorem piU_blkU_scalar (hF : Nat.card F = p ^ 2) {A : ↥(GU2Stated (p ^ 1) F)} {ℓ : F}
    (hA : ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) ℓ)
    (h6 : ℓ ^ 6 = 1) :
    piU p F (Lemma41aU3.blkU (uniData hF) A) = 1 ∨
      piU p F (Lemma41aU3.blkU (uniData hF) A) = zcU hF := by
  have hdet : (Matrix.scalar (Fin 2) ℓ).det = ℓ ^ 2 := by
    rw [Matrix.det_fin_two]
    simp [Matrix.scalar_apply, sq]
  have h3 : (ℓ ^ 3 - 1) * (ℓ ^ 3 + 1) = 0 := by linear_combination h6
  rcases mul_eq_zero.mp h3 with h3 | h3
  · left
    have hinv : (ℓ ^ 2)⁻¹ = ℓ := inv_eq_of_mul_eq_one_right (by linear_combination h3)
    apply piU_eq_one_of_matU_eq_scalar (c := ℓ)
    rw [matU_blkU hF, hA, hdet, hinv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Lemma41aL3.blkMat, Matrix.scalar_apply]
  · right
    have hinv : (ℓ ^ 2)⁻¹ = -ℓ := inv_eq_of_mul_eq_one_right (by linear_combination -h3)
    have h1 : piU p F (tU hF * Lemma41aU3.blkU (uniData hF) A) = 1 := by
      apply piU_eq_one_of_matU_eq_scalar (c := -ℓ)
      rw [matU_mul, matU_tU, matU_blkU hF, hA, hdet, hinv]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [negNegOneDiag, Lemma41aL3.blkMat, Matrix.scalar_apply]
    have htt : piU p F (tU hF) * piU p F (tU hF) = 1 := by
      rw [← map_mul, show tU hF * tU hF = 1 from ext_matU (by
        rw [matU_mul, matU_tU, negNegOneDiag_mul_self, matU_one]), map_one]
    calc piU p F (Lemma41aU3.blkU (uniData hF) A)
        = piU p F (tU hF) * piU p F (tU hF) * piU p F (Lemma41aU3.blkU (uniData hF) A) := by
          rw [htt, one_mul]
      _ = piU p F (tU hF) := by rw [mul_assoc, ← map_mul, h1, mul_one]

theorem ne_mul_of_involution (hp2 : p ≠ 2) (hp4 : p % 4 = 1) (hF : Nat.card F = p ^ 2)
    {x : PSU3F p F} (hxB : x ∈ leviCU hF) (hx2 : orderOf x = 2) (hxz : x ≠ zcU hF)
    {s c : PSU3F p F} (hs : s ∈ leviSL hF)
    (hc : c ∈ Subgroup.centralizer (leviSL hF : Set (PSU3F p F))) : x ≠ s * c := by
  intro hxsc
  have h2 := two_ne_zero_u hp2 hF
  obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hxB
  obtain ⟨S, rfl⟩ := exists_eq_piU_ofSU2 hF hs
  set N : ↥(GU2Stated (p ^ 1) F) := (Subgroup.inclusion su2_le_gu2 S)⁻¹ * A with hN
  have hAN : A = Subgroup.inclusion su2_le_gu2 S * N := by rw [hN, mul_inv_cancel_left]
  have hNc : piU p F (Lemma41aU3.blkU (uniData hF) N) = c := by
    have h1 : piU p F (Lemma41aU3.blkU (uniData hF) A) = piU p F (ofSU2 hF S) *
        piU p F (Lemma41aU3.blkU (uniData hF) N) := by
      rw [hAN, map_mul, map_mul]
      rfl
    rw [hxsc] at h1
    exact (mul_left_cancel h1).symm
  obtain ⟨μ, hμ⟩ := scalar_of_piU_mem_centralizer_leviSL hp2 hF (N := N) (by rw [hNc]; exact hc)
  have hμp : μ ^ (p + 1) = 1 := pow_succ_eq_one_of_scalar hF hμ
  have hμ0 : μ ≠ 0 := fun h0 => by
    rw [h0, zero_pow (Nat.succ_ne_zero p)] at hμp
    exact zero_ne_one hμp
  have hdS := det_of_mem_su2 hF S
  set σ := ((S : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hσ
  have hA : ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = μ • σ := by
    rw [hAN]
    show σ * ((N : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = _
    rw [hμ]
    ext i j
    simp [Matrix.scalar_apply, Matrix.mul_diagonal, mul_comm]
  have hxx : piU p F (Lemma41aU3.blkU (uniData hF) (A * A)) = 1 := by
    have h1 := pow_orderOf_eq_one (piU p F (Lemma41aU3.blkU (uniData hF) A))
    rw [hx2, sq] at h1
    rw [map_mul, map_mul]
    exact h1
  obtain ⟨ξ, hξ, hdξ⟩ := blk_eq_scalar_of_piU_eq_one hF hxx
  have hAA : (μ • σ) * (μ • σ) = Matrix.scalar (Fin 2) ξ := by rw [← hA]; exact hξ
  have hξμ : ξ * μ ^ 4 = 1 := by
    have h4 : (((A * A : ↥(GU2Stated (p ^ 1) F)) : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F).det = μ ^ 4 := by
      show (((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)).det = _
      rw [hA, Matrix.det_mul, Matrix.det_smul, hdS]
      simp only [Fintype.card_fin, mul_one]
      ring
    rw [h4] at hdξ
    rw [← hdξ, inv_mul_cancel₀ (pow_ne_zero 4 hμ0)]
  have hfin : ∀ ℓ : F, ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.scalar (Fin 2) ℓ → ℓ ^ 6 = 1 → False := fun ℓ hℓ hℓ6 => by
    rcases piU_blkU_scalar hF hℓ hℓ6 with h1 | h1
    · rw [h1, orderOf_one] at hx2
      omega
    · exact hxz h1
  rcases sq_cases hdS hμ0 hAA hξμ with h6 | ⟨h6, hS1 | hS1⟩
  ·
    have hk : (p + 1) * 3 = 6 * (2 * (p / 4) + 1) := by omega
    have h1 : (μ ^ 6) ^ (2 * (p / 4) + 1) = 1 := by
      rw [← pow_mul, ← hk, pow_mul, hμp, one_pow]
    rw [h6, Odd.neg_one_pow ⟨p / 4, rfl⟩] at h1
    exact h2 (by linear_combination -h1)
  · refine hfin μ ?_ h6
    rw [hA, hS1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
  · refine hfin (-μ) ?_ (by linear_combination h6)
    rw [hA, hS1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]

end CFSG.Quasithin.Vol2.Ch11.SecU1.U3
