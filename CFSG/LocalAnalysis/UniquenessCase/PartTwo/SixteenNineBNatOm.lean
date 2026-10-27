module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.Quasithin.Background.P3OrthoOm4
import TauCeti.FieldTheory.Finite.Four
import CFSG.RankThree.GF2n.Smith81.Lin31TwoAlg

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Quasithin CFSG.Open CFSG.Quasithin.G11.P3Ortho.Om4
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

variable {K : Type} [Field K] [CharP K 2]

private theorem s16n9b_upper_cube {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (c : K) :
    (!![ω ^ 2, c; 0, ω] : Matrix (Fin 2) (Fin 2) K) ^ 3 = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h3 : (3 : K) = 1 := by linear_combination h2
  have hω2 : ω ^ 2 = ω + 1 := by linear_combination hω - (ω + 1) * h2
  have hωadd : ω ^ 2 + ω = 1 := by linear_combination hω - h2
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω4 : ω ^ 4 = ω := by rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, hω3, one_mul]
  have hω5 : ω ^ 5 = ω ^ 2 := by
    rw [show (5 : ℕ) = 3 + 2 by norm_num, pow_add, hω3, one_mul]
  have hω6 : (ω ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 + 3 by norm_num, pow_add, hω3, one_mul]
  have h1 : (1 : K) + ω + (ω + 1) = 0 := by linear_combination (1 + ω) * h2
  have hc : ω * c + (ω + 1) * c + c = 0 := by linear_combination (ω * c + c) * h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ, hω2, hω3, hω4, hω5, hω6, hωadd, h2, h3,
      h1, hc]
  all_goals ring_nf
  all_goals simp [hω2, hω3, hω4, hω5, hω6, hωadd, h2, h3, h1, hc]

private theorem s16n9b_diag_cube {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    (!![ω, 0; 0, ω ^ 2] : Matrix (Fin 2) (Fin 2) K) ^ 3 = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω6 : ω ^ 6 = 1 := by rw [show (6 : ℕ) = 3 + 3 by norm_num, pow_add, hω3, one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ, hω3, hω6, h2]
  all_goals ring_nf
  all_goals simp [hω3, hω6, h2]

private theorem s16n9b_exists_sl2_eigen {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {a : Fin 2 → K} (ha : a ≠ 0) :
    ∃ E : Matrix.SpecialLinearGroup (Fin 2) K,
      E ^ 3 = 1 ∧ E ≠ 1 ∧ (E : Matrix (Fin 2) (Fin 2) K) *ᵥ a = ω • a := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hω2 : ω ^ 2 = ω + 1 := by linear_combination hω - (ω + 1) * h2
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h] at hω
    have h1 : (1 : K) = 0 := by linear_combination hω - h2
    exact one_ne_zero h1
  by_cases ha1 : a 1 = 0
  · have ha0 : a 0 ≠ 0 := by
      intro h
      apply ha
      funext i
      fin_cases i <;> simpa [h, ha1]
    have hdet : (!![ω, 0; 0, ω ^ 2] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
      rw [Matrix.det_fin_two]
      norm_num
      rw [← pow_succ', hω3]
    let E : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![ω, 0; 0, ω ^ 2], hdet⟩
    have hmat : (!![ω, 0; 0, ω ^ 2] : Matrix (Fin 2) (Fin 2) K) *ᵥ a = ω • a := by
      funext i
      fin_cases i <;>
        rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two] <;>
        simp [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_succ,
          Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one, Pi.smul_apply, Pi.one_apply,
          smul_eq_mul, ha1]
    refine ⟨E, ?_, ?_, ?_⟩
    · apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
      change (!![ω, 0; 0, ω ^ 2] : Matrix (Fin 2) (Fin 2) K) ^ 3 = 1
      exact s16n9b_diag_cube hω
    · intro h
      have h00 := congrArg (fun E : Matrix.SpecialLinearGroup (Fin 2) K =>
        (E : Matrix (Fin 2) (Fin 2) K) 0 0) h
      simp at h00
      exact hω1 h00
    · change (!![ω, 0; 0, ω ^ 2] : Matrix (Fin 2) (Fin 2) K) *ᵥ a = ω • a
      exact hmat
  · have ha1ne : a 1 ≠ 0 := ha1
    have hdet : (!![ω ^ 2, a 0 / a 1; 0, ω] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
      rw [Matrix.det_fin_two]
      norm_num
      rw [← pow_succ, hω3]
    let E : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![ω ^ 2, a 0 / a 1; 0, ω], hdet⟩
    have hmat : (!![ω ^ 2, a 0 / a 1; 0, ω] : Matrix (Fin 2) (Fin 2) K) *ᵥ a = ω • a := by
      funext i
      fin_cases i
      · rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_succ,
          Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one, Pi.smul_apply, Pi.one_apply,
          smul_eq_mul]
        rw [div_mul_cancel₀ (a 0) ha1ne]
        linear_combination (a 0) * hω2 + (a 0) * h2
      · rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_succ,
          Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one, Pi.smul_apply, Pi.one_apply,
          smul_eq_mul]
        ring
    refine ⟨E, ?_, ?_, ?_⟩
    · apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
      change (!![ω ^ 2, a 0 / a 1; 0, ω] : Matrix (Fin 2) (Fin 2) K) ^ 3 = 1
      exact s16n9b_upper_cube hω (a 0 / a 1)
    · intro h
      have h11 := congrArg (fun E : Matrix.SpecialLinearGroup (Fin 2) K =>
        (E : Matrix (Fin 2) (Fin 2) K) 1 1) h
      simp at h11
      exact hω1 h11
    · change (!![ω ^ 2, a 0 / a 1; 0, ω] : Matrix (Fin 2) (Fin 2) K) *ᵥ a = ω • a
      exact hmat




private theorem s16n9b_sl2_std : ∃ t : Matrix.SpecialLinearGroup (Fin 2) K, t ^ 3 = 1 ∧ t ≠ 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hdet : (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [Matrix.det_fin_two]
    norm_num
    linear_combination (-1 : K) * h2
  let t : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![0, 1; 1, 1], hdet⟩
  have ht3 : t ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    change (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) K) ^ 3 = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two] <;>
      linear_combination h2
  have ht1 : t ≠ 1 := by
    intro h
    have h01 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K =>
      (g : Matrix (Fin 2) (Fin 2) K) 0 1) h
    exact (one_ne_zero : (1 : K) ≠ 0) (by simpa [t] using h01)
  exact ⟨t, ht3, ht1⟩

private theorem s16n9b_sl2_pair_fix {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {X : Matrix (Fin 2) (Fin 2) K} (hX : X ≠ 0) :
    ∃ z : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K,
      orderOf z = 3 ∧ (z.1 : Matrix (Fin 2) (Fin 2) K) * X *
        ((z.2⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hdet : X.det = 0
  · obtain ⟨a, b, ha, hb, hXab⟩ :=
      CFSG.RankThree.GF2n.Smith81.exists_vecMulVec_of_det_eq_zero hX hdet
    obtain ⟨E, hE3, hE1, hEeig⟩ := s16n9b_exists_sl2_eigen hω ha
    obtain ⟨F, hF3, hF1, hFeig⟩ := s16n9b_exists_sl2_eigen hω hb
    let Q := Matrix.SpecialLinearGroup.transpose F
    have hQ3 : Q ^ 3 = 1 := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one,
        Matrix.SpecialLinearGroup.coe_transpose, ← Matrix.transpose_pow,
        ← Matrix.SpecialLinearGroup.coe_pow]
      have hF3m : ((F ^ 3 : Matrix.SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) = (1 : Matrix.SpecialLinearGroup (Fin 2) K) :=
        congrArg Subtype.val hF3
      rw [hF3m]
      simp [Matrix.one_apply, eq_comm]
    have hz3 : (E, Q) ^ 3 = 1 := by
      show (E ^ 3, Q ^ 3) = 1
      rw [hE3, hQ3]
      rfl
    have hz1 : (E, Q) ≠ 1 := fun h => hE1 (congrArg Prod.fst h)
    refine ⟨(E, Q), orderOf_eq_prime hz3 hz1, ?_⟩
    have hEX : (E : Matrix (Fin 2) (Fin 2) K) * X = ω • X := by
      rw [hXab, Matrix.mul_vecMulVec, hEeig, Matrix.smul_vecMulVec]
    have hXQ : X * (Q : Matrix (Fin 2) (Fin 2) K) = ω • X := by
      have hQv : (Q : Matrix (Fin 2) (Fin 2) K) = (F : Matrix (Fin 2) (Fin 2) K)ᵀ := rfl
      rw [hXab, hQv, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, hFeig,
        Matrix.vecMulVec_smul]
    have hQinv : (Q : Matrix (Fin 2) (Fin 2) K) *
        ((Q⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    change (E : Matrix (Fin 2) (Fin 2) K) * X *
        ((Q⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = X
    calc (E : Matrix (Fin 2) (Fin 2) K) * X *
          ((Q⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
        = (ω • X) * ((Q⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
          rw [hEX]
      _ = (X * (Q : Matrix (Fin 2) (Fin 2) K)) *
            ((Q⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
          rw [← hXQ]
      _ = X * ((Q : Matrix (Fin 2) (Fin 2) K) *
            ((Q⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
          rw [Matrix.mul_assoc]
      _ = X * 1 := by rw [hQinv]
      _ = X := by rw [Matrix.mul_one]
  · have hunit : IsUnit X.det := isUnit_iff_ne_zero.mpr hdet
    have hunitX : IsUnit X := (isUnit_iff_isUnit_det X).mpr hunit
    let Xu : Matrix.GeneralLinearGroup (Fin 2) K := hunitX.unit
    have hXu : (Xu : Matrix (Fin 2) (Fin 2) K) = X := hunitX.unit_spec
    obtain ⟨t, ht3, ht1⟩ := s16n9b_sl2_std (K := K)
    let g : Matrix.GeneralLinearGroup (Fin 2) K :=
      Xu⁻¹ * Matrix.SpecialLinearGroup.toGL t * Xu
    have htGL3 : (Matrix.SpecialLinearGroup.toGL t) ^ 3 = 1 := by
      rw [← map_pow, ht3, map_one]
    have hg3 : g ^ 3 = 1 := by
      have h : g ^ 3 = Xu⁻¹ * (Matrix.SpecialLinearGroup.toGL t) ^ 3 * Xu := by
        rw [show g = Xu⁻¹ * Matrix.SpecialLinearGroup.toGL t * Xu from rfl,
          pow_succ, pow_succ, pow_one, pow_succ, pow_succ, pow_one]
        group
      rw [h, htGL3]
      group
    have hXug : Xu * g = Matrix.SpecialLinearGroup.toGL t * Xu := by
      rw [show g = Xu⁻¹ * Matrix.SpecialLinearGroup.toGL t * Xu from rfl]
      group
    have hgdet : Matrix.GeneralLinearGroup.det g = 1 := by
      rw [show g = Xu⁻¹ * Matrix.SpecialLinearGroup.toGL t * Xu from rfl, map_mul, map_mul,
        map_inv, Matrix.SpecialLinearGroup.coeToGL_det, mul_one]
      exact inv_mul_cancel _
    obtain ⟨Q, hQ⟩ : ∃ Q : Matrix.SpecialLinearGroup (Fin 2) K,
        Matrix.SpecialLinearGroup.toGL Q = g := by
      have hgker : g ∈ (Matrix.GeneralLinearGroup.det :
          Matrix.GeneralLinearGroup (Fin 2) K →* Kˣ).ker := by
        rw [MonoidHom.mem_ker]; exact hgdet
      rw [← Matrix.SpecialLinearGroup.range_toGL_eq_ker_det] at hgker
      exact MonoidHom.mem_range.mp hgker
    have hQ3 : Q ^ 3 = 1 := by
      apply Matrix.SpecialLinearGroup.toGL_injective
      rw [map_pow, hQ, hg3, map_one]
    have hz3 : (t, Q) ^ 3 = 1 := by
      show (t ^ 3, Q ^ 3) = 1
      rw [ht3, hQ3]
      rfl
    have hz1 : (t, Q) ≠ 1 := fun h => ht1 (congrArg Prod.fst h)
    refine ⟨(t, Q), orderOf_eq_prime hz3 hz1, ?_⟩
    have hPQt : (t : Matrix (Fin 2) (Fin 2) K) * X = X * (Q : Matrix (Fin 2) (Fin 2) K) := by
      have h := congrArg (fun u : Matrix.GeneralLinearGroup (Fin 2) K =>
        (u : Matrix (Fin 2) (Fin 2) K)) hXug
      simp only [Units.val_mul] at h
      rw [hXu, ← hQ] at h
      simpa using h.symm
    have hQinv : (Q : Matrix (Fin 2) (Fin 2) K) *
        ((Q⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    calc (t : Matrix (Fin 2) (Fin 2) K) * X *
          ((Q⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
        = (X * (Q : Matrix (Fin 2) (Fin 2) K)) *
            ((Q⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
          rw [hPQt]
      _ = X * ((Q : Matrix (Fin 2) (Fin 2) K) *
            ((Q⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
          rw [Matrix.mul_assoc]
      _ = X * 1 := by rw [hQinv]
      _ = X := by rw [Matrix.mul_one]

private theorem s16n9b_transfer {W : Type} [CommGroup W] {ι : Type} [Fintype ι]
    [DecidableEq ι] {K : Type} [Field K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {H : Subgroup (MulAut W)}
    (hR : (FFModel.nat Γ).Realizes H ⊤ ⊥)
    (hfix : ∀ v : ι → K, v ≠ 0 →
      ∃ A ∈ Γ, orderOf A = 3 ∧ (A : Matrix ι ι K) *ᵥ v = v)
    {w : W} (hw : w ≠ 1) :
    ∃ ψ ∈ H, orderOf ψ = 3 ∧ ψ w = w := by
  unfold FFModel.nat at hR
  obtain ⟨π, hπs, hZU, hkerle, hUinv, hZinv, hsecinv, hkerinv, β, hβs, hβk, hβeq⟩ := hR
  let u : ↥(⊤ : Subgroup W) := ⟨w, Subgroup.mem_top w⟩
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
  have hmne : m ≠ 1 := by
    intro h
    have h1 : β u = 1 := by
      rw [← hm, h, QuotientGroup.mk_one]
    have h2 : (u : W) ∈ (⊥ : Subgroup W) := (hβk u).mp h1
    exact hw (Subgroup.mem_bot.mp h2)
  let hmv : ι → K := Multiplicative.toAdd (m : Multiplicative (ι → K))
  have hx : hmv ≠ 0 := by
    intro h0
    apply hmne
    apply Subtype.ext
    show (m : Multiplicative (ι → K)) = 1
    have h1 : Multiplicative.ofAdd hmv = 1 := by rw [h0]; rfl
    simpa [hmv] using h1
  obtain ⟨A, hA, hAord, hAact⟩ := hfix hmv hx
  let γ : ↥Γ := ⟨A, hA⟩
  have hγord : orderOf γ = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact hAord
  have hord : orderOf (π γ) ∣ 3 := by
    rw [← hγord]
    exact orderOf_map_dvd π γ
  have hne : π γ ≠ 1 := by
    intro hψ1
    have hTriv : ∀ m' : ↥(⊤ : Subgroup (Multiplicative (ι → K))),
        natAct Γ γ (m' : Multiplicative (ι → K)) = (m' : Multiplicative (ι → K)) := by
      intro m'
      obtain ⟨v, hv⟩ := hβs (QuotientGroup.mk m')
      have h := hβeq γ v m' (Subgroup.mem_top _) (Subgroup.mem_top _) hv
      rw [hψ1, OneMemClass.coe_one, MulAut.one_apply] at h
      have hq : (QuotientGroup.mk m' : ↥(⊤ : Subgroup (Multiplicative (ι → K))) ⧸
            (⊥ : Subgroup (Multiplicative (ι → K))).subgroupOf ⊤) =
          QuotientGroup.mk (⟨natAct Γ γ (m' : Multiplicative (ι → K)),
            Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup (Multiplicative (ι → K)))) := by
        rw [← hv]
        simpa using h
      have hmem : m' / (⟨natAct Γ γ (m' : Multiplicative (ι → K)),
            Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup (Multiplicative (ι → K)))) ∈
          (⊥ : Subgroup (Multiplicative (ι → K))).subgroupOf ⊤ :=
        QuotientGroup.eq_iff_div_mem.mp hq
      rw [Subgroup.bot_subgroupOf, Subgroup.mem_bot] at hmem
      have heq := div_eq_one.mp hmem
      exact (congrArg Subtype.val heq).symm
    have hmat : (A : Matrix ι ι K) = 1 := by
      apply Matrix.ext_iff_mulVec.mpr
      intro x
      have h2 := hTriv ⟨Multiplicative.ofAdd x, Subgroup.mem_top _⟩
      have h3 : Multiplicative.ofAdd ((A : Matrix ι ι K) *ᵥ x) =
          Multiplicative.ofAdd x := by
        simpa [natAct, γ, toAdd_ofAdd] using h2
      simpa using congrArg Multiplicative.toAdd h3
    have hA1 : A = 1 := Units.ext hmat
    have : (3 : ℕ) = 1 := by rw [← hAord, hA1, orderOf_one]
    omega
  have hψord : orderOf (π γ) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hord with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hne
    · exact h3
  have hfixw : ((π γ : ↥H) : MulAut W) w = w := by
    have hmemu : ((π γ : ↥H) : MulAut W) (u : W) ∈ (⊤ : Subgroup W) := Subgroup.mem_top _
    have hmsec : natAct Γ γ (m : Multiplicative (ι → K)) ∈
        (⊤ : Subgroup (Multiplicative (ι → K))) := Subgroup.mem_top _
    have h := hβeq γ u m hmemu hmsec hm.symm
    dsimp only at h
    have hactm : natAct Γ γ (m : Multiplicative (ι → K)) =
        (m : Multiplicative (ι → K)) := by
      have h2 : Multiplicative.ofAdd ((A : Matrix ι ι K) *ᵥ hmv) =
          Multiplicative.ofAdd hmv := by
        rw [hAact]
      have h2' : natAct Γ γ (m : Multiplicative (ι → K)) = Multiplicative.ofAdd hmv := by
        simpa [natAct, γ] using h2
      rw [h2']
      exact ofAdd_toAdd _
    rw [hactm] at h
    have h2 : β ⟨((π γ : ↥H) : MulAut W) (u : W), hmemu⟩ = β u := by
      rw [h]
      exact hm
    have h3 : β (⟨((π γ : ↥H) : MulAut W) (u : W), hmemu⟩ * u⁻¹) = 1 := by
      rw [map_mul, map_inv, h2]
      exact mul_inv_cancel _
    have h4 : ((⟨((π γ : ↥H) : MulAut W) (u : W), hmemu⟩ * u⁻¹ :
        ↥(⊤ : Subgroup W)) : W) ∈ (⊥ : Subgroup W) := (hβk _).mp h3
    rw [Subgroup.mem_bot] at h4
    exact mul_inv_eq_one.mp (by simpa [u] using h4)
  have hψord' : orderOf ((π γ : ↥H) : MulAut W) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hψord
  exact ⟨π γ, (π γ).2, hψord', hfixw⟩

private theorem s16n9b_omegaPlus_model {K : Type} [Field K] [Finite K] [CharP K 2]
    (hcard : Nat.card K = 4) (v : Fin 2 ⊕ Fin 2 → K) (hv : v ≠ 0) :
    ∃ A ∈ StatedOmega (StatedQuadPlus 2 K),
      orderOf A = 3 ∧ (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v = v := by
  obtain ⟨ω, hω⟩ := TauCeti.exists_sq_add_self_add_one_eq_zero_of_card_eq_four hcard
  have h4 : 4 ≤ Nat.card K := by rw [hcard]
  have hv' : toMat K v ≠ 0 := by
    intro h
    apply hv
    exact (toMat K).injective (by simpa using h)
  obtain ⟨z, hzord, hzact⟩ := s16n9b_sl2_pair_fix (K := K) hω hv'
  have hmem : rho' K z ∈ (StatedOmega (StatedQuadPlus 2 K)).map (Ψ K).toMonoidHom := by
    rw [map_statedOmega, commutator_eq_range h4]
    exact MonoidHom.mem_range.mpr ⟨z, rfl⟩
  obtain ⟨A, hA, hAΨ⟩ := Subgroup.mem_map.mp hmem
  refine ⟨A, hA, ?_, ?_⟩
  · have h1 : orderOf (Ψ K A) = orderOf A := MulEquiv.orderOf_eq (Ψ K) A
    rw [← h1, show (Ψ K) A = rho' K z from hAΨ,
      orderOf_injective (rho' K) (rho'_injective (K := K)) z, hzord]
  · have hfixX : rho' K z (toMat K v) = toMat K v := by
      show (specialRho z).val (toMat K v) = toMat K v
      rw [specialRho_apply]
      exact hzact
    have h := Ψ_apply K A (toMat K v)
    rw [show (Ψ K) A = rho' K z from hAΨ, hfixX,
      LinearEquiv.symm_apply_apply] at h
    exact (toMat K).injective h.symm

theorem s16n9b_natOmegaPlus_fix {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    (hN : NatOmegaPlus H (⊤ : Subgroup W) ⊥ 4 2) {w : W} (hw : w ≠ 1) :
    ∃ ψ ∈ H, orderOf ψ = 3 ∧ ψ w = w := by
  obtain ⟨-, K, hKf, hKfin, hKcard, hR⟩ := hN
  letI := hKf
  letI := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard4 : Nat.card K = 4 := by rw [hKcard]; norm_num
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hKcard])
  refine s16n9b_transfer (Γ := StatedOmega (StatedQuadPlus (4 / 2) K)) hR ?_ hw
  intro v hv
  exact s16n9b_omegaPlus_model hcard4 v hv


end CFSG.LocalAnalysis.UniquenessCase.PartTwo
