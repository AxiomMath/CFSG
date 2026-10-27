module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofDihedral
public import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofBlockCommon
public import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofLinBasics

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Res6Proof

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification
open Item211Lie2Proof Item211Res5Proof
open scoped MatrixGroups Matrix

section DihedralMain

variable {K : Type} [Field K]

abbrev innP (K : Type) [Field K] : Subgroup (MulAut (projectiveSL 3 K)) :=
  (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range

theorem two_two_pow (hK2 : (2 : K) ≠ 0) {Z : SL(3, K)} (hZ : Z * sZero = sZero * Z) (n : ℕ) :
    ((Z ^ n : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2 =
      ((Z : Matrix (Fin 3) (Fin 3) K) 2 2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hZn : Z ^ n * sZero = sZero * Z ^ n := (Commute.pow_left hZ n).eq
    rw [pow_succ, apply_two_two_mul hK2 hZn hZ, ih, pow_succ]

theorem det_jTwo : (jTwo : GL (Fin 2) K).val.det = 1 := by
  rw [coe_jTwo, Matrix.det_fin_two_of]
  ring

theorem proj_eq_of_blockScalar_cube {Z : SL(3, K)}
    (hZ : IsBlockScalar (Z : Matrix (Fin 3) (Fin 3) K))
    (hz3 : ((Z : Matrix (Fin 3) (Fin 3) K) 2 2) ^ 3 = 1) :
    proj 3 K Z = 1 ∨ proj 3 K Z = proj 3 K sZero := by
  apply eq_one_or_eq_x0_of_blockScalar hZ
  obtain ⟨⟨h02, h12, h20, h21⟩, h01, h10, h00⟩ := hZ
  have hdet := Z.2
  rw [Matrix.det_fin_three, h01, h02, h10, h12, h20, h21, ← h00] at hdet
  simp only [mul_zero, zero_mul, sub_zero, add_zero] at hdet
  set α := (Z : Matrix (Fin 3) (Fin 3) K) 0 0 with hα
  set z := (Z : Matrix (Fin 3) (Fin 3) K) 2 2 with hz
  have hαz : (α - z) * (α + z) = 0 := by
    linear_combination z ^ 2 * hdet - α ^ 2 * hz3
  have hz1 : z ≠ 0 := by
    rintro h0
    rw [h0] at hz3
    norm_num at hz3
  have hsq : ((Z : Matrix (Fin 3) (Fin 3) K) * Z) = Matrix.scalar (Fin 3) (z ^ 2) := by
    rcases mul_eq_zero.mp hαz with h | h
    · have h' : α = z := sub_eq_zero.mp h
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, h01, h02, h10, h12, h20, h21, ← h00, ← hα,
          ← hz, h', Matrix.scalar_apply, Matrix.diagonal] <;> ring
    · have h' : α = -z := by linear_combination h
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, h01, h02, h10, h12, h20, h21, ← h00, ← hα,
          ← hz, h', Matrix.scalar_apply, Matrix.diagonal] <;> ring
  rw [← map_pow, proj_eq_one_iff, mem_scalars]
  refine ⟨Units.mk0 (z ^ 2) (pow_ne_zero 2 hz1), ?_, ?_⟩
  · apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    rw [← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hz3, one_pow]
  · rw [Matrix.SpecialLinearGroup.coe_pow, pow_two, hsq]
    rfl

theorem slConjugation_eq_self_of_scalar {F : GL (Fin 2) K} {c : K}
    (h : (F : Matrix (Fin 2) (Fin 2) K) = c • (1 : Matrix (Fin 2) (Fin 2) K)) (A : SL(2, K)) :
    CatalogueBHigherLinearAction.slConjugation 2 K F A = A := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    have := (Matrix.isUnits_det_units F).ne_zero
    rw [h, zero_smul, Matrix.det_zero] at this
    exact this rfl
  have hF : F = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc0) := by
    apply Units.ext
    rw [h, Matrix.smul_one_eq_diagonal]
    rfl
  rw [hF, CatalogueBHigherLinearAction.slConjugation_scalar]
  rfl

theorem outerCentConcl_of_dihedral [Finite K] (hK2 : (2 : K) ≠ 0)
    {T : Subgroup (MulAut (projectiveSL 3 K))} (hT2 : IsPGroup 2 T) (hX : xZero ∈ T)
    (hXc : ∀ t ∈ T, t * xZero = xZero * t)
    (hnab : ¬ (∀ a ∈ innP K ⊓ Subgroup.centralizer
        ((T ⊓ innP K : Subgroup (MulAut (projectiveSL 3 K))) : Set (MulAut (projectiveSL 3 K))),
      ∀ b ∈ innP K ⊓ Subgroup.centralizer
        ((T ⊓ innP K : Subgroup (MulAut (projectiveSL 3 K))) : Set (MulAut (projectiveSL 3 K))),
      a * b = b * a))
    {d : MulAut (projectiveSL 3 K)}
    (hdC : d ∈ innP K ⊓ Subgroup.centralizer (T : Set (MulAut (projectiveSL 3 K))))
    (hd1 : d ≠ 1) (hd3 : d ^ 3 = 1)
    {t' : MulAut (projectiveSL 3 K)} (ht' : t' ∈ T)
    (hφ : ProjectivePlane.linearFieldPart K (le_refl 3) t' = 1)
    (hmove : ∃ A : SL(2, K), t' (iota A) ≠ iota A) :
    OuterCentConcl (innP K) T := by
  classical
  obtain ⟨g, σ, ε, hε, hg, ht'eq⟩ := exists_block_form hK2 (apply_x0_of_mem hXc ht')
  have hσ : σ = 1 := by
    rw [ht'eq, ProjectivePlane.linearFieldPart_eq (le_refl 3) hε] at hφ
    exact hφ
  subst hσ
  rw [map_one, mul_one] at ht'eq
  have hε1 : ε = 1 := by
    rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
    · exfalso
      rw [pow_zero, mul_one] at ht'eq
      obtain ⟨e, he⟩ := hT2 ⟨t', ht'⟩
      have he' : t' ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
      rw [ht'eq] at he'
      have h3 : ¬ 3 ∣ 2 ^ e := fun h => by
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
          (Nat.prime_three.dvd_of_dvd_pow h)
        omega
      obtain ⟨y, hy⟩ := conjAut_mem_range_of_pow_eq_one he' h3
      obtain ⟨Yl, rfl⟩ := proj_surjective 3 K y
      have hYT : MulAut.conj (proj 3 K Yl) ∈ T := by rw [hy, ← ht'eq]; exact ht'
      have hbs := isBlockScalar_of_mem hK2 hX hXc hnab hYT
      obtain ⟨A, hA⟩ := hmove
      apply hA
      rw [ht'eq, ← hy, MulAut.conj_apply, iota_apply, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have hc := commute_of_isBlockScalar_of_isBlk hbs (isBlock_blockMat (A : Matrix (Fin 2)
        (Fin 2) K))
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_blockEmb, hc,
        Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
    · rfl
  subst hε1
  rw [pow_one] at ht'eq
  obtain ⟨E, hE⟩ : ∃ E : Matrix (Fin 2) (Fin 2) K,
      E = upper (g : Matrix (Fin 3) (Fin 3) K) * (jTwo : GL (Fin 2) K).val := ⟨_, rfl⟩
  have hEv : ((upperGL hg * jTwo : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = E := by
    rw [Units.val_mul, coe_upperGL, hE]
  have hact : ∀ A : SL(2, K), t' (iota A) =
      iota (CatalogueBHigherLinearAction.slConjugation 2 K (upperGL hg * jTwo) A) := by
    intro A
    rw [ht'eq, MulAut.mul_apply, dualAut_iota, conjAut_iota hg, map_mul, MulAut.mul_apply]
  have hEdet : E.det ≠ 0 := by
    rw [hE, Matrix.det_mul, det_jTwo, mul_one]
    exact (isUnit_det_upper hg).ne_zero
  have hEns : ¬ ∃ c : K, E = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rintro ⟨c, hc⟩
    obtain ⟨A, hA⟩ := hmove
    apply hA
    rw [hact, slConjugation_eq_self_of_scalar (hEv.trans hc)]
  have hrel : ∀ Z : SL(3, K), Z * sZero = sZero * Z →
      MulAut.conj (proj 3 K Z) ∈ Subgroup.centralizer (T : Set (MulAut (projectiveSL 3 K))) →
      upper (Z : Matrix (Fin 3) (Fin 3) K) * E =
        ((Z : Matrix (Fin 3) (Fin 3) K) 2 2) ^ 3 • (E * upper (Z : Matrix (Fin 3) (Fin 3) K)) := by
    intro Z hZ hZT
    rw [hE]
    apply upper_mul_eq_of_fixed hK2 hg hZ
    rw [← ht'eq]
    apply conj_injective_three
    rw [← mul_conj_mul_inv', Subgroup.mem_centralizer_iff.mp hZT t' ht', mul_inv_cancel_right]
  have hrot3 : ∀ Z : SL(3, K), Z * sZero = sZero * Z →
      MulAut.conj (proj 3 K Z) ∈ Subgroup.centralizer (T : Set (MulAut (projectiveSL 3 K))) →
      MulAut.conj (proj 3 K Z) ^ 3 = 1 →
      upper (Z : Matrix (Fin 3) (Fin 3) K) * E = E * upper (Z : Matrix (Fin 3) (Fin 3) K) := by
    intro Z hZ hZT h3
    have hr := hrel Z hZ hZT
    set z := (Z : Matrix (Fin 3) (Fin 3) K) 2 2 with hz
    have hdC := det_upper_mul_two_two hK2 hZ
    have hCdet : (upper (Z : Matrix (Fin 3) (Fin 3) K)).det ≠ 0 := left_ne_zero_of_mul_eq_one hdC
    have hz6 : z ^ 6 = 1 := by
      have h1 := congrArg Matrix.det hr
      rw [Matrix.det_mul (upper (Z : Matrix (Fin 3) (Fin 3) K)) E, Matrix.det_smul,
        Matrix.det_mul E (upper (Z : Matrix (Fin 3) (Fin 3) K)), Fintype.card_fin] at h1
      have h2 : (upper (Z : Matrix (Fin 3) (Fin 3) K)).det * E.det * (1 - (z ^ 3) ^ 2) = 0 := by
        linear_combination h1
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h (mul_ne_zero hCdet hEdet)
      · rw [← pow_mul] at h
        linear_combination -h
    have h3' : proj 3 K Z ^ 3 = 1 := conj_injective_three (by rw [map_pow, h3, map_one])
    rw [← map_pow, proj_eq_one_iff, mem_scalars] at h3'
    obtain ⟨ζ, hζ3, hζ⟩ := h3'
    have hz3 : z ^ 3 = ζ := by
      rw [hz, ← two_two_pow hK2 hZ 3, hζ]
      simp [Matrix.scalar_apply]
    have hζ3' : (ζ : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hζ3, Units.val_one]
    have hz31 : z ^ 3 = 1 := by
      have h9 : z ^ 9 = 1 := by rw [show 9 = 3 * 3 by rfl, pow_mul, hz3, hζ3']
      have e : z ^ 3 = z ^ 9 := by rw [show 9 = 3 + 6 by rfl, pow_add, hz6, mul_one]
      rw [e, h9]
    rw [hz31, one_smul] at hr
    exact hr
  have hS3 : ∀ a ∈ {τ | τ ∈ innP K ⊓ Subgroup.centralizer (T : Set (MulAut (projectiveSL 3 K)))
        ∧ τ ^ 3 = 1}, ∀ b ∈ {τ | τ ∈ innP K ⊓ Subgroup.centralizer
          (T : Set (MulAut (projectiveSL 3 K))) ∧ τ ^ 3 = 1}, a * b = b * a := by
    rintro a ⟨haC, ha3⟩ b ⟨hbC, hb3⟩
    obtain ⟨Za, hZa, rfl⟩ := exists_block_of_mem hX haC
    obtain ⟨Zb, hZb, rfl⟩ := exists_block_of_mem hX hbC
    have hra := hrot3 Za hZa (Subgroup.mem_inf.mp haC).2 ha3
    have hrb := hrot3 Zb hZb (Subgroup.mem_inf.mp hbC).2 hb3
    have hcomm := commute_of_commute_nonscalar hEns hra hrb
    have hZZ := commute_of_upper_commute (isBlock_coe hK2 hZa) (isBlock_coe hK2 hZb) hcomm
    have h1 : Za * Zb = Zb * Za := Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      exact hZZ)
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, h1]
  have hNcomm := commute_of_mem_closure hS3
  refine ⟨fun P hPN _ _ x hx n hn => hNcomm x (hPN hx) n hn, fun P hP hP2 => ?_⟩
  obtain ⟨Zd, hZd, rfl⟩ := exists_block_of_mem hX hdC
  have hdN : MulAut.conj (proj 3 K Zd) ∈ threeClosureIn (innP K) T :=
    Subgroup.subset_closure ⟨hdC, hd3⟩
  have hrd := hrot3 Zd hZd (Subgroup.mem_inf.mp hdC).2 hd3
  have hDns : ¬ ∃ c : K, upper (Zd : Matrix (Fin 3) (Fin 3) K) =
      c • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rintro ⟨c, hc⟩
    have hbs : IsBlockScalar (Zd : Matrix (Fin 3) (Fin 3) K) := by
      refine ⟨isBlock_coe hK2 hZd, ?_, ?_, ?_⟩
      · have := congrFun (congrFun hc 0) 1
        simpa [upper] using this
      · have := congrFun (congrFun hc 1) 0
        simpa [upper] using this
      · have h0 := congrFun (congrFun hc 0) 0
        have h1 := congrFun (congrFun hc 1) 1
        simp [upper] at h0 h1
        rw [h0, h1]
    have hr := hrel Zd hZd (Subgroup.mem_inf.mp hdC).2
    rw [hc, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul] at hr
    have hz3 : ((Zd : Matrix (Fin 3) (Fin 3) K) 2 2) ^ 3 = 1 := by
      have hc0 : c ≠ 0 := by
        rintro rfl
        have := det_upper_mul_two_two hK2 hZd
        rw [hc, zero_smul, Matrix.det_zero, zero_mul] at this
        exact zero_ne_one this
      have hE0 : E ≠ 0 := by
        rintro h0
        rw [h0, Matrix.det_zero] at hEdet
        exact hEdet rfl
      have h1 : ((1 : K) - (Zd : Matrix (Fin 3) (Fin 3) K) 2 2 ^ 3) • (c • E) = 0 := by
        rw [sub_smul, one_smul, smul_smul, ← hr, sub_self]
      rcases smul_eq_zero.mp h1 with h | h
      · linear_combination -h
      · exact absurd ((smul_eq_zero.mp h).resolve_left hc0) hE0
    rcases proj_eq_of_blockScalar_cube hbs hz3 with h | h
    · exact hd1 (by rw [h, map_one])
    · apply hd1
      have h2 : MulAut.conj (proj 3 K Zd) ^ 2 = 1 := by
        rw [h, ← map_pow, ← map_pow, sZero_sq, map_one, map_one]
      calc MulAut.conj (proj 3 K Zd) = MulAut.conj (proj 3 K Zd) ^ 3 *
            (MulAut.conj (proj 3 K Zd) ^ 2)⁻¹ := by group
        _ = 1 := by rw [hd3, h2]; group
  have hProt : ∀ y ∈ P, ∃ Z : SL(3, K), Z * sZero = sZero * Z ∧ y = MulAut.conj (proj 3 K Z) ∧
      upper (Z : Matrix (Fin 3) (Fin 3) K) * E = E * upper (Z : Matrix (Fin 3) (Fin 3) K) := by
    intro y hy
    have hyC : y ∈ innP K ⊓ Subgroup.centralizer (T : Set (MulAut (projectiveSL 3 K))) :=
      (Subgroup.mem_inf.mp (hP hy)).1
    obtain ⟨Z, hZ, rfl⟩ := exists_block_of_mem hX hyC
    refine ⟨Z, hZ, rfl, ?_⟩
    have hyd : proj 3 K Z * proj 3 K Zd = proj 3 K Zd * proj 3 K Z := by
      apply conj_injective_three
      rw [map_mul, map_mul]
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hP hy)).2 _ hdN).symm
    have hZZd := commute_of_proj_commute_block hK2 hZ hZd hyd
    have hup : upper (Z : Matrix (Fin 3) (Fin 3) K) * upper (Zd : Matrix (Fin 3) (Fin 3) K) =
        upper (Zd : Matrix (Fin 3) (Fin 3) K) * upper (Z : Matrix (Fin 3) (Fin 3) K) := by
      rw [← upper_mul (isBlock_coe hK2 hZ) (isBlock_coe hK2 hZd),
        ← upper_mul (isBlock_coe hK2 hZd) (isBlock_coe hK2 hZ), hZZd]
    exact commute_of_commute_nonscalar hDns hup hrd.symm
  have hPcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    intro a ha b hb
    obtain ⟨Za, hZa, rfl, hra⟩ := hProt a ha
    obtain ⟨Zb, hZb, rfl, hrb⟩ := hProt b hb
    have hcomm := commute_of_commute_nonscalar hEns hra hrb
    have hZZ := commute_of_upper_commute (isBlock_coe hK2 hZa) (isBlock_coe hK2 hZb) hcomm
    have h1 : Za * Zb = Zb * Za := Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      exact hZZ)
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, h1]
  have hPinv : ∀ y ∈ P, y ^ 2 = 1 → y ≠ 1 → y = xZero := by
    intro y hy hy2 hy1
    obtain ⟨Z, hZ, rfl, hr⟩ := hProt y hy
    have hyC : MulAut.conj (proj 3 K Z) ∈
        Subgroup.centralizer (T : Set (MulAut (projectiveSL 3 K))) :=
      (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hP hy)).1).2
    have hr' := hrel Z hZ hyC
    set z := (Z : Matrix (Fin 3) (Fin 3) K) 2 2 with hz
    set C := upper (Z : Matrix (Fin 3) (Fin 3) K) with hC
    have hdC := det_upper_mul_two_two hK2 hZ
    have hz0 : z ≠ 0 := right_ne_zero_of_mul_eq_one hdC
    have hCdet : C.det ≠ 0 := left_ne_zero_of_mul_eq_one hdC
    have hz3 : z ^ 3 = 1 := by
      rw [hr] at hr'
      have h1 : ((1 : K) - z ^ 3) • (E * C) = 0 := by
        rw [sub_smul, one_smul, ← hr', sub_self]
      have hEC : E * C ≠ 0 := by
        intro h0
        have := congrArg Matrix.det h0
        rw [Matrix.det_mul, Matrix.det_zero] at this
        exact mul_ne_zero hEdet hCdet this
      rcases smul_eq_zero.mp h1 with h | h
      · linear_combination -h
      · exact absurd h hEC
    have h2' : proj 3 K Z ^ 2 = 1 := conj_injective_three (by rw [map_pow, hy2, map_one])
    have h2'' := h2'
    rw [← map_pow, proj_eq_one_iff, mem_scalars] at h2''
    obtain ⟨ζ, -, hζ⟩ := h2''
    have hz2 : z ^ 2 = ζ := by
      rw [hz, ← two_two_pow hK2 hZ 2, hζ]
      simp [Matrix.scalar_apply]
    have hC2 : C * C = (ζ : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [hC, ← upper_mul (isBlock_coe hK2 hZ) (isBlock_coe hK2 hZ),
        ← Matrix.SpecialLinearGroup.coe_mul, ← pow_two, hζ]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [upper, Matrix.scalar_apply]
    have hM2 : (z⁻¹ • C) * (z⁻¹ • C) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hC2, smul_smul, ← hz2]
      rw [show z⁻¹ * z⁻¹ * z ^ 2 = 1 by field_simp]
      exact one_smul _ _
    have hMdet : (z⁻¹ • C).det = 1 := by
      rw [Matrix.det_smul, Fintype.card_fin]
      have : C.det = z⁻¹ := eq_inv_of_mul_eq_one_left hdC
      rw [this]
      field_simp
      linear_combination -hz3
    have hbs : IsBlockScalar (Z : Matrix (Fin 3) (Fin 3) K) := by
      have hZb := isBlock_coe hK2 hZ
      have hsc : ∃ s : K, C = s • (1 : Matrix (Fin 2) (Fin 2) K) := by
        rcases eq_one_or_neg_of_sq hK2 hM2 hMdet with h | h
        · refine ⟨z, ?_⟩
          rw [← h, smul_smul, mul_inv_cancel₀ hz0, one_smul]
        · refine ⟨-z, ?_⟩
          rw [show (-z) • (1 : Matrix (Fin 2) (Fin 2) K) = z • (-1 : Matrix (Fin 2) (Fin 2) K) by
            rw [smul_neg, neg_smul], ← h, smul_smul, mul_inv_cancel₀ hz0, one_smul]
      obtain ⟨s, hs⟩ := hsc
      refine ⟨hZb, ?_, ?_, ?_⟩
      · have := congrFun (congrFun hs 0) 1
        simpa [hC, upper] using this
      · have := congrFun (congrFun hs 1) 0
        simpa [hC, upper] using this
      · have h0 := congrFun (congrFun hs 0) 0
        have h1 := congrFun (congrFun hs 1) 1
        simp [hC, upper] at h0 h1
        rw [h0, h1]
    rcases proj_eq_of_blockScalar_cube hbs hz3 with h | h
    · exact absurd (by rw [h, map_one]) hy1
    · rw [h]
      rfl
  have : Finite P := Subgroup.instFiniteSubtypeMem P
  exact isCyclic_of_comm_unique hPcomm hP2 fun a ha b hb ha2 hb2 ha1 hb1 => by
    rw [hPinv a ha ha2 ha1, hPinv b hb hb2 hb1]

end DihedralMain

end Item211Res6Proof

end CFSG.RankThree.PartTwo.Sec21
