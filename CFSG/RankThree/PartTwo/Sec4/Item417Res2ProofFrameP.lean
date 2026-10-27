module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
import CFSG.RankThree.PartTwo.Sec4.Item417Res2ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res417Frame

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix

variable {K : Type} [Field K]

theorem injective_smul_tau {τ κ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (hκ : κ ≠ 0) :
    Function.Injective (fun i : Fin 3 => κ * (![1, τ, τ ^ 2] : Fin 3 → K) i) := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have h12 : τ ≠ τ ^ 2 := by
    intro h
    apply hτ1
    have : τ * τ = τ * 1 := by rw [mul_one, ← pow_two, ← h]
    exact mul_left_cancel₀ hτ0 this
  have h23 : τ ^ 2 ≠ 1 := by
    intro h
    apply hτ1
    calc τ = τ ^ 3 / τ ^ 2 := by field_simp
      _ = 1 := by rw [hτ, h, div_one]
  intro i j hij
  have hij' : (![1, τ, τ ^ 2] : Fin 3 → K) i = (![1, τ, τ ^ 2] : Fin 3 → K) j :=
    mul_left_cancel₀ hκ hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

theorem pow_three_smul_tau {τ κ : K} (hτ : τ ^ 3 = 1) (i j : Fin 3) :
    (κ * (![1, τ, τ ^ 2] : Fin 3 → K) i) ^ 3 = (κ * (![1, τ, τ ^ 2] : Fin 3 → K) j) ^ 3 := by
  have hc : ∀ i : Fin 3, (κ * (![1, τ, τ ^ 2] : Fin 3 → K) i) ^ 3 = κ ^ 3 := by
    intro i
    fin_cases i
    · simp
    · simp [mul_pow, hτ]
    · simp only [Fin.reduceFinMk, Matrix.cons_val, mul_pow]
      rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hτ, one_pow, mul_one]
  rw [hc i, hc j]

variable {H : Type} [Group H] {L : Subgroup H} [L.Normal] {π : Bool} {p f : ℕ}

theorem exists_liftP_of_frame (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))]
    {e : L ≃* projImage (slPi π 3 (p ^ f) K)} {A : Subgroup H}
    (hA : Maximal (fun B : Subgroup H => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hA27 : Nat.card A = 27) {c : H} (hc3 : orderOf c = 3)
    (hAc : A ⊓ Subgroup.centralizer (L : Set H) = Subgroup.zpowers c)
    (hpgl : ∀ a ∈ A, ∃ y, IsPGLAtP e a y) {b : Fin 3 → (Fin 3 → K)}
    (hb : LinearIndependent K b)
    (hbd : ∀ a ∈ A, ∀ y, IsPGLAtP e a y →
      ∀ i, ∃ d : K, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = d • b i)
    {u v : K} (hu : u ^ 3 = 1) (hv : v ^ 3 = 1) :
    (∀ y : GL (Fin 3) K, (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈
        (pglHomP hK hq A hpgl).range →
        ∀ i, ∃ d : K, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = d • b i) ∧
      ∃ a ∈ A, ∃ y, IsPGLAtP e a y ∧ ∃ κ : K, κ ≠ 0 ∧
        (y : Matrix (Fin 3) (Fin 3) K) *ᵥ b 0 = κ • b 0 ∧
        (y : Matrix (Fin 3) (Fin 3) K) *ᵥ b 1 = (κ * u) • b 1 ∧
        (y : Matrix (Fin 3) (Fin 3) K) *ᵥ b 2 = (κ * v) • b 2 := by
  have hcardA := card_eq_card_inf_mul_card_rangeP (L := L) (e := e) (hK := hK) (hq := hq)
    (A' := A) (hA' := hpgl)
  rw [hAc, Nat.card_zpowers, hc3, hA27] at hcardA
  have hEd : ∀ y : GL (Fin 3) K, (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈
      (pglHomP hK hq A hpgl).range → ∀ i, ∃ d : K, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ b i =
        d • b i := by
    rintro y ⟨⟨a, ha⟩, hay⟩ i
    obtain ⟨z, hz⟩ := hpgl a ha
    rw [pglHomP_apply ⟨a, ha⟩ hz, QuotientGroup.eq] at hay
    obtain ⟨μ, hμ⟩ := hay
    obtain ⟨cz, hcz⟩ := hbd a ha z hz i
    refine ⟨cz * μ, ?_⟩
    have hyz : y = z * GeneralLinearGroup.scalar (Fin 3) μ := by rw [hμ]; group
    rw [hyz, Units.val_mul, ← Matrix.mulVec_mulVec, coe_scalar_eq_smul, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_smul, hcz, smul_smul, mul_comm]
  refine ⟨hEd, ?_⟩
  obtain ⟨y, ⟨⟨a, ha⟩, hay⟩, l, hy0, hy1, hy2⟩ := exists_mk_mem_of_frame _
    (range_pglHomP_pow hA.1.2) hb hEd (by omega) hu hv
  obtain ⟨ya, hya⟩ := hpgl a ha
  rw [pglHomP_apply ⟨a, ha⟩ hya, QuotientGroup.eq] at hay
  obtain ⟨μ, hμ⟩ := hay
  have hyay : ya = y * GeneralLinearGroup.scalar (Fin 3) μ⁻¹ := by rw [map_inv, hμ]; group
  have hl0 : l ≠ 0 := by
    intro hl
    rw [hl, zero_smul] at hy0
    have hinj := (Matrix.mulVec_injective_iff_isUnit (A := (y : Matrix (Fin 3) (Fin 3) K))).mpr
      y.isUnit
    exact hb.ne_zero 0 (hinj (by rw [hy0, Matrix.mulVec_zero]))
  have hsc : ∀ (i : Fin 3) (r : K), (y : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = r • b i →
      (ya : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = (((μ⁻¹ : Kˣ) : K) * r) • b i := by
    intro i r hr
    rw [hyay, Units.val_mul, ← Matrix.mulVec_mulVec, coe_scalar_eq_smul, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_smul, hr, smul_smul]
  refine ⟨a, ha, ya, hya, ((μ⁻¹ : Kˣ) : K) * l, mul_ne_zero (Units.ne_zero _) hl0, ?_, ?_, ?_⟩
  · exact hsc 0 l hy0
  · rw [hsc 1 _ hy1, mul_assoc]
  · rw [hsc 2 _ hy2, mul_assoc]

theorem exists_regular_liftP_of_frame (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))]
    {e : L ≃* projImage (slPi π 3 (p ^ f) K)} {A : Subgroup H}
    (hA : Maximal (fun B : Subgroup H => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hA27 : Nat.card A = 27) {c : H} (hc3 : orderOf c = 3)
    (hAc : A ⊓ Subgroup.centralizer (L : Set H) = Subgroup.zpowers c)
    (hpgl : ∀ a ∈ A, ∃ y, IsPGLAtP e a y) {b : Fin 3 → (Fin 3 → K)}
    (hb : LinearIndependent K b)
    (hbd : ∀ a ∈ A, ∀ y, IsPGLAtP e a y →
      ∀ i, ∃ d : K, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = d • b i)
    {τ : K} (hτ : τ ^ 3 = 1) :
    (∀ y : GL (Fin 3) K, (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈
        (pglHomP hK hq A hpgl).range →
        ∀ i, ∃ d : K, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = d • b i) ∧
      ∃ a ∈ A, ∃ y, IsPGLAtP e a y ∧ ∃ κ : K, κ ≠ 0 ∧
        ∀ i, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ b i =
          (κ * (![1, τ, τ ^ 2] : Fin 3 → K) i) • b i := by
  have hτ2 : (τ ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hτ, one_pow]
  obtain ⟨hEd, a, ha, ya, hya, κ, hκ, h0, h1, h2⟩ :=
    exists_liftP_of_frame hK hq hA hA27 hc3 hAc hpgl hb hbd hτ hτ2
  refine ⟨hEd, a, ha, ya, hya, κ, hκ, fun i => ?_⟩
  fin_cases i
  · simpa using h0
  · simpa using h1
  · simpa using h2

end CFSG.RankThree.PartTwo.Sec4.Res417Frame
