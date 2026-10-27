module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Matrix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open

theorem rowLeaves_of_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    [Finite F] {K : Type} [Group K] [Finite K] {H : Subgroup (GL ι F)}
    (hbot : (StatedScalars ι F).subgroupOf H = ⊥) (e : K ≃* StatedProj H)
    {z₀ t₀ : GL ι F} {X₀ : Subgroup (GL ι F)} (h : MatrixRowData H z₀ t₀ X₀) : RowLeaves K :=
  rowLeaves_of_matrixRowData
    (e.trans ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot)) h

theorem exists_omega_of_three_dvd {F : Type} [Field F] [Fintype F] (h : 3 ∣ Fintype.card F - 1) :
    ∃ ω : F, ω ^ 2 + ω + 1 = 0 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card Fˣ := by rwa [Nat.card_eq_fintype_card, Fintype.card_units]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 hdvd
  have h3 : (x : F) ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    simpa using congrArg Units.val this
  have h1 : (x : F) - 1 ≠ 0 := by
    intro h0
    have : x = 1 := Units.ext (sub_eq_zero.1 h0)
    rw [this, orderOf_one] at hx
    omega
  refine ⟨x, ?_⟩
  have : ((x : F) - 1) * ((x : F) ^ 2 + x + 1) = 0 := by linear_combination h3
  exact (mul_eq_zero.1 this).resolve_left h1

theorem ne_zero_of_omega {F : Type} [Field F] {ω : F} (h : ω ^ 2 + ω + 1 = 0) : ω ≠ 0 := by
  rintro rfl
  simp at h

theorem charP_of_nat_card_eq {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (h : Nat.card F = p ^ f) : CharP F p := by
  have := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])

theorem exists_gl_diagonal {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (d : ι → F) (hd : ∀ i, d i ≠ 0) :
    ∃ g : GL ι F, (g : Matrix ι ι F) = Matrix.diagonal d := by
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal d) ?_, rfl⟩
  rw [Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun i _ => hd i

theorem exists_gl_of_mul_eq_one {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (A B : Matrix ι ι F) (h : A * B = 1) : ∃ g : GL ι F, (g : Matrix ι ι F) = A := by
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A ?_, rfl⟩
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem pow_eq_one_of_scalar_mem_statedSL {n : ℕ} {F : Type} [Field F] {c : Fˣ}
    (h : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ StatedSL n F) : (c : F) ^ n = 1 := by
  have hdet := StatedAPI.det_of_mem_statedSL h
  rwa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet

theorem eq_one_of_pow_eq_one_of_coprime {F : Type} [Field F] [Fintype F] {n : ℕ}
    (hn : Nat.Coprime n (Fintype.card F - 1)) {c : F} (hc : c ≠ 0) (h : c ^ n = 1) : c = 1 := by
  have h1 := FiniteField.pow_card_sub_one_eq_one c hc
  have : c ^ Nat.gcd n (Fintype.card F - 1) = 1 := pow_gcd_eq_one.2 ⟨h, h1⟩
  rwa [Nat.Coprime.gcd_eq_one hn, pow_one] at this

theorem subgroupOf_eq_bot_of_le {G : Type} [Group G] {S H H' : Subgroup G} (h : H ≤ H')
    (h' : S.subgroupOf H' = ⊥) : S.subgroupOf H = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx' : (⟨(x : G), h x.2⟩ : H') ∈ S.subgroupOf H' := by
    simpa [Subgroup.mem_subgroupOf] using hx
  rw [h'] at hx'
  have : (x : G) = 1 := congrArg Subtype.val (Subgroup.mem_bot.1 hx')
  exact Subgroup.mem_bot.2 (Subtype.ext this)

theorem statedScalars_subgroupOf_statedSL_eq_bot {n : ℕ} {F : Type} [Field F]
    (h : ∀ c : F, c ≠ 0 → c ^ n = 1 → c = 1) :
    (StatedScalars (Fin n) F).subgroupOf (StatedSL n F) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hg
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ StatedSL n F := by
    rw [hc]
    exact g.2
  have hc1 : c = 1 := Units.ext (h c c.ne_zero (pow_eq_one_of_scalar_mem_statedSL hmem))
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

theorem statedScalars_subgroupOf_statedSU_eq_bot {n q : ℕ} {F : Type} [Field F]
    (h : ∀ c : F, c ≠ 0 → c ^ n = 1 → c = 1) :
    (StatedScalars (Fin n) F).subgroupOf (StatedSU n q F) = ⊥ :=
  subgroupOf_eq_bot_of_le (StatedAPI.statedSU_le_statedSL n q F)
    (statedScalars_subgroupOf_statedSL_eq_bot h)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
