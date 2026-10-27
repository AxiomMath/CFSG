module

public import CFSG.Quasithin.Background.F918Z4bAut
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoPglFaithful
import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.FieldFacts
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups

section Matrices

variable {K : Type} [Field K]

private theorem cayley_fin_two (M : Matrix (Fin 2) (Fin 2) K) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two,
      Matrix.one_apply] <;> ring

private theorem anticomm_fin_two {A B : Matrix (Fin 2) (Fin 2) K} (hA : A.trace = 0)
    (hB : B.trace = 0) :
    A * B + B * A = (A * B).trace • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [Matrix.trace_fin_two] at hA hB
  have hA' : A 1 1 = -A 0 0 := by linear_combination hA
  have hB' : B 1 1 = -B 0 0 := by linear_combination hB
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.one_apply, hA', hB'] <;>
    ring

private theorem eq_zero_of_smul_eq_smul_one {M : Matrix (Fin 2) (Fin 2) K}
    (hM : ∀ r : K, M ≠ r • (1 : Matrix (Fin 2) (Fin 2) K)) {u v : K}
    (h : u • M = v • (1 : Matrix (Fin 2) (Fin 2) K)) : u = 0 ∧ v = 0 := by
  have hu : u = 0 := by
    by_contra hu
    apply hM (u⁻¹ * v)
    rw [mul_smul, ← h, smul_smul, inv_mul_cancel₀ hu, one_smul]
  refine ⟨hu, ?_⟩
  subst hu
  have := congrFun (congrFun h 0) 0
  simpa using this.symm

private theorem trace_of_cube {Y : Matrix (Fin 2) (Fin 2) K} (hdet : Y.det = 1)
    (h3 : Y * Y * Y = 1) (hY : ∀ r : K, Y ≠ r • (1 : Matrix (Fin 2) (Fin 2) K)) :
    Y.trace = -1 ∧ Y * Y + Y + 1 = 0 := by
  have hcay := cayley_fin_two Y
  rw [hdet] at hcay
  have h1 : (Y.trace ^ 2 - 1) • Y = (1 + Y.trace) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have e : Y * Y * Y = (Y.trace ^ 2 - 1) • Y - Y.trace • (1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [hcay]
      simp only [sub_mul, smul_mul_assoc, one_smul, one_mul, mul_sub, mul_smul_comm, mul_one]
      rw [hcay]
      module
    rw [e, sub_eq_iff_eq_add] at h3
    rw [h3, add_smul, one_smul]
  have ht : Y.trace = -1 := by linear_combination (eq_zero_of_smul_eq_smul_one hY h1).2
  refine ⟨ht, ?_⟩
  rw [hcay, ht]
  module

private theorem eq_smul_of_commute {Y G : Matrix (Fin 2) (Fin 2) K} (h2 : (2 : K) ≠ 0)
    (h3 : (3 : K) ≠ 0) (hYtr : Y.trace = -1) (hY2 : Y * Y + Y + 1 = 0) (hGY : G * Y = Y * G)
    {μ : K} (hGG : G * G = μ • (1 : Matrix (Fin 2) (Fin 2) K))
    (hG : ∀ r : K, G ≠ r • (1 : Matrix (Fin 2) (Fin 2) K)) :
    ∃ c : K, G = c • ((2 : K) • Y + 1) := by
  obtain ⟨h, hh⟩ : ∃ h : Matrix (Fin 2) (Fin 2) K, h = (2 : K) • Y + 1 := ⟨_, rfl⟩
  rw [← hh]
  have hhtr : h.trace = 0 := by
    rw [hh, Matrix.trace_add, Matrix.trace_smul, hYtr, Matrix.trace_one]
    simp
  have hYY : Y * Y = -(Y + 1) :=
    eq_neg_of_add_eq_zero_left (by rw [← add_assoc]; exact hY2)
  have hhh : h * h = (-3 : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [hh]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
    rw [hYY]
    module
  have hGh : G * h = h * G := by
    rw [hh]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hGY]
  have hGtr : G.trace = 0 := by
    have hc := cayley_fin_two G
    rw [hGG] at hc
    have : G.trace • G = (μ + G.det) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [add_smul, hc]
      module
    exact (eq_zero_of_smul_eq_smul_one hG this).1
  have hs := anticomm_fin_two hGtr hhtr
  rw [← hGh] at hs
  obtain ⟨s, hs3⟩ : ∃ s : K, G * h = s • (1 : Matrix (Fin 2) (Fin 2) K) := by
    refine ⟨(G * h).trace / 2, ?_⟩
    have : (2 : K) • (G * h) = (G * h).trace • (1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [two_smul]; exact hs
    rw [div_eq_inv_mul, ← smul_smul, ← this, smul_smul, inv_mul_cancel₀ h2, one_smul]
  have e1 : (-3 : K) • G = s • h := by
    calc (-3 : K) • G = G * ((-3 : K) • (1 : Matrix (Fin 2) (Fin 2) K)) := by
          rw [mul_smul_comm, mul_one]
      _ = G * (h * h) := by rw [hhh]
      _ = (G * h) * h := by rw [mul_assoc]
      _ = s • h := by rw [hs3, smul_mul_assoc, one_mul]
  refine ⟨(-3 : K)⁻¹ * s, ?_⟩
  rw [← smul_smul, ← e1, smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr h3), one_smul]

end Matrices

section Lifts

variable {K : Type} [Field K]

private theorem natCast_ne_zero_of_ringChar_ne {q : ℕ} (hq : q.Prime) (h : ringChar K ≠ q) :
    (q : K) ≠ 0 := by
  intro h0
  rcases (Nat.dvd_prime hq).1 (ringChar.dvd h0) with h1 | h1
  · exact (not_subsingleton K) (ringChar.ringChar_eq_one.mp h1)
  · exact h h1

private theorem coe_scalar_eq (u : Kˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (u : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.smul_one_eq_diagonal]

private theorem ne_zero_of_coe_eq_smul {G : GL (Fin 2) K} {M : Matrix (Fin 2) (Fin 2) K} {c : K}
    (h : (G : Matrix (Fin 2) (Fin 2) K) = c • M) : c ≠ 0 := by
  rintro rfl
  have := G.mul_inv
  rw [h, zero_smul, zero_mul] at this
  exact zero_ne_one this

private theorem exists_lift_order_three {x : PSL2 K} (hx : orderOf x = 3) :
    ∃ Y : SL(2, K), (Y : PSL2 K) = x ∧ (Y : Matrix (Fin 2) (Fin 2) K).trace = -1 ∧
      (Y : Matrix (Fin 2) (Fin 2) K) * Y + Y + 1 = 0 := by
  obtain ⟨X, rfl⟩ := QuotientGroup.mk_surjective x
  have h1 : (X : PSL2 K) ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one _
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
    Matrix.SpecialLinearGroup.mem_center_iff] at h1
  obtain ⟨r, hr, hX⟩ := h1
  obtain ⟨Y, hYx, hY3⟩ : ∃ Y : SL(2, K), (Y : PSL2 K) = X ∧ Y ^ 3 = 1 := by
    have hr' : r * r = 1 := by simpa [sq] using hr
    rcases mul_self_eq_one_iff.mp hr' with rfl | rfl
    · exact ⟨X, rfl, Subtype.ext (by simpa using hX.symm)⟩
    · refine ⟨-X, ?_, ?_⟩
      · rw [QuotientGroup.eq, inv_neg, neg_mul, inv_mul_cancel]
        exact Subgroup.mem_center_iff.mpr fun g => by rw [neg_one_mul, mul_neg_one]
      · rw [Odd.neg_pow (by decide)]
        apply Subtype.ext
        have : ((X ^ 3 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1 := by
          rw [← hX, map_neg, map_one]
        simp [this]
  have hYc : Y ∉ Subgroup.center SL(2, K) := by
    intro hmem
    have h1 : (Y : PSL2 K) = 1 := (QuotientGroup.eq_one_iff Y).mpr hmem
    rw [← hYx, h1, orderOf_one] at hx
    omega
  have hYns : ∀ r : K, (Y : Matrix (Fin 2) (Fin 2) K) ≠ r • (1 : Matrix (Fin 2) (Fin 2) K) := by
    intro r hr
    apply hYc
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨r, ?_, ?_⟩
    · have := Y.det_coe
      rw [hr] at this
      simpa [Matrix.det_smul, sq] using this
    · rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
      exact hr.symm
  have hY3' : (Y : Matrix (Fin 2) (Fin 2) K) * Y * Y = 1 := by
    have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K)) hY3
    simpa [pow_succ] using this
  obtain ⟨hYtr, hYY⟩ := trace_of_cube Y.det_coe hY3' hYns
  exact ⟨Y, hYx, hYtr, hYY⟩

private theorem exists_lift_involution {g : PGL2 K} (hg : g * g = 1) (hg1 : g ≠ 1) :
    ∃ (G : GL (Fin 2) K) (μ : K), Matrix.ProjGenLinGroup.mk G = g ∧
      (G : Matrix (Fin 2) (Fin 2) K) * G = μ • (1 : Matrix (Fin 2) (Fin 2) K) ∧
      ∀ r : K, (G : Matrix (Fin 2) (Fin 2) K) ≠ r • (1 : Matrix (Fin 2) (Fin 2) K) := by
  obtain ⟨G, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  have hGG : G * G ∈ Subgroup.center (GL (Fin 2) K) := by
    rw [← Matrix.ProjGenLinGroup.mk_eq_one, map_mul]
    exact hg
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hGG
  obtain ⟨μ, hμ⟩ := hGG
  refine ⟨G, μ, rfl, ?_, fun r hr => hg1 ?_⟩
  · have := congrArg (fun A : GL (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K)) hμ
    simpa only [Units.val_mul, coe_scalar_eq] using this.symm
  · rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar]
    refine ⟨Units.mk0 r (ne_zero_of_coe_eq_smul hr), Units.ext ?_⟩
    rw [coe_scalar_eq, Units.val_mk0]
    exact hr.symm

private theorem commute_of_commute_toPGL {Y : SL(2, K)}
    (hY : (Y : Matrix (Fin 2) (Fin 2) K).trace = -1) {G : GL (Fin 2) K}
    (hc : Matrix.ProjGenLinGroup.mk G * Matrix.ProjectiveSpecialLinearGroup.toPGL (Y : PSL2 K) =
      Matrix.ProjectiveSpecialLinearGroup.toPGL (Y : PSL2 K) * Matrix.ProjGenLinGroup.mk G) :
    (G : Matrix (Fin 2) (Fin 2) K) * Y = Y * G := by
  rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, ← map_mul, ← map_mul,
    Matrix.ProjGenLinGroup.mk_eq_mk_iff] at hc
  obtain ⟨u, hu⟩ := hc
  have hu' : (u : K) • ((G : Matrix (Fin 2) (Fin 2) K) * Y) =
      (Y : Matrix (Fin 2) (Fin 2) K) * G := by
    have := congrArg (fun A : GL (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K)) hu
    simpa only [Units.val_mul, coe_scalar_eq, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.mul_smul, mul_one] using this
  have hu1 : (u : K) = 1 := by
    have e : ((G⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        ((Y : Matrix (Fin 2) (Fin 2) K) * G) = (u : K) • (Y : Matrix (Fin 2) (Fin 2) K) := by
      rw [← hu', Matrix.mul_smul, ← mul_assoc, Units.inv_mul, one_mul]
    have e2 := congrArg Matrix.trace e
    rw [Matrix.trace_mul_comm, mul_assoc, Units.mul_inv, mul_one, Matrix.trace_smul, hY,
      smul_eq_mul] at e2
    linear_combination e2
  rwa [hu1, one_smul] at hu'

private theorem exists_smul_of_commute (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {x : PSL2 K}
    (hx : orderOf x = 3) :
    ∃ h : Matrix (Fin 2) (Fin 2) K, h.det = 3 ∧ ∀ g : PGL2 K, g * g = 1 → g ≠ 1 →
      g * Matrix.ProjectiveSpecialLinearGroup.toPGL x =
        Matrix.ProjectiveSpecialLinearGroup.toPGL x * g →
      ∃ (G : GL (Fin 2) K) (c : K), Matrix.ProjGenLinGroup.mk G = g ∧ c ≠ 0 ∧
        (G : Matrix (Fin 2) (Fin 2) K) = c • h := by
  obtain ⟨Y, rfl, hYtr, hYY⟩ := exists_lift_order_three hx
  refine ⟨(2 : K) • (Y : Matrix (Fin 2) (Fin 2) K) + 1, ?_, fun g hg2 hg1 hc => ?_⟩
  · have hdet := Y.det_coe
    rw [Matrix.det_fin_two] at hdet
    rw [Matrix.trace_fin_two] at hYtr
    simp only [Matrix.det_fin_two, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), smul_eq_mul]
    linear_combination 4 * hdet + 2 * hYtr
  · obtain ⟨G, μ, rfl, hGG, hGns⟩ := exists_lift_involution hg2 hg1
    obtain ⟨c, hc'⟩ :=
      eq_smul_of_commute h2 h3 hYtr hYY (commute_of_commute_toPGL hYtr hc) hGG hGns
    exact ⟨G, c, rfl, ne_zero_of_coe_eq_smul hc', hc'⟩

end Lifts

variable {K : Type} [Field K] [Finite K]

private theorem card_le_two_of_forall_eq {G : Type*} [Group G] [Finite G]
    (h : ∀ a b : G, a ≠ 1 → b ≠ 1 → a = b) : Nat.card G ≤ 2 := by
  by_cases hG : ∃ a : G, a ≠ 1
  · obtain ⟨a₀, ha₀⟩ := hG
    have hsurj : Function.Surjective (fun i : Fin 2 => if i = 0 then (1 : G) else a₀) := by
      intro b
      by_cases hb : b = 1
      · exact ⟨0, by simp [hb]⟩
      · exact ⟨1, by simp [h b a₀ hb ha₀]⟩
    calc Nat.card G ≤ Nat.card (Fin 2) := Nat.card_le_card_of_surjective _ hsurj
      _ = 2 := by simp
  · push Not at hG
    have : Subsingleton G := ⟨fun a b => by rw [hG a, hG b]⟩
    exact (Finite.card_le_one_iff_subsingleton.mpr this).trans (by norm_num)

private theorem exists_pglAction_of_autFieldPart_eq_one {x : PSL2 K} {α : MulAut (PSL2 K)}
    (hα2 : α * α = 1) (hαx : α x = x) (hφ : CFSG.Quasithin.autFieldPart K α = 1) :
    ∃ g : PGL2 K, pglAction K g = α ∧ g * g = 1 ∧
      g * Matrix.ProjectiveSpecialLinearGroup.toPGL x =
        Matrix.ProjectiveSpecialLinearGroup.toPGL x * g := by
  obtain ⟨g, hg⟩ := CFSG.Quasithin.mem_range_pglAction_of_autFieldPart_eq_one hφ
  refine ⟨g, hg, pglAction_injective K ?_, ?_⟩
  · rw [map_mul, hg, map_one]
    exact hα2
  · rw [← hg] at hαx
    have h2 := toPGL_pglAction K g x
    rw [hαx] at h2
    exact mul_inv_eq_iff_eq_mul.mp h2.symm

theorem eq_of_commute_toPGL (hK2 : ringChar K ≠ 2) (hK3 : ringChar K ≠ 3) {x : PSL2 K}
    (hx : orderOf x = 3) {g₁ g₂ : PGL2 K} (h₁ : g₁ * g₁ = 1) (h₁1 : g₁ ≠ 1)
    (hc₁ : g₁ * Matrix.ProjectiveSpecialLinearGroup.toPGL x =
      Matrix.ProjectiveSpecialLinearGroup.toPGL x * g₁)
    (h₂ : g₂ * g₂ = 1) (h₂1 : g₂ ≠ 1)
    (hc₂ : g₂ * Matrix.ProjectiveSpecialLinearGroup.toPGL x =
      Matrix.ProjectiveSpecialLinearGroup.toPGL x * g₂) :
    g₁ = g₂ := by
  have h2 : (2 : K) ≠ 0 := by exact_mod_cast natCast_ne_zero_of_ringChar_ne Nat.prime_two hK2
  have h3 : (3 : K) ≠ 0 := by exact_mod_cast natCast_ne_zero_of_ringChar_ne Nat.prime_three hK3
  obtain ⟨h, -, hh⟩ := exists_smul_of_commute h2 h3 hx
  obtain ⟨G₁, c₁, rfl, hc₁0, hG₁⟩ := hh g₁ h₁ h₁1 hc₁
  obtain ⟨G₂, c₂, rfl, hc₂0, hG₂⟩ := hh g₂ h₂ h₂1 hc₂
  have : G₂ = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (c₂ / c₁) (div_ne_zero hc₂0 hc₁0))
      * G₁ := by
    apply Units.ext
    rw [Units.val_mul, coe_scalar_eq, Units.val_mk0, hG₁, hG₂, smul_mul_assoc, one_mul, smul_smul,
      div_mul_cancel₀ _ hc₁0]
  rw [this, map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]

theorem exists_toPGL_eq_of_commute_toPGL (hK2 : ringChar K ≠ 2) (hK3 : ringChar K ≠ 3)
    (h3 : IsSquare (3 : K)) {x : PSL2 K} (hx : orderOf x = 3) {g : PGL2 K} (hg : g * g = 1)
    (hg1 : g ≠ 1)
    (hc : g * Matrix.ProjectiveSpecialLinearGroup.toPGL x =
      Matrix.ProjectiveSpecialLinearGroup.toPGL x * g) :
    ∃ y : PSL2 K, Matrix.ProjectiveSpecialLinearGroup.toPGL y = g := by
  have h2 : (2 : K) ≠ 0 := by exact_mod_cast natCast_ne_zero_of_ringChar_ne Nat.prime_two hK2
  have h3' : (3 : K) ≠ 0 := by exact_mod_cast natCast_ne_zero_of_ringChar_ne Nat.prime_three hK3
  obtain ⟨h, hdet, hh⟩ := exists_smul_of_commute h2 h3' hx
  obtain ⟨G, c, rfl, hc0, hG⟩ := hh g hg hg1 hc
  obtain ⟨e, he⟩ := h3
  have he0 : e ≠ 0 := by
    rintro rfl
    exact h3' (by rw [he, zero_mul])
  have hM : (e⁻¹ • h : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [Matrix.det_smul, hdet, Fintype.card_fin, he]
    field_simp
  obtain ⟨M, hMval⟩ : ∃ M : SL(2, K), (M : Matrix (Fin 2) (Fin 2) K) = e⁻¹ • h :=
    ⟨⟨e⁻¹ • h, hM⟩, rfl⟩
  refine ⟨QuotientGroup.mk M, ?_⟩
  rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk]
  have : G = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (c * e) (mul_ne_zero hc0 he0)) *
      Matrix.SpecialLinearGroup.toGL M := by
    apply Units.ext
    rw [Units.val_mul, coe_scalar_eq, Units.val_mk0, hG,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hMval, smul_mul_assoc, one_mul, smul_smul,
      mul_inv_cancel_right₀ he0]
  rw [this, map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]

theorem even_of_ringEquiv {p n : ℕ} (hp : p.Prime) (hK : Nat.card K = p ^ n) {σ : K ≃+* K}
    (hσ1 : σ ≠ 1) (hσ2 : σ * σ = 1) : Even n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K hK).1
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rwa [sq]) hσ1
  have hdvd : 2 ∣ n := by
    rw [← h, ← hord]
    exact orderOf_dvd_natCard σ
  exact even_iff_two_dvd.mpr hdvd

theorem isSquare_three_of_ringEquiv (hK2 : ringChar K ≠ 2) {σ : K ≃+* K} (hσ1 : σ ≠ 1)
    (hσ2 : σ * σ = 1) : IsSquare (3 : K) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hpchar, n, hp, hcard⟩ := FiniteField.card' K
  haveI := hpchar
  haveI : Fact p.Prime := ⟨hp⟩
  have hK : Nat.card K = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hcard
  have hn : Even (n : ℕ) := even_of_ringEquiv hp hK hσ1 hσ2
  have hp2 : p ≠ 2 := by rw [← ringChar.eq K p]; exact hK2
  simpa using CFSG.LocalAnalysis.RankFourTheoremC.PPointP.isSquare_natCast_of_even hK hp2 hn 3

theorem card_le_four_of_forall_apply_eq (hK2 : ringChar K ≠ 2) (hK3 : ringChar K ≠ 3)
    {x : PSL2 K} (hx : orderOf x = 3) (E : Subgroup (MulAut (PSL2 K)))
    (hE2 : ∀ α ∈ E, α * α = 1) (hEx : ∀ α ∈ E, α x = x) :
    Nat.card E ≤ 4 ∧ (Nat.card E = 4 →
      (∃ α ∈ E, α ≠ 1 ∧ ∃ y : PSL2 K, α = MulAut.conj y) ∧
        ∃ σ : K ≃+* K, σ ≠ 1 ∧ σ * σ = 1) := by
  let f : E →* (K ≃+* K) := (CFSG.Quasithin.autFieldPart K).comp E.subtype
  have : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  have : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hcard : Nat.card f.ker * Nat.card f.range = Nat.card E :=
    Subgroup.card_ker_mul_card_range f
  have hrange_sq : ∀ σ ∈ f.range, σ * σ = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul, show a * a = 1 from Subtype.ext (hE2 a a.2), map_one]
  have hrange : Nat.card f.range ≤ 2 := by
    refine Nat.le_of_dvd two_pos ?_
    rw [← IsCyclic.exponent_eq_card]
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    rintro ⟨σ, hσ⟩
    refine Subtype.ext ?_
    change σ ^ 2 = 1
    rw [sq]
    exact hrange_sq σ hσ
  have hker_pgl : ∀ a : E, f a = 1 → ∃ g : PGL2 K, pglAction K g = (a : MulAut (PSL2 K)) ∧
      g * g = 1 ∧ g * Matrix.ProjectiveSpecialLinearGroup.toPGL x =
        Matrix.ProjectiveSpecialLinearGroup.toPGL x * g := fun a ha =>
    exists_pglAction_of_autFieldPart_eq_one (hE2 a a.2) (hEx a a.2) ha
  have hker_ne : ∀ (a : E) (ha : a ∈ f.ker) (g : PGL2 K), pglAction K g = (a : MulAut (PSL2 K)) →
      (⟨a, ha⟩ : f.ker) ≠ 1 → g ≠ 1 := by
    rintro a ha g hg hne rfl
    apply hne
    apply Subtype.ext
    apply Subtype.ext
    rw [← hg, map_one]
    rfl
  have hker : Nat.card f.ker ≤ 2 := by
    apply card_le_two_of_forall_eq
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hne₁ hne₂
    obtain ⟨g₁, hg₁, hg₁2, hg₁c⟩ := hker_pgl a ha
    obtain ⟨g₂, hg₂, hg₂2, hg₂c⟩ := hker_pgl b hb
    have := eq_of_commute_toPGL hK2 hK3 hx hg₁2 (hker_ne a ha g₁ hg₁ hne₁) hg₁c hg₂2
      (hker_ne b hb g₂ hg₂ hne₂) hg₂c
    apply Subtype.ext
    apply Subtype.ext
    rw [← hg₁, ← hg₂, this]
  refine ⟨hcard ▸ Nat.mul_le_mul hker hrange, fun h4 => ?_⟩
  have hkpos : 0 < Nat.card f.ker := Nat.card_pos
  have hrpos : 0 < Nat.card f.range := Nat.card_pos
  have key : Nat.card f.ker = 2 ∧ Nat.card f.range = 2 := by
    rw [← hcard] at h4
    rcases (by omega : Nat.card f.ker = 1 ∨ Nat.card f.ker = 2) with h | h <;>
      rcases (by omega : Nat.card f.range = 1 ∨ Nat.card f.range = 2) with h' | h' <;>
      rw [h, h'] at h4 <;> omega
  have : Nontrivial f.range := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨⟨σ, hσ⟩, hσ1⟩ := exists_ne (1 : f.range)
  have hσ1' : σ ≠ 1 := fun h => hσ1 (Subtype.ext h)
  have hσ2 := hrange_sq σ hσ
  refine ⟨?_, σ, hσ1', hσ2⟩
  have : Nontrivial f.ker := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨⟨a, ha⟩, hne⟩ := exists_ne (1 : f.ker)
  obtain ⟨g, hg, hg2, hgc⟩ := hker_pgl a ha
  have hg1 := hker_ne a ha g hg hne
  obtain ⟨y, hy⟩ := exists_toPGL_eq_of_commute_toPGL hK2 hK3
    (isSquare_three_of_ringEquiv hK2 hσ1' hσ2) hx hg2 hg1 hgc
  refine ⟨(a : MulAut (PSL2 K)), a.2, fun h1 => hne (Subtype.ext (Subtype.ext h1)), y, ?_⟩
  rw [← hg, ← hy, pglAction_toPGL]

end CFSG.RankThree.PartTwo.Sec20
