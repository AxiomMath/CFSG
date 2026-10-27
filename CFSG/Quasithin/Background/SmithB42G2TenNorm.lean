module

public import CFSG.Quasithin.Background.SmithB42G2TenQ
public import CFSG.Quasithin.Vol2.Ch11G2Q8Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aTensor

public noncomputable section

namespace CFSG.Quasithin.B42G2Ten

open Matrix CFSG.Open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.Ch11.G2Q8
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL)

variable {F : Type} [Field F] [CharP F 2]

@[expose] def uC (t₁ t₂ t₃ t₄ t₅ t₆ : F) : ↥(cayleyGroup F) :=
  g2Y ![0, t₁, 0] * g2A (uSL t₂ 0 0) * g2X ![t₃, 0, 0] * g2A (uSL 0 t₄ 0) * g2Y ![0, 0, t₅] *
    g2A (uSL 0 0 t₆)

theorem uC_mem_U0 (t₁ t₂ t₃ t₄ t₅ t₆ : F) : uC t₁ t₂ t₃ t₄ t₅ t₆ ∈ U0 F := by
  have h1 : g2Y ![0, t₁, 0] ∈ U0 F := g2Y_mem_U0 t₁ 0
  have h5 : g2Y ![0, 0, t₅] ∈ U0 F := g2Y_mem_U0 0 t₅
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem h1 (g2A_mem_U0 _ _ _)) (g2X_mem_U0 _))
    (g2A_mem_U0 _ _ _)) h5) (g2A_mem_U0 _ _ _)

theorem g2Act_uSL_q6 (x y z a b c d e f : F) :
    g2Act (g2A (uSL x y z)) (q6 a b c d e f) =
      q6 (a + x * b + y * c) (b + z * c) c d (e + x * d) (f + (x * z + y) * d + z * e) := by
  rw [g2Act_g2A_uSL]
  rfl

theorem g2Act_mul_q6 (g h : ↥(cayleyGroup F)) (w : Ix3 → F) :
    g2Act (g * h) w = g2Act g (g2Act h w) := by
  rw [map_mul]
  rfl

theorem g2Act_uC (t₁ t₂ t₃ t₄ t₅ t₆ a b c d e f : F) :
    g2Act (uC t₁ t₂ t₃ t₄ t₅ t₆) (q6 a b c d e f) =
      q6 (a + (t₁ * t₃ + t₂) * b + (t₁ * t₃ * t₆ + t₁ * t₅ ^ 2 + t₂ * t₆ + t₄) * c +
          (t₁ * t₃ * t₅ + t₁ * t₄ + t₂ * t₅ + t₃ ^ 2) * d + (t₁ * t₆ + t₅) * e + t₁ * f)
        (b + t₆ * c + t₅ * d) (c + t₁ * d) d
        (t₁ ^ 2 * b + (t₁ ^ 2 * t₆ + t₃) * c + (t₁ ^ 2 * t₅ + t₂) * d + e)
        (t₃ * b + (t₃ * t₆ + t₅ ^ 2) * c + (t₃ * t₅ + t₄) * d + t₆ * e + f) := by
  simp only [uC, g2Act_mul_q6, g2Act_uSL_q6, g2Act_y2q, g2Act_x0q, g2Act_y1q]
  apply q6_congr <;> ring

theorem uC_injective {t₁ t₂ t₃ t₄ t₅ t₆ s₁ s₂ s₃ s₄ s₅ s₆ : F}
    (h : uC t₁ t₂ t₃ t₄ t₅ t₆ = uC s₁ s₂ s₃ s₄ s₅ s₆) :
    t₁ = s₁ ∧ t₂ = s₂ ∧ t₃ = s₃ ∧ t₄ = s₄ ∧ t₅ = s₅ ∧ t₆ = s₆ := by
  have hv0 := congrArg (fun g => g2Act g (q6 0 0 0 1 0 0)) h
  have hv1 := congrArg (fun g => g2Act g (q6 0 0 0 0 1 0)) h
  have hu1 := congrArg (fun g => g2Act g (q6 0 1 0 0 0 0)) h
  simp only [g2Act_uC] at hv0 hv1 hu1
  obtain ⟨a0, a1, a2, -, -, a5⟩ := q6_inj hv0
  obtain ⟨-, -, -, -, -, b5⟩ := q6_inj hv1
  obtain ⟨c0, -, -, -, -, c5⟩ := q6_inj hu1
  have e1 : t₁ = s₁ := by linear_combination a2
  have e5 : t₅ = s₅ := by linear_combination a1
  have e6 : t₆ = s₆ := by linear_combination b5
  have e3 : t₃ = s₃ := by linear_combination c5
  subst e1 e5 e6 e3
  have e2 : t₂ = s₂ := by linear_combination c0
  have e4 : t₄ = s₄ := by linear_combination a5
  exact ⟨rfl, e2, rfl, e4, rfl, rfl⟩

@[expose] def uCU (t : F × F × F × F × F × F) : ↥(U0 F) :=
  ⟨uC t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2, uC_mem_U0 _ _ _ _ _ _⟩

theorem uCU_bijective [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Function.Bijective (uCU (F := F)) := by
  have := finite_cayleyGroup (F := F)
  refine Function.Injective.bijective_of_nat_card_le (fun t s h => ?_) ?_
  · obtain ⟨t₁, t₂, t₃, t₄, t₅, t₆⟩ := t
    obtain ⟨s₁, s₂, s₃, s₄, s₅, s₆⟩ := s
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := uC_injective (congrArg Subtype.val h)
    subst e1 e2 e3 e4 e5 e6
    rfl
  · rw [card_U0 hF]
    simp only [Nat.card_prod]
    ring_nf
    rfl

@[expose] def cQ (u : ↥(cayleyGroup F)) : F := repQ u (.inl 0) (.inr 0)

@[expose] def cG (u : ↥(cayleyGroup F)) : F :=
  repQ u (.inl 0) (.inr 0) * repQ u (.inr 2) (.inl 2) +
    repQ u (.inl 0) (.inl 2) * repQ u (.inr 2) (.inr 0)

@[expose] def cQf (t₁ t₂ t₃ t₄ t₅ : F) : F := t₁ * t₃ * t₅ + t₁ * t₄ + t₂ * t₅ + t₃ ^ 2

@[expose] def cGf (t₂ t₃ t₄ t₅ t₆ : F) : F :=
  t₂ * t₄ * t₆ + t₂ * t₅ ^ 3 + t₃ ^ 3 * t₆ + t₃ ^ 2 * t₅ ^ 2 + t₃ * t₄ * t₅ + t₄ ^ 2

omit [CharP F 2] in
theorem single_inr0 : (Pi.single (.inr 0) (1 : F) : Ix3 → F) = q6 0 0 0 1 0 0 := by
  funext i
  rcases i with i | i <;> fin_cases i <;> rfl

omit [CharP F 2] in
theorem single_inl2 : (Pi.single (.inl 2) (1 : F) : Ix3 → F) = q6 0 0 1 0 0 0 := by
  funext i
  rcases i with i | i <;> fin_cases i <;> rfl

theorem cQ_uC (t₁ t₂ t₃ t₄ t₅ t₆ : F) : cQ (uC t₁ t₂ t₃ t₄ t₅ t₆) = cQf t₁ t₂ t₃ t₄ t₅ := by
  rw [cQ, repQ_apply, single_inr0, g2Act_uC, q6_apply_inl0, cQf]
  ring

theorem cG_uC (t₁ t₂ t₃ t₄ t₅ t₆ : F) : cG (uC t₁ t₂ t₃ t₄ t₅ t₆) = cGf t₂ t₃ t₄ t₅ t₆ := by
  rw [cG, repQ_apply, repQ_apply, repQ_apply, repQ_apply, single_inr0, single_inl2, g2Act_uC,
    g2Act_uC, q6_apply_inl0, q6_apply_inl0, q6_apply_inr2, q6_apply_inr2, cGf]
  ring_nf
  reduce_mod_char!

section Sum

variable [Fintype F] [DecidableEq F]

omit [CharP F 2] in
theorem sum_affine (α β : F) : ∑ x : F, (α + β * x) ^ (Fintype.card F - 1) =
    -β ^ (Fintype.card F - 1) :=
  CFSG.QuasithinUnique.Setup.X7a.sum_add_mul_pow F α β

omit [CharP F 2] in
theorem sum_cQf_cGf :
    ∑ t₁ : F, ∑ t₂ : F, ∑ t₃ : F, ∑ t₄ : F, ∑ t₅ : F, ∑ t₆ : F,
      (cQf t₁ t₂ t₃ t₄ t₅ * cGf t₂ t₃ t₄ t₅ t₆) ^ (Fintype.card F - 1) = 1 := by
  set m := Fintype.card F - 1
  have h6 : ∀ t₁ t₂ t₃ t₄ t₅ : F, ∑ t₆ : F, (cQf t₁ t₂ t₃ t₄ t₅ * cGf t₂ t₃ t₄ t₅ t₆) ^ m =
      -(cQf t₁ t₂ t₃ t₄ t₅ * (t₂ * t₄ + t₃ ^ 3)) ^ m := fun t₁ t₂ t₃ t₄ t₅ => by
    rw [← sum_affine (cQf t₁ t₂ t₃ t₄ t₅ * (t₂ * t₅ ^ 3 + t₃ ^ 2 * t₅ ^ 2 + t₃ * t₄ * t₅ + t₄ ^ 2))]
    refine Finset.sum_congr rfl fun t₆ _ => ?_
    congr 1
    simp only [cGf]
    ring
  have h5 : ∀ t₁ t₂ t₃ t₄ : F, ∑ t₅ : F, (cQf t₁ t₂ t₃ t₄ t₅ * (t₂ * t₄ + t₃ ^ 3)) ^ m =
      -((t₁ * t₃ + t₂) * (t₂ * t₄ + t₃ ^ 3)) ^ m := fun t₁ t₂ t₃ t₄ => by
    rw [← sum_affine ((t₁ * t₄ + t₃ ^ 2) * (t₂ * t₄ + t₃ ^ 3))]
    refine Finset.sum_congr rfl fun t₅ _ => ?_
    congr 1
    simp only [cQf]
    ring
  have h4 : ∀ t₁ t₂ t₃ : F, ∑ t₄ : F, ((t₁ * t₃ + t₂) * (t₂ * t₄ + t₃ ^ 3)) ^ m =
      -((t₁ * t₃ + t₂) * t₂) ^ m := fun t₁ t₂ t₃ => by
    rw [← sum_affine ((t₁ * t₃ + t₂) * t₃ ^ 3)]
    refine Finset.sum_congr rfl fun t₄ _ => ?_
    congr 1
    ring
  have h3 : ∀ t₁ t₂ : F, ∑ t₃ : F, ((t₁ * t₃ + t₂) * t₂) ^ m = -(t₁ * t₂) ^ m := fun t₁ t₂ => by
    rw [← sum_affine (t₂ * t₂)]
    refine Finset.sum_congr rfl fun t₃ _ => ?_
    congr 1
    ring
  have h2 : ∀ t₁ : F, ∑ t₂ : F, (t₁ * t₂) ^ m = -t₁ ^ m := fun t₁ => by
    rw [← sum_affine 0 t₁]
    refine Finset.sum_congr rfl fun t₂ _ => ?_
    rw [zero_add]
  have h1 : ∑ t₁ : F, t₁ ^ m = -1 := by
    have := sum_affine (0 : F) 1
    simpa using this
  simp only [h6, Finset.sum_neg_distrib, h5, neg_neg, h4, h3, h2, h1]

theorem sum_U0_cQ_cG [Fintype ↥(U0 F)] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    ∑ u : ↥(U0 F), (cQ (u : ↥(cayleyGroup F)) * cG (u : ↥(cayleyGroup F))) ^
      (Fintype.card F - 1) = 1 := by
  rw [← Fintype.sum_bijective uCU (uCU_bijective hF)
    (fun t => (cQf t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 *
      cGf t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2) ^ (Fintype.card F - 1)) _
    (fun t => by rw [uCU, cQ_uC, cG_uC])]
  simp only [Fintype.sum_prod_type]
  exact sum_cQf_cGf

end Sum

end CFSG.Quasithin.B42G2Ten
