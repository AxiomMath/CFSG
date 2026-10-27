module

public import CFSG.Quasithin.Background.JonesParshallCurtisGroupInputs
public import CFSG.Quasithin.Background.SmithB42LnL5Gen

public section

namespace CFSG.Quasithin.B42Ln

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis Matrix

theorem vecMulVec_mulVec_eq (v φ x : Fin 5 → ZMod 2) :
    vecMulVec v φ *ᵥ x = (φ ⬝ᵥ x) • v := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem exists_dot_eq_one : ∀ φ : Fin 5 → ZMod 2, φ ≠ 0 → ∃ x : Fin 5 → ZMod 2, φ ⬝ᵥ x = 1 := by
  decide

theorem exists_dot_one_zero : ∀ φ₁ φ₂ : Fin 5 → ZMod 2, φ₁ ≠ 0 → φ₂ ≠ 0 → φ₁ ≠ φ₂ →
    ∃ x : Fin 5 → ZMod 2, φ₁ ⬝ᵥ x = 1 ∧ φ₂ ⬝ᵥ x = 0 := by
  decide

theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with h | h <;> simp [h]

theorem vecMulVec_inj {v φ v' φ' : Fin 5 → ZMod 2} (hv : v ≠ 0) (hφ : φ ≠ 0) (hv' : v' ≠ 0)
    (h : vecMulVec v φ = vecMulVec v' φ') : v = v' ∧ φ = φ' := by
  obtain ⟨x, hx⟩ := exists_dot_eq_one φ hφ
  have h1 := congrArg (· *ᵥ x) h
  simp only [vecMulVec_mulVec_eq, hx, one_smul] at h1
  have hvv : v = v' := by
    rcases zmod2_cases (φ' ⬝ᵥ x) with h0 | h0
    · rw [h0, zero_smul] at h1
      exact absurd h1 hv
    · rw [h0, one_smul] at h1
      exact h1
  subst hvv
  refine ⟨rfl, ?_⟩
  ext j
  have h2 := congrFun (congrFun h j) j
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hv (funext hall)
  have h3 := congrFun (congrFun h i) j
  simp only [vecMulVec_apply] at h3
  rcases zmod2_cases (v i) with h0 | h0
  · exact absurd h0 hi
  · rw [h0, one_mul, one_mul] at h3
    exact h3

@[expose] def IsTv (γ : G5) (v φ : Fin 5 → ZMod 2) : Prop :=
  (γ : Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 + vecMulVec v φ ∧ v ≠ 0 ∧ φ ≠ 0 ∧ φ ⬝ᵥ v = 0

theorem IsTv.unique {γ : G5} {v φ v' φ' : Fin 5 → ZMod 2} (h : IsTv γ v φ) (h' : IsTv γ v' φ') :
    v = v' ∧ φ = φ' := by
  have : vecMulVec v φ = vecMulVec v' φ' := by
    have := h.1.symm.trans h'.1
    exact add_left_cancel this
  exact vecMulVec_inj h.2.1 h.2.2.1 h'.2.1 this

theorem t0M_eq : t0M = 1 + vecMulVec (Pi.single 0 1) (Pi.single 1 1) := by decide

theorem isTv_conj_t0 (g : G5) :
    IsTv (g * t0 * g⁻¹) ((g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ Pi.single 0 1)
      (Pi.single 1 1 ᵥ* ((g⁻¹ : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2))) := by
  set M := (g : Matrix (Fin 5) (Fin 5) (ZMod 2))
  set Mi := ((g⁻¹ : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2))
  have hMMi : M * Mi = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hMiM : Mi * M = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hcoe : ((g * t0 * g⁻¹ : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = M * t0M * Mi := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcoe, t0M_eq, mul_add, mul_one, add_mul, hMMi, mul_vecMulVec, vecMulVec_mul]
  · intro h0
    have := congrArg (Mi *ᵥ ·) h0
    simp only [mulVec_mulVec, hMiM, one_mulVec, mulVec_zero] at this
    exact absurd (congrFun this 0) (by simp)
  · intro h0
    have := congrArg (· ᵥ* M) h0
    simp only [vecMul_vecMul, hMiM, vecMul_one, zero_vecMul] at this
    exact absurd (congrFun this 1) (by simp)
  · rw [dotProduct_mulVec, vecMul_vecMul, hMiM, vecMul_one]
    decide

theorem tv_mul_tv (v₁ φ₁ v₂ φ₂ : Fin 5 → ZMod 2) :
    (1 + vecMulVec v₁ φ₁) * (1 + vecMulVec v₂ φ₂) =
      1 + vecMulVec v₁ φ₁ + vecMulVec v₂ φ₂ + (φ₁ ⬝ᵥ v₂) • vecMulVec v₁ φ₂ := by
  rw [add_mul, one_mul, mul_add, mul_one, vecMulVec_mul_vecMulVec]
  have : vecMulVec v₁ ((φ₁ ⬝ᵥ v₂) • φ₂) = (φ₁ ⬝ᵥ v₂) • vecMulVec v₁ φ₂ := by
    ext i j
    simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
    ring
  rw [this]
  abel

theorem IsTv.eq_or_eq {b₁ b₂ : G5} {v₁ φ₁ v₂ φ₂ v φ : Fin 5 → ZMod 2} (h₁ : IsTv b₁ v₁ φ₁)
    (h₂ : IsTv b₂ v₂ φ₂) (hcomm : b₁ * b₂ = b₂ * b₁) (h : IsTv (b₁ * b₂) v φ) :
    v₁ = v₂ ∨ φ₁ = φ₂ := by
  by_contra hne
  push Not at hne
  obtain ⟨hv, hφ⟩ := hne
  have hm : ∀ {x y : G5}, ((x * y : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      (x : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (y : Matrix (Fin 5) (Fin 5) (ZMod 2)) := rfl
  have hc := congrArg (fun x : G5 => (x : Matrix (Fin 5) (Fin 5) (ZMod 2))) hcomm
  simp only [hm, h₁.1, h₂.1, tv_mul_tv] at hc
  have hcross : (φ₁ ⬝ᵥ v₂) • vecMulVec v₁ φ₂ = (φ₂ ⬝ᵥ v₁) • vecMulVec v₂ φ₁ := by
    have hc' : 1 + vecMulVec v₁ φ₁ + vecMulVec v₂ φ₂ + (φ₁ ⬝ᵥ v₂) • vecMulVec v₁ φ₂ =
        1 + vecMulVec v₁ φ₁ + vecMulVec v₂ φ₂ + (φ₂ ⬝ᵥ v₁) • vecMulVec v₂ φ₁ := by
      rw [hc]
      abel
    exact add_left_cancel hc'
  have hzero : ∀ {a b c d : Fin 5 → ZMod 2}, a ≠ 0 → d ≠ 0 → a ≠ c →
      (b ⬝ᵥ c) • vecMulVec a d = (d ⬝ᵥ a) • vecMulVec c b → b ⬝ᵥ c = 0 := by
    intro a b c d ha hd hac hx
    rcases zmod2_cases (b ⬝ᵥ c) with h0 | h0
    · exact h0
    · exfalso
      obtain ⟨x, hx1⟩ := exists_dot_eq_one d hd
      have hx' := congrArg (· *ᵥ x) hx
      simp only [h0, one_smul, vecMulVec_mulVec_eq, hx1, Matrix.smul_mulVec] at hx'
      rcases zmod2_cases (d ⬝ᵥ a) with h1 | h1
      · rw [h1, zero_smul] at hx'
        exact ha hx'
      · rw [h1, one_smul] at hx'
        rcases zmod2_cases (b ⬝ᵥ x) with h2 | h2
        · rw [h2, zero_smul] at hx'
          exact ha hx'
        · rw [h2, one_smul] at hx'
          exact hac hx'
  have h12 : φ₁ ⬝ᵥ v₂ = 0 := hzero h₁.2.1 h₂.2.2.1 hv hcross
  have h21 : φ₂ ⬝ᵥ v₁ = 0 := hzero h₂.2.1 h₁.2.2.1 (Ne.symm hv) hcross.symm
  have hp := h.1
  rw [hm, h₁.1, h₂.1, tv_mul_tv, h12, zero_smul, add_zero, add_assoc] at hp
  have hp' : vecMulVec v₁ φ₁ + vecMulVec v₂ φ₂ = vecMulVec v φ := add_left_cancel hp
  obtain ⟨x, hx1, hx2⟩ := exists_dot_one_zero φ₁ φ₂ h₁.2.2.1 h₂.2.2.1 hφ
  obtain ⟨y, hy1, hy2⟩ := exists_dot_one_zero φ₂ φ₁ h₂.2.2.1 h₁.2.2.1 (Ne.symm hφ)
  have ex := congrArg (· *ᵥ x) hp'
  have ey := congrArg (· *ᵥ y) hp'
  simp only [add_mulVec, vecMulVec_mulVec_eq, hx1, hx2, hy1, hy2, one_smul, zero_smul,
    add_zero, zero_add] at ex ey
  rcases zmod2_cases (φ ⬝ᵥ x) with h3 | h3 <;> rcases zmod2_cases (φ ⬝ᵥ y) with h4 | h4 <;>
    simp only [h3, h4, one_smul, zero_smul] at ex ey
  · exact h₁.2.1 ex
  · exact h₁.2.1 ex
  · exact h₂.2.1 ey
  · exact hv (ex.trans ey.symm)

variable {B : Subgroup G5}

theorem common_center_or_axis (hc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (h2 : ∀ a ∈ B, a * a = 1)
    (htv : ∀ b ∈ B, b ≠ 1 → ∃ v φ, IsTv b v φ) :
    (∃ v, ∀ b ∈ B, b ≠ 1 → ∃ φ, IsTv b v φ) ∨ (∃ φ, ∀ b ∈ B, b ≠ 1 → ∃ v, IsTv b v φ) := by
  by_cases hB : ∃ b₁ ∈ B, b₁ ≠ 1
  · obtain ⟨b₁, hb₁, hb₁1⟩ := hB
    obtain ⟨v₁, φ₁, h₁⟩ := htv b₁ hb₁ hb₁1
    have hpair : ∀ b ∈ B, b ≠ 1 → b ≠ b₁ → ∀ {v φ}, IsTv b v φ → v₁ = v ∨ φ₁ = φ := by
      intro b hb hb1 hbb v φ hv
      have hprod : b₁ * b ≠ 1 := by
        intro h0
        apply hbb
        have := congrArg (b₁ * ·) h0
        rw [← mul_assoc, h2 b₁ hb₁, one_mul, mul_one] at this
        exact this
      obtain ⟨v', φ', h'⟩ := htv _ (B.mul_mem hb₁ hb) hprod
      exact h₁.eq_or_eq hv (hc b₁ hb₁ b hb) h'
    by_cases hctr : ∃ b₂ ∈ B, b₂ ≠ 1 ∧ b₂ ≠ b₁ ∧ ∃ φ₂, IsTv b₂ v₁ φ₂
    · left
      obtain ⟨b₂, hb₂, hb₂1, hb₂b₁, φ₂, h₂⟩ := hctr
      have hφ₂ : φ₂ ≠ φ₁ := by
        intro h0
        apply hb₂b₁
        apply Subtype.ext
        rw [h₂.1, h₁.1, h0]
      refine ⟨v₁, fun b hb hb1 => ?_⟩
      obtain ⟨v, φ, hv⟩ := htv b hb hb1
      by_cases hbb₁ : b = b₁
      · subst hbb₁
        exact ⟨φ₁, h₁⟩
      rcases hpair b hb hb1 hbb₁ hv with hvv | hφφ
      · exact ⟨φ, hvv ▸ hv⟩
      · exfalso
        have hvne : v ≠ v₁ := by
          intro h0
          apply hbb₁
          apply Subtype.ext
          rw [hv.1, h₁.1, h0, hφφ]
        have hbb₂ : b ≠ b₂ := by
          intro h0
          subst h0
          exact hvne (hv.unique h₂).1
        have hprod : b₂ * b ≠ 1 := by
          intro h0
          apply hbb₂
          have := congrArg (b₂ * ·) h0
          rw [← mul_assoc, h2 b₂ hb₂, one_mul, mul_one] at this
          exact this
        obtain ⟨v', φ', h'⟩ := htv _ (B.mul_mem hb₂ hb) hprod
        rcases h₂.eq_or_eq hv (hc b₂ hb₂ b hb) h' with h0 | h0
        · exact hvne h0.symm
        · exact hφ₂ (h0.trans hφφ.symm)
    · right
      push Not at hctr
      refine ⟨φ₁, fun b hb hb1 => ?_⟩
      obtain ⟨v, φ, hv⟩ := htv b hb hb1
      by_cases hbb₁ : b = b₁
      · subst hbb₁
        exact ⟨v₁, h₁⟩
      rcases hpair b hb hb1 hbb₁ hv with hvv | hφφ
      · exact absurd (hvv ▸ hv) (hctr b hb hb1 hbb₁ φ)
      · exact ⟨v, hφφ ▸ hv⟩
  · push Not at hB
    left
    exact ⟨0, fun b hb hb1 => absurd (hB b hb) hb1⟩

end CFSG.Quasithin.B42Ln
