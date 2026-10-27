module

public import CFSG.Milestones.ASVolI.A3L3.L3Data
public import CFSG.Milestones.ASVolI.A3L3.Finish

public section

namespace CFSG.ASVolI

open Matrix CFSG.RankThree.SubgroupLists CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3 CFSG.ASVolI.ChA
open scoped MatrixGroups Pointwise

variable {F : Type} [Field F]

@[expose] def burnsideA315y_IsBlock (g : Matrix (Fin 3) (Fin 3) F) : Prop :=
  g 0 2 = 0 ∧ g 1 2 = 0 ∧ g 2 0 = 0 ∧ g 2 1 = 0

theorem burnsideA315y_IsUW_one : burnsideA315y_IsUW (1 : Matrix (Fin 3) (Fin 3) F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp

theorem burnsideA315y_IsUW_mul {g h : Matrix (Fin 3) (Fin 3) F} (hg : burnsideA315y_IsUW g)
    (hh : burnsideA315y_IsUW h) :
    burnsideA315y_IsUW (g * h) ∧ (g * h) 0 2 = g 0 2 + h 0 2 ∧ (g * h) 1 2 = g 1 2 + h 1 2 := by
  obtain ⟨a00, a01, a10, a11, a20, a21, a22⟩ := hg
  obtain ⟨b00, b01, b10, b11, b20, b21, b22⟩ := hh
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, a00, a01, a10, a11, a20, a21, a22, b00, b01, b10,
      b11, b20, b21, b22] <;> ring

theorem burnsideA315y_IsUW_ext {g h : Matrix (Fin 3) (Fin 3) F} (hg : burnsideA315y_IsUW g)
    (hh : burnsideA315y_IsUW h) (h0 : g 0 2 = h 0 2) (h1 : g 1 2 = h 1 2) : g = h := by
  obtain ⟨a00, a01, a10, a11, a20, a21, a22⟩ := hg
  obtain ⟨b00, b01, b10, b11, b20, b21, b22⟩ := hh
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [a00, a01, a10, a11, a20, a21, a22, b00, b01, b10, b11, b20, b21, b22, h0, h1]

theorem burnsideA315y_IsUW_conj {s t e : Matrix (Fin 3) (Fin 3) F} (hst : s * t = 1)
    (hs : burnsideA315y_IsBlock s) (ht : burnsideA315y_IsBlock t) (he : burnsideA315y_IsUW e) :
    burnsideA315y_IsUW (s * e * t) := by
  obtain ⟨s02, s12, s20, s21⟩ := hs
  obtain ⟨t02, t12, t20, t21⟩ := ht
  obtain ⟨e00, e01, e10, e11, e20, e21, e22⟩ := he
  have q00 := congrFun (congrFun hst 0) 0
  have q01 := congrFun (congrFun hst 0) 1
  have q10 := congrFun (congrFun hst 1) 0
  have q11 := congrFun (congrFun hst 1) 1
  have q22 := congrFun (congrFun hst 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, s02, s12, s20, s21, t02, t12,
    t20, t21] at q00 q01 q10 q11 q22
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, s02, s12, s20, s21, t02, t12, t20, t21, e00, e01,
      e10, e11, e20, e21, e22] <;>
    first
      | linear_combination q00
      | linear_combination q01
      | linear_combination q10
      | linear_combination q11
      | linear_combination q22

theorem burnsideA315y_UW_cent {e₁ e₂ g : Matrix (Fin 3) (Fin 3) F} (h1 : burnsideA315y_IsUW e₁)
    (h2 : burnsideA315y_IsUW e₂) (hD : e₁ 0 2 * e₂ 1 2 - e₁ 1 2 * e₂ 0 2 ≠ 0)
    (hg1 : g * e₁ = e₁ * g) (hg2 : g * e₂ = e₂ * g) (hdet : g.det ≠ 0) :
    ∃ w : F, w ≠ 0 ∧ burnsideA315y_IsUW (w⁻¹ • g) := by
  obtain ⟨c00, c11, c01, c10, c20, c21⟩ := burnsideA315y_centralizer_UW h1 h2 hD hg1 hg2
  have hw : g 2 2 ≠ 0 := by
    intro h0
    apply hdet
    rw [Matrix.det_fin_three, c20, c21, h0]
    ring
  refine ⟨g 2 2, hw, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.smul_apply, c00, c11, c01, c10, c20, c21, hw]

theorem burnsideA315y_IsUl_one : burnsideA315y_IsUl (1 : Matrix (Fin 3) (Fin 3) F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp

theorem burnsideA315y_IsUl_mul {g h : Matrix (Fin 3) (Fin 3) F} (hg : burnsideA315y_IsUl g)
    (hh : burnsideA315y_IsUl h) :
    burnsideA315y_IsUl (g * h) ∧ (g * h) 2 0 = g 2 0 + h 2 0 ∧ (g * h) 2 1 = g 2 1 + h 2 1 := by
  obtain ⟨a00, a01, a02, a10, a11, a12, a22⟩ := hg
  obtain ⟨b00, b01, b02, b10, b11, b12, b22⟩ := hh
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, a00, a01, a02, a10, a11, a12, a22, b00, b01, b02,
      b10, b11, b12, b22] <;> ring

theorem burnsideA315y_IsUl_ext {g h : Matrix (Fin 3) (Fin 3) F} (hg : burnsideA315y_IsUl g)
    (hh : burnsideA315y_IsUl h) (h0 : g 2 0 = h 2 0) (h1 : g 2 1 = h 2 1) : g = h := by
  obtain ⟨a00, a01, a02, a10, a11, a12, a22⟩ := hg
  obtain ⟨b00, b01, b02, b10, b11, b12, b22⟩ := hh
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [a00, a01, a02, a10, a11, a12, a22, b00, b01, b02, b10, b11, b12, b22, h0, h1]

theorem burnsideA315y_IsUl_conj {s t e : Matrix (Fin 3) (Fin 3) F} (hst : s * t = 1)
    (hs : burnsideA315y_IsBlock s) (ht : burnsideA315y_IsBlock t) (he : burnsideA315y_IsUl e) :
    burnsideA315y_IsUl (s * e * t) := by
  obtain ⟨s02, s12, s20, s21⟩ := hs
  obtain ⟨t02, t12, t20, t21⟩ := ht
  obtain ⟨e00, e01, e02, e10, e11, e12, e22⟩ := he
  have q00 := congrFun (congrFun hst 0) 0
  have q01 := congrFun (congrFun hst 0) 1
  have q10 := congrFun (congrFun hst 1) 0
  have q11 := congrFun (congrFun hst 1) 1
  have q22 := congrFun (congrFun hst 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, s02, s12, s20, s21, t02, t12,
    t20, t21] at q00 q01 q10 q11 q22
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, s02, s12, s20, s21, t02, t12, t20, t21, e00, e01,
      e02, e10, e11, e12, e22] <;>
    first
      | linear_combination q00
      | linear_combination q01
      | linear_combination q10
      | linear_combination q11
      | linear_combination q22

theorem burnsideA315y_Ul_cent {e₁ e₂ g : Matrix (Fin 3) (Fin 3) F} (h1 : burnsideA315y_IsUl e₁)
    (h2 : burnsideA315y_IsUl e₂) (hD : e₁ 2 0 * e₂ 2 1 - e₁ 2 1 * e₂ 2 0 ≠ 0)
    (hg1 : g * e₁ = e₁ * g) (hg2 : g * e₂ = e₂ * g) (hdet : g.det ≠ 0) :
    ∃ w : F, w ≠ 0 ∧ burnsideA315y_IsUl (w⁻¹ • g) := by
  obtain ⟨c00, c11, c01, c10, c02, c12⟩ := burnsideA315y_centralizer_Ul h1 h2 hD hg1 hg2
  have hw : g 2 2 ≠ 0 := by
    intro h0
    apply hdet
    rw [Matrix.det_fin_three, c02, c12, h0]
    ring
  refine ⟨g 2 2, hw, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.smul_apply, c00, c11, c01, c10, c02, c12, hw]

structure burnsideA315y_Shape (F : Type) [Field F] where
  P : Matrix (Fin 3) (Fin 3) F → Prop
  f₀ : Matrix (Fin 3) (Fin 3) F → F
  f₁ : Matrix (Fin 3) (Fin 3) F → F
  one : P 1 ∧ f₀ 1 = 0 ∧ f₁ 1 = 0
  mul : ∀ g h, P g → P h → P (g * h) ∧ f₀ (g * h) = f₀ g + f₀ h ∧ f₁ (g * h) = f₁ g + f₁ h
  ext : ∀ g h, P g → P h → f₀ g = f₀ h → f₁ g = f₁ h → g = h
  diag : ∀ g, P g → g 0 0 = 1
  conj : ∀ s t e, s * t = 1 → burnsideA315y_IsBlock s → burnsideA315y_IsBlock t → P e →
    P (s * e * t)
  cent : ∀ e₁ e₂ g, P e₁ → P e₂ → f₀ e₁ * f₁ e₂ - f₁ e₁ * f₀ e₂ ≠ 0 → g * e₁ = e₁ * g →
    g * e₂ = e₂ * g → g.det ≠ 0 → ∃ w : F, w ≠ 0 ∧ P (w⁻¹ • g)
  basis : ∀ {x y c : F} {Da Db : GL (Fin 3) F}, (2 : F) ≠ 0 → x ^ 2 + y ^ 2 ≠ 0 → c ≠ 0 →
    (Da : Matrix (Fin 3) (Fin 3) F) = blkMat (burnsideA315y_qa F) 1 →
    (Db : Matrix (Fin 3) (Fin 3) F) = blkMat (c • burnsideA315y_qb x y) 1 →
    ∀ E : Subgroup (GL (Fin 3) F), (∀ e ∈ E, P (e : Matrix (Fin 3) (Fin 3) F)) → E ≠ ⊥ →
    (∀ e ∈ E, Da * e * Da⁻¹ ∈ E ∧ Da⁻¹ * e * Da ∈ E) →
    (∀ e ∈ E, Db * e * Db⁻¹ ∈ E ∧ Db⁻¹ * e * Db ∈ E) →
    ∃ e₁ ∈ E, ∃ e₂ ∈ E, f₀ (e₁ : Matrix (Fin 3) (Fin 3) F) * f₁ (e₂ : Matrix (Fin 3) (Fin 3) F) -
      f₁ (e₁ : Matrix (Fin 3) (Fin 3) F) * f₀ (e₂ : Matrix (Fin 3) (Fin 3) F) ≠ 0

@[expose] def burnsideA315y_shapeUW (F : Type) [Field F] : burnsideA315y_Shape F where
  P := burnsideA315y_IsUW
  f₀ g := g 0 2
  f₁ g := g 1 2
  one := ⟨burnsideA315y_IsUW_one, by simp, by simp⟩
  mul _ _ hg hh := burnsideA315y_IsUW_mul hg hh
  ext _ _ hg hh h0 h1 := burnsideA315y_IsUW_ext hg hh h0 h1
  diag _ hg := hg.1
  conj _ _ _ hst hs ht he := burnsideA315y_IsUW_conj hst hs ht he
  cent _ _ _ h1 h2 hD hg1 hg2 hdet := burnsideA315y_UW_cent h1 h2 hD hg1 hg2 hdet
  basis h2 hxy hc hDa hDb E hE hne hDaE hDbE :=
    burnsideA315y_UW_basis h2 hxy hc hDa hDb E hE hne (fun e he => (hDaE e he).1)
      (fun e he => (hDbE e he).1)

@[expose] def burnsideA315y_shapeUl (F : Type) [Field F] : burnsideA315y_Shape F where
  P := burnsideA315y_IsUl
  f₀ g := g 2 0
  f₁ g := g 2 1
  one := ⟨burnsideA315y_IsUl_one, by simp, by simp⟩
  mul _ _ hg hh := burnsideA315y_IsUl_mul hg hh
  ext _ _ hg hh h0 h1 := burnsideA315y_IsUl_ext hg hh h0 h1
  diag _ hg := hg.1
  conj _ _ _ hst hs ht he := burnsideA315y_IsUl_conj hst hs ht he
  cent _ _ _ h1 h2 hD hg1 hg2 hdet := burnsideA315y_Ul_cent h1 h2 hD hg1 hg2 hdet
  basis h2 hxy hc hDa hDb E hE hne hDaE hDbE :=
    burnsideA315y_Ul_basis h2 hxy hc hDa hDb E hE hne (fun e he => (hDaE e he).2)
      (fun e he => (hDbE e he).2)

theorem burnsideA315y_Shape.pow (σ : burnsideA315y_Shape F) {g : Matrix (Fin 3) (Fin 3) F}
    (hg : σ.P g) (n : ℕ) :
    σ.P (g ^ n) ∧ σ.f₀ (g ^ n) = n * σ.f₀ g ∧ σ.f₁ (g ^ n) = n * σ.f₁ g := by
  induction n with
  | zero =>
    obtain ⟨h1, h2, h3⟩ := σ.one
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    exact ⟨h1, h2, h3⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := σ.mul _ _ ih.1 hg
    rw [pow_succ]
    refine ⟨h1, ?_, ?_⟩
    · rw [h2, ih.2.1]
      push_cast
      ring
    · rw [h3, ih.2.2]
      push_cast
      ring

theorem burnsideA315y_cramer {u₀ u₁ v₀ v₁ : F} (a b : F) (hD : u₀ * v₁ - u₁ * v₀ ≠ 0) :
    (a * v₁ - b * v₀) / (u₀ * v₁ - u₁ * v₀) * u₀ +
        (u₀ * b - u₁ * a) / (u₀ * v₁ - u₁ * v₀) * v₀ = a ∧
      (a * v₁ - b * v₀) / (u₀ * v₁ - u₁ * v₀) * u₁ +
        (u₀ * b - u₁ * a) / (u₀ * v₁ - u₁ * v₀) * v₁ = b := by
  constructor
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD]
    ring
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD]
    ring

namespace burnsideA315y_Model

variable {X : Type} [Group X] (M : burnsideA315y_Model F X) (σ : burnsideA315y_Shape F)

@[expose] def ShapeBasis (E : Subgroup ↥M.Γ) : Prop :=
  ∃ e₁ ∈ E, ∃ e₂ ∈ E,
    σ.f₀ ((e₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        σ.f₁ ((e₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) -
      σ.f₁ ((e₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        σ.f₀ ((e₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ≠ 0

theorem shape_basis {E : Subgroup ↥M.Γ}
    (hP : ∀ e ∈ E, σ.P ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) (hne : E ≠ ⊥)
    (hDa : ∀ e ∈ E, M.Da⁻¹ * e * M.Da ∈ E ∧ M.Da * e * M.Da⁻¹ ∈ E)
    (hDb : ∀ e ∈ E, M.Db⁻¹ * e * M.Db ∈ E ∧ M.Db * e * M.Db⁻¹ ∈ E) :
    M.ShapeBasis σ E := by
  have hne' : E.map M.Γ.subtype ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro e he
    have h1 : M.Γ.subtype e ∈ E.map M.Γ.subtype := ⟨e, he, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact M.Γ.subtype_injective (by rw [h1, map_one])
  obtain ⟨_, ⟨e₁, he₁, rfl⟩, _, ⟨e₂, he₂, rfl⟩, hD⟩ := σ.basis M.two_ne M.hxy M.hcc M.Da_val
    M.Db_val (E.map M.Γ.subtype) (by rintro _ ⟨e, he, rfl⟩; exact hP e he) hne'
    (by
      rintro _ ⟨e, he, rfl⟩
      exact ⟨⟨M.Da * e * M.Da⁻¹, (hDa e he).2, by simp⟩,
        ⟨M.Da⁻¹ * e * M.Da, (hDa e he).1, by simp⟩⟩)
    (by
      rintro _ ⟨e, he, rfl⟩
      exact ⟨⟨M.Db * e * M.Db⁻¹, (hDb e he).2, by simp⟩,
        ⟨M.Db⁻¹ * e * M.Db, (hDb e he).1, by simp⟩⟩)
  exact ⟨e₁, he₁, e₂, he₂, hD⟩

theorem shape_exists {E : Subgroup ↥M.Γ} (hprime : ∀ a : F, ∃ n : ℕ, (n : F) = a)
    (hP : ∀ e ∈ E, σ.P ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) (hB : M.ShapeBasis σ E)
    (a b : F) :
    ∃ e ∈ E, σ.f₀ ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = a ∧
      σ.f₁ ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = b := by
  obtain ⟨e₁, he₁, e₂, he₂, hD⟩ := hB
  obtain ⟨m, hm⟩ := hprime
    ((a * σ.f₁ ((e₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) -
        b * σ.f₀ ((e₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) /
      (σ.f₀ ((e₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          σ.f₁ ((e₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) -
        σ.f₁ ((e₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          σ.f₀ ((e₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)))
  obtain ⟨n, hn⟩ := hprime
    ((σ.f₀ ((e₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * b -
        σ.f₁ ((e₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * a) /
      (σ.f₀ ((e₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          σ.f₁ ((e₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) -
        σ.f₁ ((e₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          σ.f₀ ((e₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)))
  have hmat : (((e₁ ^ m * e₂ ^ n : ↥M.Γ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((e₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ m *
        ((e₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ n := by
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val]
  obtain ⟨p₁, p₁₀, p₁₁⟩ := σ.pow (hP e₁ he₁) m
  obtain ⟨p₂, p₂₀, p₂₁⟩ := σ.pow (hP e₂ he₂) n
  obtain ⟨-, q₀, q₁⟩ := σ.mul _ _ p₁ p₂
  refine ⟨e₁ ^ m * e₂ ^ n, E.mul_mem (E.pow_mem he₁ m) (E.pow_mem he₂ n), ?_, ?_⟩
  · rw [hmat, q₀, p₁₀, p₂₀, hm, hn]
    exact (burnsideA315y_cramer a b hD).1
  · rw [hmat, q₁, p₁₁, p₂₁, hm, hn]
    exact (burnsideA315y_cramer a b hD).2

theorem shape_mem {E : Subgroup ↥M.Γ} (hprime : ∀ a : F, ∃ n : ℕ, (n : F) = a)
    (hP : ∀ e ∈ E, σ.P ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) (hB : M.ShapeBasis σ E)
    {g : ↥M.Γ} (hg : σ.P ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) : g ∈ E := by
  obtain ⟨e, he, h0, h1⟩ := M.shape_exists σ hprime hP hB
    (σ.f₀ ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
    (σ.f₁ ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
  have hge : g = e := Subtype.ext (Units.ext (σ.ext _ _ hg (hP e he) h0.symm h1.symm))
  rw [hge]
  exact he

theorem shape_c_mem {E : Subgroup ↥M.Γ} (hprime : ∀ a : F, ∃ n : ℕ, (n : F) = a)
    (hP : ∀ e ∈ E, σ.P ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) (hB : M.ShapeBasis σ E)
    {g : ↥M.Γ} (hg : ∀ e ∈ E, g * e = e * g) : M.c g ∈ E.map M.c := by
  obtain ⟨e₁, he₁, e₂, he₂, hD⟩ := hB
  have hm : ∀ e ∈ E, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    intro e he
    have h := congrArg (fun k : ↥M.Γ => ((k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
      (hg e he)
    simpa only [Subgroup.coe_mul, Units.val_mul] using h
  have hdet : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (g : GL (Fin 3) F).isUnit).ne_zero
  obtain ⟨w, hw, hPw⟩ := σ.cent _ _ _ (hP e₁ he₁) (hP e₂ he₂) hD (hm e₁ he₁) (hm e₂ he₂) hdet
  obtain ⟨e, he, h0, h1⟩ := M.shape_exists σ hprime hP ⟨e₁, he₁, e₂, he₂, hD⟩
    (σ.f₀ (w⁻¹ • ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)))
    (σ.f₁ (w⁻¹ • ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)))
  have hee := σ.ext _ _ (hP e he) hPw h0 h1
  have hge : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      w • ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [hee, smul_smul, mul_inv_cancel₀ hw, one_smul]
  have hscal : ((g * e⁻¹ : ↥M.Γ) : GL (Fin 3) F) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 w hw) := by
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, hge, Matrix.smul_mul, Units.mul_inv,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
    rfl
  have hc1 : M.c (g * e⁻¹) = 1 := (M.ker_c _).mpr ⟨_, hscal⟩
  rw [map_mul, map_inv, mul_inv_eq_one] at hc1
  exact ⟨e, he, hc1.symm⟩

theorem shape_c_inj {E : Subgroup ↥M.Γ}
    (hP : ∀ e ∈ E, σ.P ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) {e : ↥M.Γ} (he : e ∈ E)
    (h1 : M.c e = 1) : e = 1 := by
  obtain ⟨μ, hμ⟩ := M.exists_scalar_of_c_eq_one h1
  have h00 := σ.diag _ (hP e he)
  rw [hμ] at h00
  have hμ1 : μ = 1 := Units.ext (by simpa [Matrix.GeneralLinearGroup.coe_scalar] using h00)
  apply Subtype.ext
  rw [hμ, hμ1, map_one, Subgroup.coe_one]

theorem shape_conj {s e : ↥M.Γ} (hs : s ∈ M.S₀)
    (he : σ.P ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) :
    σ.P (((s * e * s⁻¹ : ↥M.Γ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  have h1 := M.C₁_block (M.S₀_le_C₁ hs)
  have h2 := M.C₁_block (M.S₀_le_C₁ (M.S₀.inv_mem hs))
  have hst : ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (((s⁻¹ : ↥M.Γ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [Subgroup.coe_inv, Units.mul_inv]
  have h := σ.conj _ _ _ hst h1 h2 he
  simpa only [Subgroup.coe_mul, Units.val_mul] using h

@[expose] noncomputable def shapeHom (E : Subgroup ↥M.Γ)
    (hP : ∀ e ∈ E, σ.P ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) :
    ↥E →* Multiplicative (Fin 2 → F) where
  toFun e := Multiplicative.ofAdd
    ![σ.f₀ (((e : ↥M.Γ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F),
      σ.f₁ (((e : ↥M.Γ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)]
  map_one' := by
    obtain ⟨-, h0, h1⟩ := σ.one
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp [h0, h1]
  map_mul' a b := by
    obtain ⟨-, h0, h1⟩ := σ.mul _ _ (hP a a.2) (hP b b.2)
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp [h0, h1]

theorem shapeHom_apply (E : Subgroup ↥M.Γ)
    (hP : ∀ e ∈ E, σ.P ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) (e : ↥E) :
    Multiplicative.toAdd (M.shapeHom σ E hP e) =
      ![σ.f₀ (((e : ↥M.Γ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F),
        σ.f₁ (((e : ↥M.Γ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)] :=
  rfl

theorem shape_conclusion (hprime : ∀ a : F, ∃ n : ℕ, (n : F) = a) {B' : Subgroup X}
    {E : Subgroup ↥M.Γ} (hne : E ≠ ⊥)
    (hP : ∀ e ∈ E, σ.P ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) (hEB : E.map M.c ≤ B')
    (hDa : ∀ e ∈ E, M.Da⁻¹ * e * M.Da ∈ E ∧ M.Da * e * M.Da⁻¹ ∈ E)
    (hDb : ∀ e ∈ E, M.Db⁻¹ * e * M.Db ∈ E ∧ M.Db * e * M.Db⁻¹ ∈ E)
    (hlift : ∀ b ∈ B', ∃ g : ↥M.Γ, M.c g = b ∧ ∀ e ∈ E, g * e = e * g) :
    B' = E.map M.c ∧ Nonempty (↥B' ≃* Multiplicative (Fin 2 → F)) ∧
      M.S ≤ Subgroup.normalizer (B' : Set X) ∧ B' ≠ ⊥ ∧
      ∀ C : Subgroup X, C ≤ B' → M.S ≤ Subgroup.normalizer (C : Set X) → C = ⊥ ∨ C = B' := by
  have hB := M.shape_basis σ hP hne hDa hDb
  have hBeq : B' = E.map M.c := by
    refine le_antisymm (fun b hb => ?_) hEB
    obtain ⟨g, rfl, hg⟩ := hlift b hb
    exact M.shape_c_mem σ hprime hP hB hg
  refine ⟨hBeq, ?_, ?_, ?_, ?_⟩
  ·
    have hinj : ∀ h ∈ E, M.c h = 1 → h = 1 := fun h hh h1 => M.shape_c_inj σ hP hh h1
    refine ⟨(MulEquiv.subgroupCongr hBeq).trans ((burnsideA315y_equivMap M.c E hinj).symm.trans
      (MulEquiv.ofBijective (M.shapeHom σ E hP) ⟨?_, ?_⟩))⟩
    · intro a b hab
      have h := congrArg Multiplicative.toAdd hab
      rw [shapeHom_apply, shapeHom_apply] at h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      exact Subtype.ext (Subtype.ext (Units.ext (σ.ext _ _ (hP a a.2) (hP b b.2) h0 h1)))
    · intro v
      obtain ⟨e, he, h0, h1⟩ := M.shape_exists σ hprime hP hB (Multiplicative.toAdd v 0)
        (Multiplicative.toAdd v 1)
      refine ⟨⟨e, he⟩, ?_⟩
      apply Multiplicative.toAdd.injective
      rw [shapeHom_apply]
      funext i
      fin_cases i <;> simp [h0, h1]
  ·
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro b
    rw [hBeq]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨s * e * s⁻¹, M.shape_mem σ hprime hP hB (M.shape_conj σ hs (hP e he)),
        by rw [map_mul, map_mul, map_inv]⟩
    · rintro ⟨e, he, he'⟩
      have hmem := M.shape_mem σ hprime hP hB (M.shape_conj σ (M.S₀.inv_mem hs) (hP e he))
      rw [inv_inv] at hmem
      refine ⟨s⁻¹ * e * s, hmem, ?_⟩
      rw [map_mul, map_mul, map_inv, he']
      group
  ·
    rw [hBeq]
    intro h
    apply hne
    rw [eq_bot_iff]
    intro e he
    rw [Subgroup.mem_bot]
    have h1 : M.c e ∈ E.map M.c := ⟨e, he, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    exact M.shape_c_inj σ hP he h1
  ·
    intro C hCB hSC
    by_cases hC : C = ⊥
    · exact Or.inl hC
    right
    refine le_antisymm hCB ?_
    have hP' : ∀ e ∈ E ⊓ C.comap M.c, σ.P ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) :=
      fun e he => hP e he.1
    have hne' : E ⊓ C.comap M.c ≠ ⊥ := by
      obtain ⟨⟨x, hxC⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hC
      have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
      have hxB : x ∈ E.map M.c := hBeq ▸ hCB hxC
      obtain ⟨e, he, rfl⟩ := hxB
      intro h
      have h1 : e ∈ E ⊓ C.comap M.c := ⟨he, hxC⟩
      rw [h, Subgroup.mem_bot] at h1
      exact hx1' (by rw [h1, map_one])
    have hcC : ∀ D ∈ M.S₀, ∀ e : ↥M.Γ, M.c e ∈ C →
        M.c (D⁻¹ * e * D) ∈ C ∧ M.c (D * e * D⁻¹) ∈ C := by
      intro D hD e he
      have hN : M.c D ∈ Subgroup.normalizer (C : Set X) := hSC ⟨D, hD, rfl⟩
      have hN' := Subgroup.inv_mem _ hN
      constructor
      · have h := (Subgroup.mem_normalizer_iff.mp hN' (M.c e)).mp he
        rw [inv_inv] at h
        rw [map_mul, map_mul, map_inv]
        exact h
      · have h := (Subgroup.mem_normalizer_iff.mp hN (M.c e)).mp he
        rw [map_mul, map_mul, map_inv]
        exact h
    have hDa' : ∀ e ∈ E ⊓ C.comap M.c, M.Da⁻¹ * e * M.Da ∈ E ⊓ C.comap M.c ∧
        M.Da * e * M.Da⁻¹ ∈ E ⊓ C.comap M.c := fun e he =>
      ⟨⟨(hDa e he.1).1, (hcC M.Da M.Da_mem e he.2).1⟩,
        ⟨(hDa e he.1).2, (hcC M.Da M.Da_mem e he.2).2⟩⟩
    have hDb' : ∀ e ∈ E ⊓ C.comap M.c, M.Db⁻¹ * e * M.Db ∈ E ⊓ C.comap M.c ∧
        M.Db * e * M.Db⁻¹ ∈ E ⊓ C.comap M.c := fun e he =>
      ⟨⟨(hDb e he.1).1, (hcC M.Db M.Db_mem e he.2).1⟩,
        ⟨(hDb e he.1).2, (hcC M.Db M.Db_mem e he.2).2⟩⟩
    have hB' := M.shape_basis σ hP' hne' hDa' hDb'
    intro b hb
    rw [hBeq] at hb
    obtain ⟨e, he, rfl⟩ := hb
    exact (M.shape_mem σ hprime hP' hB' (hP e he)).2

end burnsideA315y_Model

theorem burnsideA315y_l3_natCast_surj [Finite F] {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p) :
    ∀ a : F, ∃ n : ℕ, (n : F) = a := by
  have := Fintype.ofFinite F
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let ψ : ZMod p ≃+* F :=
    ZMod.ringEquivOfPrime F Fact.out (by rw [← Nat.card_eq_fintype_card, hF])
  intro a
  refine ⟨(ψ.symm a).val, ?_⟩
  rw [← map_natCast ψ, ZMod.natCast_zmod_val, RingEquiv.apply_symm_apply]

theorem burnsideA315y_E_of_shape [Finite F] {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p)
    (M : burnsideA315y_Model F (MulAut PSL(3, F)))
    (hc : ∀ g : ↥M.Γ, M.c g = psl3DiagAut (g : GL (Fin 3) F)) (σ : burnsideA315y_Shape F)
    {B' : Subgroup (MulAut PSL(3, F))} {E : Subgroup ↥M.Γ} (hne : E ≠ ⊥)
    (hdet : ∀ e ∈ E, ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1)
    (hP : ∀ e ∈ E, σ.P ((e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) (hEB : E.map M.c ≤ B')
    (hDa : ∀ e ∈ E, M.Da⁻¹ * e * M.Da ∈ E ∧ M.Da * e * M.Da⁻¹ ∈ E)
    (hDb : ∀ e ∈ E, M.Db⁻¹ * e * M.Db ∈ E ∧ M.Db * e * M.Db⁻¹ ∈ E)
    (hlift : ∀ b ∈ B', ∃ g : ↥M.Γ, M.c g = b ∧ ∀ e ∈ E, g * e = e * g) :
    B' ≤ (MulAut.conj : PSL(3, F) →* MulAut PSL(3, F)).range ∧
    CFSG.Quasithin.IsElemAbelianOfRank p 2 ↥B' ∧
    M.S ≤ Subgroup.normalizer (B' : Set (MulAut PSL(3, F))) ∧ B' ≠ ⊥ ∧
    ∀ C : Subgroup (MulAut PSL(3, F)), C ≤ B' →
      M.S ≤ Subgroup.normalizer (C : Set (MulAut PSL(3, F))) → C = ⊥ ∨ C = B' := by
  have := Fintype.ofFinite F
  let ψ : ZMod p ≃+* F :=
    ZMod.ringEquivOfPrime F Fact.out (by rw [← Nat.card_eq_fintype_card, hF])
  obtain ⟨hB, ⟨φ⟩, hN, hne', hirr⟩ :=
    M.shape_conclusion σ (burnsideA315y_l3_natCast_surj hF) hne hP hEB hDa hDb hlift
  refine ⟨?_, Nonempty.intro (φ.trans (AddEquiv.toMultiplicative
    (AddEquiv.piCongrRight fun _ => ψ.symm.toAddEquiv))), hN, hne', hirr⟩
  rw [hB]
  rintro _ ⟨e, he, rfl⟩
  have hd : Matrix.GeneralLinearGroup.det (e : GL (Fin 3) F) = 1 :=
    Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, hdet e he, Units.val_one])
  rw [hc]
  exact burnsideA315h_diag_mem_inn_of_det (by rw [hd]; exact one_mem _)

theorem burnsideA315y_l3_E {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p) {x y : F} {hxy : x ^ 2 + y ^ 2 = -1} {two_ne : (2 : F) ≠ 0}
    (B' : Subgroup (MulAut PSL(3, F)))
    (hE : (burnsideA315y_l3Model x y hxy two_ne).DichE B') :
    B' ≤ (MulAut.conj : PSL(3, F) →* MulAut PSL(3, F)).range ∧
    CFSG.Quasithin.IsElemAbelianOfRank p 2 ↥B' ∧
    (burnsideA315y_l3Model x y hxy two_ne).S ≤ Subgroup.normalizer (B' : Set (MulAut PSL(3, F))) ∧
    B' ≠ ⊥ ∧
    ∀ C : Subgroup (MulAut PSL(3, F)), C ≤ B' →
      (burnsideA315y_l3Model x y hxy two_ne).S ≤ Subgroup.normalizer (C : Set (MulAut PSL(3, F))) →
        C = ⊥ ∨ C = B' := by
  obtain ⟨E, hne, hdet, hshape, hEB, hDa, hDb, hlift⟩ := hE
  rcases hshape with h | h
  · exact burnsideA315y_E_of_shape hF _ (fun g => burnsideA315y_l3Model_c g)
      (burnsideA315y_shapeUW F) hne hdet h hEB hDa hDb hlift
  · exact burnsideA315y_E_of_shape hF _ (fun g => burnsideA315y_l3Model_c g)
      (burnsideA315y_shapeUl F) hne hdet h hEB hDa hDb hlift

end CFSG.ASVolI
