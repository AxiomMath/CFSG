module

public import CFSG.Quasithin.Background.P3Sp44K
public import CFSG.Quasithin.Background.P3Sp44Comm

public section

namespace CFSG.Quasithin

namespace G11

namespace G118

open Matrix CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

theorem sp44_smul_eq (s s' : K) (h : ∀ x : Fin 2 ⊕ Fin 2 → K, s • x = s' • x) : s = s' := by
  have := congrArg (fun x : Fin 2 ⊕ Fin 2 → K => x (Sum.inl 0)) (h (Pi.single (Sum.inl 0) 1))
  simpa using this

theorem sp44_semilinear_apply (a : (Fin 2 ⊕ Fin 2 → K) ≃+ (Fin 2 ⊕ Fin 2 → K))
    (hainv : ∀ g : GL (Fin 2 ⊕ Fin 2) K, g ∈ StatedSp 2 K →
      ∃ g' : GL (Fin 2 ⊕ Fin 2) K, g' ∈ StatedSp 2 K ∧ ∀ v,
        a.symm ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
          (g' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ a.symm v)
    (t : K) : ∃ s : K, ∀ w, a (t • w) = s • a w := by
  let f : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K) :=
    (a : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K)).comp
      ((AddMonoidHom.mk' (fun x : Fin 2 ⊕ Fin 2 → K => t • x) (fun x y => smul_add t x y)).comp
        (a.symm : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K)))
  have hf : ∀ g ∈ StatedSp 2 K, ∀ v,
      f ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
        (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ f v := by
    intro g hg v
    obtain ⟨g', hg', hgg⟩ := hainv g hg
    have hconj : ∀ x, a ((g' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ x) =
        (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ a x := by
      intro x
      have := hgg (a x)
      rw [AddEquiv.symm_apply_apply] at this
      rw [← this, AddEquiv.apply_symm_apply]
    simp only [f, AddMonoidHom.comp_apply, AddMonoidHom.coe_ofClass, AddMonoidHom.mk'_apply]
    rw [hgg v, ← Matrix.mulVec_smul, hconj]
  obtain ⟨p, hp⟩ := sp44_commutant f hf
  refine ⟨p, fun w => ?_⟩
  have := hp (a w)
  simpa [f] using this

theorem sp44_semilinear (a : (Fin 2 ⊕ Fin 2 → K) ≃+ (Fin 2 ⊕ Fin 2 → K))
    (hainv : ∀ g : GL (Fin 2 ⊕ Fin 2) K, g ∈ StatedSp 2 K →
      ∃ g' : GL (Fin 2 ⊕ Fin 2) K, g' ∈ StatedSp 2 K ∧ ∀ v,
        a.symm ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
          (g' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ a.symm v) :
    ∃ θ : K →+* K, ∀ t w, a (t • w) = θ t • a w := by
  choose θ hθ using sp44_semilinear_apply a hainv
  have key : ∀ (s s' : K), (∀ w, s • a w = s' • a w) → s = s' := by
    intro s s' h
    apply sp44_smul_eq
    intro x
    obtain ⟨w, rfl⟩ := a.surjective x
    exact h w
  have h1 : θ 1 = 1 := key _ _ fun w => by rw [← hθ 1 w, one_smul, one_smul]
  have hmul : ∀ t u, θ (t * u) = θ t * θ u := fun t u => key _ _ fun w => by
    rw [← hθ, mul_smul, hθ, hθ, mul_smul]
  have hadd : ∀ t u, θ (t + u) = θ t + θ u := fun t u => key _ _ fun w => by
    rw [← hθ, add_smul, map_add, hθ, hθ, add_smul]
  have h0 : θ 0 = 0 := by
    have := hadd 0 0
    simpa using this
  exact ⟨{ toFun := θ, map_one' := h1, map_mul' := hmul, map_zero' := h0, map_add' := hadd }, hθ⟩

theorem sp44_lin_or_frob [Finite K] (hK : Nat.card K = 4)
    (a : (Fin 2 ⊕ Fin 2 → K) ≃+ (Fin 2 ⊕ Fin 2 → K))
    (hainv : ∀ g : GL (Fin 2 ⊕ Fin 2) K, g ∈ StatedSp 2 K →
      ∃ g' : GL (Fin 2 ⊕ Fin 2) K, g' ∈ StatedSp 2 K ∧ ∀ v,
        a.symm ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
          (g' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ a.symm v) :
    (∀ (t : K) (w : Fin 2 ⊕ Fin 2 → K), a (t • w) = t • a w) ∨
      (∀ (t : K) (w : Fin 2 ⊕ Fin 2 → K), a (t • w) = t ^ 2 • a w) := by
  obtain ⟨θ, hθ⟩ := sp44_semilinear a hainv
  rcases sp44_ringHom_cases hK θ with h | h
  · left
    intro t w
    rw [hθ, h]
  · right
    intro t w
    rw [hθ, h]


theorem sp44_form_twist (θ : K →+* K) (hθθ : ∀ t, θ (θ t) = t)
    (a : (Fin 2 ⊕ Fin 2 → K) ≃+ (Fin 2 ⊕ Fin 2 → K))
    (hθ : ∀ (t : K) (w : Fin 2 ⊕ Fin 2 → K), a (t • w) = θ t • a w)
    (ha : ∀ g : GL (Fin 2 ⊕ Fin 2) K, g ∈ StatedSp 2 K →
      ∃ g' : GL (Fin 2 ⊕ Fin 2) K, g' ∈ StatedSp 2 K ∧ ∀ v,
        a ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
          (g' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ a v) :
    ∃ μ : K, ∀ v w, θ (sp44ω (a v) (a w)) = μ * sp44ω v w := by
  refine sp44_form_mul (fun v w => θ (sp44ω (a v) (a w))) ?_ ?_ ?_ ?_ ?_
  · intro v v' w
    simp only [map_add, sp44ω_add_left]
  · intro t v w
    simp only [hθ, sp44ω_smul_left, map_mul, hθθ]
  · intro v w w'
    simp only [map_add, sp44ω_add_right]
  · intro t v w
    simp only [hθ, sp44ω_smul_right, map_mul, hθθ]
  · intro g hg v w
    obtain ⟨g', hg', h⟩ := ha g hg
    simp only [h]
    rw [sp44ω_mulVec _ ((sp44_mem_iff g').1 hg')]


theorem sp44ω_basis :
    sp44ω (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) (Pi.single (Sum.inr 0) 1) = 1 := by
  simp [sp44ω, Matrix.mulVec, dotProduct, fromBlocks, Pi.single_apply]

theorem sp44ω_ne_zero : ∃ v w : Fin 2 ⊕ Fin 2 → K, sp44ω v w = 1 :=
  ⟨_, _, sp44ω_basis⟩

theorem sp44_lin_isometry [Finite K] (hK : Nat.card K = 4)
    (c : (Fin 2 ⊕ Fin 2 → K) ≃+ (Fin 2 ⊕ Fin 2 → K))
    (hlin : ∀ (t : K) (w : Fin 2 ⊕ Fin 2 → K), c (t • w) = t • c w)
    (hc2 : ∀ v, c (c v) = v)
    (hc : ∀ g : GL (Fin 2 ⊕ Fin 2) K, g ∈ StatedSp 2 K →
      ∃ g' : GL (Fin 2 ⊕ Fin 2) K, g' ∈ StatedSp 2 K ∧ ∀ v,
        c ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
          (g' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ c v) :
    ∀ v w, sp44ω (c v) (c w) = sp44ω v w := by
  obtain ⟨μ, hμ⟩ := sp44_form_twist (RingHom.id K) (fun _ => rfl) c hlin hc
  simp only [RingHom.id_apply] at hμ
  have hsq : μ * μ = 1 := by
    obtain ⟨v, w, hvw⟩ := sp44ω_ne_zero (K := K)
    have h1 := hμ (c v) (c w)
    rw [hc2, hc2, hμ v w, hvw] at h1
    simpa using h1.symm
  have : CharP K 2 := sp44_charTwo hK
  have hμ1 : μ = 1 := by
    have : (μ - 1) * (μ - 1) = 0 := by
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination hsq + (1 - μ) * h2
    exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
  intro v w
  rw [hμ, hμ1, one_mul]


theorem sp44_card_le_two_mul [Finite K]
    (A : Subgroup (Equiv.Perm (Fin 2 ⊕ Fin 2 → K))) [Finite A]
    (hK : Nat.card K = 4)
    (hdich : ∀ a : Equiv.Perm (Fin 2 ⊕ Fin 2 → K), a ∈ A →
      (∀ (t : K) (w : Fin 2 ⊕ Fin 2 → K), a (t • w) = t • a w) ∨
      (∀ (t : K) (w : Fin 2 ⊕ Fin 2 → K), a (t • w) = t ^ 2 • a w))
    (a₀ : Equiv.Perm (Fin 2 ⊕ Fin 2 → K)) (ha₀ : a₀ ∈ A)
    (hfrob : ∀ (t : K) (w : Fin 2 ⊕ Fin 2 → K), a₀ (t • w) = t ^ 2 • a₀ w) :
    ∃ C : Subgroup A,
      (∀ a : A, a ∈ C ↔ ∀ (t : K) (w : Fin 2 ⊕ Fin 2 → K), a.1 (t • w) = t • a.1 w) ∧
      Nat.card A ≤ 2 * Nat.card C := by
  let C : Subgroup A :=
    { carrier := {a | ∀ (t : K) (w : Fin 2 ⊕ Fin 2 → K), a.1 (t • w) = t • a.1 w}
      one_mem' := fun t w => rfl
      mul_mem' := fun {a b} ha hb t w => by
        show a.1 (b.1 (t • w)) = t • a.1 (b.1 w)
        rw [hb, ha]
      inv_mem' := fun {a} ha t w => by
        show a.1⁻¹ (t • w) = t • a.1⁻¹ w
        apply a.1.injective
        have e1 : a.1 (a.1⁻¹ (t • w)) = t • w := by simp
        have e2 : a.1 (t • a.1⁻¹ w) = t • w := by
          have := ha t (a.1⁻¹ w)
          rw [this]
          simp
        exact e1.trans e2.symm }
  refine ⟨C, fun a => Iff.rfl, ?_⟩
  let a₀' : A := ⟨a₀, ha₀⟩
  have hmul : ∀ a : A, a ∉ C → a₀' * a ∈ C := by
    intro a ha t w
    have hf : ∀ (t : K) (w : Fin 2 ⊕ Fin 2 → K), a.1 (t • w) = t ^ 2 • a.1 w := by
      rcases hdich a.1 a.2 with h | h
      · exact absurd h ha
      · exact h
    show a₀ (a.1 (t • w)) = t • a₀ (a.1 w)
    rw [hf, hfrob]
    have : (t ^ 2) ^ 2 = t := by rw [← pow_mul]; exact sp44_pow_four hK t
    rw [this]
  classical
  let φ : A → C ⊕ C := fun a => if h : a ∈ C then Sum.inl ⟨a, h⟩ else Sum.inr ⟨a₀' * a, hmul a h⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    by_cases ha : a ∈ C <;> by_cases hb : b ∈ C
    · simp only [φ, ha, hb, dite_true, Sum.inl.injEq] at hab
      exact congrArg Subtype.val hab
    · simp [φ, ha, hb] at hab
    · simp [φ, ha, hb] at hab
    · simp only [φ, ha, hb, dite_false, Sum.inr.injEq] at hab
      have := congrArg Subtype.val hab
      exact mul_left_cancel (a := a₀') this
  have := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_sum] at this
  omega


theorem sp44_frob_normalize [Finite K] (hK : Nat.card K = 4)
    (a : (Fin 2 ⊕ Fin 2 → K) ≃+ (Fin 2 ⊕ Fin 2 → K))
    (hfrob : ∀ (t : K) (w : Fin 2 ⊕ Fin 2 → K), a (t • w) = t ^ 2 • a w)
    (ha : ∀ g : GL (Fin 2 ⊕ Fin 2) K, g ∈ StatedSp 2 K →
      ∃ g' : GL (Fin 2 ⊕ Fin 2) K, g' ∈ StatedSp 2 K ∧ ∀ v,
        a ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
          (g' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ a v) :
    ∃ ν : K, ν ≠ 0 ∧ ∀ v w, sp44ω (ν • a v) (ν • a w) = (sp44ω v w) ^ 2 := by
  have := sp44_charTwo hK
  let θ : K →+* K := frobenius K 2
  have hθθ : ∀ t, θ (θ t) = t := fun t => by
    simp only [θ, frobenius_def]
    rw [← pow_mul]
    exact sp44_pow_four hK t
  have hθ : ∀ (t : K) (w : Fin 2 ⊕ Fin 2 → K), a (t • w) = θ t • a w := fun t w => by
    rw [hfrob]
    simp [θ, frobenius_def]
  obtain ⟨μ, hμ⟩ := sp44_form_twist θ hθθ a hθ ha
  have h1 : ∀ v w, sp44ω (a v) (a w) = μ ^ 2 * (sp44ω v w) ^ 2 := by
    intro v w
    have := hμ v w
    simp only [θ, frobenius_def] at this
    calc sp44ω (a v) (a w) = (sp44ω (a v) (a w) ^ 2) ^ 2 := by
          rw [← pow_mul]; exact (sp44_pow_four hK _).symm
      _ = (μ * sp44ω v w) ^ 2 := by rw [this]
      _ = μ ^ 2 * sp44ω v w ^ 2 := by ring
  have hμ0 : μ ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := a.surjective (Pi.single (Sum.inl 0) 1)
    obtain ⟨w, hw⟩ := a.surjective (Pi.single (Sum.inr 0) 1)
    have := h1 v w
    rw [hv, hw, sp44ω_basis, h0] at this
    simp at this
  refine ⟨μ⁻¹, inv_ne_zero hμ0, fun v w => ?_⟩
  rw [sp44ω_smul_left, sp44ω_smul_right, h1]
  field_simp

end G118

end G11

end CFSG.Quasithin
