module

public import CFSG.RankThree.GF2n.Stroth80.Sec12NatDualSL
public import CFSG.ClassicalGroups.SpecialLinear.InvariantForms

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open CFSG.Open.StatedAPI Matrix CFSG.ClassicalGroups.SpecialLinear

structure QuadDatum (K E : Type) [Field K] [AddCommGroup E] [Module K E] where
  Qf : E → K
  B : E →ₗ[K] E →ₗ[K] K
  Qf_smul : ∀ (a : K) (e : E), Qf (a • e) = a ^ 2 * Qf e
  Qf_add : ∀ e f : E, Qf (e + f) = Qf e + Qf f + B e f
  alt : ∀ e : E, B e e = 0
  nondeg : ∀ e : E, (∀ f, B e f = 0) → e = 0

structure NatDualCoord {Γ : Type} [Group Γ] {K F E : Type} [Field K] [Field F] [AddCommGroup E]
    [Module K E] {n : ℕ} (ρ : Γ →* (E ≃ₗ[K] E)) (ρ' : Γ →* GL (Fin n) F) where
  Ψ : E ≃+ (Fin n → F) × (Fin n → F)
  θ₁ : K ≃+* F
  θ₂ : K ≃+* F
  smul : ∀ (c : K) (e : E), Ψ (c • e) = (θ₁ c • (Ψ e).1, θ₂ c • (Ψ e).2)
  act : ∀ (g : Γ) (e : E), Ψ (ρ g e) =
    (((ρ' g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ (Ψ e).1,
     ((tinvGL (ρ' g) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ (Ψ e).2)

namespace QuadDatum

variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] (Q : QuadDatum K E)

theorem B_comm (e f : E) : Q.B e f = - Q.B f e := by
  have h := Q.alt (e + f)
  simp only [map_add, LinearMap.add_apply, Q.alt] at h
  linear_combination h

theorem Qf_zero : Q.Qf 0 = 0 := by
  simpa using Q.Qf_smul 0 0

theorem B_eq_of_isometry (T : E →+ E) (hT : ∀ e, Q.Qf (T e) = Q.Qf e) (e f : E) :
    Q.B (T e) (T f) = Q.B e f := by
  have h1 := Q.Qf_add (T e) (T f)
  have h2 := Q.Qf_add e f
  rw [← map_add, hT, hT e, hT f] at h1
  linear_combination h2 - h1

end QuadDatum

namespace NatDualCoord

variable {Γ : Type} [Group Γ] {K F E : Type} [Field K] [Field F] [AddCommGroup E] [Module K E]
  {n : ℕ} {ρ : Γ →* (E ≃ₗ[K] E)} {ρ' : Γ →* GL (Fin n) F} (C : NatDualCoord ρ ρ')

@[expose] def inl : (Fin n → F) →+ E :=
  C.Ψ.symm.toAddMonoidHom.comp (AddMonoidHom.inl (Fin n → F) (Fin n → F))

@[expose] def inr : (Fin n → F) →+ E :=
  C.Ψ.symm.toAddMonoidHom.comp (AddMonoidHom.inr (Fin n → F) (Fin n → F))

theorem Ψ_inl (x : Fin n → F) : C.Ψ (C.inl x) = (x, 0) := C.Ψ.apply_symm_apply _

theorem Ψ_inr (y : Fin n → F) : C.Ψ (C.inr y) = (0, y) := C.Ψ.apply_symm_apply _

theorem eq_inl_add_inr (e : E) : e = C.inl (C.Ψ e).1 + C.inr (C.Ψ e).2 := by
  apply C.Ψ.injective
  rw [map_add, Ψ_inl, Ψ_inr]
  simp

theorem ρ_inl (g : Γ) (x : Fin n → F) :
    ρ g (C.inl x) = C.inl (((ρ' g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ x) := by
  apply C.Ψ.injective
  rw [C.act, Ψ_inl, Ψ_inl]
  simp

theorem ρ_inr (g : Γ) (y : Fin n → F) :
    ρ g (C.inr y) =
      C.inr (((tinvGL (ρ' g) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ y) := by
  apply C.Ψ.injective
  rw [C.act, Ψ_inr, Ψ_inr]
  simp

theorem smul_inl (c : K) (x : Fin n → F) : c • C.inl x = C.inl (C.θ₁ c • x) := by
  apply C.Ψ.injective
  rw [C.smul, Ψ_inl, Ψ_inl]
  simp

theorem smul_inr (c : K) (y : Fin n → F) : c • C.inr y = C.inr (C.θ₂ c • y) := by
  apply C.Ψ.injective
  rw [C.smul, Ψ_inr, Ψ_inr]
  simp

end NatDualCoord

namespace NatDualCoord

variable {Γ : Type} [Group Γ] {K F E : Type} [Field K] [Field F] [AddCommGroup E] [Module K E]
  {n : ℕ} {ρ : Γ →* (E ≃ₗ[K] E)} {ρ' : Γ →* GL (Fin n) F} (C : NatDualCoord ρ ρ')
  (Q : QuadDatum K E)

theorem exists_eq_of_mem_statedSL (hrange : ρ'.range = StatedSL n F) {A : GL (Fin n) F}
    (hA : A ∈ StatedSL n F) : ∃ g : Γ, ρ' g = A := by
  rw [← hrange] at hA
  exact hA

theorem Qf_inl_eq_zero (hn : 2 ≤ n) (hrange : ρ'.range = StatedSL n F)
    (hQρ : ∀ (g : Γ) (e : E), Q.Qf (ρ g e) = Q.Qf e) (hK : ∃ c : K, c ≠ 0 ∧ c ^ 2 ≠ 1)
    (x : Fin n → F) : Q.Qf (C.inl x) = 0 := by
  by_cases hx : x = 0
  · rw [hx, map_zero]
    exact Q.Qf_zero
  · obtain ⟨c, hc0, hc2⟩ := hK
    have ha : C.θ₁ c ≠ 0 := by simpa using hc0
    obtain ⟨A, hA, hAx⟩ := exists_statedSL_mulVec_eq hn hx (smul_ne_zero ha hx)
    obtain ⟨g, hg⟩ := exists_eq_of_mem_statedSL hrange hA
    have h1 : Q.Qf (C.inl (((ρ' g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ x)) =
        Q.Qf (C.inl x) := by rw [← C.ρ_inl, hQρ]
    rw [hg, hAx, ← C.smul_inl, Q.Qf_smul] at h1
    have h2 : (c ^ 2 - 1) * Q.Qf (C.inl x) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (sub_eq_zero.mp h) hc2
    · exact h

theorem Qf_inr_eq_zero (hn : 2 ≤ n) (hrange : ρ'.range = StatedSL n F)
    (hQρ : ∀ (g : Γ) (e : E), Q.Qf (ρ g e) = Q.Qf e) (hK : ∃ c : K, c ≠ 0 ∧ c ^ 2 ≠ 1)
    (y : Fin n → F) : Q.Qf (C.inr y) = 0 := by
  by_cases hy : y = 0
  · rw [hy, map_zero]
    exact Q.Qf_zero
  · obtain ⟨c, hc0, hc2⟩ := hK
    have ha : C.θ₂ c ≠ 0 := by simpa using hc0
    obtain ⟨A, hA, hAy⟩ := exists_statedSL_mulVec_eq hn hy (smul_ne_zero ha hy)
    obtain ⟨g, hg⟩ := exists_eq_of_mem_statedSL hrange (tinvGL_mem_statedSL hA)
    have h1 : Q.Qf (C.inr (((tinvGL (ρ' g) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ y)) =
        Q.Qf (C.inr y) := by rw [← C.ρ_inr, hQρ]
    rw [hg, tinvGL_tinvGL, hAy, ← C.smul_inr, Q.Qf_smul] at h1
    have h2 : (c ^ 2 - 1) * Q.Qf (C.inr y) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (sub_eq_zero.mp h) hc2
    · exact h

theorem Qf_eq_B (hn : 2 ≤ n) (hrange : ρ'.range = StatedSL n F)
    (hQρ : ∀ (g : Γ) (e : E), Q.Qf (ρ g e) = Q.Qf e) (hK : ∃ c : K, c ≠ 0 ∧ c ^ 2 ≠ 1)
    (x y : Fin n → F) : Q.Qf (C.inl x + C.inr y) = Q.B (C.inl x) (C.inr y) := by
  rw [Q.Qf_add, C.Qf_inl_eq_zero Q hn hrange hQρ hK, C.Qf_inr_eq_zero Q hn hrange hQρ hK]
  ring

theorem B_inr_inr (hn : 2 ≤ n) (hrange : ρ'.range = StatedSL n F)
    (hQρ : ∀ (g : Γ) (e : E), Q.Qf (ρ g e) = Q.Qf e) (hK : ∃ c : K, c ≠ 0 ∧ c ^ 2 ≠ 1)
    (y y' : Fin n → F) : Q.B (C.inr y) (C.inr y') = 0 := by
  have h := Q.Qf_add (C.inr y) (C.inr y')
  rw [← map_add, C.Qf_inr_eq_zero Q hn hrange hQρ hK, C.Qf_inr_eq_zero Q hn hrange hQρ hK,
    C.Qf_inr_eq_zero Q hn hrange hQρ hK] at h
  linear_combination -h

@[expose] def pairing : (Fin n → F) →+ (Fin n → F) →+ K :=
  AddMonoidHom.mk' (fun x => (Q.B (C.inl x)).toAddMonoidHom.comp C.inr)
    (fun x x' => by
      ext y
      simp [map_add])

theorem B_inl_inr_eq_zero_of_dot (hn : 2 ≤ n) (hrange : ρ'.range = StatedSL n F)
    (hQρ : ∀ (g : Γ) (e : E), Q.Qf (ρ g e) = Q.Qf e) {x y : Fin n → F} (h : y ⬝ᵥ x = 0) :
    Q.B (C.inl x) (C.inr y) = 0 := by
  have hinv : ∀ g ∈ StatedSL n F, ∀ x y : Fin n → F,
      C.pairing Q ((g : Matrix (Fin n) (Fin n) F) *ᵥ x)
        (((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ *ᵥ y) = C.pairing Q x y := by
    intro g hg x y
    obtain ⟨s, hs⟩ := exists_eq_of_mem_statedSL hrange hg
    have := Q.B_eq_of_isometry (ρ s).toLinearMap.toAddMonoidHom (fun e => hQρ s e)
      (C.inl x) (C.inr y)
    simp only [LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe, C.ρ_inl, C.ρ_inr, hs] at this
    exact this
  exact pairing_eq_zero_of_statedSL_invariant hn (C.pairing Q) hinv h

theorem dot_eq_zero_of_B_inl_inr_eq_zero (hn : 2 ≤ n) (hrange : ρ'.range = StatedSL n F)
    (hQρ : ∀ (g : Γ) (e : E), Q.Qf (ρ g e) = Q.Qf e) (hK : ∃ c : K, c ≠ 0 ∧ c ^ 2 ≠ 1)
    {x y : Fin n → F} (h : Q.B (C.inl x) (C.inr y) = 0) : y ⬝ᵥ x = 0 := by
  by_contra hxy
  have hz : ∀ z : Fin n → F, Q.B (C.inl z) (C.inr y) = 0 := by
    intro z
    set a : F := (y ⬝ᵥ z) / (y ⬝ᵥ x) with ha
    have hu : y ⬝ᵥ (z - a • x) = 0 := by
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, ha, div_mul_cancel₀ _ hxy, sub_self]
    have h1 := C.B_inl_inr_eq_zero_of_dot Q hn hrange hQρ hu
    have h2 : Q.B (C.inl (a • x)) (C.inr y) = 0 := by
      have : a • x = C.θ₁ (C.θ₁.symm a) • x := by simp
      rw [this, ← C.smul_inl, map_smul, LinearMap.smul_apply, h, smul_zero]
    have h3 : C.inl z = C.inl (a • x) + C.inl (z - a • x) := by
      rw [← map_add]
      congr 1
      abel
    rw [h3, map_add, LinearMap.add_apply, h2, h1, add_zero]
  have hall : ∀ e : E, Q.B e (C.inr y) = 0 := by
    intro e
    calc Q.B e (C.inr y) = Q.B (C.inl (C.Ψ e).1 + C.inr (C.Ψ e).2) (C.inr y) := by
          rw [← C.eq_inl_add_inr e]
      _ = 0 := by
          rw [map_add, LinearMap.add_apply, hz, C.B_inr_inr Q hn hrange hQρ hK, add_zero]
  have h0 : C.inr y = 0 := Q.nondeg _ fun f => by rw [Q.B_comm, hall f, neg_zero]
  have h00 : y = 0 := by
    have := congrArg C.Ψ h0
    rw [Ψ_inr, map_zero] at this
    exact (Prod.mk.inj this).2
  exact hxy (by rw [h00, zero_dotProduct])

theorem B_inl_inr_eq_zero_iff (hn : 2 ≤ n) (hrange : ρ'.range = StatedSL n F)
    (hQρ : ∀ (g : Γ) (e : E), Q.Qf (ρ g e) = Q.Qf e) (hK : ∃ c : K, c ≠ 0 ∧ c ^ 2 ≠ 1)
    (x y : Fin n → F) : Q.B (C.inl x) (C.inr y) = 0 ↔ y ⬝ᵥ x = 0 :=
  ⟨C.dot_eq_zero_of_B_inl_inr_eq_zero Q hn hrange hQρ hK,
    C.B_inl_inr_eq_zero_of_dot Q hn hrange hQρ⟩

theorem Qf_inl_add_inr_eq_zero_iff (hn : 2 ≤ n) (hrange : ρ'.range = StatedSL n F)
    (hQρ : ∀ (g : Γ) (e : E), Q.Qf (ρ g e) = Q.Qf e) (hK : ∃ c : K, c ≠ 0 ∧ c ^ 2 ≠ 1)
    (x y : Fin n → F) : Q.Qf (C.inl x + C.inr y) = 0 ↔ y ⬝ᵥ x = 0 := by
  rw [C.Qf_eq_B Q hn hrange hQρ hK, C.B_inl_inr_eq_zero_iff Q hn hrange hQρ hK]

end NatDualCoord

end CFSG.RankThree.GF2n.Stroth80
