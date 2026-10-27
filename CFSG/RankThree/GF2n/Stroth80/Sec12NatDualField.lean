module

public import CFSG.RankThree.GF2n.Stroth80.Sec12NatDualCoord

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open CFSG.Open.StatedAPI Matrix CFSG.ClassicalGroups.SpecialLinear

theorem exists_ringEquiv_of_semilinear {K F E : Type} [Field K] [Field F] [Finite K] [Finite F]
    (hcard : Nat.card K = Nat.card F) [AddCommGroup E] [Module K E] (ψ : E →+ F) (a : K → F)
    (ha : ∀ (c : K) (e : E), ψ (c • e) = a c * ψ e) (e₁ : E) (he₁ : ψ e₁ = 1) :
    ∃ θ : K ≃+* F, ∀ c, θ c = a c := by
  have hval : ∀ c : K, a c = ψ (c • e₁) := fun c => by rw [ha, he₁, mul_one]
  let θr : K →+* F :=
    { toFun := a
      map_one' := by rw [hval, one_smul, he₁]
      map_zero' := by rw [hval, zero_smul, map_zero]
      map_add' := fun c d => by rw [hval, hval c, hval d, add_smul, map_add]
      map_mul' := fun c d => by
        rw [hval (c * d), mul_smul, ha, ← hval d] }
  have hbij : Function.Bijective θr :=
    θr.injective.bijective_of_nat_card_le (le_of_eq hcard.symm)
  exact ⟨RingEquiv.ofBijective θr hbij, fun c => rfl⟩

theorem exists_natDualCoord_of_equivariant {Γ : Type} [Group Γ] {K F E : Type} [Field K]
    [Field F] [Finite K] [Finite F] [AddCommGroup E] [Module K E] {n : ℕ}
    (ρ : Γ →* (E ≃ₗ[K] E)) (ρ' : Γ →* GL (Fin n) F) (hn : 3 ≤ n)
    (hrange : ρ'.range = StatedSL n F) (hcard : Nat.card K = Nat.card F)
    (Φ : E ≃+ (Fin n → F) × (Fin n → F))
    (hact : ∀ (g : Γ) (e : E), Φ (ρ g e) =
      (((ρ' g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ (Φ e).1,
       ((tinvGL (ρ' g) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ (Φ e).2)) :
    ∃ C : NatDualCoord ρ ρ', C.Ψ = Φ := by
  let f : K → ((Fin n → F) × (Fin n → F) →+ (Fin n → F) × (Fin n → F)) := fun c =>
    Φ.toAddMonoidHom.comp
      ((AddMonoidHom.mk' (fun e : E => c • e) (smul_add c)).comp Φ.symm.toAddMonoidHom)
  have hf_app : ∀ c p, f c p = Φ (c • Φ.symm p) := fun c p => rfl
  have hfeq : ∀ c : K, ∀ g ∈ StatedSL n F, ∀ p : (Fin n → F) × (Fin n → F),
      f c ((g : Matrix (Fin n) (Fin n) F) *ᵥ p.1,
          ((tinvGL g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ p.2) =
        ((g : Matrix (Fin n) (Fin n) F) *ᵥ (f c p).1,
          ((tinvGL g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ (f c p).2) := by
    intro c g hg p
    obtain ⟨s, hs⟩ : g ∈ ρ'.range := hrange ▸ hg
    have h1 : Φ.symm ((g : Matrix (Fin n) (Fin n) F) *ᵥ p.1,
        ((tinvGL g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ p.2) = ρ s (Φ.symm p) := by
      apply Φ.injective
      rw [hact, Φ.apply_symm_apply, Φ.apply_symm_apply, hs]
    rw [hf_app, h1, ← (ρ s).map_smul c, hact, ← hs, ← hf_app]
  choose a b hab using fun c => exists_scalars_of_equivariant hn (f c) (hfeq c)
  have hΦsmul : ∀ (c : K) (e : E), Φ (c • e) = (a c • (Φ e).1, b c • (Φ e).2) := by
    intro c e
    have := hab c (Φ e)
    rwa [hf_app, Φ.symm_apply_apply] at this
  have hn1 : 0 < n := by omega
  set i₀ : Fin n := ⟨0, hn1⟩ with hi₀
  let ψ₁ : E →+ F :=
    (Pi.evalAddMonoidHom (fun _ : Fin n => F) i₀).comp
      ((AddMonoidHom.fst (Fin n → F) (Fin n → F)).comp Φ.toAddMonoidHom)
  let ψ₂ : E →+ F :=
    (Pi.evalAddMonoidHom (fun _ : Fin n => F) i₀).comp
      ((AddMonoidHom.snd (Fin n → F) (Fin n → F)).comp Φ.toAddMonoidHom)
  have hψ₁ : ∀ e, ψ₁ e = (Φ e).1 i₀ := fun e => rfl
  have hψ₂ : ∀ e, ψ₂ e = (Φ e).2 i₀ := fun e => rfl
  obtain ⟨θ₁, hθ₁⟩ := exists_ringEquiv_of_semilinear hcard ψ₁ a
    (fun c e => by rw [hψ₁, hψ₁, hΦsmul]; simp) (Φ.symm (Pi.single i₀ 1, 0))
    (by rw [hψ₁, Φ.apply_symm_apply]; simp)
  obtain ⟨θ₂, hθ₂⟩ := exists_ringEquiv_of_semilinear hcard ψ₂ b
    (fun c e => by rw [hψ₂, hψ₂, hΦsmul]; simp) (Φ.symm (0, Pi.single i₀ 1))
    (by rw [hψ₂, Φ.apply_symm_apply]; simp)
  refine ⟨⟨Φ, θ₁, θ₂, fun c e => ?_, hact⟩, rfl⟩
  rw [hΦsmul, hθ₁, hθ₂]

theorem exists_ne_zero_sq_ne_one_of_two_lt_card (K : Type) [Field K] [Finite K] [CharP K 2]
    (h : 2 < Nat.card K) : ∃ c : K, c ≠ 0 ∧ c ^ 2 ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have h1 : ∀ c : K, c ≠ 0 → c = 1 := by
    intro c hc
    have h2 : (c - 1) ^ 2 = 0 := by
      have h3 : c ^ 2 = 1 := hcon c hc
      have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination h3 + (1 - c) * h2'
    have := pow_eq_zero_iff (two_ne_zero) |>.mp h2
    exact sub_eq_zero.mp this
  have : Nat.card K ≤ 2 := by
    haveI : Fintype K := Fintype.ofFinite K
    classical
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := by
      intro c _
      by_cases hc : c = 0
      · simp [hc]
      · simp [h1 c hc]
    have h3 := Finset.card_le_card hsub
    rw [Finset.card_univ] at h3
    have h4 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
    rw [Nat.card_eq_fintype_card]
    omega
  omega

end CFSG.RankThree.GF2n.Stroth80
