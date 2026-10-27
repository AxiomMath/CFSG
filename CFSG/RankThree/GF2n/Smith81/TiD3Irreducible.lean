module

public import CFSG.RankThree.GF2n.Smith81.TiD3KForm

public section

namespace CFSG.RankThree.GF2n.Stroth80.SL2Descent

open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.D3
open scoped MatrixGroups

theorem d3_of_irreducible {K F : Type} [Field K] [Fintype K] [CharP K 2] [Field F] [Finite F]
    [Algebra K F] (hcard : Nat.card F = Nat.card K ^ 3) (hK4 : 4 ≤ Nat.card K)
    {E : Type} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (B : LinearMap.BilinForm K E) (Qf : E → K) (halt : ∀ e, B e e = 0)
    (hnd : ∀ e, (∀ f, B e f = 0) → e = 0) (hQadd : ∀ e f, Qf (e + f) = Qf e + Qf f + B e f)
    (hQsmul : ∀ (a : K) e, Qf (a • e) = a ^ 2 * Qf e) (hdim : Module.finrank K E = 8)
    (ρ : SL(2, F) →* (E ≃ₗ[K] E)) (hρQ : ∀ g e, Qf (ρ g e) = Qf e)
    (hirr : ∀ W : Submodule K E, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hnt : ∃ g, ρ g ≠ 1) :
    ∃ (σ : F ≃+* F) (θ : E ≃ₗ[K] kForm (FiniteField.frobeniusAlgHom K F)),
      (∀ g e, (θ (ρ g e) : Hyp F) = act (FiniteField.frobeniusAlgHom K F : F →+* F)
        ((D2.slMap σ g : SL(2, F)) : Mat2 F) (θ e : Hyp F)) ∧
      ∀ e, algebraMap K F (Qf e) = quad (θ e : Hyp F) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_injective_algebraMap (algebraMap K F).injective 2
  obtain ⟨k, -, hk⟩ := FiniteField.card K 2
  have hkK : Fintype.card K = 2 ^ (k : ℕ) := hk
  have hK4' : 4 ≤ Fintype.card K := by rwa [Nat.card_eq_fintype_card] at hK4
  have hk2 : 2 ≤ (k : ℕ) := by
    by_contra h
    have : (k : ℕ) ≤ 1 := by omega
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) this
    omega
  have hcardF : Fintype.card F = Fintype.card K ^ 3 := by
    rw [← Nat.card_eq_fintype_card, hcard, Nat.card_eq_fintype_card]
  let ρ' : Representation K SL(2, F) E :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ
  haveI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ (n := 7) hdim
  have hirr' : ρ'.IsIrreducible :=
    (isIrreducible_iff ρ').mpr ⟨inferInstance, fun W hW => hirr W hW⟩
  haveI : Fact ρ'.IsIrreducible := ⟨hirr'⟩
  have hnt' : ∃ g, ρ' g ≠ 1 := by
    obtain ⟨g, hg⟩ := hnt
    exact ⟨g, fun h => hg (LinearEquiv.toLinearMap_injective h)⟩
  obtain ⟨σ, θ₁, hθ₁⟩ := exists_kForm_equiv hkK hk2 hcardF hdim ρ' hnt'
  let τ : F →ₐ[K] F := FiniteField.frobeniusAlgHom K F
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  let Q : kForm τ → K := fun x => Qf (θ₁.symm x)
  let β : LinearMap.BilinForm K (kForm τ) :=
    B.compl₁₂ (θ₁.symm : kForm τ →ₗ[K] E) (θ₁.symm : kForm τ →ₗ[K] E)
  have hQs : ∀ (a : K) (x : kForm τ), Q (a • x) = a ^ 2 * Q x := fun a x => by
    simp only [Q, map_smul]
    exact hQsmul a _
  have hQa : ∀ x y, Q (x + y) = Q x + Q y + β x y := fun x y => by
    simp only [Q, β, map_add, LinearMap.compl₁₂_apply]
    exact hQadd _ _
  have hQg : ∀ (g : SL(2, F)) (x y : kForm τ),
      (y : Hyp F) = act (τ : F →+* F) (g : Mat2 F) (x : Hyp F) → Q y = Q x := by
    intro g x y hy
    have h1 := hθ₁ (D2.slMap σ.symm g) (θ₁.symm x)
    rw [LinearEquiv.apply_symm_apply, D2.slMap_symm_apply σ g] at h1
    have h2 : y = θ₁ (ρ' (D2.slMap σ.symm g) (θ₁.symm x)) := Subtype.ext (hy.trans h1.symm)
    show Qf (θ₁.symm y) = Qf (θ₁.symm x)
    rw [h2, LinearEquiv.symm_apply_apply]
    exact hρQ _ _
  obtain ⟨c, hc⟩ := invariant_quad_eq_quad_frob (K := K) (F := F) hcardF hK4' h2K Q β hQs hQa hQg
  have hc0 : c ≠ 0 := by
    intro h0
    have hQ0 : ∀ e, Qf e = 0 := by
      intro e
      have h3 := hc (θ₁ e)
      rw [h0, map_zero, zero_mul] at h3
      have h4 : Q (θ₁ e) = 0 := (algebraMap K F).injective (by rw [h3, map_zero])
      simpa [Q] using h4
    obtain ⟨e, he⟩ := exists_ne (0 : E)
    apply he
    refine hnd e fun f => ?_
    have h5 := hQadd e f
    rw [hQ0, hQ0, hQ0] at h5
    linear_combination -h5
  obtain ⟨t, ht⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) c
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hc0 (by rw [ht, mul_zero])
  let θ : E ≃ₗ[K] kForm τ := (LinearEquiv.smulOfNeZero K E t ht0).trans θ₁
  refine ⟨σ, θ, fun g e => ?_, fun e => ?_⟩
  · show (θ₁ (t • ρ g e) : Hyp F) = act _ _ (θ₁ (t • e))
    have h6 : t • ρ g e = ρ' g (t • e) := by
      show t • ρ g e = ρ g (t • e)
      rw [map_smul]
    rw [h6]
    exact hθ₁ g (t • e)
  · show algebraMap K F (Qf e) = quad ((θ₁ (t • e) : kForm τ) : Hyp F)
    have h7 : ((θ₁ (t • e) : kForm τ) : Hyp F) = algebraMap K F t • (θ₁ e : Hyp F) := by
      rw [map_smul, Submodule.coe_smul, algebraMap_smul]
    rw [h7, quad_smulF]
    have h8 := hc (θ₁ e)
    simp only [Q, LinearEquiv.symm_apply_apply] at h8
    rw [h8, ht, map_mul]
    ring

end CFSG.RankThree.GF2n.Stroth80.SL2Descent
