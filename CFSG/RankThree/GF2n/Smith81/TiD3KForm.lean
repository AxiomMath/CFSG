module

public import CFSG.RankThree.GF2n.Smith81.TiD3Descent
public import CFSG.RankThree.GF2n.Smith81.TiD3Quad
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.TotallySplit

public section

namespace CFSG.RankThree.GF2n.Stroth80.SL2Descent

open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.D3
open scoped MatrixGroups

theorem exists_kForm_equiv {K F : Type} [Field K] [Fintype K] [CharP K 2] [Field F] [Fintype F]
    [Algebra K F] {k : ℕ} (hk : Fintype.card K = 2 ^ k) (hk2 : 2 ≤ k)
    (hcardF : Fintype.card F = Fintype.card K ^ 3) {E : Type} [AddCommGroup E] [Module K E]
    [Module.Finite K E] (hdim : Module.finrank K E = 8) (ρ : Representation K SL(2, F) E)
    [Fact ρ.IsIrreducible] (hnt : ∃ g, ρ g ≠ 1) :
    ∃ (σ : F ≃+* F) (θ : E ≃ₗ[K] kForm (FiniteField.frobeniusAlgHom K F)),
      ∀ (g : SL(2, F)) (e : E), (θ (ρ g e) : Hyp F) =
        act (FiniteField.frobeniusAlgHom K F : F →+* F)
          ((D2.slMap σ g : SL(2, F)) : Mat2 F) (θ e : Hyp F) := by
  classical
  haveI : CharP F 2 := charP_of_injective_algebraMap (algebraMap K F).injective 2
  have hk0 : 0 < k := by omega
  have hn : 1 ≤ 3 * k := by omega
  have hF : Fintype.card F = 2 ^ (3 * k) := by rw [hcardF, hk, ← pow_mul, mul_comm]
  haveI : Finite E := Module.finite_of_finite K
  have hq : 2 ≤ Fintype.card K := by
    rw [hk]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨a, σ, θ₁, hσ, hinj, hequiv⟩ := exists_hyp_map hk hk2 hcardF hdim ρ hnt
  let τ : F →ₐ[K] F := FiniteField.frobeniusAlgHom K F
  have hτ : ∀ x, τ x = x ^ Fintype.card K := fun x => rfl
  have hτ3 : ∀ x, τ (τ (τ x)) = x := by
    intro x
    have h1 : ((x ^ Fintype.card K) ^ Fintype.card K) ^ Fintype.card K = x ^ Fintype.card F := by
      rw [← pow_mul, ← pow_mul, hcardF]
      ring_nf
    rw [hτ, hτ, hτ, h1, FiniteField.pow_card]
  haveI : Finite (EndRing ρ) := finite_endRing ρ
  have hnt1 : (1 : ℕ) < Nat.card (EndRing ρ) := Finite.one_lt_card
  have hfixU := card_fixRoot_gen (ρ := ρ) hk hn hF hnt
  obtain ⟨e₀, he₀, he₀0⟩ : ∃ e₀ : E, (∀ t : F, ρ (uElt t) e₀ = e₀) ∧ e₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h1 : Nat.card {w : E // ∀ t : F, ρ (uElt t) w = w} ≤ 1 := by
      rw [Finite.card_le_one_iff_subsingleton]
      refine ⟨fun x y => Subtype.ext ?_⟩
      rw [hcon x.1 x.2, hcon y.1 y.2]
    omega
  have hx : ∀ a' : F, act (τ : F →+* F) ((D2.uSL a' : SL(2, F)) : Mat2 F) (θ₁ e₀) = θ₁ e₀ := by
    intro a'
    have h1 := hequiv (uElt (σ.symm a')) e₀
    rw [he₀ (σ.symm a')] at h1
    have h2 : D2.slMap σ (uElt (σ.symm a')) = D2.uSL a' := by
      rw [uElt_eq_uSL, D2.slMap_uSL, σ.apply_symm_apply]
    rw [h2] at h1
    exact h1.symm
  have hcoord := coords_zero_of_fixed hq hcardF (τ : F →+* F) hτ (θ₁ e₀)
    (fun a' => by rw [hx a'])
  set μ : F := θ₁ e₀ 0 0 0 with hμ
  have hxμ : θ₁ e₀ = μ • e0 F := by
    funext i j k
    by_cases h : i = 0 ∧ j = 0 ∧ k = 0
    · obtain ⟨rfl, rfl, rfl⟩ := h
      simp [e0, hμ]
    · rw [hcoord i j k h]
      simp [e0, h]
  have hμ0 : μ ≠ 0 := by
    intro h0
    apply he₀0
    apply hinj
    rw [hxμ, h0, zero_smul, map_zero]
  let θ₂ : E →ₗ[K] Hyp F :=
    { toFun := fun e => μ⁻¹ • θ₁ e
      map_add' := fun e e' => by rw [map_add, smul_add]
      map_smul' := fun c e => by rw [map_smul, smul_comm]; rfl }
  have hθ₂ : ∀ e, θ₂ e = μ⁻¹ • θ₁ e := fun e => rfl
  have hequiv₂ : ∀ (g : SL(2, F)) (e : E), θ₂ (ρ g e) =
      act (τ : F →+* F) ((D2.slMap σ g : SL(2, F)) : Mat2 F) (θ₂ e) := by
    intro g e
    rw [hθ₂, hθ₂, hequiv, act_smul]
  have hθ₂e₀ : θ₂ e₀ = e0 F := by
    rw [hθ₂, hxμ, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
  have hmemk : ∀ e, θ₂ e ∈ kForm τ := by
    obtain ⟨-, hirr⟩ := (isIrreducible_iff ρ).mp Fact.out
    let S : Submodule K E := Submodule.span K (Set.range fun g : SL(2, F) => ρ g e₀)
    have hS : ∀ g, ∀ u ∈ S, ρ g u ∈ S := by
      intro g u hu
      refine Submodule.span_induction (p := fun u _ => ρ g u ∈ S) ?_ ?_ ?_ ?_ hu
      · rintro _ ⟨h, rfl⟩
        refine Submodule.subset_span ⟨g * h, ?_⟩
        simp [map_mul]
      · simp
      · intro x y _ _ hx hy
        rw [map_add]
        exact S.add_mem hx hy
      · intro c x _ hx
        rw [map_smul]
        exact S.smul_mem c hx
    have hSne : S ≠ ⊥ := by
      intro h
      have : e₀ ∈ S := Submodule.subset_span ⟨1, by simp⟩
      rw [h] at this
      exact he₀0 ((Submodule.mem_bot K).mp this)
    have hStop : S = ⊤ := (hirr S hS).resolve_left hSne
    intro e
    have he : e ∈ S := hStop ▸ Submodule.mem_top
    refine Submodule.span_induction (p := fun e _ => θ₂ e ∈ kForm τ) ?_ ?_ ?_ ?_ he
    · rintro _ ⟨g, rfl⟩
      show θ₂ (ρ g e₀) ∈ kForm τ
      rw [hequiv₂ g e₀, hθ₂e₀]
      exact act_mem_kForm τ hτ3 _ (e0_mem_kForm τ)
    · simp only [map_zero]
      exact (kForm τ).zero_mem
    · intro x y _ _ hx hy
      rw [map_add]
      exact (kForm τ).add_mem hx hy
    · intro c x _ hx
      rw [map_smul]
      exact (kForm τ).smul_mem c hx
  let θ' : E →ₗ[K] kForm τ := θ₂.codRestrict (kForm τ) hmemk
  have hθ'inj : Function.Injective θ' := by
    intro e e' h
    have h1 : θ₂ e = θ₂ e' := congrArg Subtype.val h
    exact hinj (smul_right_injective _ (inv_ne_zero hμ0) h1)
  have hcardk := D3.card_kForm_le hcardF τ hτ
  have hcardE : Nat.card E = Fintype.card K ^ 8 := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := E), hdim, Nat.card_eq_fintype_card]
  have hbij : Function.Bijective θ' :=
    hθ'inj.bijective_of_nat_card_le (by rw [hcardE]; exact hcardk)
  exact ⟨σ, LinearEquiv.ofBijective θ' hbij, fun g e => hequiv₂ g e⟩

end CFSG.RankThree.GF2n.Stroth80.SL2Descent
