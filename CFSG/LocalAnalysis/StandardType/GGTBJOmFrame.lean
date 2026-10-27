module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusCore
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmMvMoves
public import CFSG.LocalAnalysis.StandardType.GGTBJOmFrameAux

public section

open Module Multiplicative QuadraticMap Polynomial

namespace CFSG.StandardType

namespace OrthTorus

open SpCoord NbrOrth
open CFSG.RankThree.Classical2 (orthDerived)

section Blocks

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem exists_torus_blocks {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1) {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    {A : Subgroup (V ≃ₗ[K] V)} (hAΩ : A ≤ orthDerived Q) (hApow : ∀ a ∈ A, a ^ p = 1)
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    (hne : ∃ b ∈ A, b ≠ 1) :
    ∃ (r : ℕ) (τ : (Fin r → Multiplicative (ZMod p)) →* (V ≃ₗ[K] V)) (F : SevOm.Frame Q p A r)
      (D : Type) (_ : AddCommGroup D) (_ : Module K D) (_ : FiniteDimensional K D)
      (c : D ≃ₗ[K] D) (θ : Fin r → D →ₗ[K] V),
      (∀ f, τ f = F.ι (piMul r p f)) ∧ Function.Injective τ ∧ τ.range = A ∧
      finrank K D = 2 ∧ c ^ p = 1 ∧ (∀ u, c u = u → u = 0) ∧
      (∃ T : D ≃ₗ[K] D, T * c * T⁻¹ = c⁻¹) ∧
      (∀ (e : ZMod p) (θ' : D →ₗ[K] D), Function.Injective θ' →
        (∀ x, θ' (c x) = (c ^ e.val) (θ' x)) → e = 1 ∨ e = -1) ∧
      (∀ j, Function.Injective (θ j)) ∧ (∀ j, LinearMap.range (θ j) = F.U j) ∧
      (∀ (s : Multiplicative (Fin r → ZMod p)) (j : Fin r) (d : D),
        F.ι s (θ j d) = θ j ((c ^ (toAdd s j).val) d)) ∧
      (∀ g : V ≃ₗ[K] V, (∀ a ∈ A, g * a * g⁻¹ ∈ A) →
        ∃ (π : Equiv.Perm (Fin r)) (ε : Fin r → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
          ∀ f f', g * τ f * g⁻¹ = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i)) ∧
      (∀ i j : Fin r, i ≠ j → ∃ w ∈ orthDerived Q,
        (∀ v : V, (∀ u ∈ F.U i, QuadraticMap.polar Q u v = 0) →
          (∀ u ∈ F.U j, QuadraticMap.polar Q u v = 0) → w v = v) ∧
        ∀ f, w * τ f * w⁻¹ = τ (permAut (Equiv.swap i j) f)) ∧
      (∀ i j : Fin r, i ≠ j → ∃ w ∈ orthDerived Q,
        (∀ v : V, (∀ u ∈ F.U i, QuadraticMap.polar Q u v = 0) →
          (∀ u ∈ F.U j, QuadraticMap.polar Q u v = 0) → w v = v) ∧
        ∀ f, w * τ f * w⁻¹ = τ (dinv i j f)) ∧
      ((∃ v : V, v ≠ 0 ∧ ∀ a ∈ A, a v = v) → ∀ i : Fin r, ∃ w ∈ orthDerived Q,
        (∀ v : V, (∀ u ∈ F.U i, QuadraticMap.polar Q u v = 0) →
          (∀ u : V, (∀ a ∈ A, a u = u) → QuadraticMap.polar Q u v = 0) → w v = v) ∧
        ∀ f, w * τ f * w⁻¹ = τ (sgnAut i f)) ∧
      (OrdPNsOm.charSum Q ⊤ ≡ 1 [ZMOD p] → ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) ∧
      (OrdPNsOm.charSum Q ⊤ ≡ -1 [ZMOD p] → ∃ v : V, v ≠ 0 ∧ ∀ a ∈ A, a v = v) := by
  classical
  have hpp : p.Prime := Fact.out
  have hpK : (p : K) ≠ 0 := by
    intro h
    have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff K 2 p).mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpp).mp h2).symm
  have hne' : ¬ IsUnit (cyclotomic p K) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree (cyclotomic_ne_zero p _),
      natDegree_cyclotomic, Nat.totient_prime hpp]
    have := hpp.two_le
    norm_cast
    omega
  obtain ⟨g, hg, hgd⟩ := WfDvdMonoid.exists_irreducible_factor hne' (cyclotomic_ne_zero p _)
  have : Fact (Irreducible g) := ⟨hg⟩
  have hζ := NSFrame.root_isPrimitiveRoot (g := g) hpp hpK hgd
  have hζp : AdjoinRoot.root g ^ p = 1 := hζ.pow_eq_one
  have hζ0 : AdjoinRoot.root g ≠ 0 := hζ.ne_zero hpp.ne_zero
  have : Module.Finite K (AdjoinRoot g) := (CoordSL.rootPB g).finite
  have hζ1 : AdjoinRoot.root g ≠ 1 := hζ.ne_one hpp.one_lt
  have hζ1' : AdjoinRoot.root g ^ (p - 1) ≠ 1 :=
    hζ.pow_ne_one_of_pos_of_lt (by have := hpp.two_le; omega) (by have := hpp.pos; omega)
  have hζ0' : AdjoinRoot.root g ^ (p - 1) ≠ 0 := pow_ne_zero _ hζ0
  have hfix : ∀ μ : AdjoinRoot g, μ ≠ 1 → ∀ d : AdjoinRoot g, μ * d = d → d = 0 :=
    fun μ hμ d hd => by
      have h0 : (μ - 1) * d = 0 := by rw [sub_mul, hd, one_mul, sub_self]
      exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hμ)
  have hsurj : ∀ μ : AdjoinRoot g, μ ≠ 1 → ∀ u : AdjoinRoot g, ∃ u₀, μ * u₀ - u₀ = u :=
    fun μ hμ u => ⟨(μ - 1)⁻¹ * u, by
      rw [← sub_one_mul, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hμ), one_mul]⟩
  rcases hpq with hpq | hpq
  · have hσ := aeval_pred_ne_zero hpp hp2 hpK hpq hgd
    obtain ⟨r, τ, F, θ, hbody⟩ := ggTBJomF_ofBlock hp2 hQ hT hAΩ hApow hAcomm hmax hne
      (D := AdjoinRoot g × AdjoinRoot g)
      (c := (LinearMap.mulLeft K (AdjoinRoot.root g)).prodMap
        (LinearMap.mulLeft K (AdjoinRoot.root g ^ (p - 1))))
      (cE := CoordSpNs.prC hζ0 hζ0') (fun x => rfl) (CoordSpNs.prC_pow_eq_one hζ0 hζ0' hζp)
      (SpNS.spBlockExists_paired hpp hpK hgd hσ)
      (fun u => by
        obtain ⟨u₁, hu₁⟩ := hsurj _ hζ1 u.1
        obtain ⟨u₂, hu₂⟩ := hsurj _ hζ1' u.2
        exact ⟨(u₁, u₂), Prod.ext hu₁ hu₂⟩)
      (fun d hd => by
        obtain ⟨μ, ν⟩ := d
        rw [LinearMap.prodMap_apply, Prod.mk.injEq] at hd
        exact Prod.ext (hfix _ hζ1 μ hd.1) (hfix _ hζ1' ν hd.2))
      (CoordSpNs.formTransitive_pr hζ0 hζ0' hζp hζ hσ)
      (fun ω hωa hωnd hωc =>
        CoordSpNs.galSigns_le_twistGroup_pr hζ0 hζ0' hζp hζ hσ hωa hωnd hωc)
      (finrank_pr hpp hp2 hpq hgd)
      (fun e θ hθ hθc => eq_one_or_neg_one_pr hpp hp2 hpK hpq hgd hζ0 hζ0' e θ hθ hθc)
    exact ⟨r, τ, F, AdjoinRoot g × AdjoinRoot g, inferInstance, inferInstance, inferInstance,
      CoordSpNs.prC hζ0 hζ0', θ, hbody⟩
  · have hσ := SpNS.aeval_root_pow_pred hpp hpK hgd hpq
    obtain ⟨r, τ, F, θ, hbody⟩ := ggTBJomF_ofBlock hp2 hQ hT hAΩ hApow hAcomm hmax hne
      (D := AdjoinRoot g) (c := LinearMap.mulLeft K (AdjoinRoot.root g))
      (cE := CoordSpNs.sdC hζ0) (fun x => rfl) (CoordSpNs.sdC_pow_eq_one hζ0 hζp)
      (SpNS.spBlockExists_selfDual hpp hp2 hpK hgd hσ)
      (hsurj _ hζ1) (fun d hd => hfix _ hζ1 d hd) (CoordSpNs.formTransitive_sd hζp hζ0)
      (fun ω hωa hωnd hωc =>
        CoordSpNs.galSigns_le_twistGroup_sd hζp hζ hσ hζ0 hωa hωnd hωc)
      (finrank_sd hpp hp2 hpK hgd hpq)
      (fun e θ hθ hθc => eq_one_or_neg_one_sd hpp hp2 hpK hgd hpq hζ0 e θ hθ hθc)
    exact ⟨r, τ, F, AdjoinRoot g, inferInstance, inferInstance, inferInstance,
      CoordSpNs.sdC hζ0, θ, hbody⟩

end Blocks

end OrthTorus

end CFSG.StandardType

end
