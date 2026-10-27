module

public import CFSG.LocalAnalysis.StandardType.GGTwE6E4bOriginalLift
public import CFSG.LocalAnalysis.StandardType.GGTwE6E4bActorSeed
public import CFSG.LocalAnalysis.ComponentInitial.EvenPairingCover

public noncomputable section


namespace CFSG.StandardType.E4bOriginalLift

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.StandardType.E4bLift

variable {n : ℕ} {K : Type} [Field K] [Finite K]
  {σ : K ≃+* K} {ε : ↥(twistedE6RootGroup K σ) ≃* TwE6Delta.RecipeR K n}
  {J : Type} [Group J] [Finite J] {ψ : J →* TwE6Delta.RecipeR K n}
  {F : Type} [Field F] [Finite F] (ι : K →+* F) (t : ↥(e6Data_valid.minGroup F))
  {ζ ω : Fˣ}

local notation "M₀" => (originalM (K := K) (F := F) (σ := σ) (ε := ε) (ψ := ψ) (ι := ι) (t := t))
local notation "s₀" => (Subtype.val (fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ω)))

theorem originalM_inverted_actor_seed (τ : MulAut J) (g : J)
    (hω3 : ω ^ 3 = 1)
    (hτg : M₀ (τ g) = s₀ * M₀ g * s₀⁻¹)
    (hg : M₀ g * s₀ * (M₀ g)⁻¹ = s₀⁻¹) :
    M₀ (g * (τ g)⁻¹) = s₀ := by
  have hs3 : s₀ ^ 3 = 1 := by
    have h := congrArg (fun x : ↥(adjointGroup Tag.E6 F) => (x : ModGL Tag.E6 F))
      (show (fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ω)) ^ 3 = 1 by
        rw [← map_pow, fixedA2Scalar_pow_three hω3, map_one])
    exact h
  have hs2 : s₀ * s₀ = s₀⁻¹ := eq_inv_iff_mul_eq_one.mpr (by
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using hs3)
  calc
    M₀ (g * (τ g)⁻¹) = M₀ g * (s₀ * M₀ g * s₀⁻¹)⁻¹ := by
      rw [map_mul, map_inv, hτg]
    _ = (M₀ g * s₀ * (M₀ g)⁻¹) * s₀⁻¹ := by group
    _ = s₀⁻¹ * s₀⁻¹ := by rw [hg]
    _ = (s₀ * s₀) * s₀⁻¹ := by rw [hs2]
    _ = s₀ := by group

theorem exists_originalCube_inducing_inverted_actor
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center J)
    (hperf : commutator J = ⊤) (hF : 4 < Nat.card F) (h3 : 3 ∣ 2 ^ n + 1)
    (hζ : ζ ^ 3 = ω) (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (τ : MulAut J) (hτ3 : τ ^ 3 = 1) (g : J)
    (hinv : MulAut.conj g * τ * (MulAut.conj g)⁻¹ = τ⁻¹)
    (hτg : M₀ (τ g) = s₀ * M₀ g * s₀⁻¹)
    (hg : M₀ g * s₀ * (M₀ g)⁻¹ = s₀⁻¹)
    {Ω : Type} [Field Ω] (κ : F →+* Ω) (σF : Ω →+* Ω)
    (hσF : ∀ b : Ω, σF b = b ^ Nat.card F) :
    ∃ c : J, c ^ 3 = 1 ∧ c ≠ 1 ∧ MulAut.conj c = τ ∧ M₀ c = s₀ ∧
      ∀ (v : MulAut J) (w : MulAut (TwE6Delta.RecipeR K n)),
        (∀ j, ψ (v j) = w (ψ j)) →
        ∀ (X : ↥(adjointGroup Tag.E6 F)),
          (∀ j, M₀ (v j) = (X : ModGL Tag.E6 F) * M₀ j * (X : ModGL Tag.E6 F)⁻¹) →
          (baseChangeGL (τ := Tag.E6) κ (X : ModGL Tag.E6 F) ∈
            Subgroup.normalizer (CFSG.StandardType.TwE6E4bTorus.fixedA2Torus Ω)) →
          ∀ (m : ℤ),
            X * fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ω) * X⁻¹ =
              (fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ω)) ^ m →
            v c = c ^ m := by
  let d : J := g * (τ g)⁻¹
  have hd : M₀ d = s₀ := originalM_inverted_actor_seed ι t τ g hω3 hτg hg
  have hconjd : MulAut.conj d = τ := E4bActorSeed.conj_of_inverted_cube τ hτ3 g hinv
  obtain ⟨c, hc3, hc1, hcd, hcov⟩ :=
    exists_originalCube_covariance_of_normalizer (K := K) (F := F) (σ := σ) (ε := ε)
      (ψ := ψ) (ι := ι) (t := t) hn hK hσ hψ hker hperf hF h3 hζ hω3 hω1 hd κ σF hσF
  have hMc : M₀ c = s₀ := by
    calc M₀ c = M₀ d := by
           simp only [originalM_eq_comp_originalMR, MonoidHom.comp_apply, hcd]
      _ = s₀ := hd
  refine ⟨c, hc3, hc1, ?_, hMc, hcov⟩
  rw [← hconjd]
  apply MulEquiv.ext
  intro x
  exact CFSG.LocalAnalysis.ComponentInitial.EvenCoverPairing.conj_eq_of_map_eq hker hcd x

end CFSG.StandardType.E4bOriginalLift
