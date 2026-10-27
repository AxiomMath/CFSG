module

public import CFSG.RankThree.Chevalley.SteinbergCDTrialityThreeSixSylow
public import CFSG.RankThree.Chevalley.SteinbergCFERootSL2Traces
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.LieType.Chevalley.OddF4CosetDescent
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.Lattice CFSG.RankThree.LocalRank
open Subgroup
open scoped Matrix

theorem triality_normal_form_full
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    (∀ α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      ∃ gδ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom × (K ≃+* K),
        α = MulAut.conj gδ.1 * fieldActor σ gδ.2) ∧
    (∃ Θ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* (K ≃+* K),
      (∀ α g δ, α = MulAut.conj g * fieldActor σ δ → Θ α = δ) ∧
      Θ.ker = (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range ∧
      ∀ α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), α ^ 2 = 1 →
        Θ α = 1 ∨ (Even f ∧ ∀ c, Θ α c = c ^ (ℓ ^ (3 * f / 2)))) ∧
    IsCyclic (K ≃+* K) ∧
    Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ := by
  rcases eq_or_ne ℓ 2 with rfl | hℓ2
  · obtain ⟨-, hex, ⟨Θ, hΘ, -, hker, hinv⟩, hcyc, -, -, hZ, -⟩ :=
      even_triality_exact_automorphism_normal_form hf K hK σ hσ
    exact ⟨fun α => (hex α).exists, ⟨Θ, hΘ, hker, hinv⟩, hcyc, hZ⟩
  · obtain ⟨-, hex, ⟨Θ, hΘ, -, hker, hinv⟩, hcyc, -, -, hZ, -⟩ :=
      odd_triality_exact_automorphism_normal_form hℓ hℓ2 hf K hK σ hσ
    exact ⟨fun α => (hex α).exists, ⟨Θ, hΘ, hker, hinv⟩, hcyc, hZ⟩

theorem fieldActor_trace_fixed
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    {η : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    {y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} {δ : K ≃+* K}
    (hη : η = MulAut.conj y * fieldActor σ δ) {r : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hr : η r = r) :
    δ (LinearMap.trace K (RootModule TwistTag.D4.tag K)
        ((r : ModGL TwistTag.D4.tag K) : Module.End K (RootModule TwistTag.D4.tag K))) =
      LinearMap.trace K (RootModule TwistTag.D4.tag K)
        ((r : ModGL TwistTag.D4.tag K) : Module.End K (RootModule TwistTag.D4.tag K)) := by
  have h1 : ((η r : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
      (y : ModGL TwistTag.D4.tag K) * baseChangeGL δ.toRingHom (r : ModGL TwistTag.D4.tag K) *
        (y : ModGL TwistTag.D4.tag K)⁻¹ := by
    rw [hη, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, coe_fieldActor, units_map_entrywiseHom_eq_baseChangeGL]
  rw [hr] at h1
  have h2 := congrArg (fun g : ModGL TwistTag.D4.tag K =>
    LinearMap.trace K (RootModule TwistTag.D4.tag K)
      (g : Module.End K (RootModule TwistTag.D4.tag K))) h1
  simp only [Units.val_mul] at h2
  rw [LinearMap.trace_mul_comm, ← mul_assoc, Units.inv_mul, one_mul, trace_baseChangeGL] at h2
  exact h2.symm

theorem threeSixEmb_injective
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (σ : K ≃+* K) :
    Function.Injective (threeSixEmb K Ω σ) :=
  (baseChangeGL_injective (τ := TwistTag.D4.tag) (algebraMap K Ω)).comp Subtype.val_injective

theorem threeSix_conj_dichotomy
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (Ω : Type)
    [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {d : ℕ}
    (hd : (d : ℤ) = ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * (ℓ ^ f : ℕ) + 1) {g : ModGL TwistTag.D4.tag Ω}
    (hgG : g ∈ adjointGroup TwistTag.D4.tag Ω) (hFg : trialityFrob Ω Fr g = g * threeSixN Ω ε)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpd : p ∣ d)
    (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (hx : orderOf x = p) :
    ∃ c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, ∃ a : Fin TwistTag.D4.tag.rank → Ωˣ,
      rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorsion Ω Fr ε p ∧
      rootDiagUnit TwistTag.D4.tag a ≠ 1 ∧
      threeSixEmb K Ω σ (c * x * c⁻¹) = g * rootDiagUnit TwistTag.D4.tag a * g⁻¹ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Finite (Module.End K (RootModule TwistTag.D4.tag K)) := Module.finite_of_finite K
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, -, hall⟩ :=
    triality_three_six_tori_Sylow_and_root_kernels hℓ hf K hK σ hσ Ω Fr hFr hε hd
  obtain ⟨-, -, hp'⟩ := hall g hgG hFg
  obtain ⟨-, hconj, -⟩ := hp' p hp hp3 hpd
  have hPx : IsPGroup p (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨c, hc⟩ := hconj _ hPx
  obtain ⟨u, hu, hux⟩ := hc ⟨x, mem_zpowers x, rfl⟩
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hu.1
  have hgx : threeSixEmb K Ω σ (c * x * c⁻¹) = g * rootDiagUnit TwistTag.D4.tag a * g⁻¹ :=
    hux.symm
  have hx1 : (c * x * c⁻¹) ^ p = 1 := by
    rw [conj_pow, ← hx, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  refine ⟨c, a, ⟨hu, ?_⟩, fun h1 => ?_, hgx⟩
  · have h2 : (g * rootDiagUnit TwistTag.D4.tag a * g⁻¹) ^ p = 1 := by
      rw [← hgx, ← map_pow, hx1, map_one]
    rwa [conj_pow, conj_eq_one_iff] at h2
  · rw [h1, mul_one, mul_inv_cancel] at hgx
    have h3 : c * x * c⁻¹ = 1 := threeSixEmb_injective K Ω σ (hgx.trans (map_one _).symm)
    rw [conj_eq_one_iff] at h3
    rw [h3, orderOf_one] at hx
    exact hp.one_lt.ne hx

end CFSG.RankThree.Chevalley
