module

public import CFSG.LocalAnalysis.StandardType.GGRootNormInner
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TriD4InnerField

public section

namespace CFSG.StandardType.LieKnownR2.TriD4.Inner

open CFSG.Open CFSG.StandardType CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedD4
  CFSG.SeitzReduction
open scoped commutatorElement

theorem triD4_inner_C0
    {K : Type} [Field K] [Finite K] (σ : K →+* K) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    GGRootNormInner (Bridge.triD4C0HighRoot K σ) := by
  have hσsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  let σ' : K ≃+* K := RingEquiv.ofBijective σ ⟨σ.injective, hσsurj⟩
  have hσ' : σ'.toRingHom = σ := rfl
  have hσ'f : ∀ c, σ' c = c ^ (2 ^ f) := hσ
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK3
  have hσ3 : ∀ c, σ' (σ' (σ' c)) = c := by
    intro c
    haveI : Fintype K := Fintype.ofFinite K
    have hexp : ((c ^ 2 ^ f) ^ 2 ^ f) ^ 2 ^ f = c ^ ((2 ^ f) ^ 3) := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring
    rw [hσ'f, hσ'f, hσ'f, hexp, ← hK, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  obtain ⟨-, hnorm, hΘex, -, -, -, -, -⟩ :=
    even_triality_exact_automorphism_normal_form hf K hK σ' hσ'f
  obtain ⟨Θ, hΘ, -⟩ := hΘex
  intro y hy2 hyR hymod
  obtain ⟨w, hw, -⟩ := hnorm y
  obtain ⟨g, δ⟩ := w
  have hgδ : y = MulAut.conj g * fieldActor (t := TwistTag.D4) σ' δ := hw
  have hfix : ∀ c : K, σ' c = c → δ c = c :=
    triD4_delta_fixes_k σ' hσ3 hf hK hσ'f hgδ hyR (fun n hn => hymod n hn)
  have h2 : ∃ n : ℕ, δ ^ 2 ^ n = 1 := by
    let y' : MulAut (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom) := y
    have hgδ' : y' = MulAut.conj g * fieldActor (t := TwistTag.D4) σ' δ := hgδ
    have hΘy' : Θ y' = δ := hΘ y' g δ hgδ'
    obtain ⟨n, hn⟩ := hy2
    refine ⟨n, ?_⟩
    have hn' : y' ^ 2 ^ n = 1 := hn
    have h := congrArg Θ hn'
    rw [map_pow Θ y' (2 ^ n), hΘy', map_one] at h
    exact h
  have hδ1 : δ = 1 := triD4_delta_eq_one_of_fixes_k σ' hK hσ'f hfix h2
  refine ⟨g, ?_⟩
  rw [hgδ, hδ1, fieldActor_one, mul_one]
  rfl

theorem ggRootNormInner_triD4_highRoot
    {K : Type} [Field K] [Finite K] (σ : K →+* K) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    GGRootNormInner ((twistedDatum σ).rootGroup (highRoot .G2)) := by
  have hC0 := triD4_inner_C0 σ hf hK hσ
  have h := ggRootNormInner_map_mulEquiv
    (Bridge.triD4BridgeEquiv σ hf hK hσ).symm hC0
  have hEq := Bridge.triD4BridgeEquiv_twistedRootGroup_highRoot σ hf hK hσ
  rw [← hEq, GGRootNorm.map_symm_map] at h
  exact h

end CFSG.StandardType.LieKnownR2.TriD4.Inner
