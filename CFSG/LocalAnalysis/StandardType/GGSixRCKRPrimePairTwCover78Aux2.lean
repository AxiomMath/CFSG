module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairTwCover78Aux1
public import CFSG.LieType.AlgebraicGroups.SupportedNativeLang
public import CFSG.LieType.AlgebraicGroups.FrobeniusDiagramRealized

public noncomputable section

namespace CFSG.StandardType.RCKRP

variable {CoeffField : Type} [Field CoeffField] [IsAlgClosed CoeffField] [CharP CoeffField 2]
attribute [local instance] ZMod.algebra


open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Twist CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T

theorem rckTw78_lang_pt
    {τ : Tag} [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L]
    {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]
    (hf : 1 ≤ f) {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L)
    {π : Equiv.Perm (Fin τ.rank)} (hπ : ∀ i ∈ e6Set τ, π i ∈ e6Set τ)
    (hπ' : ∀ i ∈ e6Set τ, π.symm i ∈ e6Set τ)
    {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (e6Set τ))
    (hact : ∀ j ∈ e6Set τ, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ)) :
    ∃ q n₁ h : ModGL τ L, q ∈ subsystemGroup τ L (e6Set τ) ∧
      n₁ ∈ monomialSubgroup τ L ∧ h ∈ subsystemGroup τ L (e6Set τ) ∧ n = q * n₁ ∧
      (∀ j ∈ e6Set τ, ∀ c : L, n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L (π j) c ∧
        n₁ * yUnit τ L j c * n₁⁻¹ = yUnit τ L (π j) c) ∧
      ∀ g : ModGL τ L,
        n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ =
          h⁻¹ * (n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹) *
            h := by
  obtain ⟨q, n₁, hq, hn₁, hnq, hgen⟩ :=
    CFSG.RankThree.PartOne.KE6.exists_normalized (τ := τ) (L := L) hn hπ hπ' hu hact
  have hA := CFSG.RankThree.PartOne.KE6.mem_normalizer_subsystemGroup_of_conj
    (τ := τ) (L := L) hπ hπ' hgen
  obtain ⟨h, hh, hlang⟩ :=
    ((supported_native_affine_realization_and_Lang τ L (e6Set τ)).2 ℓ f hf n₁ hA).2.2.2 q hq
  refine ⟨q, n₁, h, hq, hn₁, hh, hnq, hgen, fun g => ?_⟩
  have h1 : q * (n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n₁⁻¹) * q⁻¹ =
      h⁻¹ * (n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹) *
        h := by
    simpa only [frobTwistGL_apply] using hlang g
  rw [hnq]
  convert h1 using 1 <;> group

end CFSG.StandardType.RCKRP
