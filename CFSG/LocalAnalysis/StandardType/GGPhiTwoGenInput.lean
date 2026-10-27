module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenDefs

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] noncomputable def phiTwoCompIn
    {τ : Tag} {K : Type} [Field K] (R : Subgroup (ModGL τ K))
    (g0 : ModGL τ (AlgebraicClosure K)) (β : Fin τ.rank → ℤ) : Subgroup ↥R :=
  ((rootSpan τ (AlgebraicClosure K) {β, -β}).map (MulAut.conj g0).toMonoidHom).comap
    ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp R.subtype)

theorem mem_phiTwoCompIn_iff
    {τ : Tag} {K : Type} [Field K] (R : Subgroup (ModGL τ K))
    {g0 : ModGL τ (AlgebraicClosure K)} {β : Fin τ.rank → ℤ} {x : ↥R} :
    x ∈ phiTwoCompIn R g0 β ↔
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * g0 ∈
        rootSpan τ (AlgebraicClosure K) {β, -β} := by
  rw [phiTwoCompIn, Subgroup.mem_comap, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  rfl

@[expose] def PhiTwoGenAt
    (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    ∀ (w : WeylGroup τ) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
      (g0 : ModGL τ (AlgebraicClosure K)), ExcIsLongest τ w → (∀ c, Fr c = c ^ Nat.card K) →
      g0 ∈ adjointGroup τ (AlgebraicClosure K) →
      Units.map (entrywiseHom Fr) g0 =
        g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w →
      (⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ}, PhiTwoRootGen.phiTwoComp g0 γ.1) = ⊤

@[expose] def PhiTwoTwE6GenInput :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (n : ℕ), 2 ≤ n → Nat.card K = (2 ^ n) ^ 2 →
    (∀ c, σ c = c ^ 2 ^ n) → ∀ (v : WeylGroup TwistTag.E6.tag)
      (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
      (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)), ExcIsLongest TwistTag.E6.tag v →
      (∀ c, Fr c = c ^ 2 ^ n) → g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) →
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v →
      (⨆ γ : {γ : Fin TwistTag.E6.tag.rank → ℤ // IsRoot TwistTag.E6.tag γ},
        phiTwoCompIn (twistedE6RootGroup K σ) g0 γ.1) = ⊤

end CFSG.StandardType

end
