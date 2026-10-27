module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesAbstractFrame
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwistedFixed
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwistedNormalForm

public section

namespace CFSG.StandardType

namespace ExcFrames

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration CFSG.Open

section CentralizeTw


theorem centralizes_twistedE6 {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) {θ : K →+* K}
    (hθ : σ.toRingHom = θ) {G : Type} [Group G] {p m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hp3 : p ≠ 3)
    (hdata : ∀ f₀ : ℕ, 1 ≤ f₀ → ∀ (K₀ : Type) [Field K₀] [Finite K₀],
      Nat.card K₀ = (2 ^ f₀) ^ 2 → ∀ σ₀ : K₀ ≃+* K₀, (∀ c, σ₀ c = c ^ 2 ^ f₀) →
        ((2 ^ f₀ : ℕ) : ZMod p) = ((2 ^ f : ℕ) : ZMod p) →
          SylowTorus ↥(twistedE6RootGroup K₀ σ₀) p m)
    (ψ : ↥(graphFixedRootGroup TwistTag.E6 K θ) →* G) (hψ : Function.Injective ψ)
    {Bs : Subgroup G} (hBsR : Bs ≤ ψ.range) (hBs : IsElemAbelian p Bs)
    (hBsc : p ^ m ≤ Nat.card Bs) {g : G} (hgN : g ∈ Subgroup.normalizer (ψ.range : Set G))
    (hgB : g ∈ Subgroup.normalizer (Bs : Set G)) (hgp : g ^ p = 1) :
    g ∈ Subgroup.centralizer (Bs : Set G) := by
  subst hθ
  classical
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hk : ¬ p ∣ 3 := fun hd =>
    hp3 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).1 hd)
  have hSyl : SylowTorus ↥(twistedE6RootGroup K σ) p m := hdata f hf K hK σ hσ rfl
  refine centralizes_of_induced_abstract (Γ := ModGL TwistTag.E6.tag K) (k := 3) hk
    (twistedE6RootGroup K σ) hSyl ?_ ψ hψ hBsR hBs hBsc hgN hgB hgp
  intro α hαp
  obtain ⟨Dg, x, δ, hDgN, hDg3, hx, hδ, hαx⟩ :=
    exists_normalForm_twistedE6 hf hK σ hσ rfl α hαp
  obtain ⟨E, hEC, hEel, hEcard, hEfix⟩ :=
    exists_fixedElemAbelian_twistedE6 hf hK hσ hp2 hδ hdata
  exact ⟨Dg, x, Units.map (entrywiseHom δ.toRingHom), E, hDgN, hDg3, hx, hEC, hEel, hEcard.ge,
    hEfix, hαx⟩

end CentralizeTw

end ExcFrames

end CFSG.StandardType
