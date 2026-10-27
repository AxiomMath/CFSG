module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKMap
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def S16kStar (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  ∃ (ρ : Vtil V₀ V hV →* vStar D.M V₀ V hV L)
    (θ : ↥(lBar V₀ V hV L) →* ↥(lStar D.M V₀ V hV L)),
    Function.Surjective θ ∧
    (∀ (h : ↥(lBar V₀ V hV L)) (w : Vtil V₀ V hV),
      ρ ((h : MulAut (Vtil V₀ V hV)) w) =
        ((θ h : ↥(lStar D.M V₀ V hV L)) : MulAut (vStar D.M V₀ V hV L)) (ρ w)) ∧
    ρ.ker = commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L) ∧
    (commSub ⊤ (lBar V₀ V hV L)).map ρ = wStar D.M V₀ V hV L

variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem S16kStar.realizes_map (hs : S16kStar D V₀ V L hV) {Dm : FFModel}
    (hR : Dm.Realizes (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L))) :
    Dm.Realizes (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ := by
  obtain ⟨ρ, θ, hθ, hequiv, hker, himg⟩ := hs
  have h1 := s16k_realizes_map hR ρ hker.le θ hθ hequiv
  have h2 : (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)).map ρ = ⊥ :=
    (Subgroup.map_eq_bot_iff _).2 hker.ge
  rwa [h2, himg] at h1

theorem S16kStar.natural_map (hs : S16kStar D V₀ V L hV) {Dm : FFModel}
    (hfix : commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L) = ⊥)
    (hR : Dm.Realizes (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L)) ⊥) :
    Dm.Realizes (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ :=
  hs.realizes_map (hfix ▸ hR)

theorem S16kStar.sumOfNat_map (hs : S16kStar D V₀ V L hV)
    {N : Subgroup (MulAut (Vtil V₀ V hV)) → Subgroup (Vtil V₀ V hV) → Subgroup (Vtil V₀ V hV) →
      Prop}
    {N' : Subgroup (MulAut (vStar D.M V₀ V hV L)) → Subgroup (vStar D.M V₀ V hV L) →
      Subgroup (vStar D.M V₀ V hV L) → Prop} {k : ℕ}
    (hN : ∀ (ρ : Vtil V₀ V hV →* vStar D.M V₀ V hV L)
      (θ : ↥(lBar V₀ V hV L) →* ↥(lStar D.M V₀ V hV L)), Function.Surjective θ →
      (∀ (h : ↥(lBar V₀ V hV L)) (w : Vtil V₀ V hV),
        ρ ((h : MulAut (Vtil V₀ V hV)) w) =
          ((θ h : ↥(lStar D.M V₀ V hV L)) : MulAut (vStar D.M V₀ V hV L)) (ρ w)) →
      ρ.ker = commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L) →
      ∀ I : Subgroup (Vtil V₀ V hV),
        commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L) ≤ I →
        N (lBar V₀ V hV L) I (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) →
        N' (lStar D.M V₀ V hV L) (I.map ρ) ⊥)
    (hS : SumOfNat N (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) k) :
    SumOfNat N' (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ k := by
  obtain ⟨ρ, θ, hθ, hequiv, hker, himg⟩ := hs
  have h2 : (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)).map ρ = ⊥ :=
    (Subgroup.map_eq_bot_iff _).2 hker.ge
  have h1 := s16k_sumOfNat_map hS ρ hker.le (fun I hI hNI => by
    rw [h2]
    exact hN ρ θ hθ hequiv hker I hI hNI)
  rwa [h2, himg] at h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
