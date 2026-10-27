module

public import CFSG.LocalAnalysis.StandardType.GGLinearFusionFrame
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwo

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix

@[expose] def GGLinearSemisimpleComponentInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m f : ℕ)
    (ψ : SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* G),
    ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) →
    ∀ (P : GL (Fin (m + 1)) (GaloisField 2 f)) (d : Fin (m + 1) → (GaloisField 2 f)ˣ) (b : G),
      (b, LinFusion.ggFrameDiag P d) ∈ LinFusion.ggInducedPairs ψ →
      ∀ L₁ : Subgroup G, IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer {b}) →
        ∃ I : Finset (Fin (m + 1)), L₁ = LinFusion.ggFrameBlock (GaloisField 2 f) ψ P I ∧
          ∀ i ∈ I, ∀ j ∈ I, d i = d j

section Inputs

@[expose] def GGLinearFrameInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (m f : ℕ) (ψ : (ggU .PSL (m + 1) f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU .PSL (m + 1) f).D .PSL (m + 1) f ψ →
    GGSixStepOne p B Bs x L D J → p ∣ 2 ^ f - 1 →
      ∃ (P : GL (Fin (m + 1)) (GaloisField 2 f)) (I₀ : Finset (Fin (m + 1))),
        Bs ≤ LinFusion.ggFrameTorus (GaloisField 2 f) ψ P ∧
        (∀ b ∈ Bs, b ∈ Subgroup.centralizer
          (LinFusion.ggFrameBlock (GaloisField 2 f) ψ P I₀ : Set G) → b ∈ D) ∧
        ∀ I : Finset (Fin (m + 1)), Nat.card (Bs ⊓ Subgroup.centralizer
          (LinFusion.ggFrameBlock (GaloisField 2 f) ψ P I : Set G) : Subgroup G) ≤ p ^ 2 →
            I₀.card ≤ I.card

@[expose] def GGStepTwoUnitaryFusionInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU .PSU n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU .PSU n f).D .PSU n f ψ → GGSixStepOne p B Bs x L D J →
    p ∣ 2 ^ f + 1 →
      ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ →
        ∃ m ∈ Subgroup.normalizer (Bs : Set G), m⁻¹ * b * m ∈ D

theorem ggStepTwoLinearFusion_PSL_of_frame (hcomp : GGLinearSemisimpleComponentInput)
    (hL : GGLinearFrameInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {m f : ℕ} {ψ : (ggU .PSL (m + 1) f).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU .PSL (m + 1) f).D .PSL (m + 1) f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hp : p ∣ 2 ^ f - 1) {b : G} {L₁ : Subgroup G}
    (hpair : GGStepTwoPair p B Bs x L D J b L₁) :
    ∃ w ∈ Subgroup.normalizer (Bs : Set G), w ∈ ggG0 p B x L D J ∧ w⁻¹ * b * w ∈ D := by
  obtain ⟨P, I₀, hBT, hD, hrich⟩ := hL G p B Bs x L D J m f ψ hctx s1 hp
  obtain ⟨⟨-, hBel, -, hSC⟩, -, -, ⟨hrange, hker⟩, -⟩ := hctx.2
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by rw [hrange]; exact s1.1
  obtain ⟨hbB, -, hcomp₁, hcard₁⟩ := hpair
  obtain ⟨d, hd⟩ := hBT hbB
  have hcomp₂ : IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer {b}) := by
    rw [hrange]
    exact hcomp₁
  obtain ⟨I, hLI, hdI⟩ := hcomp G m f ψ hker P d b hd L₁ hcomp₂
  have hcard : I₀.card ≤ I.card := hrich I (by rw [← hLI]; exact hcard₁)
  obtain ⟨w, hwN, hwR, hwB, hwC⟩ :=
    LinFusion.exists_frame_conj_mem hC hBT (fun b hb => hBel.2 b hb) hSC hcard hbB hd hdI
  exact ⟨w, hwN, hrange ▸ hwR, hD _ hwB hwC⟩

theorem ggStepTwoLinearFusionInput_of_frame (hcomp : GGLinearSemisimpleComponentInput)
    (hL : GGLinearFrameInput) (hU : GGStepTwoUnitaryFusionInput) :
    GGStepTwoLinearFusionInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair
  rcases hlin with ⟨rfl, hp⟩ | ⟨rfl, hp⟩
  · obtain ⟨-, -, hn, -⟩ := hctx.2.2.2.1.1
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨w, hwN, -, hw⟩ := ggStepTwoLinearFusion_PSL_of_frame hcomp hL hctx s1 hp hpair
    exact ⟨w, hwN, hw⟩
  · exact hU G p B Bs x L D J n f ψ hctx s1 hp b L₁ hpair

end Inputs

end CFSG.StandardType
