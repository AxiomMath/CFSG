module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderClassicalDefs
public import CFSG.LocalAnalysis.StandardType.GGSixBstarRestSU
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderUOProj

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Inputs

@[expose] def GGPOmegaPlusD4Three (t : StatedLieTag) (n _f p : ℕ) : Prop :=
  t = .POmegaPlus ∧ n = 4 ∧ p = 3

@[expose] def GGPOmegaPlusNotD4Three (t : StatedLieTag) (n _f p : ℕ) : Prop :=
  t = .POmegaPlus ∧ ¬ (n = 4 ∧ p = 3)

@[expose] def GGPOmegaMinusLabel (t : StatedLieTag) (_n _f _p : ℕ) : Prop :=
  t = .POmegaMinus

@[expose] def GGSixBstarMonoFrameOn (P : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), P t n f p →
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ →
    ∃ (r : ℕ) (ι : Multiplicative (Fin r → ZMod p) →* G), Function.Injective ι ∧ ι.range = Bs ∧
      ∀ g ∈ ggM p B x L D J, g ∈ Subgroup.normalizer (Bs : Set G) → g ^ p = 1 →
        NoOffUO.GGMonoAct ι g

@[expose] def GGSixBstarProjFrameOn (P : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), P t n f p →
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ →
    ∃ (m : ℕ) (κ : G → (Fin m → ZMod p)), 4 ≤ m ∧
      (∀ b ∈ Bs, ∀ b' ∈ Bs, (∃ c : ZMod p, ∀ i, κ b i = κ b' i + c) → b = b') ∧
      (∀ v : Fin m → ZMod p, ∑ i, v i = 0 → ∃ b ∈ Bs, ∃ c : ZMod p, ∀ i, κ b i = v i + c) ∧
      ∀ g ∈ ggM p B x L D J, g ∈ Subgroup.normalizer (Bs : Set G) → g ^ p = 1 →
        ∃ (π : Equiv.Perm (Fin m)) (s : ZMod p), s ≠ 0 ∧ NoOffUO.IsProjRep κ Bs g π s

theorem ggNoOffender_of_monoFrameOn {P : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (h : GGSixBstarMonoFrameOn P) : GGSixBstarNoOffenderOn P := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  obtain ⟨r, ι, hinj, hrange, hmono⟩ := h G p B Bs x L D J t n f ψ hP hctx hC
  exact NoOffUO.noOffender_of_monoAct hctx.1.2.2.2.2.2.1.1 hctx.1.2.2.2.2.2.1.2.1 hinj hrange
    hmono

theorem ggNoOffender_of_projFrameOn {P : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (h : GGSixBstarProjFrameOn P) : GGSixBstarNoOffenderOn P := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  obtain ⟨m, κ, hm, hinj, hsurj, hrep⟩ := h G p B Bs x L D J t n f ψ hP hctx hC
  exact NoOffUO.noOffender_of_projRep hctx.1.2.2.2.2.2.1.1 hctx.1.2.2.2.2.2.1.2.1 hm
    hctx.2.1.2.1 κ hinj hsurj hrep

theorem ggSixBstarNoOffenderAt_PSU_of_frames (hS : GGSixBstarProjFrameOn GGPSUSplit)
    (hN : GGSixBstarMonoFrameOn GGPSUNonsplit) : GGSixBstarNoOffenderAt .PSU :=
  ggSixBstarNoOffenderAt_of_on .PSU (ggNoOffender_of_projFrameOn hS)
    (ggNoOffender_of_monoFrameOn hN) fun _ f p => by
      by_cases hp : p ∣ 2 ^ f + 1
      · exact Or.inl ⟨rfl, hp⟩
      · exact Or.inr ⟨rfl, hp⟩

theorem ggSixBstarNoOffenderAt_POmegaPlus_of_frame
    (hM : GGSixBstarMonoFrameOn GGPOmegaPlusNotD4Three)
    (hD4 : GGSixBstarNoOffenderOn GGPOmegaPlusD4Three) : GGSixBstarNoOffenderAt .POmegaPlus :=
  ggSixBstarNoOffenderAt_of_on .POmegaPlus hD4 (ggNoOffender_of_monoFrameOn hM) fun n _ p => by
    by_cases h43 : n = 4 ∧ p = 3
    · exact Or.inl ⟨rfl, h43⟩
    · exact Or.inr ⟨rfl, h43⟩

theorem ggSixBstarNoOffenderAt_POmegaMinus_of_frame
    (hM : GGSixBstarMonoFrameOn GGPOmegaMinusLabel) : GGSixBstarNoOffenderAt .POmegaMinus :=
  ggSixBstarNoOffenderAt_of_on .POmegaMinus (ggNoOffender_of_monoFrameOn hM)
    (ggNoOffender_of_monoFrameOn hM) fun _ _ _ => Or.inl rfl

end Inputs

end CFSG.StandardType
