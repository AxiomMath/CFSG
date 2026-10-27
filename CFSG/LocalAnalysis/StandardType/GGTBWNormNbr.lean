module

public import CFSG.LocalAnalysis.StandardType.GGGammaHypsK
public import CFSG.LocalAnalysis.StandardType.GGTBWNorm
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTBWNormInputNbr (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
    GGInnerDiagOnLab S p Bs K →
    ∀ (hBsN : Bs ≤ Subgroup.normalizer (K : Set G)) [Fact p.Prime]
      (Λ : Type) [Fintype Λ] [DecidableEq Λ] (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
      (V : Type) [AddCommGroup V] [Module (ZMod p) V]
      (ι : Additive ↥(ggGamma K hBsN).range ≃+ V) (φ : Λ → MulAut ↥(ggGamma K hBsN).range)
      (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V),
      GGIsWeylMatrix M → GGIntCartan M C → (∀ i j, α i (h j) = (C i j : ZMod p)) →
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) →
      ggAutomizer (MulAut.conj : K →* MulAut K).range (ggGamma K hBsN).range =
        Subgroup.closure (Set.range φ) →
      ∀ g ∈ Subgroup.normalizer (Bs : Set G), ∀ hgK : g ∈ Subgroup.normalizer (K : Set G),
        ∀ φ' : MulAut ↥(ggGamma K hBsN).range,
          (∀ a, ((φ' a : ↥(ggGamma K hBsN).range) : MulAut K) =
            K.normalizerMonoidHom ⟨g, hgK⟩ * a * (K.normalizerMonoidHom ⟨g, hgK⟩)⁻¹) →
          GGWNormConcl ι φ h α φ'

theorem ggTBWNormInputNbr_of_labels {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSCLift p R I) :
    GGTBWNormInputNbr S := by
  intro G _ _ p B Bs x L D J y K hres hM hBsN _ Λ _ _ M C V _ _ ι φ hh α hMw hC hpair hlin hA
    g hg hgK φ' hφ'
  have hp : p.Prime := hres.1.1.2.2.2.2.2.1.1
  obtain ⟨hKc, lab, -, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, -, hBs3⟩, hT⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hAe, hAI, h3, hsc⟩ := ggGamma_range_hypsSC_K hres θ hBsN hBs3
  have hrank : ∀ r, GGTorusLift p r R → p ^ r ≤ Nat.card (ggGamma K hBsN).range := by
    intro r hlift
    have hcfg : GGConfig p B Bs x L D J := hres.1
    have hS : LargeEvenSHat p B y K := hres.2.2.2.2.1.1
    have hBBs : B ≤ Bs := hcfg.2.1.1
    have hBN : B ≤ Subgroup.normalizer (K : Set G) := hBBs.trans hBsN
    have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hS.2.2.2.1
    have hcA := card_range_ggGamma_mul_of_sHat hp hS hBN
    have hle : Nat.card (ggGamma K hBN).range ≤ Nat.card (ggGamma K hBsN).range := by
      refine Subgroup.card_le_of_le ?_
      rintro _ ⟨b, rfl⟩
      exact ⟨⟨b, hBBs b.2⟩, rfl⟩
    have h1 := succ_le_twoLocalRank_of_torusLift hp hKy (hS.1.1.2 y hS.2.1) hS.2.2.1 hKc θ hlift
    have h2 : p ^ (r + 1) ≤ Nat.card (ggGamma K hBN).range * p := by
      rw [hcA, hS.1.2.1]
      exact Nat.pow_le_pow_right hp.pos h1
    rw [pow_succ] at h2
    exact (Nat.le_of_mul_le_mul_right h2 hp.pos).trans hle
  exact hT K (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hKc _ hAe hAI h3 hsc
    hrank Λ M C V ι φ hh α hMw hC hpair hlin hA φ'
    ⟨_, Subgroup.mem_top _, normalizerMonoidHom_mem_normalizer_range_ggGamma hBsN hg hgK, hφ'⟩

end CFSG.StandardType
