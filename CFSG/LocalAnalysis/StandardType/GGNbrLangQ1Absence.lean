module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1Regimes
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGTableBTwDThree

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.S2MathAs51642Interfaces

theorem ggLabelIso_eq_of_exceptional {lab lab' : LargeEvenLabel}
    (hA : lab.tag ≠ .A) (hTwA : lab.tag ≠ .twA) (hB : lab.tag ≠ .B) (hC : lab.tag ≠ .C)
    (hD : lab.tag ≠ .D) (hTwD : lab.tag ≠ .twD) (h : GGLabelIso lab lab') : lab' = lab := by
  rcases h with h | ⟨hb, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h1⟩
  · exact h.symm
  · rcases hb with hb | hb
    · exact absurd hb hB
    · exact absurd hb hC
  · exact absurd (by rw [h1]) hD
  · exact absurd (by rw [h1]) hA
  · exact absurd (by rw [h1]) hTwD
  · exact absurd (by rw [h1]) hTwA
  · exact absurd (by rw [h1]) hTwD
  · exact absurd (by rw [h1]) hA

theorem ggConfig_false_of_rigid_label (hRig : GGLabelRigidInput)
    {S : ℕ → LargeEvenLabel → Prop}
    (hrigid : ∀ (p : ℕ) (lab lab' : LargeEvenLabel), S p lab → GGLabelIso lab lab' → lab' = lab)
    (hRank : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenSplit p lab → LargeEvenLabelAll lab fun R _ I _ =>
        ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X →
          Nat.card X < p ^ 3)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hM : CFSG.StandardType.LargeEvenMarking L (fun lab _ _ _ _ _ => S p lab)) : False := by
  have hst : LargeEvenStandardType p B x L := hcfg.1.2.2.2.2.2.2.2
  obtain ⟨hperf₁, lab₁, hΛ₁, hraw₁⟩ := hM
  obtain ⟨hperf₂, lab₂, hΛ₂, hraw₂⟩ := hst.1
  have has₁ : GGHasLabel lab₁ (↥L ⧸ Subgroup.center ↥L) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono (fun R _ I F hh => ?_) hraw₁
    obtain ⟨-, -, θ, -⟩ := hh
    exact ⟨θ⟩
  have has₂ : GGHasLabel lab₂ (↥L ⧸ Subgroup.center ↥L) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono (fun R _ I F hh => ?_) hraw₂
    obtain ⟨-, -, θ, -⟩ := hh
    exact ⟨θ⟩
  have hiso : GGLabelIso lab₁ lab₂ := hRig lab₁ lab₂ _ hΛ₁ hΛ₂ has₁ has₂
  obtain ⟨R₁, _, I₁, F₁, -, -, -, hS₁⟩ := largeEvenRawDatum_exists hraw₁
  have heq : lab₂ = lab₁ := hrigid p lab₁ lab₂ hS₁ hiso
  have hS₂ : S p lab₂ := by rw [heq]; exact hS₁
  refine ggThmIHyp_false_of_labelAll (S := S)
    (fun p lab hp hΛ hS hsplit => hRank p lab hp hΛ hS hsplit) hcfg.1 ?_
  refine ⟨hperf₂, lab₂, hΛ₂, ?_⟩
  refine largeEvenRawDatum_mono (fun R _ I F hh => ?_) hraw₂
  obtain ⟨hs, hna, θ, hsplit, hBN, hact⟩ := hh
  exact ⟨hs, hna, θ, hS₂, hsplit, hBN, hact⟩

theorem q1On_of_absence {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G), GGConfig p B Bs x L D J →
      CFSG.StandardType.LargeEvenMarking L (fun lab _ _ _ _ _ => S p lab) → False) :
    GGBstarInnerDiagJInputOn S := by
  intro G _ _ p B Bs x L D J hcfg hM
  exact (h G p B Bs x L D J hcfg
    (largeEvenMarking_mono (fun lab R _ I F θ hp => hp.1) hM)).elim

theorem q1SelectedTransfer_of_absence {S : ℕ → LargeEvenLabel → Prop}
    {Rel : ℕ → LargeEvenLabel → LargeEvenLabel → Prop}
    (h : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G), GGConfig p B Bs x L D J →
      CFSG.StandardType.LargeEvenMarking L (fun lab _ _ _ _ _ => S p lab) → False) :
    Q1SelectedTransfer S Rel := by
  intro G _ _ p B Bs x L D J hcfg
  unfold GGMarkingAll
  intro P hP
  obtain ⟨hperf, lab, hlab, hraw⟩ := hP
  refine ⟨hperf, lab, hlab, ?_⟩
  refine largeEvenRawDatum_mono (fun R _ I F hh => ?_) hraw
  obtain ⟨hs, hna, θ, hPθ⟩ := hh
  refine ⟨hs, hna, θ, hPθ, ?_⟩
  intro hS hNL hact
  have hmem : CFSG.StandardType.LargeEvenMarking L (fun lab _ _ _ _ _ => S p lab) := by
    refine ⟨hperf, lab, hlab, ?_⟩
    refine largeEvenRawDatum_mono (fun R' _ I' F' hh' => ?_) hraw
    obtain ⟨hs', hna', θ', hPθ'⟩ := hh'
    exact ⟨hs', hna', θ', hS⟩
  exact (h G p B Bs x L D J hcfg hmem).elim

end CFSG.StandardType
