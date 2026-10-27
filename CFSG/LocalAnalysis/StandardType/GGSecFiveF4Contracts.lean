module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveDataResF4
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGSecFiveF4SmallDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGSecFiveF4OriginalTypesInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J → 𝒦.Nonempty →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → GGIsWeylMatrixF4 M →
        (GGWeylOfType p (CoxeterMatrix.A 3) (ggAutomizer L Bs) ∨
          GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer L Bs))

@[expose] def GGSecFiveF4OriginalBCPairInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → GGIsWeylMatrixF4 M →
        GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer L Bs) →
        GGSecFiveWeylAt p B Bs x L D J M

@[expose] def GGSecFiveF4SmallExclusionInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (ks : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J ks →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs ks)),
        GGCoxeterPres p (ggAutomizerJoin L Bs ks) M e → GGIsWeylMatrixF4 M →
        GGWeylOfType p (CoxeterMatrix.A 3) (ggAutomizer L Bs) →
        (∀ K ∈ ks, ggAutomizer L Bs ⊔ ggAutomizer K Bs ≠ ggAutomizerJoin L Bs ks) →
        p = 3 → GGHasLabel ⟨.A, 3, 2⟩ (L ⧸ Subgroup.center L) →
        (∀ K ∈ ks, GGHasLabel ⟨.A, 5, 1⟩ (K ⧸ Subgroup.center K)) →
        False

theorem ggSecFiveF4SmallData_of_exclusion
    (h : GGSecFiveF4SmallExclusionInput) : GGSecFiveF4SmallDataInput := by
  intro G _ _ p B Bs x L D J ks hcfg hT1 ι M e hpres hType hA3 hNoSpan hp3 hLabL hLabK
  exact (h G p B Bs x L D J ks hcfg hT1 ι M e hpres hType hA3 hNoSpan hp3 hLabL hLabK).elim

theorem ggSecFiveDataResAt_F4_of_contracts
    (hF : GGSecFiveWeylF4ResInput) (hTypes : GGSecFiveF4OriginalTypesInput)
    (hBCPair : GGSecFiveF4OriginalBCPairInput) (hLabels : GGSecFiveF4SmallLabelInput)
    (hSmall : GGSecFiveF4SmallDataInput) :
    GGSecFiveDataResAt (fun M => GGIsWeylMatrixF4 M) := by
  refine ggSecFiveDataResAt_F4_of_weylF4Res hF ?_
  intro G _ _ p B Bs x L D J 𝒦 hcfg hReg hCard hNoSpan ι M e hpres hType
  rcases hTypes G p B Bs x L D J 𝒦 hcfg hReg (Finset.card_pos.1 (by omega)) ι M e hpres hType with
    hA3L | hB3L
  · obtain ⟨hp3, hLabL, hLabK⟩ :=
      hLabels G p B Bs x L D J 𝒦 hcfg hReg ι M e hpres hType hA3L hNoSpan
    exact hSmall G p B Bs x L D J 𝒦 hcfg hReg ι M e hpres hType hA3L hNoSpan hp3 hLabL hLabK
  · obtain ⟨y, K, hN, hW⟩ :=
      hBCPair G p B Bs x L D J 𝒦 hcfg hReg ι M e hpres hType hB3L
    obtain ⟨e', hM⟩ := hType
    rw [hM] at hW
    exact hF G p B Bs x L D J hcfg.1 hcfg.2.1 ⟨y, K, hN, hW.of_reindex⟩ hReg

end CFSG.StandardType

end
