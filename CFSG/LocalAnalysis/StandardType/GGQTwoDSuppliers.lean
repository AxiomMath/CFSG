module

public import CFSG.LocalAnalysis.StandardType.GGQTwoPhanDData

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.PhanDn.QTwo

section Cases

@[expose] def GGSecFivePhanDQTwoAt (R : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e →
        ∀ (m : ℕ) (e' : Fin m ≃ ι), R m → M = (ggCoxeterMatrixD m).reindex e' →
        (∃ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e ∧ Nat.card (ggRankOneIn L Bs r) = 6) →
        GGSecFiveData p B x L D J ∨
          ∃ (U : Fin m → Subgroup G) (W : Fin m → Fin m → Subgroup G),
            QTwoWeakPhanSystemD (GaloisField 2 2) m (ggG0 p B x L D J) U W

@[expose] def GGSecFivePhanDQTwoFour : Prop :=
  GGSecFivePhanDQTwoAt fun m => m = 4

@[expose] def GGSecFivePhanDQTwoFiveSix : Prop :=
  GGSecFivePhanDQTwoAt fun m => m = 5 ∨ m = 6

@[expose] def GGSecFivePhanDQTwoSeven : Prop :=
  GGSecFivePhanDQTwoAt fun m => 7 ≤ m

theorem ggSecFivePhanDQTwoSystemInput_of_cases (h4 : GGSecFivePhanDQTwoFour)
    (h56 : GGSecFivePhanDQTwoFiveSix) (h7 : GGSecFivePhanDQTwoSeven) :
    GGSecFivePhanDQTwoSystemInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg ht hs ι M e hpres m e' hm hM hsix
  have hcases : m = 4 ∨ (m = 5 ∨ m = 6) ∨ 7 ≤ m := by omega
  rcases hcases with h | h | h
  · exact h4 G p B Bs x L D J 𝒦 hcfg ht hs ι M e hpres m e' h hM hsix
  · exact h56 G p B Bs x L D J 𝒦 hcfg ht hs ι M e hpres m e' h hM hsix
  · exact h7 G p B Bs x L D J 𝒦 hcfg ht hs ι M e hpres m e' h hM hsix

end Cases

end CFSG.StandardType.QTwo

end
