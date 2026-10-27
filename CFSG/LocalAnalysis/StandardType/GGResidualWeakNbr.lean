module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinOutWeakDefs
public import CFSG.LocalAnalysis.StandardType.GGNSJoinQFourExact
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

section Weak


@[expose] def GGRk1ResidualWeakInputExOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦 ∨ (T M ∧
            (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) ∧
            GGSecFiveWeakNbr p B Bs x L D J 𝒦 X)) →
          ¬ GGSplitLie p X → ¬ GGMemberUnitary p Bs X →
          ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → GGRk1ConclEx p Bs X r

@[expose] def GGGenResidualWeakInputOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦 ∨ (T M ∧ GGSecFiveWeakNbr p B Bs x L D J 𝒦 X)) →
          ¬ GGSplitLie p X → ¬ (GGMemberUnitary p Bs X ∧ GGMemberUnitary p Bs L) →
          GGGenConcl M Bs X L 𝒦 e

theorem GGRk1ResidualWeakInputExOf.toMember {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (h : GGRk1ResidualWeakInputExOf T) : GGRk1ResidualMemberInputEx :=
  fun G _ _ p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 X hX =>
    h G p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 X (hX.imp_right Or.inl)

theorem GGGenResidualWeakInputOf.toMember {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (h : GGGenResidualWeakInputOf T) : GGGenResidualMemberInput :=
  fun G _ _ p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 hbig X hX =>
    h G p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 hbig X (hX.imp_right Or.inl)

namespace NSJoin

theorem nsWeakNonUnitaryInputOf_of_weakResidual {T T' : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hRk1W : GGRk1ResidualWeakInputExOf T) (hGenW : GGGenResidualWeakInputOf T)
    (hT : ∀ {ι : Type} {M : CoxeterMatrix ι}, T' M → T M)
    (hT3 : ∀ {ι : Type} {M : CoxeterMatrix ι}, T' M → ∀ i j : ι, i ≠ j → M.M i j ≤ 3) :
    NSWeakNonUnitaryInputOf T' := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns hguard K hK hKns hKU
  obtain ⟨ι, M, e, hpres, hT', hbig⟩ := hguard
  have h3 := hT3 hT'
  have hX : K = L ∨ K ∈ 𝒦 ∨ (T M ∧ GGSecFiveWeakNbr p B Bs x L D J 𝒦 K) :=
    Or.inr (Or.inr ⟨hT hT', hK⟩)
  have hXr : K = L ∨ K ∈ 𝒦 ∨ (T M ∧
      (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) ∧
      GGSecFiveWeakNbr p B Bs x L D J 𝒦 K) :=
    Or.inr (Or.inr ⟨hT hT', hbig, hK⟩)
  refine ⟨fun r hrK hr => ?_, ?_⟩
  · have hrC : r ∈ ggCoxRefl M e :=
      ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3 (hK.2 hrK) hr
    exact (hRk1W G p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 K hXr hKns hKU r hrK hrC).toConcl
  · have hgen : K = ⨆ r ∈ {r : MulAut ↥Bs | r ∈ ggAutomizer K Bs ∧ r ∈ ggCoxRefl M e},
        ggRankOneIn K Bs r :=
      hGenW G p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 hbig K hX hKns (fun h => hKU h.1)
    refine hgen.le.trans (iSup₂_le fun r hr => ?_)
    obtain ⟨hrK, hrC⟩ := hr
    exact le_iSup_of_le r (le_iSup_of_le hrK
      (le_iSup_of_le (ggCoxRefl_isReflection hpres.2 hrC) le_rfl))

end NSJoin

end Weak

end CFSG.StandardType

end
