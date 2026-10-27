module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNCells
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneHolds
import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneOmegaLabel

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggRowNAP_absurd
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {K : Subgroup G} (hK : GGSecFiveWeakNbr p B Bs x L D J 𝒦 K)
    (hrow : GGInnerDiagOnLabel ggRowP_NAP p Bs K) : False := by
  refine ggRow_absurd_of_cells ggLabelRigidInput_holds
    (Sf := fun p lab => lab.tag = .A ∧ 5 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1) ?_
    (fun p hp hp2 lab hlab h => ggNbrFrameInputOne_holds p hp hp2 lab hlab (Or.inr (Or.inl h)))
    ggRowPRankLeTwo_smallPlus hcfg hpres hle3 hK hrow
  rintro p lab ⟨⟨ht, hr⟩ | ⟨ht, hr⟩, hd⟩
  · by_cases h5 : 5 ≤ lab.rank
    · exact Or.inl ⟨ht, h5, hd⟩
    · exact Or.inr ⟨Or.inl ⟨ht, by omega⟩, hd⟩
  · exact Or.inr ⟨Or.inr ⟨ht, hr⟩, hd⟩

theorem ggRowNTwD_absurd
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {K : Subgroup G} (hK : GGSecFiveWeakNbr p B Bs x L D J 𝒦 K)
    (hrow : GGInnerDiagOnLabel ggRowP_NTwD p Bs K) : False := by
  refine ggRow_absurd_of_frame ggLabelRigidInput_holds ?_ hcfg hpres hle3 hK hrow
  rintro p hp hp2 lab hlab ⟨ht, hr, ⟨he, hd⟩ | hd⟩
  · exact largeEvenLabelAll_frame_omegaMinusNs hp hlab ⟨ht, hr, he, hd⟩
  · exact largeEvenLabelAll_frame_omegaMinus hp hp2 hlab ⟨ht, hr, hd⟩

theorem ggRowNDOdd_absurd
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {K : Subgroup G} (hK : GGSecFiveWeakNbr p B Bs x L D J 𝒦 K)
    (hrow : GGInnerDiagOnLabel ggRowP_NDOdd p Bs K) : False :=
  ggRow_absurd_of_frame ggLabelRigidInput_holds
    (fun _ hp _ _ hlab h => largeEvenLabelAll_frame_omegaPlusNs hp hlab h) hcfg hpres hle3 hK hrow

end CFSG.StandardType

end
