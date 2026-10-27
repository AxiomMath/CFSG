module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanPrimDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanL2Leaf
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitOrthA
import CFSG.LocalAnalysis.StandardType.GGSecFiveL1OddLeaves

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT

private theorem ggPhanL2_orbPair_of_typeA
    (hGen : GGSecFiveGenPhanInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hns : ¬ GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)
    {n : ℕ} {σ : Fin n ≃ ι} (hA : M = (CoxeterMatrix.A n).reindex σ) {i j : ι} (h2 : M.M i j = 2) :
    GGOrbPair L Bs 𝒦 M e i j := by
  have hgenL := hGen G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hbig L (Or.inl rfl) hns
  obtain ⟨r, hrA, r', hrA', hrC, hr'C, hne, hcomm⟩ :=
    ggPhan_comm_reflections_of_genL hcfg hpres hle3 hgenL
  obtain ⟨w₁, i₁, hw₁⟩ := hrC
  obtain ⟨w₂, i₂, hw₂⟩ := hr'C
  let t : M.Group := w₁ * M.simple i₁ * w₁⁻¹
  let t' : M.Group := w₂ * M.simple i₂ * w₂⁻¹
  have hra_e : r = ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := hw₁
  have hrb_e : r' = ((e t' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := hw₂
  have hne' : t ≠ t' := by
    intro ht
    apply hne
    rw [hra_e, hrb_e, ht]
  have hcomm' : t * t' = t' * t := by
    apply e.injective
    apply Subtype.coe_injective
    calc ((e (t * t') : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)
        = ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
          ((e t' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) :=
          congrArg Subtype.val (map_mul e t t')
      _ = r * r' := by rw [← hra_e, ← hrb_e]
      _ = r' * r := hcomm
      _ = ((e t' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
          ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by rw [hrb_e, hra_e]
      _ = ((e (t' * t) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) :=
          (congrArg Subtype.val (map_mul e t' t)).symm
  obtain ⟨w, hw1, hw2⟩ :=
    ggOrth_conj_A hA ⟨w₁, i₁, rfl⟩ ⟨w₂, i₂, rfl⟩ hne' hcomm' h2
  refine ⟨w, L, Or.inl rfl, ?_, ?_⟩
  · have h : ((e (w * M.simple i * w⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
        ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by rw [hw1]
    rw [h, ← hra_e]
    exact hrA
  · have h : ((e (w * M.simple j * w⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
        ((e t' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by rw [hw2]
    rw [h, ← hrb_e]
    exact hrA'

theorem ggSecFiveL2PhanInput_of_gen_DE
    (hGen : GGSecFiveGenPhanInput) (hL2 : GGSecFiveL2PhanDEInput) : GGSecFiveL2PhanInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hbig i j hij h2 hno
  rcases SecFiveL1Odd.weyl_ad_or_e_or_small hpres.1 hle3 with (⟨n, σ, -, hA⟩ | ⟨k, σ, hk, hD⟩) | hE |
    ⟨n, σ, -, -, hA⟩
  · exact absurd (ggPhanL2_orbPair_of_typeA hGen hcfg hns hpres hle3 hbig hA h2) hno
  · exact hL2 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres (Or.inl ⟨k, σ, hk, hD⟩) hbig i j hij h2 hno
  · exact hL2 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres (Or.inr hE) hbig i j hij h2 hno
  · exact absurd (ggPhanL2_orbPair_of_typeA hGen hcfg hns hpres hle3 hbig hA h2) hno

end CFSG.StandardType

end
