module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanL2DDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanL2Leaf
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitOrthE

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT

private theorem ggPhanL2_orbPair_of_conj
    (hGen : GGSecFiveGenPhanInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hns : ¬ GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)
    (hconj : ∀ (t t' : M.Group) (i j : ι), (∃ (w : M.Group) (k : ι), t = w * M.simple k * w⁻¹) →
      (∃ (w : M.Group) (k : ι), t' = w * M.simple k * w⁻¹) → t ≠ t' → t * t' = t' * t →
      M.M i j = 2 → ∃ w : M.Group, w * M.simple i * w⁻¹ = t ∧ w * M.simple j * w⁻¹ = t')
    {i j : ι} (h2 : M.M i j = 2) :
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
  obtain ⟨w, hw1, hw2⟩ := hconj t t' i j ⟨w₁, i₁, rfl⟩ ⟨w₂, i₂, rfl⟩ hne' hcomm' h2
  refine ⟨w, L, Or.inl rfl, ?_, ?_⟩
  · have h : ((e (w * M.simple i * w⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
        ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by rw [hw1]
    rw [h, ← hra_e]
    exact hrA
  · have h : ((e (w * M.simple j * w⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
        ((e t' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by rw [hw2]
    rw [h, ← hrb_e]
    exact hrA'

theorem ggSecFiveL2PhanDEInput_of_D
    (hGen : GGSecFiveGenPhanInput) (hD : GGSecFiveL2PhanDInput) : GGSecFiveL2PhanDEInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns ι M e hpres hDE hbig i j hij h2 hno
  rcases hDE with hDM | hE
  · exact hD G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hDM hbig i j hij h2 hno
  · have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := GGIsWeylMatrixE.le_three hE
    refine absurd ?_ hno
    rcases hE with ⟨e6, h6⟩ | ⟨e7, h7⟩ | ⟨e8, h8⟩
    · exact ggPhanL2_orbPair_of_conj hGen hcfg hns hpres hle3 hbig
        (fun t t' _ _ ht ht' hne hcomm h => ggOrth_conj_E6 h6 ht ht' hne hcomm h) h2
    · exact ggPhanL2_orbPair_of_conj hGen hcfg hns hpres hle3 hbig
        (fun t t' _ _ ht ht' hne hcomm h => ggOrth_conj_E7 h7 ht ht' hne hcomm h) h2
    · exact ggPhanL2_orbPair_of_conj hGen hcfg hns hpres hle3 hbig
        (fun t t' _ _ ht ht' hne hcomm h => ggOrth_conj_E8 h8 ht ht' hne hcomm h) h2

end CFSG.StandardType

end
