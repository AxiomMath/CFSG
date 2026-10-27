module

public import CFSG.LocalAnalysis.StandardType.GGTorusMaxSemiTransfer
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxWeylE8
public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.Open.StatedDefs

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem tmSemi_E8
    {G : Type} [Group G] [Finite G] (E : Subgroup G) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 8)
    (π : ↥(Subgroup.normalizer (E : Set G)) →* WeylGroup Tag.E8) (hπs : Function.Surjective π)
    (hπk : π.ker = E.subgroupOf (Subgroup.normalizer (E : Set G)))
    (hcent : ∀ g ∈ Subgroup.normalizer (E : Set G), (∀ e ∈ E, g * e = e * g) → g ∈ E)
    (hirr : ∀ F : Subgroup G, F ≤ E →
      (∀ g ∈ Subgroup.normalizer (E : Set G), ∀ f ∈ F, g * f * g⁻¹ ∈ F) → F = ⊥ ∨ F = E)
    (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    (ψ : ↥(Subgroup.normalizer (E : Set G)) →* MulAut (StatedProj (StatedSU 10 (2 ^ 1) K)))
    (hψ : Function.Injective ψ) : False := by
  refine tmSemi_transfer 10 8 (by norm_num) (Or.inr (by norm_num)) (W := WeylGroup Tag.E8) ?_
    (fun n hn f => tmW8_hom_trivial_of_le_ten hn f) E hE hcard π hπs hπk hcent hirr K hK ψ hψ
  intro h
  have h1 := tmW8_card_commutator
  rw [h, Subgroup.card_bot] at h1
  omega

end CFSG.StandardType.FrameRoute

end
