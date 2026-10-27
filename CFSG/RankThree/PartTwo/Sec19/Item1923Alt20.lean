module

import CFSG.RankThree.PartTwo.Sec19.Hyp1921Basic
public import CFSG.RankThree.PartTwo.Sec19.Item19Res3ProofAsc93

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.RankThree.PartTwo.Sec19 (starIm IsList194 IsSmall194 IsTripleA6 IsProperParabolic
  Item194UsedWide3 Item316)

variable {G : Type} [Group G] [Finite G] {A M N L K : Subgroup G} {c : G}

theorem step1923_normalizer_A_le (h : Hyp1921 G A M N L)
    (hKM : M ≤ Subgroup.normalizer (K : Set G)) (hAK : A ⊓ K = Subgroup.zpowers c) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  intro g hg
  have hnorm : Subgroup.normalizer (A : Set G) ≤ CFSG.RankThree.PartTwo.gamma 2 A :=
    CFSG.RankThree.PartTwo.normalizer_le_gamma le_rfl (by rw [h.isE27.pRank_eq]; norm_num)
  have hgM : g ∈ M := h.mem_scriptM.2 (hnorm hg)
  have hgK : g ∈ Subgroup.normalizer (K : Set G) := hKM hgM
  have hA' := Subgroup.mem_normalizer_iff.mp hg
  have hK' := Subgroup.mem_normalizer_iff.mp hgK
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 : x ∈ A ↔ g * x * g⁻¹ ∈ A := hA' x
  have h2 : x ∈ K ↔ g * x * g⁻¹ ∈ K := hK' x
  rw [← hAK]
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  exact and_congr h1 h2

end CFSG.RankThree.PartTwo.Late
