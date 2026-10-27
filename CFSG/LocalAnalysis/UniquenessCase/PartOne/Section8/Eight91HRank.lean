module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.ABGLocalTools (IsSylowOf)

private theorem k891hrank_A_le_H {G : Type} [Group G] [Finite G]
    {D : Data G} {L S R A : Subgroup G} {n : ℕ} (hst : R891State D L S R A n) :
    A ≤ R891H L S := by
  intro a ha
  change a ∈ Subgroup.centralizer ((ZOf (S ⊓ L) : Subgroup G) : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hz' : z ∈ (S ⊓ L : Subgroup G) ⊓ Subgroup.centralizer ((S ⊓ L : Subgroup G) : Set G) := hz
  have hzC : z ∈ Subgroup.centralizer ((S ⊓ L : Subgroup G) : Set G) := (Subgroup.mem_inf.mp hz').2
  have hr : a ∈ (S ⊓ L : Subgroup G) := hst.ctx.xShape.rSylow (hst.ctx.aLeR ha)
  exact (Subgroup.mem_centralizer_iff.mp hzC a hr).symm

private theorem k891hrank_le_of_mem_uniqueSet_of_isPGroup {G : Type} [Group G] [Finite G]
    {M E P : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hM : rankThreeIsMaxTwoLocal M) (hE : E ∈ uniqueSet M) (hEP : E ≤ P)
    (hP : IsPGroup p ↥P) : P ≤ M := by
  by_contra hnot
  have hlt : P ⊓ M < P := lt_of_le_of_ne inf_le_left (fun hEq => hnot (hEq ▸ inf_le_right))
  have hgrow : P ⊓ M < P ⊓ Subgroup.normalizer ((P ⊓ M : Subgroup G) : Set G) :=
    CFSG.ABGTheoremB.TotallyInverted.Conjugacy.lt_inf_normalizer hP hlt
  have hYU : P ⊓ M ∈ uniqueSet M :=
    CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_le hE (le_inf hEP hE.1) inf_le_right
  have hNY : Subgroup.normalizer ((P ⊓ M : Subgroup G) : Set G) ≤ M :=
    CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet hM hYU
  exact (not_lt_of_ge (le_inf inf_le_left (inf_le_right.trans hNY))) hgrow

private theorem k891hrank_pRank_le_of_mem_uniqueSet {G : Type} [Group G] [Finite G]
    {M E H : Subgroup G} {p : ℕ} (hp : p.Prime) (hM : rankThreeIsMaxTwoLocal M)
    (hE : E ∈ uniqueSet M) (hEp : IsPGroup p ↥E) (hEH : E ≤ H) :
    CFSG.Open.pRank p H ≤ CFSG.Open.pRank p M := by
  have hpF : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hES⟩ := (hEp.comap_subtype (K := H)).exists_le_sylow
  let P : Subgroup G := (S : Subgroup ↥H).map H.subtype
  have hP : IsSylowOf p P H := ⟨S, rfl⟩
  have hEP : E ≤ P := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hEH]
    exact Subgroup.map_mono hES
  have hPM : P ≤ M := k891hrank_le_of_mem_uniqueSet_of_isPGroup hM hE hEP hP.isPGroup
  have h1 : CFSG.Open.pRank p H = CFSG.Open.pRank p (S : Subgroup ↥H) := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup H,
      ← (CFSG.SectionRank.pRank_sylow (hp := hpF) S).1]
  calc
    CFSG.Open.pRank p H = CFSG.Open.pRank p (S : Subgroup ↥H) := h1
    _ ≤ CFSG.Open.pRank p P := CFSG.SectionRank.pRank_le_map hp.one_lt H.subtype H.subtype_injective S
    _ ≤ CFSG.Open.pRank p M := CFSG.SectionRank.pRank_mono hp.one_lt hPM

theorem s891_h_rank {G : Type} [Group G] [Finite G] (D : Data G) (hM3 : CFSG.Open.pRank 3 D.M ≤ 3) (L S R A : Subgroup G) (n : ℕ)
    (hst : R891State D L S R A n) :
    CFSG.Open.pRank 3 (R891H L S) ≤ 3 := by
  have hAH : A ≤ R891H L S := k891hrank_A_le_H hst
  have hA3 : IsPGroup 3 ↥A :=
    IsPGroup.of_card (n := 1) (by rw [hst.ctx.classes.aOrder]; norm_num)
  have hbound : CFSG.Open.pRank 3 (R891H L S) ≤ CFSG.Open.pRank 3 D.M :=
    k891hrank_pRank_le_of_mem_uniqueSet Nat.prime_three D.maxLocal hst.uniq hA3 hAH
  exact hbound.trans hM3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
