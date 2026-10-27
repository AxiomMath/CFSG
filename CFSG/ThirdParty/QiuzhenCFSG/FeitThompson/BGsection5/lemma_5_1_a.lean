module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_7

namespace CFSG
end CFSG
open CFSG
/-! # Lemma 5.1(a) from BG Section 5 -/

section

public theorem CFSG.lemma_5_1_a
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hpR : IsPGroup p R) (hR : 3 ≤ groupRank R) :
    ∃ A : Subgroup R, A ∈ scnSubgroups 3 R := by
  classical
  have hscn_old_of_new :
      ∀ {A : Subgroup R}, A ∈ selfCentralizingAbelianSubgroupsAtLeast R 3 → A ∈ scnSubgroups 3 R := by
    intro A hA
    rcases hA with ⟨⟨hAnorm, hAcent⟩, hArank⟩
    have hAcomm : IsMulCommutative A := by
      have hAle : A ≤ Subgroup.centralizer (A : Set R) := by
        simp [hAcent]
      exact (Subgroup.le_centralizer_iff_isMulCommutative (K := A)).1 hAle
    letI : IsMulCommutative A := hAcomm
    haveI : Fact (IsPGroup p A) := ⟨hpR.to_subgroup A⟩
    exact ⟨hAnorm, hAcent, hArank.trans (generatorRank_le_groupRank_of_commutative_pgroup (p := p) A)⟩
  by_contra hnone
  have hempty : selfCentralizingAbelianSubgroupsAtLeast R 3 = ∅ := by
    ext A
    constructor
    · intro hA
      exact False.elim (hnone ⟨A, hscn_old_of_new hA⟩)
    · intro hA
      simp at hA
  have hle : groupRank R ≤ 2 := by
    have h47 := lemma_4_7 (R := R) (p := p) hpodd
    exact (h47 hpR).mp hempty
  exact (by decide : ¬ 3 ≤ (2 : ℕ)) (le_trans hR hle)

end
