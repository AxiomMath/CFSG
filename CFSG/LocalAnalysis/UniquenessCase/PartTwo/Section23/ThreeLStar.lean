module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ThreeWeakClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {Ch : Choice2011 G}

theorem exists_calLOf_le_normalizer_wClos (c : Ctx23L D Ch)
    (h205 : S20_5 D) (h1930 : H1930 D)
    (hL0W : c.L0 ≤ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G)) :
    ∃ L₁ ∈ calLOf D.T D.M (Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G)), c.L0 ≤ L₁ :=
  h205 h1930 c.L0 c.hL0.1 _ (normalizer_wClos_mem_hSet c hL0W) hL0W

theorem exists_calLStar_of_calLOf {T M H L : Subgroup G} (hL : L ∈ calLOf T M H) :
    ∃ L' ∈ calLStar T M, L ≤ L' := by
  classical
  let : Finite (Subgroup G) := by
    let : Fintype G := Fintype.ofFinite G
    refine Finite.of_injective (fun S : Subgroup G => (S : Set G).toFinset) ?_
    intro S S' h
    apply SetLike.ext
    intro x
    have hh : x ∈ (S : Set G).toFinset ↔ x ∈ (S' : Set G).toFinset := by
      rw [← Finset.ext_iff.mp h x]
    simpa using hh
  obtain ⟨L', hle, hmax⟩ :=
    Finite.exists_le_maximal (p := fun L : Subgroup G => L ∈ calL T M) hL.1
  exact ⟨L', hmax, hle⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
