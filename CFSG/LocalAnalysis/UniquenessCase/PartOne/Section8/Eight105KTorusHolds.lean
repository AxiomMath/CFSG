module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KFacts
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KTorusTransport
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KTorusU4
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KTorusU5
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KTorusAbelian
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Syl3Holds
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.Models.PGL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartTwo.Sec21.U4Lines (nonempty_projSU_mulEquiv_SU card_galoisField_two_mul)

private theorem torusAt_of_isU45 {X : Type} [Group X] [Finite X] {n : ℕ} (hX : IsU45 X n) :
    K105.TorusAt X ⊤ n := by
  rcases hX with ⟨hU5, rfl⟩ | ⟨hU4, hn⟩
  · obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel
      (CFSG.Blueprint.LieModel.statedClassicalModel hU5 (by decide))
      (CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU
        (CFSG.Blueprint.LieModel.admissible hU5) (MulEquiv.refl _))
    exact (K105.u5_torusAt (card_galoisField_two_mul 2 (by norm_num))).of_mapL
      (topEquiv.trans ((e.trans (CFSG.PGLModel.projSUEquivStatedProj 5 2 2)).trans topEquiv.symm))
  · have hn0 : 0 < n := (CFSG.Blueprint.LieModel.admissible hU4).2.1
    obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel
      (CFSG.Blueprint.LieModel.statedClassicalModel hU4 (by decide))
      (CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU
        (CFSG.Blueprint.LieModel.admissible hU4) (MulEquiv.refl _))
    obtain ⟨e₀⟩ := nonempty_projSU_mulEquiv_SU n hn0
    exact (K105.u4_torusAt hn0 hn (card_galoisField_two_mul n hn0)).of_mapL
      (topEquiv.trans (e.trans e₀))

theorem kU45Lines_holds : KU45Lines := by
  intro X _ _ n hX S hS hSi
  refine ⟨K105.sylow_three_comm hX hS hSi, fun B₀ hB₀ => ?_⟩
  obtain ⟨⟨E, hES, hE, hE9, hSE⟩, -⟩ := kU45Syl3_holds X n hX S hS hSi
  have hiff := fun B => K105.notationB8103_iff_of_le (L := ⊤) (n := n) (B := B) hES hSE
  obtain ⟨B₁, h1, h2, h3, h4, -⟩ :=
    torusAt_of_isU45 hX E le_top hE hE9 B₀ ((hiff B₀).mp hB₀)
  exact ⟨B₁, h1, (hiff B₁).mpr h2, h3, fun Y hY => h4 Y ((hiff Y).mp hY)⟩

theorem kU45CentP_holds : KU45CentP := by
  intro X _ _ n hX p hp hpn S hS hSi B₀ hB₀
  obtain ⟨⟨E, hES, hE, hE9, hSE⟩, -⟩ := kU45Syl3_holds X n hX S hS hSi
  obtain ⟨_, -, -, -, -, h⟩ :=
    torusAt_of_isU45 hX E le_top hE hE9 B₀ ((K105.notationB8103_iff_of_le (L := ⊤) hES hSE).mp hB₀)
  obtain ⟨⟨D₀, hD₀K, hD₀p, hD₀C⟩, -⟩ := h p hp hpn
  refine ⟨D₀, hD₀K, hD₀p, fun d hd => mem_centralizer_iff.mpr fun s hs => ?_⟩
  refine mem_centralizer_iff.mp (hD₀C hd) s (mem_inf.mpr ⟨mem_top s, ?_⟩)
  exact mem_centralizer_iff.mpr fun e he => K105.sylow_three_comm hX hS hSi e (hES he) s hs

theorem kU45GenRank_holds : KU45GenRank := by
  intro X _ _ n hX p hp hpn S hS hSi B₀ B₁ hB₀ hB₁ hne
  obtain ⟨⟨E, hES, hE, hE9, hSE⟩, -⟩ := kU45Syl3_holds X n hX S hS hSi
  have hiff := fun B => K105.notationB8103_iff_of_le (L := ⊤) (n := n) (B := B) hES hSE
  obtain ⟨B₂, -, -, -, hY, h⟩ := torusAt_of_isU45 hX E le_top hE hE9 B₀ ((hiff B₀).mp hB₀)
  obtain rfl : B₁ = B₂ := (hY B₁ ((hiff B₁).mp hB₁)).resolve_left (Ne.symm hne)
  exact (h p hp hpn).2

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
