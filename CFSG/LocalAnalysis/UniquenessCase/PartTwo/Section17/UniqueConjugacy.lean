module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rq
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem conjSetOf_eq_of_mem_uniqueSet (D : Data G) {X : Subgroup G}
    (hX : X ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M) :
    (conjSetOf (⊤ : Subgroup G) X ∩ {Y : Subgroup G | Y ≤ D.M}) = conjSetOf D.M X := by
  ext Y
  constructor
  · rintro ⟨⟨g, -, rfl⟩, hYM⟩
    have hg : g ∈ D.M := by
      have hgi : g⁻¹ ∈ D.M := uc22p22r_mem_of_conj_le_of_unique D hX (g := g⁻¹)
        (fun y hy => by simpa using hYM ⟨y, hy, rfl⟩)
      simpa using D.M.inv_mem hgi
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    have hMg : D.M.map (MulAut.conj g).toMonoidHom = D.M :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)
    refine ⟨⟨g, Subgroup.mem_top g, rfl⟩, ?_⟩
    calc X.map (MulAut.conj g).toMonoidHom ≤ D.M.map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono hX.1
      _ = D.M := hMg

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
