module

public import CFSG.RankThree.PartTwo.Sec14.Std
import CFSG.RankThree.PartTwo.Sec14.Closure
import CFSG.RankThree.PartTwo.Sec14.LBNatural
public import CFSG.RankThree.PartTwo.Sec14.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14

variable {G : Type} [Group G] [Finite G]

theorem map_conj_deltaZero_le {A : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) (Y : Subgroup G) :
    (deltaZero A (lB A) Y).map (MulAut.conj g).toMonoidHom ≤
      deltaZero A (lB A) (Y.map (MulAut.conj g).toMonoidHom) := by
  rw [deltaZero, Subgroup.map_le_iff_le_comap]
  refine sSup_le fun Q hQ => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_deltaZero (rank3II_14_4_5_zero (isNaturalFamily_lB A) hg hQ.1)
    (Subgroup.map_mono hQ.2)

theorem map_conj_deltaZero {A : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (A : Set G))
    (Y : Subgroup G) :
    (deltaZero A (lB A) Y).map (MulAut.conj g).toMonoidHom =
      deltaZero A (lB A) (Y.map (MulAut.conj g).toMonoidHom) := by
  refine le_antisymm (map_conj_deltaZero_le hg Y) ?_
  have h := map_conj_deltaZero_le (inv_mem hg) (Y.map (MulAut.conj g).toMonoidHom)
  rw [CFSG.RankThree.PartTwo.Late.map_conj_map_conj, inv_mul_cancel,
    CFSG.RankThree.PartTwo.Late.map_conj_one] at h
  have h' := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) h
  rwa [CFSG.RankThree.PartTwo.Late.map_conj_map_conj, mul_inv_cancel,
    CFSG.RankThree.PartTwo.Late.map_conj_one] at h'

end CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf
