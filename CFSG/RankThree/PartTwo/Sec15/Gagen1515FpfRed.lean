module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfCtx
import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfG
import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfConjDelta
public import CFSG.RankThree.PartTwo.Sec14.Closure
public import CFSG.RankThree.PartTwo.Sec14.LBNatural

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank
  CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {A L : Subgroup G} {c d : G}

theorem case2_reduce
    (h134 : Item134) (h48 : Sec4.Item4_8) (h : Ctx A c L d)
    {g : G} (hgA : g ∈ Subgroup.normalizer (A : Set G))
    (hgX : g ∈ Subgroup.centralizer (x₀ L d : Set G)) (hgc : g * c * g⁻¹ = c * d)
    {Y : Subgroup G} (hgY : g ∈ Subgroup.normalizer (Y : Set G)) {c' : G}
    (hc' : Subgroup.zpowers c' ∈ omegaA A)
    (hX : deltaZero A (lB A) Y = pPrimeCoreOf 3 (deltaZero A (lB A) Y) ⊔
      deltaZero A (lB A) (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c' : Set G))) :
    deltaZero A (lB A) Y = pPrimeCoreOf 3 (deltaZero A (lB A) Y) ⊔
      deltaZero A (lB A) (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) := by
  obtain ⟨i, -, hc'eq⟩ := omega_eq_map_conj_pow h134 h48 h hgX hgc (Subgroup.zpowers c') hc'
  set w : G := (g ^ i)⁻¹ with hwdef
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := by
    rw [hwdef]; exact inv_mem (pow_mem hgA i)
  have hwY : w ∈ Subgroup.normalizer (Y : Set G) := by
    rw [hwdef]; exact inv_mem (pow_mem hgY i)
  have hwX : w ∈ Subgroup.normalizer (deltaZero A (lB A) Y : Set G) :=
    Sec14.mem_normalizer_deltaZero (Sec14.isNaturalFamily_lB A) hwA hwY
  have hXmap : (deltaZero A (lB A) Y).map (MulAut.conj w).toMonoidHom =
      deltaZero A (lB A) Y :=
    Late.map_conj_eq_of_mem_normalizer hwX
  have hYmap : Y.map (MulAut.conj w).toMonoidHom = Y :=
    Late.map_conj_eq_of_mem_normalizer hwY
  have hc'map : (Subgroup.zpowers c').map (MulAut.conj w).toMonoidHom =
      Subgroup.zpowers c := by
    rw [hc'eq, Late.map_conj_map_conj, hwdef, inv_mul_cancel, Late.map_conj_one]
  have hNmap : (Subgroup.normalizer (Subgroup.zpowers c' : Set G)).map
        (MulAut.conj w).toMonoidHom =
      Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    rw [Subgroup.map_equiv_normalizer_eq, hc'map]
  have hDmap : (deltaZero A (lB A)
        (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c' : Set G))).map
          (MulAut.conj w).toMonoidHom =
      deltaZero A (lB A) (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) := by
    rw [map_conj_deltaZero (A := A) hwA,
      Subgroup.map_inf_eq _ _ _ (MulAut.conj w).injective, hYmap, hNmap]
  have hmain := congrArg (Subgroup.map (MulAut.conj w).toMonoidHom) hX
  rw [Subgroup.map_sup, Sec14.map_pPrimeCoreOf 3 (MulAut.conj w) (deltaZero A (lB A) Y),
    hXmap, hDmap] at hmain
  exact hmain

end Ctx

end CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf
