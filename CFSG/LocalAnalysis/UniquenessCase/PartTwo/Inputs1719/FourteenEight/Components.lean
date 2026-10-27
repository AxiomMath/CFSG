module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCFooteBlocks
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ConjClosureSimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem map_conj_mem_calC {M L : Subgroup G} (hL : L ∈ calC M) {g : G} (hg : g ∈ M) :
    L.map (MulAut.conj g).toMonoidHom ∈ calC M := by
  have hM : M.map (MulAut.conj g).toMonoidHom = M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)
  exact CFSG.LocalAnalysis.UniquenessCase.UC6S846.calC_map M (MulAut.conj g) hM hL

omit [Finite G] in
theorem mem_calC_of_le {M K L : Subgroup G} (hL : L ∈ calC M) (hLK : L ≤ K) (hKM : K ≤ M) :
    L ∈ calC K := by
  obtain ⟨hsn, hp, hq⟩ := hL
  exact ⟨CFSG.LocalAnalysis.GLTheoremA.I142N.isSubnormal_of_le_of_le hsn hLK hKM, hp, hq⟩

theorem fstar_eq_pCoreOf_of_mem_calC {M L : Subgroup G}
    (hM : M ⊓ centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M) (hL : L ∈ calC M) :
    Fstar L = pCoreOf 2 L := by
  have h :=
    CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.generalizedFitting_eq_pCore_of_isSubnormal_of_charTwo
      (H := M) (J := L) hM hL.1
  simp only [Fstar, pCoreOf, CFSG.Adapters.genFittingFStar_eq_foundations]
  rw [h]

theorem exists_conj_of_ncard_eq_two {M L : Subgroup G} (h2 : (conjSetOf M L).ncard = 2) :
    ∃ t ∈ M, L.map (MulAut.conj t).toMonoidHom ≠ L ∧
      conjSetOf M L = {L, L.map (MulAut.conj t).toMonoidHom} := by
  obtain ⟨x, y, hxy, hset⟩ := Set.ncard_eq_two.mp h2
  have hL : L ∈ conjSetOf M L := self_mem_conjSetOf M L
  rw [hset] at hL
  have hcases : L = x ∨ L = y := by simpa using hL
  rcases hcases with rfl | hLy
  · obtain ⟨t, htM, hty⟩ := (show y ∈ conjSetOf M L by rw [hset]; simp)
    exact ⟨t, htM, by rw [← hty]; exact hxy.symm, by rw [hset, ← hty]⟩
  · subst hLy
    obtain ⟨t, htM, htx⟩ := (show x ∈ conjSetOf M L by rw [hset]; simp)
    exact ⟨t, htM, by rw [← htx]; exact hxy, by rw [hset, ← htx, Set.pair_comm]⟩

omit [Finite G] in
theorem conjClosure_eq_sup_of_conjSetOf_eq {M L K : Subgroup G} (h : conjSetOf M L = {L, K}) :
    conjClosure M L = L ⊔ K := by
  apply le_antisymm
  · refine iSup₂_le fun A hA => ?_
    rw [h] at hA
    rcases (by simpa using hA : A = L ∨ A = K) with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  · refine sup_le ?_ ?_
    · exact le_iSup₂_of_le (f := fun A (_ : A ∈ conjSetOf M L) => A) L (by rw [h]; simp) le_rfl
    · exact le_iSup₂_of_le (f := fun A (_ : A ∈ conjSetOf M L) => A) K (by rw [h]; simp) le_rfl

theorem conjClosure_ne_of_ncard_eq_two {M L : Subgroup G} (h2 : (conjSetOf M L).ncard = 2) :
    conjClosure M L ≠ L := by
  obtain ⟨t, -, hne, hset⟩ := exists_conj_of_ncard_eq_two h2
  have hsup := conjClosure_eq_sup_of_conjSetOf_eq hset
  rw [hsup]
  intro hEq
  have hle : L.map (MulAut.conj t).toMonoidHom ≤ L := le_trans le_sup_right hEq.le
  have hcard : Nat.card (L.map (MulAut.conj t).toMonoidHom) = Nat.card L :=
    Subgroup.card_map_of_injective (MulAut.conj t).injective
  exact hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard]))

omit [Finite G] in
theorem inf_normalizer_le_normalizer_of_conjSetOf_eq {M L K : Subgroup G}
    (h : conjSetOf M L = {L, K}) (hne : K ≠ L) :
    M ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G) := by
  intro g hg
  obtain ⟨hgM, hgN⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨t, htM, htK⟩ := (show K ∈ conjSetOf M L by rw [h]; simp)
  subst htK
  have hLg : L.map (MulAut.conj g).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  have hmap : (L.map (MulAut.conj t).toMonoidHom).map (MulAut.conj g).toMonoidHom
      = L.map (MulAut.conj (g * t)).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hmem : (L.map (MulAut.conj t).toMonoidHom).map (MulAut.conj g).toMonoidHom
      ∈ conjSetOf M L := ⟨g * t, M.mul_mem hgM htM, hmap⟩
  rw [h] at hmem
  have hcases : (L.map (MulAut.conj t).toMonoidHom).map (MulAut.conj g).toMonoidHom = L ∨
      (L.map (MulAut.conj t).toMonoidHom).map (MulAut.conj g).toMonoidHom
        = L.map (MulAut.conj t).toMonoidHom := by
    simpa using hmem
  rcases hcases with hL | hK
  · exfalso
    rw [hmap] at hL
    have hgt : g * t ∈ normalizer (L : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hL
    have hginv : g⁻¹ ∈ normalizer (L : Set G) := Subgroup.inv_mem _ hgN
    have ht : t ∈ normalizer (L : Set G) := by
      have := Subgroup.mul_mem (normalizer (L : Set G)) hginv hgt
      simpa using this
    exact hne (Subgroup.mem_normalizer_iff_map_conj_eq.mp ht)
  · exact hK

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight
