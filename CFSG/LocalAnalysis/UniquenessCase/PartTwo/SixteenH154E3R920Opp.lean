module

import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddPair
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3OmegaA
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem normal_of_pRank_le_one {M L X : Subgroup G} (hL : L ∈ calC M) (hL2 : IsL2 (Bar2 L) 3)
    (hLX : L ≤ X) (hXM : X ≤ M) (hrk : CFSG.Open.pRank 3 X ≤ 1) : (L.subgroupOf X).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hLX]
  intro x hxX
  by_contra hxN
  have hxM : x ∈ M := hXM hxX
  let f : MulAut G := MulAut.conj x
  have hM : M.map f.toMonoidHom = M :=
    UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer hxM)
  have hL' : L.map f.toMonoidHom ∈ calC M := UC6S846.calC_map M f hM hL
  have hne : L ≠ L.map f.toMonoidHom := fun h =>
    hxN (UC6S846.mem_normalizer_iff_map_conj.2 h.symm)
  haveI : IsSimpleGroup (Bar2 L) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
  have hZ : Subgroup.center (Bar2 L) = ⊥ := uc22p21k_center_eq_bot hL.2.2
  have hcard : Nat.card (Bar2 L) = 504 := by
    rw [s16h_e3_omega_card_of_isL2 hL2]
    decide
  obtain ⟨a, haL, ha⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.exists_orderOf_eq_of_dvd_card_bar2
      Nat.prime_three (by rw [hcard]; norm_num)
  have haX : a ∈ X := hLX haL
  have hyL' : x * a * x⁻¹ ∈ L.map f.toMonoidHom := by
    rw [Subgroup.mem_map]
    exact ⟨a, haL, by simp [f, MulAut.conj_apply]⟩
  have hyX : x * a * x⁻¹ ∈ X := X.mul_mem (X.mul_mem hxX haX) (X.inv_mem hxX)
  have hy : orderOf (x * a * x⁻¹) = 3 := by
    rw [← ha]
    exact orderOf_injective f.toMonoidHom f.injective a
  have h2 : 2 ≤ CFSG.Open.pRank 3 X :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.two_le_pRank_of_pair Nat.prime_three
      (by norm_num) hL hL' hne hZ hXM haL hyL' haX hyX ha hy
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
