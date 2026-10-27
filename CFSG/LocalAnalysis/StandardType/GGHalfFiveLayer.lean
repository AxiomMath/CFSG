module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveCommutant
public import CFSG.Assembly.LargeEvenDefs
public import CFSG.Foundations.QuasisimpleMulEquiv
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups

public section

namespace CFSG.StandardType.GGHalf

open CFSG.Assembly CFSG.LieType.Universal.SpecialLinear Matrix

theorem isQuasisimple_sl3four : IsQuasisimple ↥sl3four := by
  have hSL : CFSG.IsQuasisimple (SpecialLinearGroup (Fin 3) F4) :=
    CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup
      (n := 3) (K := F4) (by norm_num)
  exact CFSG.IsQuasisimple.of_mulEquiv sl3fourEquiv.symm hSL

private theorem assembly_isQuasisimple_sl3four : CFSG.Assembly.IsQuasisimple ↥sl3four := by
  have h := isQuasisimple_sl3four
  exact ⟨Group.isPerfect_def.mp h.1, h.2.1⟩

theorem card_center_sl3four : Nat.card (Subgroup.center ↥sl3four) = 3 := by
  have hF4 : Nat.card F4 = 4 := by
    simpa using GaloisField.card 2 2 (by norm_num)
  have hunits : Nat.card F4ˣ = 3 := by
    rw [Nat.card_units, hF4]
  have hroot : rootsOfUnity 3 F4 = ⊤ := by
    ext u
    simp only [mem_rootsOfUnity, Subgroup.mem_top, iff_true]
    letI : Fintype F4ˣ := Fintype.ofFinite F4ˣ
    have h := pow_card_eq_one (x := u)
    rwa [← Nat.card_eq_fintype_card, hunits] at h
  have hroots : Nat.card (rootsOfUnity 3 F4) = 3 := by
    calc
      Nat.card (rootsOfUnity 3 F4) = Nat.card (⊤ : Subgroup F4ˣ) := by rw [hroot]
      _ = Nat.card F4ˣ := Nat.card_congr (Subgroup.topEquiv).toEquiv
      _ = 3 := hunits
  rw [← Nat.card_congr (Subgroup.centerCongr sl3fourEquiv).toEquiv,
    Nat.card_congr
      (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (R := F4) (0 : Fin 3)).toEquiv,
    Fintype.card_fin]
  exact hroots

private theorem toGL_range_normal :
    (SpecialLinearGroup.toGL.range :
      Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)).Normal := by
  rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
  exact MonoidHom.normal_ker _

private theorem map_toGL_range_resGL :
    Subgroup.map (resGL 3)
        (SpecialLinearGroup.toGL.range :
          Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)) = sl3four := by
  rw [sl3four, resSL, MonoidHom.range_comp]

private theorem isSubnormal_sl3four :
    IsSubnormal sl3four
      (Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2))) := by
  have hstep : IsSubnormal
      (SpecialLinearGroup.toGL.range :
        Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)) ⊤ :=
    IsSubnormal.step (M := ⊤) (K := ⊤) le_top
      (toGL_range_normal.subgroupOf ⊤) (IsSubnormal.refl ⊤)
  have hmap := hstep.map (resGL 3)
  rw [Subgroup.map_top, map_toGL_range_resGL] at hmap
  rwa [← centralizer_zeta5] at hmap

private theorem commutator_centralizer_le_sl3four :
    ⁅Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2)),
      Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2))⁆ ≤ sl3four := by
  have hderiv : ⁅(⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)),
      (⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4))⁆ ≤
      SpecialLinearGroup.toGL.range := by
    rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact Commute.commutator_eq (Commute.all _ _)
  calc
    ⁅Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2)),
      Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2))⁆
        = ⁅(resGL 3).range, (resGL 3).range⁆ := by rw [centralizer_zeta5]
    _ = Subgroup.map (resGL 3) ⁅(⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)),
        (⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4))⁆ := by
      rw [MonoidHom.range_eq_map, Subgroup.map_commutator]
    _ ≤ Subgroup.map (resGL 3) SpecialLinearGroup.toGL.range := Subgroup.map_mono hderiv
    _ = sl3four := map_toGL_range_resGL

private theorem component_le (Q : Subgroup (SpecialLinearGroup (Fin 6) F2))
    (hQ : IsComponentOf Q
      (Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2)))) :
    Q ≤ sl3four := by
  haveI : Group.IsPerfect ↥Q := by
    rw [Group.isPerfect_def]
    exact hQ.2.2.1
  calc
    Q ≤ ⁅Q, Q⁆ := le_of_eq (Subgroup.commutator_eq_self (H := Q)).symm
    _ ≤ ⁅Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2)),
        Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2))⁆ :=
      Subgroup.commutator_mono hQ.1 hQ.1
    _ ≤ sl3four := commutator_centralizer_le_sl3four

private theorem isComponentOf_sl3four :
    IsComponentOf sl3four
      (Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2))) :=
  ⟨sl3four_le_centralizer, isSubnormal_sl3four, assembly_isQuasisimple_sl3four⟩

theorem sl3four_layer :
    LargeEvenLayer (Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2))) =
        sl3four ∧
      IsComponentOf sl3four
        (Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2))) := by
  have hcomp := isComponentOf_sl3four
  refine ⟨?_, hcomp⟩
  change sSup {Q | IsComponentOf Q
    (Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2)))} = sl3four
  refine le_antisymm ?_ ?_
  · refine sSup_le ?_
    intro Q hQ
    exact component_le Q hQ
  · exact le_sSup hcomp

end CFSG.StandardType.GGHalf

end
