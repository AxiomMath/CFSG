module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U4U5Delta
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.MaxParabolicTransport
public import CFSG.Quasithin.H13.U5ParPointStable
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4G2TwoAutInnerHolds
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieRed

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin
  CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
  CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Quasithin.H13.Sec53F.Unit
  CFSG.Quasithin.H13.U5Par

variable {K : Type} [Field K]

private theorem isSylowIn_hypProjUnitriangular (h : UnitaryFieldData 2 2 K) :
    IsSylowIn 2 (hypProjUnitriangular h 2 1) ⊤ := by
  obtain ⟨P, hP⟩ := (unitary_order_and_Sylow h (r := 2) (ε := 1)
    (by norm_num) (by norm_num)).2.2.2.2.1
  rw [← hP]
  exact CFSG.Quasithin.isSylowIn_top P

private theorem isMaxParabolicOver_u5PtP (h : UnitaryFieldData 2 2 K) :
    IsMaxParabolicOver (⊤ : Subgroup (hypPSU h 2 1))
      (hypProjUnitriangular h 2 1) (u5PtP h) := by
  have hcoatom : IsCoatom (u5PtP h) :=
    isCoatom_projIsoStabilizer_hypFlag h (r := 2) (ε := 1) (d := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hN : normalizer (hypProjUnitriangular h 2 1 : Set (hypPSU h 2 1)) ≤ u5PtP h := by
    rw [normalizer_hypProjUnitriangular h (by norm_num) (by norm_num)]
    exact hypProjBorel_le_projIsoStabilizer h (d := 1) (by norm_num) (by norm_num)
  exact isMaxParabolicOver_top_of_isCoatom hcoatom hN

private theorem opp_eq_perfectCore_u5PtP (h : UnitaryFieldData 2 2 K) :
    Opp 2 (u5PtP h) = perfectCore (u5PtP h) := by
  have := h.finite
  haveI : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  have hUP : hypProjUnitriangular h 2 1 ≤ u5PtP h :=
    (U_le_perfectCore_u5PtP (h := h) (by norm_num)).trans (perfectCore_le _)
  have hU : IsSylowIn 2 (hypProjUnitriangular h 2 1) ⊤ :=
    isSylowIn_hypProjUnitriangular h
  have hS : IsSylowIn 2 (hypProjUnitriangular h 2 1) (u5PtP h) := by
    refine ⟨hUP, hU.isPGroup, ?_⟩
    intro hdvd
    have h1 := Subgroup.relIndex_mul_relIndex (H := hypProjUnitriangular h 2 1)
      (K := u5PtP h) (L := ⊤) hUP le_top
    exact hU.not_dvd_relIndex (by rw [← h1]; exact dvd_mul_of_dvd_left hdvd _)
  exact opp_eq_of_isSimpleGroup_bar2 (perfectCore_le _)
    (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _)) hS
    (U_le_perfectCore_u5PtP (h := h) (by norm_num))
    (isSimpleGroup_modO2_perfectCore_u5PtP h)
    (two_dvd_card_modO2_perfectCore_u5PtP h (by norm_num))

private theorem opp_map_u5PtP (h : UnitaryFieldData 2 2 K) {Y : Type} [Group Y]
    (φ : hypPSU h 2 1 ≃* Y) :
    Opp 2 ((u5PtP h).map φ.toMonoidHom) = (perfectCore (u5PtP h)).map φ.toMonoidHom := by
  have := h.finite
  haveI : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  rw [opp_map φ 2 (u5PtP h), opp_eq_perfectCore_u5PtP h]

private theorem isMaxParabolicOver_u5PtP_map (h : UnitaryFieldData 2 2 K) {Y : Type} [Group Y]
    (φ : hypPSU h 2 1 ≃* Y) {S : Subgroup Y}
    (hφS : (hypProjUnitriangular h 2 1).map φ.toMonoidHom = S) :
    IsMaxParabolicOver (⊤ : Subgroup Y) S ((u5PtP h).map φ.toMonoidHom) := by
  have hm := isMaxParabolicOver_u5PtP h
  rw [← hφS]
  exact isMaxParabolicOver_top_map φ hm

private theorem map_u5PtP_map_of_forall_map_eq (h : UnitaryFieldData 2 2 K) {Y : Type}
    [Group Y] (φ : hypPSU h 2 1 ≃* Y) {S : Subgroup Y} {R : Subgroup (MulAut Y)}
    (hφS : (hypProjUnitriangular h 2 1).map φ.toMonoidHom = S)
    (hRS : ∀ r ∈ R, S.map r.toMonoidHom = S) :
    ∀ r ∈ R, ((u5PtP h).map φ.toMonoidHom).map r.toMonoidHom = (u5PtP h).map φ.toMonoidHom := by
  intro r hr
  have hθ : (hypProjUnitriangular h 2 1).map ((φ.trans r).trans φ.symm).toMonoidHom =
      hypProjUnitriangular h 2 1 :=
    Subgroup.map_injective (f := φ.toMonoidHom) φ.injective (by
      rw [← map_map_trans_symm φ r (hypProjUnitriangular h 2 1), hφS, hRS r hr, ← hφS])
  rw [map_map_trans_symm φ r (u5PtP h),
    map_u5PtP_of_map_hypProjUnitriangular h (by norm_num) hθ]

private theorem opp_perfect_u5PtP_map (h : UnitaryFieldData 2 2 K) {Y : Type} [Group Y]
    (φ : hypPSU h 2 1 ≃* Y) :
    ⁅Opp 2 ((u5PtP h).map φ.toMonoidHom), Opp 2 ((u5PtP h).map φ.toMonoidHom)⁆ =
      Opp 2 ((u5PtP h).map φ.toMonoidHom) := by
  have := h.finite
  haveI : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  rw [opp_map_u5PtP h φ, ← Subgroup.map_commutator, perfectCore_perfect]

private theorem isQuasisimple_bar2_opp_u5PtP_map (h : UnitaryFieldData 2 2 K) {Y : Type}
    [Group Y] (φ : hypPSU h 2 1 ≃* Y) :
    CFSG.Open.IsQuasisimple (Bar2 (Opp 2 ((u5PtP h).map φ.toMonoidHom))) := by
  have := h.finite
  haveI : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  rw [opp_map_u5PtP h φ]
  obtain ⟨e⟩ := nonempty_bar2_map φ (perfectCore (u5PtP h))
  exact CFSG.Open.IsQuasisimple.of_mulEquiv e
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff (Bar2 (perfectCore (u5PtP h)))).2.2.1.mp
      (isQuasisimple_modO2_perfectCore_u5PtP h))

private theorem isU3_bar2_opp_u5PtP_map (h : UnitaryFieldData 2 2 K) {Y : Type} [Group Y]
    (φ : hypPSU h 2 1 ≃* Y) :
    IsU3 (Bar2 (Opp 2 ((u5PtP h).map φ.toMonoidHom))) 2 := by
  have := h.finite
  haveI : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  rw [opp_map_u5PtP h φ]
  obtain ⟨e⟩ := nonempty_bar2_map φ (perfectCore (u5PtP h))
  exact CFSG.Blueprint.LieModel.of_mulEquiv e.symm (lieModel_modO2_perfectCore_u5PtP h)

theorem kU5Delta_holds : KU5Delta := by
  intro Y _ _ hY S R hS _ hRS
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, h, ⟨e⟩⟩ := CFSG.Quasithin.H13.F431.Un.OL5.exists_model5 hY
  haveI : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_map_eq_of_isSylowIn e.symm
    (isSylowIn_hypProjUnitriangular h) hS
  refine ⟨(u5PtP h).map φ.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · exact isMaxParabolicOver_u5PtP_map h φ hφ
  · exact map_u5PtP_map_of_forall_map_eq h φ hφ hRS
  · exact opp_perfect_u5PtP_map h φ
  · exact isQuasisimple_bar2_opp_u5PtP_map h φ
  · exact isU3_bar2_opp_u5PtP_map h φ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
