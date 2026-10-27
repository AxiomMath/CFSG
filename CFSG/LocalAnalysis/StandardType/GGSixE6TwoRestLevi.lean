module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestDefs
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestFrame
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestBasic
public import CFSG.LieType.Chevalley.ParabolicRadicalNormalizer
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYRoots

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint

private theorem e6lv_qStd_eq_parabolicRadical :
    qStd = (parabolicRadical .E6 F2 E6Pilot.nodes16).subgroupOf (adjointGroup .E6 F2) := by
  rw [qStd, parabolicRadical, E6Pilot.parabolicRadicalRoots_nodes16, stdQRoots]

private theorem e6lv_parabolicRadical_le_adjointGroup :
    parabolicRadical .E6 F2 E6Pilot.nodes16 ≤ adjointGroup .E6 F2 :=
  (parabolicRadical_le_posUnipotent E6Pilot.nodes16).trans
    ((posUnipotent_le_parabolicSubgroup E6Pilot.nodes16).trans
      (parabolicSubgroup_le_adjointGroup .E6 F2 E6Pilot.nodes16))

private theorem e6lv_parabolicLevi_le_adjointGroup :
    parabolicLevi .E6 F2 E6Pilot.nodes16 ≤ adjointGroup .E6 F2 :=
  (parabolicLevi_le_parabolicSubgroup E6Pilot.nodes16).trans
    (parabolicSubgroup_le_adjointGroup .E6 F2 E6Pilot.nodes16)

private theorem e6lv_parabolicLevi_le_normalizer :
    parabolicLevi .E6 F2 E6Pilot.nodes16 ≤
      Subgroup.normalizer (parabolicRadical .E6 F2 E6Pilot.nodes16 : Set (ModGL .E6 F2)) :=
  (parabolicLevi_le_parabolicSubgroup E6Pilot.nodes16).trans
    (parabolicSubgroup_le_normalizer_parabolicRadical E6Pilot.nodes16)

@[expose] noncomputable def lamLevi :
    Subgroup EC :=
  ((parabolicLevi .E6 F2 E6Pilot.nodes16).subgroupOf (adjointGroup .E6 F2)).map
    (MulAut.conj nQ).toMonoidHom

theorem lamLevi_le_normalizer_qE :
    lamLevi ≤ Subgroup.normalizer (qE : Set EC) := by
  have hmStd : ((parabolicLevi .E6 F2 E6Pilot.nodes16).subgroupOf (adjointGroup .E6 F2)) ≤
      Subgroup.normalizer (qStd : Set EC) := by
    rw [e6lv_qStd_eq_parabolicRadical, ← Subgroup.subgroupOf_normalizer_eq
      e6lv_parabolicRadical_le_adjointGroup]
    exact Subgroup.subgroupOf_mono _ e6lv_parabolicLevi_le_normalizer
  calc lamLevi
      = ((parabolicLevi .E6 F2 E6Pilot.nodes16).subgroupOf (adjointGroup .E6 F2)).map
          (MulAut.conj nQ).toMonoidHom := rfl
    _ ≤ (Subgroup.normalizer (qStd : Set EC)).map (MulAut.conj nQ).toMonoidHom :=
          Subgroup.map_mono (f := (MulAut.conj nQ).toMonoidHom) hmStd
    _ = Subgroup.normalizer ((qStd : Subgroup EC).map (MulAut.conj nQ).toMonoidHom : Set EC) :=
          Subgroup.map_equiv_normalizer_eq qStd (MulAut.conj nQ)
    _ = Subgroup.normalizer (qE : Set EC) := by rw [← qE_eq_map_qStd]

theorem normalizer_qE_le_sup_lamLevi :
    Subgroup.normalizer (qE : Set EC) ≤ qE ⊔ lamLevi := by
  have hNA : (Subgroup.normalizer (parabolicRadical .E6 F2 E6Pilot.nodes16 :
        Set (ModGL .E6 F2))).subgroupOf (adjointGroup .E6 F2) =
      (parabolicSubgroup .E6 F2 E6Pilot.nodes16).subgroupOf (adjointGroup .E6 F2) := by
    rw [← Subgroup.inf_subgroupOf_right
        (Subgroup.normalizer (parabolicRadical .E6 F2 E6Pilot.nodes16 : Set (ModGL .E6 F2)))
        (adjointGroup .E6 F2),
      inf_comm, adjointGroup_inf_normalizer_parabolicRadical]
  have h1 : Subgroup.normalizer (qE : Set EC) =
      (Subgroup.normalizer (qStd : Set EC)).map (MulAut.conj nQ).toMonoidHom := by
    rw [qE_eq_map_qStd]
    exact (Subgroup.map_equiv_normalizer_eq qStd (MulAut.conj nQ)).symm
  have h2 : (Subgroup.normalizer (qStd : Set EC)).map (MulAut.conj nQ).toMonoidHom =
      ((parabolicSubgroup .E6 F2 E6Pilot.nodes16).subgroupOf (adjointGroup .E6 F2)).map
        (MulAut.conj nQ).toMonoidHom := by
    rw [e6lv_qStd_eq_parabolicRadical, ← Subgroup.subgroupOf_normalizer_eq
      e6lv_parabolicRadical_le_adjointGroup, hNA]
  have h3 : ((parabolicSubgroup .E6 F2 E6Pilot.nodes16).subgroupOf (adjointGroup .E6 F2)).map
        (MulAut.conj nQ).toMonoidHom = qE ⊔ lamLevi := by
    rw [← parabolicRadical_sup_parabolicLevi (τ := .E6) (K := F2) E6Pilot.nodes16,
      Subgroup.subgroupOf_sup e6lv_parabolicRadical_le_adjointGroup
        e6lv_parabolicLevi_le_adjointGroup,
      Subgroup.map_sup, ← e6lv_qStd_eq_parabolicRadical, ← qE_eq_map_qStd]
    rfl
  exact le_of_eq (h1.trans (h2.trans h3))

end CFSG.StandardType.GGSixE6Two
