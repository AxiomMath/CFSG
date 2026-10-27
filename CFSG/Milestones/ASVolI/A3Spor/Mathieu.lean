module

public import CFSG.Milestones.ASVolI.A3Spor.Core
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM11
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM22
public import CFSG.Quasithin.H13.NQCatT513Hall
public import CFSG.Quasithin.H13.NQCatA314M23
public import CFSG.Quasithin.H13.A7Nat1238YCases
public import CFSG.Quasithin.Vol2.Ch10SecD33
public import CFSG.Quasithin.Vol2.Ch10SecDClA
public import CFSG.Quasithin.Vol2.Ch11SecA11Main
public import CFSG.Quasithin.Vol2.Ch11SecBL2ODone
public import CFSG.Quasithin.Vol2.Ch11SecBL2UOver
public import CFSG.Quasithin.Vol2.Ch11SecBTCStar
public import CFSG.Quasithin.Vol2.Ch11SecSMain
public import CFSG.Quasithin.Vol2.Ch11SecSShape2
public import CFSG.Quasithin.Vol2.Ch11SecSSym2
public import CFSG.Quasithin.Vol2.Ch11SecSSym4
public import CFSG.Quasithin.Vol2.Ch11SecSSym5
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsG
public import CFSG.Quasithin.Vol2.Ch11StatementsH
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveA7
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112M23
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Type
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem512
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpA
public import CFSG.Walter.J1Props
public import CFSG.Walter.J1Recog
public import CFSG.Walter.PSL2Facts
public import CFSG.Walter.W67.Statements

public section

namespace CFSG.ASVolI

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

theorem burnsideA315s_noConfig_M11Grp :
    ∀ S B : Subgroup ↥M11Lat.Mgrp, ¬ burnsideA315x_Config ↥M11Lat.Mgrp S B := by
  classical
  intro S B hc
  have hck := M11Lat.cert_check
  have hcl := LatCert.closedOK_of_check hck
  have hsz := LatCert.sizesOK_of_check hck
  have hU : IsSylowTwoOf M11Lat.Ugrp ⊤ :=
    M11Lat.cert.isSylowTwoOf_top (rawIsEnc 11) hck (k := 4) (m := 495) (by decide) (by decide)
      (by omega)
  have hUc : Nat.card ↥M11Lat.Ugrp = 16 :=
    CFSG.Quasithin.H13.NQCat.T513P.card_of_isSylowTwoOf_top hU (a := 4) (m := 495)
      (M11Lat.cert.card_m (rawIsEnc 11) hcl hsz) (by decide)
  refine burnsideA315s_false_of_overgroups hU (fun Z hZ _ m hm => ?_) hc
  obtain ⟨j, hj, hLM, hZL, hcardj⟩ := M11Lat.cert.overgroup_cases_idx (rawIsEnc 11) hck Z hZ
  have hlen : (M11Lat.cert.tGens :: M11Lat.cert.lat).length = 5 := by
    simp [M11Lat.cert, M11Lat.lat]
  rw [hlen] at hj
  rw [hZL, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv, hcardj, hUc] at hm
  have hs : M11Lat.cert.sizes = [16, 720, 48, 7920, 144] := rfl
  rw [hs] at hm
  interval_cases j <;> simp only [List.getD_cons_zero, List.getD_cons_succ] at hm <;> omega

theorem burnsideA315s_noConfig_M11 :
    ∀ S B : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .M11),
      ¬ burnsideA315x_Config (CFSG.Blueprint.NativeSporadic.Carrier .M11) S B :=
  burnsideA315s_noConfig_of_equiv (MulEquiv.subgroupCongr M11Lat.mGens_closure).symm
    burnsideA315s_noConfig_M11Grp

theorem burnsideA315s_noConfig_M22Grp :
    ∀ S B : Subgroup ↥M22Lat.Mgrp, ¬ burnsideA315x_Config ↥M22Lat.Mgrp S B := by
  classical
  intro S B hc
  have hck := M22Lat.cert_check
  have hcl := LatCert.closedOK_of_check hck
  have hsz := LatCert.sizesOK_of_check hck
  have hU : IsSylowTwoOf M22Lat.Ugrp ⊤ :=
    M22Lat.cert.isSylowTwoOf_top (rawIsEnc 22) hck (k := 7) (m := 3465) (by decide) (by decide)
      (by omega)
  have hUc : Nat.card ↥M22Lat.Ugrp = 128 :=
    CFSG.Quasithin.H13.NQCat.T513P.card_of_isSylowTwoOf_top hU (a := 7) (m := 3465)
      (M22Lat.cert.card_m (rawIsEnc 22) hcl hsz) (by decide)
  refine burnsideA315s_false_of_overgroups hU (fun Z hZ _ m hm => ?_) hc
  obtain ⟨j, hj, hLM, hZL, hcardj⟩ := M22Lat.cert.overgroup_cases_idx (rawIsEnc 22) hck Z hZ
  have hlen : (M22Lat.cert.tGens :: M22Lat.cert.lat).length = 6 := by
    simp [M22Lat.cert, M22Lat.lat]
  rw [hlen] at hj
  rw [hZL, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv, hcardj, hUc] at hm
  have hs : M22Lat.cert.sizes = [128, 384, 1920, 5760, 443520, 384] := rfl
  rw [hs] at hm
  interval_cases j <;> simp only [List.getD_cons_zero, List.getD_cons_succ] at hm <;> omega

theorem burnsideA315s_noConfig_M22 :
    ∀ S B : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .M22),
      ¬ burnsideA315x_Config (CFSG.Blueprint.NativeSporadic.Carrier .M22) S B :=
  burnsideA315s_noConfig_of_equiv (MulEquiv.subgroupCongr M22Lat.mGens_closure).symm
    burnsideA315s_noConfig_M22Grp

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.A312M23 CFSG.Quasithin.H.MathieuLat in
theorem burnsideA315s_noConfig_M23 :
    ∀ S B : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .M23),
      ¬ burnsideA315x_Config (CFSG.Blueprint.NativeSporadic.Carrier .M23) S B := by
  intro S B hc
  refine burnsideA315s_false_of_overgroups m23_S_sylow (fun Z hZ _ m hm => ?_) hc
  obtain ⟨j, hj, rfl⟩ := m23_complete Z hZ
  have hS : Nat.card ↥m23Ctx.S = 128 :=
    CFSG.Quasithin.H13.NQCat.T513P.card_of_isSylowTwoOf_top m23_S_sylow (a := 7) (m := 79695)
      (by rw [CFSG.Sporadic.Schreier.m23_card]; norm_num) (by decide)
  rw [CFSG.Quasithin.H13.NQCat.A314D.card_memberOrTop hj, hS] at hm
  interval_cases j <;> simp at hm <;> omega

end CFSG.ASVolI
