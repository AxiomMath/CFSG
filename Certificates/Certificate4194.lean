module

public import CFSG.Quasithin.EmptyFaithful.S151S9TChecks
public import Certificates.Kernel.J2Dc.IdxG
public import Certificates.Kernel.M12Dc.Final
public import Certificates.Kernel.M12Dc.Idx3
public import Certificates.Kernel.M22Dc.Final
public import Certificates.Kernel.M22Dc.Idx3
public import Certificates.Kernel.M23Dc.Idx3
public import CFSG.Quasithin.EmptyFaithful.S151S9TM23K
import CFSG.Quasithin.EmptyFaithful.S151S9TJ2
import CFSG.Quasithin.EmptyFaithful.S151S9TM12
import CFSG.Quasithin.EmptyFaithful.S151S9TM22
import CFSG.Quasithin.EmptyFaithful.S151S9TM23
import CFSG.Quasithin.EmptyFaithful.S151S9UM22
import CFSG.Quasithin.EmptyFaithful.S151S9UM23
import CFSG.Certificates.Kernel.SporLatDcPair
import all CFSG.Quasithin.Background.E2TwoProofSporJ2
import all CFSG.Quasithin.Background.HSporLatMathieu
import all CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Inputs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Certificate4170

set_option maxRecDepth 100000

public section

namespace Certificates

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.S151S9T

private theorem j2Sg_eq : CFSG.KD.J2Dc.j2SgK = CFSG.Quasithin.E2P.SporB.j2Sg := rfl

private theorem m12Sg_eq : CFSG.KD.M12Dc.m12Sg = CFSG.Quasithin.H.MathieuLat.m12Sg := rfl

private theorem m22Sg_eq : CFSG.KD.M22Dc.m22Sg = CFSG.Quasithin.H.MathieuLat.m22Sg := rfl

private theorem m23_mw_eq : CFSG.KD.M23Dc.J.mw.toArray = CFSG.Quasithin.A312M23.m23MwLit := by
  apply eq_of_beq
  quickRfl

private theorem j2_facts :
    j2FactsK := by
  refine ⟨CFSG.KD.J2Dc.j2LatK, ⟨rfl, CFSG.KD.J2Dc.j2K_membersOK, ?_, ?_⟩,
    CFSG.KD.J2Dc.j2K_Om_size, CFSG.KD.J2Dc.j2K_checkG⟩
  · rw [← j2Sg_eq]
    exact CFSG.KD.J2Dc.j2K_stab
  · rw [← j2Sg_eq]
    exact CFSG.KD.J2Dc.j2K_comp

private theorem m12_facts :
    m12FactsK := by
  refine ⟨CFSG.KD.M12Dc.m12LatK, ⟨rfl, CFSG.KD.M12Dc.m12K_membersOK, ?_, ?_⟩,
    CFSG.KD.M12Dc.m12K_Om_size, CFSG.KD.M12Dc.m12K_check⟩
  · rw [← m12Sg_eq]
    exact CFSG.KD.M12Dc.m12K_stab
  · rw [← m12Sg_eq]
    exact CFSG.KD.M12Dc.m12K_comp

private theorem m22_facts :
    m22FactsK := by
  refine ⟨CFSG.KD.M22Dc.m22LatK, ⟨rfl, CFSG.KD.M22Dc.m22K_membersOK, ?_, ?_⟩,
    CFSG.KD.M22Dc.m22K_Om_size, CFSG.KD.M22Dc.m22K_check⟩
  · rw [← m22Sg_eq]
    exact CFSG.KD.M22Dc.m22K_stab
  · rw [← m22Sg_eq]
    exact CFSG.KD.M22Dc.m22K_comp

private theorem m23_check : m23CheckK := by
  refine Idx3Wit.ok_of_eq (D := CFSG.KD.M23Dc.m23LatK) rfl ?_ (fun j _ => ?_)
    CFSG.KD.M23Dc.m23K_check
  · change CFSG.KD.M23Dc.J.mw.toArray.size = _
    rw [m23_mw_eq]
    rfl
  · change (CFSG.KD.M23Dc.J.mw.toArray.map _)[j]! = (CFSG.Quasithin.A312M23.m23MwLit.map _)[j]!
    rw [m23_mw_eq, CFSG.KC.SLDc.wordTabA_eq_L]

theorem certificate4194 : CFSG.Quasithin.S151S9T.ThreeDFacts :=
  { j2 := j2_threeD j2_facts
    m12 := m12_threeD m12_facts
    m22 := m22_threeD m22_facts
    m23 := m23_threeD (m23Check_of_K m23_check)
    mld22 := CFSG.Quasithin.S151S9U.mldAt_m22 (m23Check_of_K m23_check)
    mld23 := CFSG.Quasithin.S151S9U.mldAt_m23 (m23Check_of_K m23_check) }

end Certificates
