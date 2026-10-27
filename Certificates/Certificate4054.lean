module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRadM11Inputs
import Certificates.Kernel.LocalQT.M11.C4054P
import CFSG.Certificates.Kernel.LocalQTM11CntProved
import CFSG.Sporadic.Schreier.M11

public section

namespace Certificates

open CFSG.KD.LQT.C4054 CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Fin253 in
open CFSG.Sporadic.Schreier CFSG.Blueprint in
theorem certificate4054 : (CenterOK m11mul 1 m11Elements)
    ∧ (OddOK m11mul 1 495 m11Elements CFSG.QuasithinUnique.Fin253.m11Invs m11Ord4)
    ∧ (QuatAll m11mul 1 m11Elements CFSG.QuasithinUnique.Fin253.m11Invs)
    ∧ (CoreAll m11mul 1 m11inv m11Elements CFSG.QuasithinUnique.Fin253.m11Invs) :=
  CFSG.KC.LQT.M.s4054_codes m11gA m11gB m11Elements (fun g => by rw [mem_m11Elements, m11_eq])
    m11Elements_nodup CFSG.KD.LQT.M11.ha CFSG.KD.LQT.M11.hb CFSG.KD.LQT.M11.hg hk hm hp

end Certificates
