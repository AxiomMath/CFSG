module

public import CFSG.Sporadic.Schreier.M11Data
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M11CheckInputs
import Certificates.Kernel.LocalQT.M11.C4135M
import Certificates.Kernel.LocalQT.M11.C4135N
import Certificates.Kernel.LocalQT.M11.C4135T
import Certificates.Kernel.LocalQT.M11.C4135P
import Certificates.Kernel.LocalQT.M11.C4154
import Certificates.Kernel.LocalQT.M11.C4135
import Certificates.Kernel.LocalQT.M11.C4054
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.LocalQTM11CntProved
import Certificates.Certificate2191
import CFSG.Sporadic.Schreier.M11

public section

namespace Certificates

open CFSG.KD.LQT.C4135 CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu
  CFSG.QuasithinUnique.Setup.X1 in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 in
open CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu in
theorem certificate4135 : (((m11Elements.filter (CFSG.Sporadic.Schreier.orderIs · 2) ×ˢ m11Elements.filter (CFSG.Sporadic.Schreier.orderIs · 4)).filter
            fun q => CFSG.Sporadic.Schreier.orderIs (q.1 * q.2) 11 && CFSG.Sporadic.Schreier.orderIs (m11Word q.1 q.2) 3).length = 7920)
    ∧ (CFSG.Sporadic.Schreier.orderIs m11gA 2 = true ∧ CFSG.Sporadic.Schreier.orderIs m11gB 4 = true ∧ CFSG.Sporadic.Schreier.orderIs (m11gA * m11gB) 11 = true ∧
            CFSG.Sporadic.Schreier.orderIs (m11Word m11gA m11gB) 3 = true)
    ∧ ((m11Invs.all fun x => m11Invs.all fun y =>
            !(x * y == y * x) || m11Invs.all fun z =>
              !(x * z == z * x && y * z == z * y) ||
                (x == z || x == y || x == y * z || y == z)) = true)
    ∧ ((m11Invs.all fun x => m11ConjsA.contains x) = true)
    ∧ ((List.finRange 3).all (fun i => m11Invs.contains (m11G i)) = true ∧
          (m11WordA.map m11G).prod = m11gA ∧ (m11WordB.map m11G).prod = m11gB) := by
  obtain ⟨h1, h2, h3, h4⟩ := CFSG.KC.LQT.M.s4135_codes m11gA m11gB m11Elements _
    (fun g => by rw [mem_m11Elements, m11_eq]) m11Elements_nodup CFSG.KD.LQT.M11.ha
    CFSG.KD.LQT.M11.hb hgs CFSG.KD.LQT.M11.hg hk hm hc ht hp
  have ho : orderIs m11gA 2 = true ∧ orderIs m11gB 4 = true ∧ orderIs (m11gA * m11gB) 11 = true ∧
      orderIs (m11Word m11gA m11gB) 3 = true := by decide +kernel
  have hw : (m11WordA.map m11G).prod = m11gA ∧ (m11WordB.map m11G).prod = m11gB := by
    decide +kernel
  refine ⟨?_, ho, ?_, ?_, ?_, hw⟩
  · exact h1
  · exact h2
  · exact h3
  · exact List.all_eq_true.2 fun i hi =>
      List.all_eq_true.1 h4 (m11G i) (List.mem_map_of_mem hi)

end Certificates
