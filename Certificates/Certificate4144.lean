module

public import CFSG.Sporadic.Schreier.M11Data
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsM11Inputs
import Certificates.Kernel.LocalQT.M11.C4144
import CFSG.Certificates.Kernel.LocalQTM11GrpProved
import CFSG.Sporadic.Schreier.M11

public section

namespace Certificates

open CFSG.KD.LQT.C4144 CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Unc25K1 in
open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu in
theorem certificate4144 : (m11Elements.all
          (fun g => decide ((g * m11gA = m11gA * g ∧ g ^ 3 = 1) ↔ g ∈ TlP)) = true)
    ∧ (m11Elements.all
          (fun g => decide (g * m11gA = m11gA * g → TlP.all (fun t => decide (t * g = g * t)) = true →
            g = 1 ∨ g = m11gA)) = true)
    ∧ (m11Elements.all
          (fun g => decide (TlP.all (fun t => decide (g * t = t * g)) = true →
            g = 1 ∨ g = m11gA)) = true)
    ∧ (m11Elements.all
          (fun u => decide (u ≠ 1 → u * u = 1 →
            m11Elements.any (fun g => decide (g * m11gA = u * g)) = true)) = true)
    ∧ (∀ t ∈ TlM, ∃ w ∈ WsM, t = evB aM bM w)
    ∧ (aM ≠ 1 ∧ bM ≠ 1 ∧ (aM * bM) ^ 2 ≠ 1 ∧ (aM * bM) ^ 4 = 1)
    ∧ (PlM.length ≤ 24)
    ∧ (m11a = evB aM bM [true, false, true, false]) := by
  obtain ⟨h1, h2, h3, h4⟩ := CFSG.KC.LQT.M.s4144_proved m11gA m11gB _ m11Elements
    (fun g => by rw [mem_m11Elements, m11_eq]) CFSG.KD.LQT.M11.ha CFSG.KD.LQT.M11.hb ht
    CFSG.KD.LQT.M11.hg hk
  refine ⟨List.all_eq_true.2 fun g hg => decide_eq_true (h1 g hg),
    List.all_eq_true.2 fun g hg => decide_eq_true fun hc ht =>
      h2 g hg hc fun t htl => of_decide_eq_true (List.all_eq_true.1 ht t htl),
    List.all_eq_true.2 fun g hg => decide_eq_true fun ht =>
      h3 g hg fun t htl => of_decide_eq_true (List.all_eq_true.1 ht t htl),
    List.all_eq_true.2 fun u hu => decide_eq_true fun hu1 hu2 => ?_, hgen, hab, hpl, hu0⟩
  obtain ⟨g, hg, e⟩ := h4 u hu hu1 hu2
  exact List.any_eq_true.2 ⟨g, hg, decide_eq_true e⟩

end Certificates
