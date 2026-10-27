module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporHe
import Certificates.Kernel.He4049.Hall
import Certificates.Kernel.He4049.Orb
import all CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporHe

namespace Certificates

open CFSG.QuasithinUnique.A5.Kc3SporHe CFSG.QuasithinUnique.K1.SporadicPerm

set_option maxRecDepth 10000 in
theorem heSg_eq :
    heSg = CFSG.KD.He4049.gs.map (CFSG.KD.He4049.G.E CFSG.Sporadic.He.a CFSG.Sporadic.He.b) := by
  unfold heSg heQp CFSG.KD.He4049.gs
  simp only [List.map_cons, List.map_nil]
  rw [CFSG.KD.He4049.H.slpElts_heProg _ _ (by decide),
    CFSG.KD.He4049.H.slpElts_heProg _ _ (by decide),
    CFSG.KD.He4049.H.slpElts_heProg _ _ (by decide),
    CFSG.KD.He4049.H.slpElts_heProg _ _ (by decide)]

theorem chainBase_eq : CFSG.Sporadic.He.Native.chainBase.toList = CFSG.KD.He4049.B := rfl

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.A5.Kc3SporHe in
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.A5.Kc3SporLine in
public theorem certificate4049 : 
    (tab 8330 (CFSG.Sporadic.He.a : CFSG.Sporadic.He.J)).toArray = heTa →
    (tab 8330 (CFSG.Sporadic.He.b : CFSG.Sporadic.He.J)).toArray = heTb →
    (∀ g : CFSG.Sporadic.He.J,
      (∀ p ∈ CFSG.Sporadic.He.Native.chainBase.toList, act 8330 g p = p) → g = 1) →
    ∀ E : Subgroup CFSG.Sporadic.He.J, E ≤ heR → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
      (∀ x ∈ E, x * x = 1) → Nat.card E = 16 → ¬ PairFibersAllowed (Fin 8330) E := by
  refine fun hta htb hbase => ?_
  have hR : heR = CFSG.KD.He4049.H.RX CFSG.Sporadic.He.a CFSG.Sporadic.He.b := by
    unfold heR CFSG.KD.He4049.H.RX
    rw [heSg_eq]
  rw [hR]
  exact CFSG.KD.He4049.H.hall (hta.trans CFSG.KD.He4049.heTa_eq)
    (htb.trans CFSG.KD.He4049.heTb_eq) (fun g hg => hbase g (by rw [chainBase_eq]; exact hg))

end Certificates
