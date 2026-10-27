module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporRuCertificateInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporLineGroup
import Certificates.Kernel.Ru4120.Hall

namespace Certificates

open CFSG.QuasithinUnique.A5.Kc3SporRu CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Sporadic.SmallF2
open CFSG.Sporadic.Ru.Native (ruData)

theorem ruB_eq : ruB = CFSG.KD.Ru4120.B := by decide

set_option maxRecDepth 10000 in
theorem ruSg_eq :
    ruSg = CFSG.KD.Ru4120.gs.map (CFSG.KD.Ru4120.G.E (a ruData) (b ruData)) := by
  unfold ruSg ruQp CFSG.KD.Ru4120.gs
  simp only [List.map_cons, List.map_nil]
  rw [CFSG.KD.Ru4120.H.slpElts_ruProg _ _ (by decide), CFSG.KD.Ru4120.H.slpElts_ruProg _ _ (by decide),
    CFSG.KD.Ru4120.H.slpElts_ruProg _ _ (by decide)]

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.A5.Kc3SporRu in
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.A5.Kc3SporLine in
open CFSG.Sporadic.SmallF2 in
open CFSG.Sporadic.Ru.Native (ruData) in
public theorem certificate4120 : (tab ruData.n (a ruData)).toArray = ruTa → (tab ruData.n (b ruData)).toArray = ruTb →
    (∀ g : J ruData, (∀ p ∈ ruB, act ruData.n g p = p) → g = 1) →
    ∀ E : Subgroup (J ruData), E ≤ ruR → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
      (∀ x ∈ E, x * x = 1) → Nat.card E = 16 → ¬ PairFibersAllowed (Fin ruPD.n) E := by
  refine fun hta htb hbase => ?_
  have hfin : Finite (J ruData) := inferInstance
  have hR : ruR = CFSG.KD.Ru4120.H.RX (a ruData) (b ruData) := by
    unfold ruR CFSG.KD.Ru4120.H.RX
    rw [ruSg_eq]
  have h := @CFSG.KD.Ru4120.H.Ctx.mk (J ruData) _ ruAct (a ruData) (b ruData) hta htb
    (fun g hg => hbase g (by rw [ruB_eq]; exact hg))
  rw [hR]
  exact @CFSG.KD.Ru4120.H.hall (J ruData) _ ruAct (a ruData) (b ruData) hfin h

end Certificates
