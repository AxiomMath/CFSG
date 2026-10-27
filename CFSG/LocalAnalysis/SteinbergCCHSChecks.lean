module

public import Certificates.Certificate18010

public section

namespace CFSG.LocalAnalysis.HigmanSimsCover

open CFSG.CosetTable CFSG.LieType.Multipliers

theorem presented_bound :
    Finite (PG 3 rels) ∧ Nat.card (PG 3 rels) ≤ 44352000 :=
  Certificates.certificate18010.1

theorem cover_bound :
    Finite (PG 3 coverWs) ∧ Nat.card (PG 3 coverWs) ≤ 88704000 :=
  Certificates.certificate18010.2.1

theorem kerWord_order :
    2 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin 3) | r ∈ coverWs.map FreeGroup.mk}
      (FreeGroup.mk kerWord)) :=
  Certificates.certificate18010.2.2.1

theorem hs_check :
    CFSG.Sporadic.Bridge.TwoGen.Native.vecRelCheck CFSG.Sporadic.HS.Native.hsData
      (hsWords.map (List.map fun l => (l.1.val, l.2))) = true :=
  Certificates.certificate18010.2.2.2

end CFSG.LocalAnalysis.HigmanSimsCover
