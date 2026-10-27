
module

public import CFSG.Quasithin.Vol2.KGFactE64Lat
public import CFSG.Quasithin.Vol2.KGFactE64M24Data
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24Base
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRows
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24Facts
import all CFSG.Blueprint.NativeSporadic
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24Base

@[expose] public section

namespace CFSG.Quasithin.H13.KGE64

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.M24 CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Quasithin.H13.KGInsp CFSG.Blueprint

theorem m24_o2_card [M24Lat]
    (j : ℕ) (hj : j < 13) :
    Nat.card (pCoreOf 2 (m24Ctx.Y j)) = (m24Mems.getD j ⟨0, 0, 0⟩).o2 := by
  have h1 : j < m24Ctx.J := by rw [m24_J]; exact hj
  rw [(m24Ctx.memStmt_default m24_o2OK h1).2.1]
  have h2 := m24_rows
  have h3 : m24Mems.getD j ⟨0, 0, 0⟩ = defaultRow 10 m24Ctx.D m24OtK j := by
    rw [← h2, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]
  rw [h3]
  rfl

end CFSG.Quasithin.H13.KGE64
