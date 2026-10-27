module

public import CFSG.Quasithin.EmptyFaithful.S151S9TKInputs
public import CFSG.Quasithin.EmptyFaithful.S151S9TM23

public section

namespace CFSG.Quasithin.S151S9T

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Quasithin.H.MathieuLat

theorem Idx3Wit.ok_of_eq {Lab : Type} [DecidableEq Lab] {W : Idx3Wit} {n : ℕ}
    {act : Array ℕ → Lab → Lab} {Δ : Lab} {D D' : LatData Lab} {zT : Array ℕ}
    (hs : D.sTabs = D'.sTabs) (hm : D.mw.size = D'.mw.size)
    (ht : ∀ j < D.mw.size, D.mt[j]! = D'.mt[j]!) (h : W.Ok n act Δ D zT) :
    W.Ok n act Δ D' zT := by
  have hp : W.p < D.mw.size := h.1
  have ex : W.xT n D = W.xT n D' := by
    unfold Idx3Wit.xT Idx3Wit.letters
    rw [hs, ht _ hp]
  have er : ∀ i, W.rT n D i = W.rT n D' i := fun i => by
    unfold Idx3Wit.rT
    rw [hs]
  have eri : ∀ i, W.riT n D i = W.riT n D' i := fun i => by
    unfold Idx3Wit.riT
    rw [hs]
  have edc : ∀ i, W.dcT n D i = W.dcT n D' i := fun i => by
    unfold Idx3Wit.dcT
    rw [er, ex, eri]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  refine ⟨hm ▸ h1, ht _ hp ▸ h2, hs ▸ h3, ex ▸ h4, ex ▸ h5, h6, h7, fun i hi => ?_,
    fun i hi i' hi' e => h9 i hi i' hi' (by rw [edc, edc, e]), hm ▸ h10, fun j hj => ?_⟩
  · rw [← er, ← eri, ← ex, ← hs]
    exact h8 i hi
  · rw [← ht j (hm ▸ hj)]
    exact h11 j (hm ▸ hj)

theorem m23Check_of_K
    (h : m23CheckK) : m23CheckD := by
  have hw : m23Ctx.D.mw = A312M23.m23MwLit := m23_mw
  have hM := m23_lat_cert.1.2.2.2.1
  have hsT : m23Ctx.D.sTabs = m23STabs := by
    rw [← m23Ctx.hsg]
    exact m23_sGens.1
  refine Idx3Wit.ok_of_eq (D := m23MemW) hsT.symm (by rw [hw]; rfl) (fun j hj => ?_) h
  have hj' : j < m23Ctx.D.mw.size := by rw [hw]; exact hj
  rw [(hM.2.2.2.2 j hj').2.1, hw]
  have hj2 : j < A312M23.m23MwLit.size := hj
  change (A312M23.m23MwLit.map fun ws =>
    ws.map (wordTabA #[m23ta.toArray, m23tb.toArray] 23))[j]! = _
  rw [getElem!_pos (A312M23.m23MwLit.map fun ws =>
      ws.map (wordTabA #[m23ta.toArray, m23tb.toArray] 23)) j (by simpa using hj2),
    Array.getElem_map, getElem!_pos A312M23.m23MwLit j hj2]

end CFSG.Quasithin.S151S9T

end
