module

public import CFSG.Quasithin.MS93.MResDefs
public import CFSG.Quasithin.MS93.S45C14
public import CFSG.Quasithin.MS93.S45B12
public import CFSG.Quasithin.MS93.S45RE
public import CFSG.Quasithin.MS93.S45RF

public section

namespace CFSG.Quasithin.MS93.MRes

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S45
open scoped commutatorElement Matrix

section Ctx

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F] {M T L : Subgroup G}
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem hC1_of_two (hB : S45C1BTwo) (c : Ctx M T L φ) (hZV : c.HZV) (hq : Fintype.card F = 2)
    {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ} (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a)
    (h34 : 34 ≤ a) (haN : a + 30 ≤ N) :
    ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓ Zloc c.hyp.le L (p a) ≤
      Hloc c.hyp.le L (p a) := by
  by_cases hZH : Zloc c.hyp.le L (p a) ≤ Hloc c.hyp.le L (p a)
  · exact inf_le_right.trans hZH
  have hh := c.hyp
  have h20 := hh.hyp20
  have hα : IsMVtx (puAmalgam hh.le) (p a) := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hαβ : (puAmalgam hh.le).treeGraph.Adj (p a) (p (a + 1)) := hp.adj a (by omega)
  have hEZ : ⁅Qv (puAmalgam hh.le) (p a), Ltil hh.le L (p a)⁆ ⊓
      (Zloc hh.le L (p a) ⊓ Zloc hh.le L (p (a + 2))) ≤ Zloc hh.le L (p a) :=
    inf_le_right.trans inf_le_left
  have hET := hEZ.trans ((zloc_le_zm hh c.full hα).trans
    ((zm_le_qv_self _ hα hh.critDist_pos).trans (qv_le_qv _ h20 hα hαβ)))
  have hEα := (Subgroup.le_centralizer_iff.mp
    (hEZ.trans (zloc_le_centralizer_stab hh c.full hα))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hE := ms21_iii _ h20 hα hαβ hET hEα (hB G M T L F φ c hZV hq p N hp a ha h34 haN hZH)
  exact (S45R.Ctx.inf_zloc_le_hloc_iff c hZV hp ha h34 haN).mpr hE

theorem hC14_of_two (h14 : MS14AS) (hSQ : SQTKQuot) (hB : S45C1BTwo) (c : Ctx M T L φ)
    (hZV : c.HZV) (hq : Fintype.card F = 2) : c.HC14 :=
  fun _ _ hp _ ha h34 haN => ⟨hC1_of_two hB c hZV hq hp ha h34 haN,
    S45R.Ctx.not_frattiniIn_le c h14 hSQ hZV hp ha h34 haN⟩

theorem hQ2b_of_two (h14 : MS14AS) (hSQ : SQTKQuot) (hB : S45C1BTwo) (c : Ctx M T L φ)
    (hZV : c.HZV) (hq : Fintype.card F = 2) : c.HQ2b := by
  intro p p' N hp hp' a ha h34 haN hpp' hU1 hU3
  have hQ4 := S45Q4.hQ4 c
  obtain ⟨hC1, hC4⟩ := hC14_of_two h14 hSQ hB c hZV hq p N hp a ha h34 haN
  exact ⟨c.inf_centralizer_ltil_le h14 hSQ hZV hQ4 hp hp' ha h34 haN hpp' hU1 hU3 hC1,
    c.center_le_uloc_sup_hloc h14 hSQ hZV hQ4 hp hp' ha h34 haN hpp' hU1 hU3 hC1,
    c.frattiniIn_eq_vcirc h14 hSQ hZV hQ4 hp hp' ha h34 haN hpp' hU1 hU3 hC1 hC4,
    c.inf_centralizer_vcirc_le_whv h14 hSQ hZV hQ4 hp hp' ha h34 haN hpp' hU1 hU3,
    c.commutator_qv_ltil_le_top hZV hp hp' ha h34 haN hpp' hU3⟩

end Ctx

end CFSG.Quasithin.MS93.MRes
