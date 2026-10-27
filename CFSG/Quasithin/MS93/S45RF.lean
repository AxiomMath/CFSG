module

public import CFSG.Quasithin.MS93.S45RG
public import CFSG.Quasithin.MS93.S45Phi4
public import CFSG.Quasithin.MS93.S45Q4PD

public section

namespace CFSG.Quasithin.MS93.S45R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93.S45
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

variable {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem hloc_inf_zloc_eq_bot (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a) (h10 : 10 ≤ a)
    (haN : a + 6 ≤ N) : Hloc c.hyp.le L (p a) ⊓ Zloc c.hyp.le L (p (a + 2)) = ⊥ := by
  have h := c.hyp
  obtain ⟨x, rfl⟩ : ∃ x, a = x + 6 := ⟨a - 6, by omega⟩
  have hx : Even x := by
    obtain ⟨u, hu⟩ := ha
    exact ⟨u - 3, by omega⟩
  have hM8 := c.isMVtx_of_isGoodPath hp (k := x + 8) (by omega) (hx.add (by decide))
  have hadj : (puAmalgam h.le).treeGraph.Adj (p (x + 8)) (p (x + 7)) :=
    (hp.adj (x + 7) (by omega)).symm
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h c.via hM8
  have hHU : Hloc h.le L (p (x + 6)) ≤ Uloc h.le L (p (x + 8)) :=
    (c.hloc_eq_usup' hp hx (by omega) (by omega)).le.trans
      ((c.usup_eq_uloc_inf_centralizer hψ hM8 hadj).le.trans inf_le_left)
  exact eq_bot_iff.mpr ((inf_le_inf_right _ hHU).trans (uloc_inf_zloc h c.full _).le)

theorem zloc_eq_hloc_sup_inf (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a) (h10 : 10 ≤ a)
    (haN : a + 6 ≤ N) :
    Zloc c.hyp.le L (p a) =
      Hloc c.hyp.le L (p a) ⊔ (Zloc c.hyp.le L (p a) ⊓ Zloc c.hyp.le L (p (a + 2))) := by
  have h := c.hyp
  obtain ⟨x, rfl⟩ : ∃ x, a = x + 6 := ⟨a - 6, by omega⟩
  have hx : Even x := by
    obtain ⟨u, hu⟩ := ha
    exact ⟨u - 3, by omega⟩
  have hM6 := c.isMVtx_of_isGoodPath hp (k := x + 6) (by omega) ha
  have hM8 := c.isMVtx_of_isGoodPath hp (k := x + 8) (by omega) (hx.add (by decide))
  have hadj : (puAmalgam h.le).treeGraph.Adj (p (x + 8)) (p (x + 7)) :=
    (hp.adj (x + 7) (by omega)).symm
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h c.via hM8
  have hHU := c.hloc_eq_usup' hp hx (by omega) (by omega)
  have hZH : ZH (puAmalgam h.le) (p (x + 7)) =
      Hloc h.le L (p (x + 6)) ⊔ Zloc h.le L (p (x + 8)) := by
    rw [hHU]
    exact c.zh_eq_usup_sup_zloc hψ hM8 hadj
  have hZ6 : Zloc h.le L (p (x + 6)) ≤ ZH (puAmalgam h.le) (p (x + 7)) :=
    zloc_le_zh h c.full hM6 (hp.adj (x + 6) (by omega))
  have hH6 : Hloc h.le L (p (x + 6)) ≤ Zloc h.le L (p (x + 6)) :=
    (Subgroup.commutator_mono (c.vcirc_le_vv _) le_rfl).trans (c.commutator_vv_qv_le_zloc hM6)
  have hHs : Hloc h.le L (p (x + 6)) ≤ stab (puAmalgam h.le) (p (x + 8)) :=
    hHU.le.trans ((c.usup_eq_uloc_inf_centralizer hψ hM8 hadj).le.trans (inf_le_left.trans
      ((uloc_le_zm h c.full hM8).trans ((zm_le_qv_self _ hM8 h.critDist_pos).trans
        (qv_le_stab _ _)))))
  have hn : Hloc h.le L (p (x + 6)) ≤
      Subgroup.normalizer (Zloc h.le L (p (x + 8)) : Set (puAmalgam h.le).Universal) :=
    (Subgroup.le_centralizer_iff.mp ((zloc_le_centralizer_stab h c.full hM8).trans
      (Subgroup.centralizer_le hHs))).trans (Subgroup.centralizer_le_normalizer _)
  refine le_antisymm (fun z hz => ?_) (sup_le hH6 inf_le_left)
  have hz' := hZ6 hz
  rw [hZH, mem_sup_iff_mul_of_le_normalizer hn] at hz'
  obtain ⟨u, hu, w, hw, rfl⟩ := hz'
  have hw6 : w ∈ Zloc h.le L (p (x + 6)) := by
    have := (Zloc h.le L (p (x + 6))).mul_mem ((Zloc h.le L (p (x + 6))).inv_mem (hH6 hu)) hz
    rwa [inv_mul_cancel_left] at this
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right ⟨hw6, hw⟩)

theorem inf_zloc_le_hloc_iff (hZV : c.HZV) (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a)
    (h34 : 34 ≤ a) (haN : a + 30 ≤ N) :
    ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓ Zloc c.hyp.le L (p a) ≤
        Hloc c.hyp.le L (p a) ↔
      ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓
        (Zloc c.hyp.le L (p a) ⊓ Zloc c.hyp.le L (p (a + 2))) = ⊥ := by
  have h := c.hyp
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  obtain ⟨p', hp', hpp', hU1, hU3⟩ := c.exists_branch hp ha (by omega) (by omega)
  have hHV : Hloc h.le L (p a) ≤ ⁅Qv (puAmalgam h.le) (p a), Ltil h.le L (p a)⁆ :=
    (c.hloc_le_commutator_qv_ltil hZV (S45Q4.hQ4 c) hp hp' ha h34 haN hpp' hU1 hU3).trans
      (Subgroup.commutator_le_self _)
  have hHC := hloc_inf_zloc_eq_bot c hp ha (by omega) (by omega)
  constructor
  · intro hC1
    refine eq_bot_iff.mpr fun v hv => ?_
    obtain ⟨hvV, hv02⟩ := Subgroup.mem_inf.mp hv
    obtain ⟨hv0, hv2⟩ := Subgroup.mem_inf.mp hv02
    rw [← hHC]
    exact Subgroup.mem_inf.mpr ⟨hC1 (Subgroup.mem_inf.mpr ⟨hvV, hv0⟩), hv2⟩
  · intro hC v hv
    obtain ⟨hvV, hvZ⟩ := Subgroup.mem_inf.mp hv
    have hH6 : Hloc h.le L (p a) ≤ Zloc h.le L (p a) :=
      (Subgroup.commutator_mono (c.vcirc_le_vv _) le_rfl).trans (c.commutator_vv_qv_le_zloc hα)
    have hCs : Zloc h.le L (p a) ⊓ Zloc h.le L (p (a + 2)) ≤ stab (puAmalgam h.le) (p a) :=
      inf_le_left.trans ((zloc_le_zm h c.full hα).trans
        ((zm_le_qv_self _ hα h.critDist_pos).trans (qv_le_stab _ _)))
    have hn : Hloc h.le L (p a) ≤ Subgroup.normalizer
        ((Zloc h.le L (p a) ⊓ Zloc h.le L (p (a + 2)) : Subgroup _) :
          Set (puAmalgam h.le).Universal) :=
      (hH6.trans ((zloc_le_centralizer_stab h c.full hα).trans
        (Subgroup.centralizer_le hCs))).trans (Subgroup.centralizer_le_normalizer _)
    have hvZ' := hvZ
    rw [zloc_eq_hloc_sup_inf c hp ha (by omega) (by omega), mem_sup_iff_mul_of_le_normalizer hn]
      at hvZ'
    obtain ⟨u, hu, w, hw, rfl⟩ := hvZ'
    have hwV : w ∈ ⁅Qv (puAmalgam h.le) (p a), Ltil h.le L (p a)⁆ := by
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hHV hu)) hvV
      rwa [inv_mul_cancel_left] at this
    have hw1 : w = 1 := by
      rw [← Subgroup.mem_bot, ← hC]
      exact Subgroup.mem_inf.mpr ⟨hwV, hw⟩
    rw [hw1, mul_one]
    exact hu

end Ctx

end CFSG.Quasithin.MS93.S45R
