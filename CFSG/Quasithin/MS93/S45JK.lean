module

public import CFSG.Quasithin.MS93.S45JA
public import CFSG.Quasithin.MS93.S45GQ
public import CFSG.Quasithin.MS93.S45M2

public section

namespace CFSG.Quasithin.MS93.S45J

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93.S45
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

variable {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem mem_qv_of_mem_bloc (hp : IsGoodPath _ p N) {x : ℕ} (hx : Even x) (h4 : 4 ≤ x)
    (hxN : x + 18 ≤ N) {d : (puAmalgam c.hyp.le).Universal}
    (hdB : d ∈ Bloc c.hyp.le L (p (x + 6)))
    (hdL : d ∈ Subgroup.centralizer (Ltil c.hyp.le L (p (x + 6)) : Set _)) :
    d ∈ Qv (puAmalgam c.hyp.le) (p (x + 14)) := by
  have h := c.hyp
  have h20 := h.hyp20
  have hM12 := c.isMVtx_of_isGoodPath hp (k := x + 12) (by omega) (hx.add (by decide))
  have hM14 := c.isMVtx_of_isGoodPath hp (k := x + 14) (by omega) (hx.add (by decide))
  have h12 : d ∈ Qv (puAmalgam h.le) (p (x + 12)) := by
    have := c.bloc_le_qv hp (x := x + 6) (hx.add (by decide)) (by omega) (by omega) hdB
    rwa [show x + 6 + 6 = x + 12 by omega] at this
  have ha : (puAmalgam h.le).treeGraph.Adj (p (x + 12)) (p (x + 13)) :=
    hp.adj (x + 12) (by omega)
  have ha' : (puAmalgam h.le).treeGraph.Adj (p (x + 14)) (p (x + 13)) :=
    (hp.adj (x + 13) (by omega)).symm
  have h13 : d ∈ Qv (puAmalgam h.le) (p (x + 13)) := qv_le_qv _ h20 hM12 ha h12
  rw [← c.cent _ _ hM14 ha']
  refine ⟨h13, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
  have hz' : z ∈ ZM (puAmalgam h.le) (p (x + 6 + 8)) := by
    rwa [show x + 6 + 8 = x + 14 by omega]
  exact (S45G.Ctx.commute_zm_of_mem_bloc c hp (y := x + 6) (hx.add (by decide)) (by omega)
    (by omega) hdB hdL hz').symm

theorem mem_zm_sup_qv (hq : Fintype.card F = 2) (hp : IsGoodPath _ p N) {x : ℕ} (hx : Even x)
    (h4 : 4 ≤ x) (hxN : x + 22 ≤ N)
    (hne : ¬ ZM (puAmalgam c.hyp.le) (p (x + 8)) ≤
      Vcirc c.hyp.le L (p (x + 6)) ⊔ ZM _ (p (x + 6)))
    {d : (puAmalgam c.hyp.le).Universal} (hdB : d ∈ Bloc c.hyp.le L (p (x + 6)))
    (hdL : d ∈ Subgroup.centralizer (Ltil c.hyp.le L (p (x + 6)) : Set _))
    (hdH : ∀ g ∈ stab (puAmalgam c.hyp.le) (p (x + 6)), ⁅d, g⁆ ∈ Hloc c.hyp.le L (p (x + 6))) :
    d ∈ ZM (puAmalgam c.hyp.le) (p (x + 8)) ⊔ Qv _ (p (x + 16)) := by
  have h := c.hyp
  have h20 := h.hyp20
  have : CharP F 2 := c.charP
  have hb2 : 2 < critDist (puAmalgam h.le) := by rw [c.b8]; norm_num
  have hM : ∀ k, k ≤ N → Even k → IsMVtx (puAmalgam h.le) (p k) := fun k hk hev =>
    c.isMVtx_of_isGoodPath hp hk hev
  have hd' : ∀ i j, i ≤ j → j ≤ N → (puAmalgam h.le).treeGraph.dist (p i) (p j) = j - i :=
    fun i j hij hj => hp.dist_eq' hij hj
  have hM4 := hM (x + 4) (by omega) (hx.add (by decide))
  have hM8 := hM (x + 8) (by omega) (hx.add (by decide))
  have hM10 := hM (x + 10) (by omega) (hx.add (by decide))
  have hM12 := hM (x + 12) (by omega) (hx.add (by decide))
  have hM14 := hM (x + 14) (by omega) (hx.add (by decide))
  have hM16 := hM (x + 16) (by omega) (hx.add (by decide))
  have hadj : ∀ i, i < N → (puAmalgam h.le).treeGraph.Adj (p i) (p (i + 1)) := hp.adj
  have hc16 : IsCritical (puAmalgam h.le) (p (x + 16)) (p (x + 8)) := by
    have := hp.crit (x + 8) (hx.add (by decide)) (by omega)
    rwa [show x + 8 + 8 = x + 16 by omega] at this
  have hc12 : IsCritical (puAmalgam h.le) (p (x + 12)) (p (x + 4)) := by
    have := hp.crit (x + 4) (hx.add (by decide)) (by omega)
    rwa [show x + 4 + 8 = x + 12 by omega] at this
  have hc10 : IsCritical (puAmalgam h.le) (p (x + 10)) (p (x + 2)) := by
    have := hp.crit (x + 2) (hx.add (by decide)) (by omega)
    rwa [show x + 2 + 8 = x + 10 by omega] at this
  by_contra hd3
  have hdQ14 := mem_qv_of_mem_bloc c hp hx h4 (by omega) hdB hdL
  set Y := ZM (puAmalgam h.le) (p (x + 8)) ⊔ Subgroup.zpowers d with hYdef
  have ha1615 : (puAmalgam h.le).treeGraph.Adj (p (x + 16)) (p (x + 15)) :=
    (hadj (x + 15) (by omega)).symm
  have hQT : Qv (puAmalgam h.le) (p (x + 14)) ≤ Qv _ (p (x + 15)) :=
    qv_le_qv _ h20 hM14 (hadj (x + 14) (by omega))
  have hZ8Q : ZM (puAmalgam h.le) (p (x + 8)) ≤ Qv _ (p (x + 14)) :=
    zm_le_qv_of_dist_lt _ hM8 (by rw [hd' (x + 8) (x + 14) (by omega) (by omega), c.b8]; omega)
  have hYT : Y ≤ Qv (puAmalgam h.le) (p (x + 15)) :=
    sup_le (hZ8Q.trans hQT) ((Subgroup.zpowers_le).mpr (hQT hdQ14))
  have hYs : Y ≤ stab (puAmalgam h.le) (p (x + 16)) :=
    hYT.trans (qv_le_stab_of_adj _ ha1615.symm)
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h c.via hM16
  set E := natImage ψ Y with hEdef
  have hET : E ≤ natImage ψ (Qv (puAmalgam h.le) (p (x + 15))) := natImage_mono hYT
  have hT := c.fixN_eq_commN_qv hψ hM16 ha1615
  have hZ8E : natImage ψ (ZM (puAmalgam h.le) (p (x + 8))) ≤ E := natImage_mono le_sup_left
  have hcardZ : Nat.card ↥(natImage ψ (ZM (puAmalgam h.le) (p (x + 8)))) = Fintype.card F :=
    c.card_natImage_zm hc16 hψ
  have hEq : Fintype.card F < Nat.card ↥E := by
    by_contra hle
    push Not at hle
    apply hd3
    have hfinE : Finite ↥E := Nat.finite_of_card_ne_zero (by
      have := Nat.card_pos (α := ↥(natImage ψ (ZM (puAmalgam h.le) (p (x + 8)))))
      have := Subgroup.card_le_of_le hZ8E
      omega)
    have hEeq : E = natImage ψ (ZM (puAmalgam h.le) (p (x + 8))) :=
      (Subgroup.eq_of_le_of_card_ge hZ8E (by rw [hcardZ]; exact hle)).symm
    have hdY : d ∈ Y := Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
    have hdE : toSL3 ψ ⟨d, hYs hdY⟩ ∈ natImage ψ (ZM (puAmalgam h.le) (p (x + 8))) :=
      hEeq ▸ mem_natImage.mpr ⟨⟨d, hYs hdY⟩, hdY, rfl⟩
    obtain ⟨z, hz, hzd⟩ := mem_natImage.mp hdE
    have hk : toSL3 ψ (z⁻¹ * ⟨d, hYs hdY⟩) = 1 := by rw [map_mul, map_inv, hzd, inv_mul_cancel]
    rw [toSL3_eq_one_iff hψ] at hk
    have hq' : (z : (puAmalgam h.le).Universal)⁻¹ * d ∈ Qv (puAmalgam h.le) (p (x + 16)) := by
      rw [← S4A.stab_inf_centralizer_uloc h c.via hM16]
      refine ⟨(z⁻¹ * ⟨d, hYs hdY⟩ : ↥(stab _ _)).2,
        Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      have h1 := hk v hv
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      calc v * ((z : (puAmalgam h.le).Universal)⁻¹ * d) =
          ((z : (puAmalgam h.le).Universal)⁻¹ * d * v *
            ((z : (puAmalgam h.le).Universal)⁻¹ * d)⁻¹) *
              ((z : (puAmalgam h.le).Universal)⁻¹ * d) := by rw [h1]
        _ = (z : (puAmalgam h.le).Universal)⁻¹ * d * v := by group
    rw [show d = (z : (puAmalgam h.le).Universal) * ((z : (puAmalgam h.le).Universal)⁻¹ * d) by
      group]
    exact mul_mem (Subgroup.mem_sup_left hz) (Subgroup.mem_sup_right hq')
  have hE : E ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hEq
    have := Fintype.one_lt_card (α := F)
    omega
  have hfix : Module.finrank F ↥(fixN E) = 2 := by
    have h1 : 2 ≤ Module.finrank F ↥(fixN E) := hT.2 ▸ Submodule.finrank_mono (fixN_anti hET)
    have h2 : Module.finrank F ↥(fixN E) < 3 := by
      have := Submodule.finrank_lt (fixN_ne_top hE)
      rwa [Module.finrank_fin_fun] at this
    omega
  have hcomm : commN E = fixN (natImage ψ (Qv (puAmalgam h.le) (p (x + 15)))) := by
    have hle : commN E ≤ fixN (natImage ψ (Qv (puAmalgam h.le) (p (x + 15)))) :=
      hT.1 ▸ commN_mono hET
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    rw [hT.2]
    by_contra hlt2
    push Not at hlt2
    have hb := card_le_pow_finrank E
    rw [hfix, show 3 - 2 = 1 by rfl, one_mul, Nat.card_eq_fintype_card (α := F)] at hb
    have : Fintype.card F ^ Module.finrank F ↥(commN E) ≤ Fintype.card F ^ 1 :=
      Nat.pow_le_pow_right Fintype.card_pos (by omega)
    rw [pow_one] at this
    omega
  have hW : Usup (puAmalgam h.le) (p (x + 16)) (p (x + 15)) ≤
      ⁅Uloc h.le L (p (x + 16)), Y⁆ := by
    intro w hw
    have hwU : w ∈ Uloc h.le L (p (x + 16)) := by
      rw [c.usup_eq_uloc_inf_centralizer hψ hM16 ha1615] at hw; exact hw.1
    refine (S4A.mem_commutator_iff_natVec hψ hYs ⟨w, hwU⟩).mpr ?_
    rw [← hEdef, hcomm]
    exact (c.mem_usup_iff hψ hM16 ha1615 ⟨w, hwU⟩).mp hw
  have hQU : Uloc h.le L (p (x + 8)) ≤
      Subgroup.centralizer (Qv (puAmalgam h.le) (p (x + 8)) : Set _) :=
    (uloc_le_zm h c.full hM8).trans (zm_le_centralizer_qv _ h20 hM8)
  obtain ⟨ψ₈, -, hψ₈⟩ := exists_natural_Uloc h c.via hM8
  have hKn : stab (puAmalgam h.le) (p (x + 8)) ≤
      Subgroup.normalizer (relCen (Qv (puAmalgam h.le) (p (x + 8))) _ hQU : Set _) :=
    le_normalizer_relCen hQU (stab_le_normalizer_qv _ _) hψ₈.1
  have ha87 : (puAmalgam h.le).treeGraph.Adj (p (x + 8)) (p (x + 7)) :=
    (hadj (x + 7) (by omega)).symm
  have ha76 : (puAmalgam h.le).treeGraph.Adj (p (x + 7)) (p (x + 6)) :=
    (hadj (x + 6) (by omega)).symm
  have hHU : Hloc h.le L (p (x + 6)) ≤ Uloc h.le L (p (x + 8)) := by
    rw [c.hloc_eq_usup' hp hx h4 (by omega), c.usup_eq_uloc_inf_centralizer hψ₈ hM8 ha87]
    exact inf_le_left
  have hQ8s : Qv (puAmalgam h.le) (p (x + 8)) ≤ stab _ (p (x + 6)) :=
    (qv_le_qv _ h20 hM8 ha87).trans (qv_le_stab_of_adj _ ha76)
  have hYK : Y ≤ relCen (Qv (puAmalgam h.le) (p (x + 8))) _ hQU := by
    refine sup_le (fun z hz => mem_relCen_iff.mpr ⟨zm_le_qv_self _ hM8 h.critDist_pos hz,
      fun s hs => ?_⟩) ((Subgroup.zpowers_le).mpr (mem_relCen_iff.mpr
        ⟨?_, fun s hs => hHU (hdH s (hQ8s hs))⟩))
    · rw [(commutatorElement_eq_one_iff_mul_comm).mpr
        ((Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hM8 hz) s hs).symm)]
      exact one_mem _
    · exact vi_le_qv _ (by rw [hd' (x + 6) (x + 8) (by omega) (by omega), c.b8]; omega)
        (bloc_le_vv h _ hdB)
  have hc8' : IsCritical (puAmalgam h.le) (p (x + 8)) (p (x + 16)) := c.isCritical_symm hc16
  have hU16s : Uloc h.le L (p (x + 16)) ≤ stab (puAmalgam h.le) (p (x + 8)) :=
    (uloc_le_zm h c.full hM16).trans (zm_le_stab_of_isCritical _ h20 c.bpos hc8')
  have hUYK : ⁅Uloc h.le L (p (x + 16)), Y⁆ ≤ relCen (Qv (puAmalgam h.le) (p (x + 8))) _ hQU := by
    rw [Subgroup.commutator_le]
    intro v hv y hy
    have hvy := (Subgroup.mem_normalizer_iff.mp (hKn (hU16s hv)) y).mp (hYK hy)
    rw [commutatorElement_def]
    exact mul_mem hvy (inv_mem (hYK hy))
  have e14a : Hloc h.le L (p (x + 14)) = Usup _ (p (x + 16)) (p (x + 15)) := by
    have := c.hloc_eq_usup' hp (x := x + 8) (hx.add (by decide)) (by omega) (by omega)
    rwa [show x + 8 + 6 = x + 14 by omega, show x + 8 + 8 = x + 16 by omega,
      show x + 8 + 7 = x + 15 by omega] at this
  have e14b : Hloc h.le L (p (x + 14)) = Usup _ (p (x + 12)) (p (x + 13)) := by
    have := c.hloc_eq_usup hp (x := x + 8) (hx.add (by decide)) (by omega) (by omega)
    rwa [show x + 8 + 6 = x + 14 by omega, show x + 8 + 4 = x + 12 by omega,
      show x + 8 + 5 = x + 13 by omega] at this
  obtain ⟨ψ₁₂, -, hψ₁₂⟩ := exists_natural_Uloc h c.via hM12
  have ha1211 : (puAmalgam h.le).treeGraph.Adj (p (x + 12)) (p (x + 11)) :=
    (hadj (x + 11) (by omega)).symm
  have ha1213 : (puAmalgam h.le).treeGraph.Adj (p (x + 12)) (p (x + 13)) := hadj (x + 12) (by omega)
  have hne1113 : Usup (puAmalgam h.le) (p (x + 12)) (p (x + 13)) ≠
      Usup _ (p (x + 12)) (p (x + 11)) := by
    intro heq
    have hz := c.zh_ne_of_isGoodPath hp (y := x + 12) (hx.add (by decide)) (by omega) (by omega)
    rw [show x + 12 - 1 = x + 11 by omega, show x + 12 + 1 = x + 13 by omega] at hz
    exact hz ((c.usup_eq_iff_zh_eq hψ₁₂ hM12 ha1213 ha1211).mp heq).symm
  obtain ⟨u, hu13, hu11⟩ : ∃ u ∈ Usup (puAmalgam h.le) (p (x + 12)) (p (x + 13)),
      u ∉ Usup (puAmalgam h.le) (p (x + 12)) (p (x + 11)) := by
    by_contra hcon
    push Not at hcon
    have hfin : Finite ↥(Usup (puAmalgam h.le) (p (x + 12)) (p (x + 11))) :=
      Nat.finite_of_card_ne_zero (by
        rw [c.card_usup hψ₁₂ hM12 ha1211]; exact pow_ne_zero _ Fintype.card_ne_zero)
    exact hne1113 (Subgroup.eq_of_le_of_card_ge hcon (by
      rw [c.card_usup hψ₁₂ hM12 ha1211, c.card_usup hψ₁₂ hM12 ha1213]))
  have huK : u ∈ relCen (Qv (puAmalgam h.le) (p (x + 8))) _ hQU :=
    hUYK (hW (by rw [← e14a, e14b]; exact hu13))
  obtain ⟨-, huQ⟩ := mem_relCen_iff.mp huK
  have hu12 : u ∈ Uloc h.le L (p (x + 12)) := by
    rw [c.usup_eq_uloc_inf_centralizer hψ₁₂ hM12 ha1213] at hu13; exact hu13.1
  have huZ12 : u ∈ ZM (puAmalgam h.le) (p (x + 12)) := uloc_le_zm h c.full hM12 hu12
  have huV : u ∈ Vv (puAmalgam h.le) (p (x + 10)) :=
    c.zm_le_vv_of_le hM12 (by rw [hd' (x + 10) (x + 12) (by omega) (by omega)]; omega) huZ12
  have hne10 : ¬ ZM (puAmalgam h.le) (p (x + 8)) ≤
      Vcirc h.le L (p (x + 10)) ⊔ ZM _ (p (x + 10)) := by
    rwa [← zm_le_vhat_iff_of_isGoodPath c hp hx (by omega)]
  have ha89 : (puAmalgam h.le).treeGraph.Adj (p (x + 8)) (p (x + 9)) := hadj (x + 8) (by omega)
  have ha109 : (puAmalgam h.le).treeGraph.Adj (p (x + 10)) (p (x + 9)) :=
    (hadj (x + 9) (by omega)).symm
  have hidx := zm_inf_vhat_le c hq hM8 ha89 ha109 hne10
  have hQ8s10 : Qv (puAmalgam h.le) (p (x + 8)) ≤ stab _ (p (x + 10)) :=
    (qv_le_qv _ h20 hM8 ha89).trans (qv_le_stab_of_adj _ ha109.symm)
  have huQ8 : ∀ s ∈ Qv (puAmalgam h.le) (p (x + 8)), ⁅u, s⁆ ∈ Bloc h.le L (p (x + 10)) := by
    intro s hs
    have h1 : ⁅u, s⁆ ∈ ZM (puAmalgam h.le) (p (x + 8)) := uloc_le_zm h c.full hM8 (huQ s hs)
    have h2 : ⁅u, s⁆ ∈ Vcirc h.le L (p (x + 10)) ⊔ ZM _ (p (x + 10)) :=
      c.commutator_vv_stab_le hM10 (Subgroup.commutator_mem_commutator huV (hQ8s10 hs))
    exact zm_le_bloc h hb2 hM10 (hidx ⟨h1, h2⟩)
  have ha1011 : (puAmalgam h.le).treeGraph.Adj (p (x + 10)) (p (x + 11)) :=
    hadj (x + 10) (by omega)
  have huT11 : ∀ t ∈ Qv (puAmalgam h.le) (p (x + 11)), ⁅u, t⁆ ∈ Bloc h.le L (p (x + 10)) := by
    intro t ht
    have h1 : ⁅u, t⁆ ∈ Usup (puAmalgam h.le) (p (x + 12)) (p (x + 11)) := by
      rw [Usup, zv_of_isMVtx _ hM12]
      exact Subgroup.commutator_mem_commutator huZ12 ht
    exact zm_le_bloc h hb2 hM10 (c.usup_le_zm hM12 ha1211 ha1011 h1)
  obtain ⟨ψ₁₀, hψ₁₀s, hψ₁₀⟩ := exists_natural_Uloc h c.via hM10
  obtain ⟨dual, hdual⟩ := c.exists_isSum_vhat hM10 hψ₁₀s hψ₁₀
  have hdB10 := c.isSum_bloc hM10 hdual
  obtain rfl : dual = true :=
    c.dual_eq_true hp (x := x + 4) (hx.add (by decide)) (by omega) (by omega) hψ₁₀s hψ₁₀ hdB10
  have hZ2Q8 : ZM (puAmalgam h.le) (p (x + 2)) ≤ Qv _ (p (x + 8)) :=
    zm_le_qv_of_dist_lt _ (hM (x + 2) (by omega) (hx.add (by decide)))
      (by rw [hd' (x + 2) (x + 8) (by omega) (by omega), c.b8]; omega)
  have huB : u ∈ Bloc h.le L (p (x + 10)) := by
    refine mem_of_commutator_mem_of_not_le hdB10 (A := Qv (puAmalgam h.le) (p (x + 11)))
      (B := ZM (puAmalgam h.le) (p (x + 2))) ?_ ?_ huV (fun a ha => huT11 a ha)
      (fun b hb => huQ8 b (hZ2Q8 hb))
    · rw [← (c.fixN_eq_commN_qv hψ₁₀ hM10 ha1011).1]
      exact (c.fixN_eq_commN_qv hψ₁₀ hM10 ha1011).2
    ·
      intro hle
      have hpe := hp.pe (x + 10) (hx.add (by decide)) (by omega) (by omega)
      rw [show x + 10 - 8 = x + 2 by omega, show x + 10 + 1 = x + 11 by omega] at hpe
      apply hpe
      rw [Subgroup.le_normalizer_iff_commutator_le_right]
      intro r hr
      have hUZ : Usup (puAmalgam h.le) (p (x + 10)) (p (x + 11)) ≤ ZM _ (p (x + 10)) :=
        c.usup_le_zm hM10 ha1011 ha1011
      have hr' : r ∈ critR (puAmalgam h.le) (p (x + 10)) (p (x + 2)) := by
        rw [critR, Subgroup.commutator_comm]
        exact Subgroup.commutator_mono le_rfl hUZ hr
      have hrU : r ∈ Uloc h.le L (p (x + 10)) := c.critR_le_uloc hc10 hr'
      rw [c.mem_usup_iff hψ₁₀ hM10 ha1011 ⟨r, hrU⟩, (c.fixN_eq_commN_qv hψ₁₀ hM10 ha1011).1]
      exact hle ((c.mem_critR_iff hc10 hψ₁₀ ⟨r, hrU⟩).mp hr')
  have huZ10 : u ∈ ZM (puAmalgam h.le) (p (x + 10)) := by
    have := c.zm_inf_bloc_le hp (x := x + 4) (hx.add (by decide)) (by omega) (by omega)
    rw [show x + 4 + 8 = x + 12 by omega, show x + 4 + 6 = x + 10 by omega] at this
    exact this ⟨huZ12, huB⟩
  have hZ4Q10 : ZM (puAmalgam h.le) (p (x + 4)) ≤ Qv _ (p (x + 10)) :=
    zm_le_qv_of_dist_lt _ hM4 (by rw [hd' (x + 4) (x + 10) (by omega) (by omega), c.b8]; omega)
  have hgeo : geo (puAmalgam h.le) (p (x + 12)) (p (x + 4)) 1 = p (x + 11) := by
    rw [hp.eq_geo_rev (i := x + 4) (j := x + 12) (k := x + 11) (by omega) (by omega) (by omega),
      show x + 12 - (x + 11) = 1 by omega]
  have hu11' := mem_usup_geo_of_commute c hc12 hu12 fun z hz =>
    (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hM10 huZ10) z (hZ4Q10 hz)).symm
  rw [hgeo] at hu11'
  exact hu11 hu11'

theorem commutator_mem_hloc (hq : Fintype.card F = 2) (hp : IsGoodPath _ p N) {x : ℕ}
    (hx : Even x) (h4 : 4 ≤ x) (hxN : x + 22 ≤ N)
    (hne : ¬ ZM (puAmalgam c.hyp.le) (p (x + 8)) ≤
      Vcirc c.hyp.le L (p (x + 6)) ⊔ ZM _ (p (x + 6)))
    {d : (puAmalgam c.hyp.le).Universal} (hdB : d ∈ Bloc c.hyp.le L (p (x + 6)))
    (hdL : d ∈ Subgroup.centralizer (Ltil c.hyp.le L (p (x + 6)) : Set _))
    (hdH : ∀ g ∈ stab (puAmalgam c.hyp.le) (p (x + 6)), ⁅d, g⁆ ∈ Hloc c.hyp.le L (p (x + 6))) :
    ∀ s ∈ Qv (puAmalgam c.hyp.le) (p (x + 8)), ⁅d, s⁆ ∈ Hloc c.hyp.le L (p (x + 10)) := by
  intro s hs
  have h := c.hyp
  have h20 := h.hyp20
  have hM : ∀ k, k ≤ N → Even k → IsMVtx (puAmalgam h.le) (p k) := fun k hk hev =>
    c.isMVtx_of_isGoodPath hp hk hev
  have hM8 := hM (x + 8) (by omega) (hx.add (by decide))
  have hM16 := hM (x + 16) (by omega) (hx.add (by decide))
  have hadj : ∀ i, i < N → (puAmalgam h.le).treeGraph.Adj (p i) (p (i + 1)) := hp.adj
  have hc16 : IsCritical (puAmalgam h.le) (p (x + 16)) (p (x + 8)) := by
    have := hp.crit (x + 8) (hx.add (by decide)) (by omega)
    rwa [show x + 8 + 8 = x + 16 by omega] at this
  have hc8 : IsCritical (puAmalgam h.le) (p (x + 8)) (p (x + 16)) := c.isCritical_symm hc16
  have hd3 := mem_zm_sup_qv c hq hp hx h4 hxN hne hdB hdL hdH
  have hZn : ZM (puAmalgam h.le) (p (x + 8)) ≤
      Subgroup.normalizer (Qv (puAmalgam h.le) (p (x + 16)) : Set _) :=
    (zm_le_stab_of_isCritical _ h20 c.bpos hc16).trans (stab_le_normalizer_qv _ _)
  rw [S45R.mem_sup_iff_mul_of_le_normalizer hZn] at hd3
  obtain ⟨zα, hzα, t, ht, hdeq⟩ := hd3
  obtain ⟨ψ₈, -, hψ₈⟩ := exists_natural_Uloc h c.via hM8
  have ha87 : (puAmalgam h.le).treeGraph.Adj (p (x + 8)) (p (x + 7)) :=
    (hadj (x + 7) (by omega)).symm
  have ha76 : (puAmalgam h.le).treeGraph.Adj (p (x + 7)) (p (x + 6)) :=
    (hadj (x + 6) (by omega)).symm
  have hHU : Hloc h.le L (p (x + 6)) ≤ Uloc h.le L (p (x + 8)) := by
    rw [c.hloc_eq_usup' hp hx h4 (by omega), c.usup_eq_uloc_inf_centralizer hψ₈ hM8 ha87]
    exact inf_le_left
  have hQ8s : Qv (puAmalgam h.le) (p (x + 8)) ≤ stab _ (p (x + 6)) :=
    (qv_le_qv _ h20 hM8 ha87).trans (qv_le_stab_of_adj _ ha76)
  have hx₀H : ⁅d, s⁆ ∈ Hloc h.le L (p (x + 6)) := hdH s (hQ8s hs)
  have hx₀U : ⁅d, s⁆ ∈ Uloc h.le L (p (x + 8)) := hHU hx₀H
  have e10 : Hloc h.le L (p (x + 10)) = Usup _ (p (x + 8)) (p (x + 9)) := by
    have := c.hloc_eq_usup hp (x := x + 4) (hx.add (by decide)) (by omega) (by omega)
    rwa [show x + 4 + 6 = x + 10 by omega, show x + 4 + 4 = x + 8 by omega,
      show x + 4 + 5 = x + 9 by omega] at this
  have hgeo : geo (puAmalgam h.le) (p (x + 8)) (p (x + 16)) 1 = p (x + 9) := by
    rw [hp.eq_geo (i := x + 8) (j := x + 16) (k := x + 9) (by omega) (by omega) (by omega),
      show x + 9 - (x + 8) = 1 by omega]
  rw [e10, ← hgeo]
  refine mem_usup_geo_of_commute c hc8 hx₀U fun z hz => ?_
  by_contra hzx
  have hzs : z ∈ stab (puAmalgam h.le) (p (x + 8)) := zm_le_stab_of_isCritical _ h20 c.bpos hc8 hz
  have htz : t * z = z * t :=
    Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hM16 hz) t ht
  have htz' : t * z⁻¹ = z⁻¹ * t := by
    calc t * z⁻¹ = z⁻¹ * (z * t) * z⁻¹ := by group
      _ = z⁻¹ * (t * z) * z⁻¹ := by rw [htz]
      _ = z⁻¹ * t := by group
  have hs' : z * s * z⁻¹ ∈ Qv (puAmalgam h.le) (p (x + 8)) :=
    (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_qv _ _ hzs) s).mp hs
  have hr : ⁅z, zα⁆ ∈ Uloc h.le L (p (x + 8)) :=
    c.critR_le_uloc hc8 (by
      rw [critR, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hz hzα)
  have hrZ : ⁅z, zα⁆ ∈ ZM (puAmalgam h.le) (p (x + 8)) := uloc_le_zm h c.full hM8 hr
  have hzd : z * d * z⁻¹ = ⁅z, zα⁆ * d := by
    rw [← hdeq, commutatorElement_def]
    calc z * (zα * t) * z⁻¹ = z * zα * (t * z⁻¹) := by group
      _ = z * zα * (z⁻¹ * t) := by rw [htz']
      _ = z * zα * z⁻¹ * zα⁻¹ * (zα * t) := by group
  have hrs : ⁅z, zα⁆ * (z * s * z⁻¹) = (z * s * z⁻¹) * ⁅z, zα⁆ :=
    (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hM8 hrZ) _ hs').symm
  have hds : ⁅d, z * s * z⁻¹⁆ ∈ Hloc h.le L (p (x + 6)) := hdH _ (hQ8s hs')
  have hdsZ : ⁅d, z * s * z⁻¹⁆ ∈ ZM (puAmalgam h.le) (p (x + 8)) :=
    uloc_le_zm h c.full hM8 (hHU hds)
  have hrc : ⁅z, zα⁆ * ⁅d, z * s * z⁻¹⁆ = ⁅d, z * s * z⁻¹⁆ * ⁅z, zα⁆ :=
    (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hM8 hrZ) _
      (zm_le_qv_self _ hM8 h.critDist_pos hdsZ)).symm
  have hconj : z * ⁅d, s⁆ * z⁻¹ = ⁅d, z * s * z⁻¹⁆ := by
    have e1 : z * ⁅d, s⁆ * z⁻¹ = ⁅z * d * z⁻¹, z * s * z⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    have e2 : ⁅⁅z, zα⁆ * d, z * s * z⁻¹⁆ =
        ⁅z, zα⁆ * ⁅d, z * s * z⁻¹⁆ * ⁅z, zα⁆⁻¹ * ⁅⁅z, zα⁆, z * s * z⁻¹⁆ := by
      rw [commutatorElement_def (⁅z, zα⁆ * d), commutatorElement_def d,
        commutatorElement_def ⁅z, zα⁆ (z * s * z⁻¹)]
      group
    rw [e1, hzd, e2, (commutatorElement_eq_one_iff_mul_comm).mpr hrs, mul_one, hrc,
      mul_inv_cancel_right]
  have hcH : ⁅z, ⁅d, s⁆⁆ ∈ Hloc h.le L (p (x + 6)) := by
    rw [commutatorElement_def z]
    exact mul_mem (hconj ▸ hds) (inv_mem hx₀H)
  have hcR : ⁅z, ⁅d, s⁆⁆ ∈ critR (puAmalgam h.le) (p (x + 8)) (p (x + 16)) := by
    rw [critR, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hz (uloc_le_zm h c.full hM8 hx₀U)
  have hne1 : ⁅z, ⁅d, s⁆⁆ ≠ 1 := by
    rw [Ne, commutatorElement_eq_one_iff_mul_comm]
    exact fun h' => hzx h'.symm
  have hcardR : Nat.card ↥(critR (puAmalgam h.le) (p (x + 8)) (p (x + 16))) = 2 := by
    have hs10 := c.straight_of_isGoodPath hp (y := x + 8) (hx.add (by decide)) (by omega)
    have hgpd := c.zh_ne_of_isGoodPath hp (y := x + 12) (hx.add (by decide)) (by omega)
      (by omega)
    rw [show x + 12 - 1 = x + 8 + 3 by omega, show x + 12 + 1 = x + 8 + 5 by omega] at hgpd
    have hc8'' : IsCritical (puAmalgam h.le) (p (x + 8)) (p (x + 8 + 8)) := by
      rwa [show x + 8 + 8 = x + 16 by omega]
    have := c.card_critR hp.toIsNBPath (x := x + 8) (by omega) hc8'' hs10 hgpd
    rwa [show x + 8 + 8 = x + 16 by omega, hq] at this
  have hRH : critR (puAmalgam h.le) (p (x + 8)) (p (x + 16)) ≤ Hloc h.le L (p (x + 6)) := by
    intro y hy
    rcases eq_one_or_eq_of_card_two hcardR hcR hne1 hy with rfl | rfl
    · exact one_mem _
    · exact hcH
  have hpe := c.not_zm_le_normalizer_rev hp (j := x + 8) (hx.add (by decide)) (by omega)
    (by omega)
  rw [show x + 8 + 8 = x + 16 by omega, show x + 8 - 1 = x + 7 by omega,
    ← c.hloc_eq_usup' hp hx h4 (by omega), Subgroup.le_normalizer_iff_commutator_le_right] at hpe
  apply hpe
  refine le_trans ?_ hRH
  rw [critR, Subgroup.commutator_comm]
  exact Subgroup.commutator_mono (hHU.trans (uloc_le_zm h c.full hM8)) le_rfl

end Ctx

end CFSG.Quasithin.MS93.S45J
