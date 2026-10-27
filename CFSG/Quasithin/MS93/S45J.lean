module

public import CFSG.Quasithin.MS93.S45JK
public import CFSG.Quasithin.MS93.S45Inputs

public section

namespace CFSG.Quasithin.MS93.S45J

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93.S45
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

variable {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem hloc_inf_hloc (hp : IsGoodPath _ p N) {x : ℕ} (hx : Even x) (h4 : 4 ≤ x)
    (hxN : x + 16 ≤ N) :
    Hloc c.hyp.le L (p (x + 6)) ⊓ Hloc c.hyp.le L (p (x + 10)) =
        Usup (puAmalgam c.hyp.le) (p (x + 8)) (p (x + 7)) ⊓ Usup _ (p (x + 8)) (p (x + 9)) ∧
      Nat.card ↥(Hloc c.hyp.le L (p (x + 6)) ⊓ Hloc c.hyp.le L (p (x + 10))) =
        Fintype.card F := by
  have h := c.hyp
  have hM8 := c.isMVtx_of_isGoodPath hp (k := x + 8) (by omega) (hx.add (by decide))
  have e6 := c.hloc_eq_usup' hp hx h4 (by omega)
  have e10 : Hloc h.le L (p (x + 10)) = Usup _ (p (x + 8)) (p (x + 9)) := by
    have := c.hloc_eq_usup hp (x := x + 4) (hx.add (by decide)) (by omega) (by omega)
    rwa [show x + 4 + 6 = x + 10 by omega, show x + 4 + 4 = x + 8 by omega,
      show x + 4 + 5 = x + 9 by omega] at this
  have e : Hloc h.le L (p (x + 6)) ⊓ Hloc h.le L (p (x + 10)) =
      Usup (puAmalgam h.le) (p (x + 8)) (p (x + 7)) ⊓ Usup _ (p (x + 8)) (p (x + 9)) := by
    rw [e6, e10]
  refine ⟨e, ?_⟩
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h c.via hM8
  have ha7 : (puAmalgam h.le).treeGraph.Adj (p (x + 8)) (p (x + 7)) :=
    (hp.adj (x + 7) (by omega)).symm
  have ha9 : (puAmalgam h.le).treeGraph.Adj (p (x + 8)) (p (x + 9)) := hp.adj (x + 8) (by omega)
  have hne : Usup (puAmalgam h.le) (p (x + 8)) (p (x + 7)) ≠ Usup _ (p (x + 8)) (p (x + 9)) := by
    intro heq
    have hz := c.zh_ne_of_isGoodPath hp (y := x + 8) (hx.add (by decide)) (by omega) (by omega)
    rw [show x + 8 - 1 = x + 7 by omega, show x + 8 + 1 = x + 9 by omega] at hz
    exact hz ((c.usup_eq_iff_zh_eq hψ hM8 ha7 ha9).mp heq)
  rw [e]
  exact c.card_usup_inf_usup hψ hM8 ha7 ha9 hne

theorem exists_isGoodPath_hloc_inf_ne (hp : IsGoodPath _ p N) {x : ℕ} (hx : Even x) (h4 : 4 ≤ x)
    (hxN : x + 16 ≤ N) :
    ∃ p' : ℕ → Vtx (puAmalgam c.hyp.le), IsGoodPath _ p' (x + 22) ∧
      (∀ i, i ≤ x + 8 → p' i = p i) ∧
      Hloc c.hyp.le L (p (x + 6)) ⊓ Hloc c.hyp.le L (p (x + 10)) ≠
        Hloc c.hyp.le L (p (x + 6)) ⊓ Hloc c.hyp.le L (p' (x + 10)) := by
  have h := c.hyp
  obtain ⟨γ', hγa, hγZ, hγne⟩ :=
    c.exists_adj_branch hp (y := x + 8) (hx.add (by decide)) (by omega) (by omega)
  obtain ⟨p₁, hp₁e, hp₁, hU1⟩ := (hp.mono (show x + 8 ≤ N by omega)).extend_of h c.b8 c.c444
    (by omega) (hx.add (by decide)) hγa hγZ
  obtain ⟨p', hp'e, hp'⟩ := c.exists_extend hp₁ (by omega) ((hx.add (by decide)).add even_two) 6
  have hpp' : ∀ i, i ≤ x + 8 → p' i = p i := fun i hi => (hp'e i (by omega)).trans (hp₁e i hi)
  have hU' : Usup (puAmalgam h.le) (p (x + 8)) (p' (x + 9)) = Usup _ (p (x + 8)) γ' := by
    rw [hp'e (x + 9) (by omega)]; exact hU1
  refine ⟨p', hp', hpp', ?_⟩
  obtain ⟨eA, -⟩ := hloc_inf_hloc c hp hx h4 (by omega)
  obtain ⟨eB, -⟩ := hloc_inf_hloc c hp' hx h4 (by omega)
  rw [hpp' (x + 6) (by omega), hpp' (x + 7) (by omega), hpp' (x + 8) le_rfl, hU'] at eB
  rw [eA, eB]
  intro heq
  apply hγne
  rw [show x + 8 - 1 = x + 7 by omega, show x + 8 + 1 = x + 9 by omega,
    inf_comm (Usup _ _ γ'), inf_comm (Usup _ _ (p (x + 9)))]
  exact heq.symm

theorem zm_le_vhat_of_two_of_le (hq : Fintype.card F = 2) (hp : IsGoodPath _ p N) {x : ℕ}
    (hx : Even x) (h4 : 4 ≤ x) (hxN : x + 22 ≤ N) :
    ZM (puAmalgam c.hyp.le) (p (x + 8)) ≤ Vcirc c.hyp.le L (p (x + 6)) ⊔ ZM _ (p (x + 6)) := by
  have h := c.hyp
  have h20 := h.hyp20
  have hM8 := c.isMVtx_of_isGoodPath hp (k := x + 8) (by omega) (hx.add (by decide))
  by_contra hne
  obtain ⟨p', hp', hpp', hAB⟩ := exists_isGoodPath_hloc_inf_ne c hp hx h4 (by omega)
  have e6 : p' (x + 6) = p (x + 6) := hpp' (x + 6) (by omega)
  have e8 : p' (x + 8) = p (x + 8) := hpp' (x + 8) le_rfl
  have hne' : ¬ ZM (puAmalgam h.le) (p' (x + 8)) ≤
      Vcirc h.le L (p' (x + 6)) ⊔ ZM _ (p' (x + 6)) := by
    rwa [e8, e6]
  obtain ⟨-, hcA⟩ := hloc_inf_hloc c hp hx h4 (by omega)
  obtain ⟨-, hcB⟩ := hloc_inf_hloc c hp' hx h4 (by omega)
  rw [e6] at hcB
  rw [hq] at hcA hcB
  apply hne
  intro z hz
  obtain ⟨w, hw, d, hdB, z₁, hz₁, rfl, hdL, hdH⟩ := exists_decomp c hp hx h4 (by omega) hz
  have hK1 := commutator_mem_hloc c hq hp hx h4 hxN hne hdB hdL hdH
  have hK2 := commutator_mem_hloc c hq hp' hx h4 le_rfl hne' (by rwa [e6])
    (by rwa [e6]) (by rwa [e6])
  rw [e8] at hK2
  have hQ8s : Qv (puAmalgam h.le) (p (x + 8)) ≤ stab _ (p (x + 6)) :=
    (qv_le_qv _ h20 hM8 (hp.adj (x + 7) (by omega)).symm).trans
      (qv_le_stab_of_adj _ (hp.adj (x + 6) (by omega)).symm)
  have hdc : ∀ s ∈ Qv (puAmalgam h.le) (p (x + 8)), ⁅d, s⁆ = 1 := fun s hs =>
    eq_one_of_mem_of_card_two hcA hcB hAB ⟨hdH s (hQ8s hs), hK1 s hs⟩
      ⟨hdH s (hQ8s hs), hK2 s hs⟩
  have hdV : d ∈ Vv (puAmalgam h.le) (p (x + 6)) := bloc_le_vv h _ hdB
  have hdα : d ∈ ZM (puAmalgam h.le) (p (x + 8)) := by
    have hE := isElemAbelian_vi _ h20 h.critDist_pos (δ := p (x + 6)) (i := 2)
      (by rw [c.b8]; norm_num)
    rw [← xm_eq_zm h c.full hM8, XM]
    refine mem_omegaOneCenterOf (vi_le_qv _ (by
      rw [hp.dist_eq' (i := x + 6) (j := x + 8) (by omega) (by omega), c.b8]; omega) hdV)
      (fun y hy => ?_) (hE.2 d hdV)
    have := hdc y hy
    rw [commutatorElement_eq_one_iff_commute] at this
    exact this.symm.eq
  have hdγ : d ∈ ZM (puAmalgam h.le) (p (x + 6)) :=
    c.zm_inf_bloc_le hp hx h4 (by omega) ⟨hdα, hdB⟩
  exact mul_mem hw (mul_mem (Subgroup.mem_sup_right hdγ) (Subgroup.mem_sup_right hz₁))

theorem zm_le_vhat_of_two (hq : Fintype.card F = 2) (hp : IsGoodPath _ p N) {x : ℕ}
    (hx : Even x) (h4 : 4 ≤ x) (hxN : x + 14 ≤ N) :
    ZM (puAmalgam c.hyp.le) (p (x + 8)) ≤ Vcirc c.hyp.le L (p (x + 6)) ⊔ ZM _ (p (x + 6)) := by
  obtain ⟨p₁, hp₁e, hp₁⟩ := c.exists_extend (hp.mono hxN) (by omega) (hx.add (by decide)) 4
  have key := zm_le_vhat_of_two_of_le c hq hp₁ hx h4 (by omega)
  rwa [hp₁e (x + 8) (by omega), hp₁e (x + 6) (by omega)] at key

theorem hZV : c.HZV := fun _ _ hp _ hx h4 hxN => by
  by_cases hq : Fintype.card F = 2
  · exact zm_le_vhat_of_two c hq hp hx h4 hxN
  · exact c.zm_le_vhat_of_ne_two hp hx h4 hxN hq

end Ctx

theorem s45Q2a_holds : S45.S45Q2a := fun _ _ _ _ _ _ _ _ _ _ c _ => Ctx.hZV c

end CFSG.Quasithin.MS93.S45J
