module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Rank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Inputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem c8_rk_eq_mQuot_add {X : Type*} [Group X] [Finite X] {A B : Subgroup X} (hBA : B ≤ A) :
    rk ↥A = E3.mQuot A B + rk ↥B := by
  have h1 := rk_add_rkIdx (B.subgroupOf A)
  have h2 : rk ↥(B.subgroupOf A) = rk ↥B := by
    unfold rk
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv]
  rw [E3.mQuot_eq_rkIdx]
  omega

variable {G : Type} [Group G] [Finite G]

theorem c8_wTil_ne_bot {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) : wTil V₀ V hV L ≠ ⊥ :=
  fun h0 => hL (s15_Lin_eq_bot_of_commSub_top_eq_bot h0)

theorem c8_commSub_wTil {D : Data G} {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) : commSub (wTil V₀ V hV L) (lBar V₀ V hV L) = wTil V₀ V hV L := by
  have h1 := s15_Core_commSub_wTil_conj h D.M.one_mem
  rw [conjSubgroup_one] at h1
  exact h1

theorem c8_wTil_spin (D : Data G) (h1217 : R1217 D) (hA : RSp6SmallMod) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hc : Case167_8 D V₀ V hV L) :
    s15 D.M V₀ V hV L = 1 ∧ rk ↥(wTil V₀ V hV L) = 8 ∧
      IsIrrOn (lBar V₀ V hV L) (wTil V₀ V hV L) ⊥ := by
  have h := hS.setting.hyp151
  have hL := hS.ne_bot
  have hW : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have h8 : s15 D.M V₀ V hV L * gamma15 D.M V₀ V hV L = 8 := by
    rw [← c8_rk_vStar_eq D h1217 h hV hL]
    exact hc.2.1
  have hq := c8_mQuot_wTil_le_gamma15 D h hV
  have hγW := c8_gamma15_le_rk_wTil D h.hyp125 hV L
  have hs0 : 0 < s15 D.M V₀ V hV L := by
    rcases Nat.eq_zero_or_pos (s15 D.M V₀ V hV L) with h0 | h0
    · rw [h0, zero_mul] at h8
      exact absurd h8 (by norm_num)
    · exact h0
  have hγ8 : gamma15 D.M V₀ V hV L ≤ 8 :=
    (Nat.le_mul_of_pos_left _ hs0).trans h8.le
  have hsplit := c8_rk_eq_mQuot_add
    (inf_le_left : wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L) ≤ wTil V₀ V hV L)
  rcases hA (Vtil V₀ V hV) hW (lBar V₀ V hV L) (wTil V₀ V hV L) hc.1 (c8_wTil_ne_bot hV hL)
      (c8_commSub_wTil h hV) (hq.trans hγ8) with ⟨hrk, hbot, hirr⟩ | ⟨h6, h1⟩
  · rw [hbot, rk_bot, add_zero] at hsplit
    rw [hbot] at hq
    have hγ : gamma15 D.M V₀ V hV L = 8 := by omega
    rw [hγ] at h8
    exact ⟨by omega, hrk, hirr⟩
  · exfalso
    have hγ6 : 6 ≤ gamma15 D.M V₀ V hV L := h6 ▸ hq
    have hγ7 : gamma15 D.M V₀ V hV L ≤ 7 := by omega
    rcases Nat.lt_or_ge (s15 D.M V₀ V hV L) 2 with hs2 | hs2
    · have hs1 : s15 D.M V₀ V hV L = 1 := by omega
      rw [hs1, one_mul] at h8
      omega
    · have := Nat.mul_le_mul_right (gamma15 D.M V₀ V hV L) hs2
      omega

theorem c8_map_conj_lbar_eq (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (L : Subgroup G)
    (hs : s15 M V₀ V hV L = 1) :
    ∀ φ ∈ Mbar M V₀ V hV,
      (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom = lBar V₀ V hV L := by
  intro φ hφ
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 hs
  have h1 : barSub V₀ V hV L ∈ {X : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar M V₀ V hV, X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom} := by
    refine ⟨1, (Mbar M V₀ V hV).one_mem, ?_⟩
    ext x
    simp
  have h2 : (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom ∈
      {X : Subgroup (MulAut (Vtil V₀ V hV)) |
        ∃ φ ∈ Mbar M V₀ V hV, X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom} :=
    ⟨φ, hφ, rfl⟩
  rw [ha] at h1 h2
  exact (Set.mem_singleton_iff.1 h2).trans (Set.mem_singleton_iff.1 h1).symm

theorem c8_wTil_eq_top (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    (hs : s15 D.M V₀ V hV L = 1) : wTil V₀ V hV L = ⊤ := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hN := c8_map_conj_lbar_eq D.M V₀ V hV L hs
  have hterm : ∀ m : D.M, commSub ⊤ (barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))) =
      wTil V₀ V hV L := by
    intro m
    have hm := hMs m.2
    rw [s15_Infra_barSub_conjSubgroup V₀ V h.isElemAbelian hm L]
    have hmem : (actTil V₀ V hV ⟨m, hm⟩)⁻¹ ∈ Mbar D.M V₀ V hV :=
      (Mbar D.M V₀ V hV).inv_mem (actTil_mem_barSub V₀ V hV m.2 hm)
    have h1 : (barSub V₀ V hV L).map (MulAut.conj (actTil V₀ V hV ⟨m, hm⟩)⁻¹).toMonoidHom =
        barSub V₀ V hV L := hN _ hmem
    rw [h1]
    rfl
  have h2 := s15_Two_iSup_commSub_eq_top D h1217 h hL
  rw [iSup_congr hterm, iSup_const] at h2
  exact h2

theorem c8_spin_module (D : Data G) (h1217 : R1217 D) (hA : RSp6SmallMod) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hc : Case167_8 D V₀ V hV L) :
    rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 8 ∧ IsIrrOn (lBar V₀ V hV L) ⊤ ⊥ ∧
      ∀ φ ∈ Mbar D.M V₀ V hV,
        (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom = lBar V₀ V hV L := by
  obtain ⟨hs, hrk, hirr⟩ := c8_wTil_spin D h1217 hA hS hc
  have htop := c8_wTil_eq_top D h1217 hS.setting.hyp151 hV hS.ne_bot hs
  rw [htop] at hrk hirr
  exact ⟨hrk, hirr, c8_map_conj_lbar_eq D.M V₀ V hV L hs⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
