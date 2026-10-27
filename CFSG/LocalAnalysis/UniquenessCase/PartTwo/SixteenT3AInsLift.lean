module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Bar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2LnLift
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGlue
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G42Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Ctx

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s16t_a_insp_of_stable_subgroup (D : Data G) {V : Subgroup G} (h : Hyp125 D ⊥ V)
    {p : ℕ} (hp : p ∈ D.sig) {Ut : Subgroup (Vtil ⊥ V h.isElemAbelian)} (hU1 : Ut ≠ ⊥)
    (hUfix : Ut ≤ fixV (barSub ⊥ V h.isElemAbelian (E3.wClos V D.k D.T)))
    {X : Subgroup G} (hXM : X ≤ D.M) (hXp : IsPGroup p X) (hXc : ¬ IsCyclic X)
    (hstab : StableUnder (barSub ⊥ V h.isElemAbelian X) Ut) : Insp1613U D V := by
  haveI : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
  have hV := h.isElemAbelian
  have hP := h.pairFacts
  have hMst : D.M ≤ stabTil ⊥ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hWT : E3.wClos V D.k D.T ≤ D.T := E3.wClos_le_of_forall fun A hA => hA.1
  have hWst : E3.wClos V D.k D.T ≤ stabTil ⊥ V := hWT.trans (D.sylowM.le.trans hMst)
  refine ⟨preTil ⊥ V hV Ut, ?_, ?_, p, hp, X, ?_, hXp, hXc⟩
  · intro h0
    apply hU1
    have h1 := imgTil_preTil ⊥ V hV Ut
    rw [h0] at h1
    rw [← h1, eq_bot_iff]
    intro q hq
    obtain ⟨x, hx, rfl⟩ := (mem_imgTil ⊥ V hV ⊥ q).1 hq
    rw [Subgroup.mem_bot] at hx ⊢
    have : x = 1 := IntMod.val_injective (by simpa using hx)
    rw [this, map_one]
  · refine le_inf (preTil_le ⊥ V hV Ut) ?_
    intro u hu
    have h1 : u ∈ preTil ⊥ V hV (fixV (barSub ⊥ V hV (E3.wClos V D.k D.T))) :=
      s15_LP_preTil_mono hV hUfix hu
    have h2 := (s15_Glue_mem_preTil_fixV_iff ⊥ V (E3.wClos V D.k D.T) hV hWst
      (preTil_le ⊥ V hV Ut hu)).1 h1
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have h3 := h2 e he
    rw [Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
    exact h3
  · refine le_inf hXM ?_
    intro x hx
    have hxst : x ∈ stabTil ⊥ V := hMst (hXM hx)
    refine s16c1G_mem_normalizer_of_forall_actTil_mem_imgTil hV (preTil_le ⊥ V hV Ut) hxst ?_
    rw [imgTil_preTil]
    exact fun w hw => hstab _ (actTil_mem_barSub ⊥ V hV hx hxst) w hw

theorem s16t_a_insp_of_fixing_lift (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) {V : Subgroup G} (h : Hyp125 D ⊥ V) {p : ℕ} (hp : p ∈ D.sig)
    (hsmall : ¬ p ^ 3 ∣ Nat.card (Mbar D.M ⊥ V h.isElemAbelian))
    {n : Vtil ⊥ V h.isElemAbelian} (hn1 : n ≠ 1)
    (hnfix : n ∈ fixV (barSub ⊥ V h.isElemAbelian (E3.wClos V D.k D.T)))
    {a : MulAut (Vtil ⊥ V h.isElemAbelian)} (ha : a ∈ Mbar D.M ⊥ V h.isElemAbelian)
    (hao : orderOf a = p) (han : a n = n) : Insp1613U D V := by
  classical
  have hV := h.isElemAbelian
  have hpf := h.pairFacts
  have hMn : D.M ≤ normalizer (V : Set G) := hpf.le_normalizer
  have hMst : D.M ≤ stabTil ⊥ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  have hpp : p.Prime := (D.sig_prime p hp).1
  haveI : Fact p.Prime := ⟨hpp⟩
  have hc4 : Nat.card (⊥ : Subgroup G) ≤ 4 := by simp
  have h115 : F11.R115 D := uc22p22q_r115_of D hx h61
  obtain ⟨E, hEel, hE3, hY⟩ := exists_rank_data h115 (Hyp125.hyp11 h127 h) hc4 hp
  have hYker : ∀ Y : Subgroup ↥D.M, IsElemAbelian p Y → Y ≤ (barHom ⊥ V hV hMst).ker →
      Nat.card Y ≤ p := fun Y hYel hYk =>
    hY Y hYel (by rwa [ker_barHom ⊥ V hV hMn hMst] at hYk)
  obtain ⟨k, hk⟩ := hEel.isPGroup.exists_card_eq
  have hk3 : 3 ≤ k := by
    rw [hk] at hE3
    exact (Nat.pow_le_pow_iff_right hpp.one_lt).1 hE3
  obtain ⟨s, rfl⟩ : ∃ s, k = s + 1 := ⟨k - 1, by omega⟩
  have hR : ¬ p ^ (s + 1) ∣ Nat.card (barHom ⊥ V hV hMst).range := by
    rw [range_barHom]
    exact fun hd => hsmall ((pow_dvd_pow p hk3).trans hd)
  obtain ⟨B, hBp, hBc, hB⟩ := exists_noncyclic_pGroup_of_kernel_trick (barHom ⊥ V hV hMst) hpp
    hEel hk hR hYker (y := a) (by rw [range_barHom]; exact ha)
    (by rw [← hao]; exact pow_orderOf_eq_one a)
    (by
      intro h1
      rw [h1, orderOf_one] at hao
      exact hpp.one_lt.ne hao)
  have hnfixk : ∀ j : ℤ, (a ^ j) n = n := by
    intro j
    have hy : a ∈ MulAction.stabilizer (MulAut (Vtil ⊥ V hV)) n := by
      rw [MulAction.mem_stabilizer_iff]
      exact han
    have h2 := (MulAction.stabilizer (MulAut (Vtil ⊥ V hV)) n).zpow_mem hy j
    rwa [MulAction.mem_stabilizer_iff] at h2
  refine s16t_a_insp_of_stable_subgroup D h hp (Ut := Subgroup.zpowers n)
    (Subgroup.zpowers_eq_bot.not.2 hn1) (Subgroup.zpowers_le.2 hnfix)
    (X := B.map D.M.subtype) (Subgroup.map_subtype_le B) (hBp.map D.M.subtype)
    (fun hc => hBc ((MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective B D.M.subtype D.M.subtype_injective)).2 hc)) ?_
  intro xb hxb u hu
  obtain ⟨g, hgX, rfl⟩ := (mem_barSub ⊥ V hV _ xb).1 hxb
  obtain ⟨b, hb, hbg⟩ := Subgroup.mem_map.1 hgX
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hB b hb)
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
  have hact : actTil ⊥ V hV g = barHom ⊥ V hV hMst b := by
    have hg : g = ⟨(b : G), hMst b.2⟩ := Subtype.ext hbg.symm
    rw [hg]
    rfl
  rw [hact, ← hj]
  have h3 : (a ^ j) (n ^ i) = (a ^ j) n ^ i := map_zpow (a ^ j) n i
  rw [h3, hnfixk j]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers n) i

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
