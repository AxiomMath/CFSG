module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Eseven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3SixteenOrd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AInsLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AInsNorm
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAAux
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Norm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16t_a_ieor_of_card {p n : ℕ} [hp : Fact p.Prime] {W : Type} [Group W] [Finite W]
    (hcomm : ∀ a b : W, a * b = b * a) (hpow : ∀ a : W, a ^ p = 1)
    (hcard : Nat.card W = p ^ n) : IsElemAbelianOfRank p n W := by
  let _ : CommGroup W := { (inferInstance : Group W) with mul_comm := hcomm }
  let _ : Module (ZMod p) (Additive W) := AddCommGroup.zmodModule (n := p) fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, hpow, ofMul_one]
  have hF : Module.Finite (ZMod p) (Additive W) := Module.Finite.of_finite
  have hFr : Module.Free (ZMod p) (Additive W) := Module.Free.of_divisionRing _ _
  have h := @Module.natCard_eq_pow_finrank (ZMod p) (Additive W) _ _ _ hF
  have hfin : Module.finrank (ZMod p) (Additive W) =
      Module.finrank (ZMod p) (Fin n → ZMod p) := by
    rw [Nat.card_zmod] at h
    rw [Module.finrank_fin_fun]
    exact Nat.pow_right_injective hp.out.two_le (h.symm.trans hcard)
  exact ⟨AddEquiv.toMultiplicativeRight
    (@LinearEquiv.ofFinrankEq (ZMod p) (Additive W) (Fin n → ZMod p) _ _ _ hFr _ _ _ _ hF _
      hfin).toAddEquiv⟩

theorem s16t_a_case168_4_two_three_small (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) {V L : Subgroup G} {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV)
    (hL : IsElemAbelianOfRank 3 2 ↥(lBar ⊥ V hV L))
    (hS : SymSumOfConj (Mbar D.M ⊥ V hV) (⊤ : Subgroup (Vtil ⊥ V hV)) 2 (dParam 3))
    (h3σ : 3 ∈ D.sig) (hsmall : ¬ 3 ^ 3 ∣ Nat.card (Mbar D.M ⊥ V hV)) : Insp1613U D V := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h125 : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  have hcore := s16n9b_case4_pcore D hV hc (by norm_num : Nat.Prime 3) (by norm_num : 1 < 2) hL
  obtain ⟨ι, hι, Y, hind, hinj, hsup, hcard, hrk, hperm, hsurj⟩ := s16n9b_case4_data hS
  letI := hι
  have hLM : lBar ⊥ V hV L ≤ Mbar D.M ⊥ V hV := barSub_mono ⊥ V hV hc.setting.hyp151.le
  have hLcard : Nat.card ↥(lBar ⊥ V hV L) = 9 := by
    rw [s16c167_card_isElemAbelianOfRank hL]
    norm_num
  have hNp : IsPGroup 3 ↥(pCoreOf 3 (Mbar D.M ⊥ V hV)) :=
    (CFSG.pCore_isPGroup (p := 3) (G := ↥(Mbar D.M ⊥ V hV))).map (Mbar D.M ⊥ V hV).subtype
  have hNM : pCoreOf 3 (Mbar D.M ⊥ V hV) ≤ Mbar D.M ⊥ V hV := Subgroup.map_subtype_le _
  have hNcard : Nat.card ↥(pCoreOf 3 (Mbar D.M ⊥ V hV)) ≤ 9 := by
    obtain ⟨k, hk⟩ := hNp.exists_card_eq
    have hdvd : Nat.card ↥(pCoreOf 3 (Mbar D.M ⊥ V hV)) ∣ Nat.card (Mbar D.M ⊥ V hV) :=
      Subgroup.card_dvd_of_le hNM
    by_contra hlt
    push Not at hlt
    have hk3 : 3 ≤ k := by
      by_contra hk'
      push Not at hk'
      interval_cases k <;> omega
    exact hsmall ((pow_dvd_pow 3 hk3).trans (hk ▸ hdvd))
  have hΛN : lBar ⊥ V hV L = pCoreOf 3 (Mbar D.M ⊥ V hV) :=
    Subgroup.eq_of_le_of_card_ge hcore (by rw [hLcard]; exact hNcard)
  have hBΛ : ∀ b ∈ barSub ⊥ V hV (E3.wClos V D.k D.T), ∀ f ∈ lBar ⊥ V hV L,
      b * f * b⁻¹ ∈ lBar ⊥ V hV L := by
    intro b hb f hf
    have hbM : b ∈ Mbar D.M ⊥ V hV := s16c13bcA_wBar_le_mbar D hV hb
    rw [hΛN] at hf ⊢
    obtain ⟨f', hf', rfl⟩ := Subgroup.mem_map.1 hf
    refine Subgroup.mem_map.2 ⟨⟨b, hbM⟩ * f' * ⟨b, hbM⟩⁻¹, ?_, rfl⟩
    exact (CFSG.pCore_normal (p := 3) (G := ↥(Mbar D.M ⊥ V hV))).conj_mem f' hf' ⟨b, hbM⟩
  have hmove : ∃ f ∈ lBar ⊥ V hV L, ∃ i, (Y i).map f.toMonoidHom ≠ Y i := by
    by_contra hno
    push Not at hno
    have h27 := s16t_a_dvd_card_of_fixing (by rw [hcard]) hinj hperm hsurj hLM
      (by rw [hLcard]) hno
    exact hsmall (by norm_num; exact h27)
  have hY : ∀ i, Y i ≠ ⊥ := by
    intro i h0
    have h1 := hrk i
    rw [h0, rk_bot, s16c1610_dParam_three] at h1
    omega
  obtain ⟨a, haΛ, hao, n, hn1, han, hBn⟩ := s16t_a_exists_fixed_of_norm
    (s15_Infra_vtil_sq_eq_one ⊥ V hV) (by rw [hcard]) hinj hind hY hL
    (s16c13bcA_wBar_isPGroup D hV) (fun f hf i => hperm f (hLM hf) i)
    (fun b hb i => hperm b (s16c13bcA_wBar_le_mbar D hV hb) i) hBΛ hmove
  exact s16t_a_insp_of_fixing_lift D hx h61 h127 h125 h3σ hsmall hn1 (mem_fixV.2 hBn)
    (hLM haΛ) hao han

theorem s16t_a_case168_4_two_three_norm (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) {V : Subgroup G} (h : Hyp125 D ⊥ V) (h3σ : 3 ∈ D.sig)
    (hrank : ¬ 3 ≤ CFSG.Open.pRank 3 (Mbar D.M ⊥ V h.isElemAbelian))
    {ι : Type} [Fintype ι] {Y : ι → Subgroup (Vtil ⊥ V h.isElemAbelian)}
    (hinj : Function.Injective Y) (hind : iSupIndep Y) (hcard : Fintype.card ι = 3)
    (hY : ∀ i, Y i ≠ ⊥)
    (hperm : ∀ g ∈ Mbar D.M ⊥ V h.isElemAbelian, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j)
    {E : Subgroup G} (hEM : E ≤ D.M) (hEel : IsElemAbelian 3 E) (hEc : 3 ^ 3 ≤ Nat.card E)
    (hmove : ∃ b ∈ barSub ⊥ V h.isElemAbelian E, ∃ i, (Y i).map b.toMonoidHom ≠ Y i)
    (hnorm : ∀ w ∈ barSub ⊥ V h.isElemAbelian (E3.wClos V D.k D.T),
      ∀ f ∈ barSub ⊥ V h.isElemAbelian E, w * f * w⁻¹ ∈ barSub ⊥ V h.isElemAbelian E) :
    Insp1613U D V := by
  classical
  have hV := h.isElemAbelian
  have hpf := h.pairFacts
  have hMn : D.M ≤ normalizer (V : Set G) := hpf.le_normalizer
  have hMst : D.M ≤ stabTil ⊥ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  have hEst : E ≤ stabTil ⊥ V := hEM.trans hMst
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hc4 : Nat.card (⊥ : Subgroup G) ≤ 4 := by simp
  have h115 : F11.R115 D := uc22p22q_r115_of D hx h61
  obtain ⟨-, -, -, hY'⟩ := exists_rank_data h115 (Hyp125.hyp11 h127 h) hc4 h3σ
  have hYker : ∀ Y' : Subgroup ↥D.M, IsElemAbelian 3 Y' → Y' ≤ (barHom ⊥ V hV hMst).ker →
      Nat.card Y' ≤ 3 := fun Y' hYel hYk =>
    hY' Y' hYel (by rwa [ker_barHom ⊥ V hV hMn hMst] at hYk)
  have hΛM : barSub ⊥ V hV E ≤ Mbar D.M ⊥ V hV := barSub_mono ⊥ V hV hEM
  have hΛel : IsElemAbelian 3 (barSub ⊥ V hV E) :=
    (hEel.subgroupOf (stabTil ⊥ V)).map (actTil ⊥ V hV)
  have hE₀E : preBarSub E ⊥ V hV ⊥ ≤ E := inf_le_left
  have hE₀M : preBarSub E ⊥ V hV ⊥ ≤ D.M := hE₀E.trans hEM
  have hE₀card : Nat.card (preBarSub E ⊥ V hV ⊥) ≤ 3 := by
    have hel : IsElemAbelian 3 ((preBarSub E ⊥ V hV ⊥).subgroupOf D.M) :=
      (hEel.mono hE₀E).subgroupOf D.M
    have hker : (preBarSub E ⊥ V hV ⊥).subgroupOf D.M ≤ (barHom ⊥ V hV hMst).ker := by
      intro x hx'
      obtain ⟨-, hst, hx1⟩ := (mem_preBarSub E ⊥ V hV ⊥).1 (Subgroup.mem_subgroupOf.1 hx')
      rw [MonoidHom.mem_ker]
      have : barHom ⊥ V hV hMst x = actTil ⊥ V hV ⟨(x : G), hst⟩ := rfl
      rw [this]
      exact Subgroup.mem_bot.1 hx1
    have h3 := hYker _ hel hker
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀M).toEquiv] at h3
  have hid := s16c7_card_mul_card_preBarSub hV hEst (Q := ⊥) bot_le
  rw [Subgroup.card_bot, mul_one] at hid
  have hΛge : 9 ≤ Nat.card (barSub ⊥ V hV E) := by
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card (preBarSub E ⊥ V hV ⊥) * Nat.card (barSub ⊥ V hV E) ≤ 3 * 8 :=
      Nat.mul_le_mul hE₀card (by omega)
    omega
  obtain ⟨k, hk⟩ := hΛel.isPGroup.exists_card_eq
  have hk_le : k ≤ CFSG.Open.pRank 3 (Mbar D.M ⊥ V hV) :=
    UC6S846.le_pRank' (by norm_num) hΛM hΛel hk
  have hk2 : k ≤ 2 := by
    by_contra hcon
    exact hrank (le_trans (by omega) hk_le)
  have hk2' : k = 2 := by
    by_contra hne
    have hk1 : k ≤ 1 := by omega
    have hle : 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
    omega
  have hΛ9 : Nat.card (barSub ⊥ V hV E) = 9 := by
    rw [hk, hk2']
    norm_num
  have hΛ : IsElemAbelianOfRank 3 2 ↥(barSub ⊥ V hV E) :=
    s16t_a_ieor_of_card (fun a b => hΛel.1.is_comm.comm a b)
      (fun a => Subtype.ext (by simpa using hΛel.2 a a.2)) (by rw [hΛ9]; norm_num)
  obtain ⟨a, haΛ, hao, n, hn1, han, hBn⟩ := s16t_a_exists_fixed_of_norm
    (s15_Infra_vtil_sq_eq_one ⊥ V hV) hcard hinj hind hY hΛ (s16c13bcA_wBar_isPGroup D hV)
    (fun f hf i => hperm f (hΛM hf) i)
    (fun b hb i => hperm b (s16c13bcA_wBar_le_mbar D hV hb) i) hnorm hmove
  have hnfix : n ∈ fixV (barSub ⊥ V hV (E3.wClos V D.k D.T)) := mem_fixV.2 hBn
  have hnfixk : ∀ j : ℤ, (a ^ j) n = n := by
    intro j
    have hy : a ∈ MulAction.stabilizer (MulAut (Vtil ⊥ V hV)) n := by
      rw [MulAction.mem_stabilizer_iff]
      exact han
    have h2 := (MulAction.stabilizer (MulAut (Vtil ⊥ V hV)) n).zpow_mem hy j
    rwa [MulAction.mem_stabilizer_iff] at h2
  have hzΛ : Subgroup.zpowers a ≤ barSub ⊥ V hV E := Subgroup.zpowers_le.2 haΛ
  have hid2 := s16c7_card_mul_card_preBarSub hV hEst hzΛ
  rw [Nat.card_zpowers, hao, hΛ9] at hid2
  have hXE : preBarSub E ⊥ V hV (Subgroup.zpowers a) ≤ E := inf_le_left
  have hXcard : 9 ≤ Nat.card (preBarSub E ⊥ V hV (Subgroup.zpowers a)) := by
    have h3 : 3 ^ 3 * 3 ≤ Nat.card (preBarSub E ⊥ V hV (Subgroup.zpowers a)) * 9 := by
      rw [← hid2]
      exact Nat.mul_le_mul_right 3 hEc
    omega
  refine s16t_a_insp_of_stable_subgroup D h h3σ (Ut := Subgroup.zpowers n)
    (Subgroup.zpowers_eq_bot.not.2 hn1) (Subgroup.zpowers_le.2 hnfix)
    (X := preBarSub E ⊥ V hV (Subgroup.zpowers a)) (hXE.trans hEM)
    (fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hEel.2 x (hXE x.2))⟩)
    (s16c7_not_isCyclic_of_elemAbelian (by norm_num) (hEel.mono hXE)
      (by norm_num; exact hXcard)) ?_
  intro xb hxb u hu
  obtain ⟨g, hgX, rfl⟩ := (mem_barSub ⊥ V hV _ xb).1 hxb
  obtain ⟨-, hgst, hgz⟩ := (mem_preBarSub E ⊥ V hV _).1 hgX
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hgz
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
  have hact : actTil ⊥ V hV g = a ^ j := by
    have hg : g = ⟨(g : G), hgst⟩ := Subtype.ext rfl
    rw [hg]
    exact hj.symm
  rw [hact]
  have h3 : (a ^ j) (n ^ i) = (a ^ j) n ^ i := map_zpow (a ^ j) n i
  rw [h3, hnfixk j]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers n) i

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
