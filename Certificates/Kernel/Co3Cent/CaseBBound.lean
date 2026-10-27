module

public import Certificates.Kernel.Co3Cent.CaseBCent

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo3Cent

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KC.PGrp CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.PF
  CFSG.KD.Co3Cent Subgroup
open CFSG.KC.Misc.ArrEnum (permB)
open CFSG.Sporadic.Schreier.Co3 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T
open CFSG.Monster.B.Co2 (permOfArr)
open CFSG.RankThree.Native (permsA)

theorem getS_mem {L : List ℕ} {t : ℕ} (ht : t < L.length) : getS L t ∈ L := by
  rw [getS_eq, List.getD_eq_getElem _ _ ht]
  exact List.getElem_mem ht

theorem card_filter_list {L : List ℕ} (hL : L.Nodup) (hlt : ∀ y ∈ L, y < 276) (P : ℕ → Bool) :
    (Finset.univ.filter fun y : Fin 276 => y.val ∈ L ∧ P y.val = true).card = (L.filter P).length := by
  rw [← List.toFinset_card_of_nodup (hL.filter P)]
  refine Finset.card_bij (fun y _ => y.val) (fun y hy => ?_) (fun y _ z _ he => Fin.ext he)
    (fun q hq => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rw [List.mem_toFinset, List.mem_filter]
    exact hy
  · rw [List.mem_toFinset, List.mem_filter] at hq
    exact ⟨⟨q, hlt q hq.1⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hq, rfl⟩

theorem card_le_list (L : List ℕ) :
    (Finset.univ.filter fun y : Fin 276 => y.val ∈ L).card ≤ L.length := by
  refine le_trans ?_ (List.toFinset_card_le L)
  refine Finset.card_le_card_of_injOn (fun y => y.val) (fun y hy => ?_) (fun y _ z _ he => Fin.ext he)
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hy
  simpa using hy

@[expose] noncomputable def FBs : Finset (Fin 276) :=
  Finset.univ.filter fun y => y.val ∈ BB.take 15

theorem nodupF : (BB.take 15).Nodup := by decide +kernel

theorem ltF : ∀ y ∈ BB.take 15, y < 276 := by decide +kernel

theorem mem_FBs {y : Fin 276} : y ∈ FBs ↔ y ∈ Set.range FB := by
  rw [FBs, Finset.mem_filter, take15, List.mem_ofFn]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, Fin.ext ht⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl⟩

theorem fix_iff {y : Fin 276} : xB y = y ↔ y ∈ FBs := by rw [mem_FBs, fixB]

theorem perm_F {g : Equiv.Perm (Fin 276)} (hg : g ∈ CB) : ∀ r, g r ∈ FBs ↔ r ∈ FBs := by
  have hc : ∀ h ∈ CB, ∀ r, xB r = r → xB (h r) = h r := by
    intro h hh r hr
    have e := congrArg (fun σ : Equiv.Perm (Fin 276) => σ r) (mem_CB.1 hh).1
    simp only [Equiv.Perm.mul_apply, hr] at e
    exact e.symm
  intro r
  rw [← fix_iff, ← fix_iff]
  constructor
  · intro h
    have := hc g⁻¹ (CB.inv_mem hg) _ h
    simpa using this
  · exact hc g hg r

theorem bB_mem {t : ℕ} (ht : t < 15) : bB t ∈ FBs := mem_FBs.2 ⟨⟨t, ht⟩, rfl⟩

@[expose] noncomputable def DelB (i : ℕ) : Finset (Fin 276) := ptsD (getS CFSG.KD.Co3Cent.DB i)

theorem orbB : ∀ i < 17, (DelB i).card = getS KB i ∧
    ∀ x ∈ DelB i, ∃ g ∈ Gv SB MB 14 i, g (bB i) = x :=
  orbD hBB (permS sFacts.2.1) ch17370_tB

theorem GB_eq {i : ℕ} (hi : i ≤ 17) :
    Gv SB MB 14 i = stabB co3P bB i := (chainB i hi).1

theorem img_Del {i : ℕ} (hi : i < 17) :
    ∀ g ∈ Gv SB MB 14 i, g (bB i) ∈ DelB i := by
  refine CFSG.KC.Co3Cent.mem_of_tight _ (bB i) _ (orbB i hi).2 (Gv SB MB 14 (i + 1)) (fun g hg => ?_) ?_
  · rw [GB_eq (by omega)] at hg
    rw [GB_eq hi.le]
    exact ⟨⟨hg.1, fun t ht => hg.2 t (by omega)⟩, hg.2 i (by omega)⟩
  · rw [(chainB i hi.le).2, (chainB (i + 1) (by omega)).2, (orbB i hi).1,
      Finset.prod_eq_prod_Ico_succ_bot hi]

theorem Del_inv {i : ℕ} (hi : i < 17)
    {h : Equiv.Perm (Fin 276)} (hh : h ∈ Gv SB MB 14 i) : ∀ y, h y ∈ DelB i ↔ y ∈ DelB i := by
  have key : ∀ k ∈ Gv SB MB 14 i, ∀ y ∈ DelB i, k y ∈ DelB i := by
    intro k hk y hy
    obtain ⟨g, hg, rfl⟩ := (orbB i hi).2 y hy
    rw [← Equiv.Perm.mul_apply]
    exact img_Del hi _ (mul_mem hk hg)
  intro y
  refine ⟨fun h1 => ?_, key h hh y⟩
  have := key h⁻¹ (inv_mem hh) _ h1
  simpa using this

theorem stab_CB_le {i : ℕ}
    (hi : i ≤ 17) {g : Equiv.Perm (Fin 276)} (hg : g ∈ stabB CB bB i) : g ∈ Gv SB MB 14 i := by
  rw [GB_eq hi]
  exact ⟨(mem_CB.1 hg.1).2, hg.2⟩

theorem img_cap {i : ℕ} (hi : i < 15)
    {g : Equiv.Perm (Fin 276)} (hg : g ∈ stabB CB bB i) : g (bB i) ∈ FBs ∩ DelB i :=
  Finset.mem_inter.2 ⟨(perm_F hg.1 _).2 (bB_mem hi), img_Del (by omega) g (stab_CB_le (by omega) hg)⟩

theorem capFacts : allN 6 (fun i => capK (getS CFSG.KD.Co3Cent.DB i) (BB.take 15)
    (getS [15, 14, 9, 6, 2, 1] i)) = true := ch17370_cap

theorem card_cap {i : ℕ} (hi : i < 6) : (FBs ∩ DelB i).card = getS [15, 14, 9, 6, 2, 1] i := by
  have h := capK_sound (allN_spec capFacts i hi)
  rw [← h, ← card_filter_list nodupF ltF]
  congr 1
  ext y
  simp [FBs, DelB, ptsD]

@[expose] noncomputable def wvB (wd : List ℕ) : Equiv.Perm (Fin 276) := (wd.map (sv SB)).prod

theorem wvB_prep {lv : ℕ} {wd : List ℕ}
    (h : ∀ j ∈ wd, j < 14 ∧ Nat.beq fld(lv, j, nat_lit 1) (nat_lit 1) = true) :
    PRep 276 9 (posWordK 276 9 (getS SB) wd) (wvB wd) :=
  posWordK_rep (by norm_num) (by norm_num) fun l hl => prep_pv (permS sFacts.2.1 l (h l hl).1)

theorem wvB_mem {i : ℕ} {wd : List ℕ}
    (h : ∀ j ∈ wd, j < 14 ∧ Nat.beq fld(getS MB i, j, nat_lit 1) (nat_lit 1) = true) :
    wvB wd ∈ Gv SB MB 14 i := by
  refine list_prod_mem fun g hg => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
  exact subset_closure ⟨j, lvOk_of_letter (h j hj), rfl⟩

theorem degFacts : allN 14 (fun t => degK 276 9 511 SB 14 (getS MB 1) (getS BB 1)
      (getS CFSG.KD.Co3Cent.DB 2) (BB.take 15) (getS BB (Nat.succ t)) (getS DG t) (getLs UQ t)) =
      true ∧ Nat.beq (lenS DG) 14 = true ∧ Nat.beq (getS DG 0) 9 = true ∧
    Nat.beq (cntK DG (fun d => Nat.beq d 9)) 12 = true := by
  have h := ch17370_deg
  simp only [bAnd_iff] at h
  exact h

@[expose] noncomputable def uq (t : ℕ) : Equiv.Perm (Fin 276) := wvB (getLs UQ t)

theorem uq_facts {t : ℕ} (ht : t < 14) : uq t ∈ Gv SB MB 14 1 ∧ uq t (bB 1) = bB (t + 1) ∧
    (FBs.filter fun r => (uq t)⁻¹ r ∈ DelB 2).card = getS DG t := by
  obtain ⟨hl, hb, hp, hc⟩ := degK_sound (allN_spec degFacts.1 t ht)
  have hpr := wvB_prep hl
  have hinv := prep_inv hp hpr
  refine ⟨wvB_mem hl, Fin.ext ?_, ?_⟩
  · have e : pg 9 (mask 9) (posWordK 276 9 (getS SB) (getLs UQ t)) (getS BB 1) = getS BB (t + 1) := hb
    change ((uq t) (bB 1) : ℕ) = getS BB (t + 1)
    rw [← e]
    exact (hpr (bB 1)).symm
  · rw [← hc, ← card_filter_list nodupF ltF]
    congr 1
    ext y
    have e : ((uq t)⁻¹ y : ℕ) =
        pg 9 511 (CFSG.KS.pinvS 276 9 511 (posWordK 276 9 (getS SB) (getLs UQ t))) y :=
      (hinv y).symm
    simp only [FBs, DelB, ptsD, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [e]

@[expose] noncomputable def Q1 : List ℕ :=
  ((List.range 14).filter fun t => Nat.beq (getS DG t) 9).map fun t => getS BB (t + 1)

theorem Q1_len : Q1.length = 12 := by decide +kernel

theorem b01 : getS BB 0 ≠ getS BB 1 := by decide +kernel

theorem lvl1
    {g : Equiv.Perm (Fin 276)} (hg : g ∈ stabB CB bB 1) : (g (bB 1)).val ∈ Q1 := by
  obtain ⟨s, hs⟩ := mem_FBs.1 ((perm_F hg.1 _).2 (bB_mem (t := 1) (by norm_num)))
  have hs0 : s.val ≠ 0 := by
    intro h0
    have e1 : FB s = bB 0 := by
      change bB s.val = bB 0
      rw [h0]
    have e2 : g (bB 0) = bB 0 := hg.2 0 (by norm_num)
    rw [e1, ← e2] at hs
    exact b01 (congrArg Fin.val (g.injective hs))
  set t := s.val - 1 with ht
  have ht14 : t < 14 := by omega
  have hst : s.val = t + 1 := by omega
  have hgb : g (bB 1) = bB (t + 1) := by
    rw [← hs]
    change bB s.val = bB (t + 1)
    rw [hst]
  obtain ⟨hu1, hu2, hu3⟩ := uq_facts ht14
  obtain ⟨hv1, hv2, hv3⟩ := uq_facts (t := 0) (by norm_num)
  have hgP : g ∈ co3P := (mem_CB.1 hg.1).2
  have hu1' := hu1
  have hv1' := hv1
  rw [GB_eq (by norm_num)] at hu1' hv1'
  have hh : (uq t)⁻¹ * g * uq 0 ∈ Gv SB MB 14 2 := by
    rw [GB_eq (by norm_num)]
    refine ⟨co3P.mul_mem (co3P.mul_mem (co3P.inv_mem hu1'.1) hgP) hv1'.1, fun l hl => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
    · have hl0 : l = 0 := by omega
      subst hl0
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hv1'.2 0 (by norm_num), hg.2 0 (by norm_num),
        Equiv.Perm.inv_eq_iff_eq, hu1'.2 0 (by norm_num)]
    · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hv2, hgb, Equiv.Perm.inv_eq_iff_eq, hu2]
  have hdeg := CFSG.KC.Co3Cent.deg_invariant FBs (fun y => y ∈ DelB 2) g (uq t) (uq 0)
    (perm_F hg.1) (Del_inv (by norm_num) hh)
  rw [hu3, hv3, Nat.eq_of_beq_eq_true degFacts.2.2.1] at hdeg
  rw [hgb]
  exact List.mem_map.2 ⟨t, List.mem_filter.2 ⟨List.mem_range.2 ht14, by rw [hdeg]; rfl⟩, rfl⟩

theorem l4Facts : wordEqK 276 9 SB 14 (getS MB 4) U4 WU4 = true ∧
    Nat.beq (pg 9 511 U4 (getS BB 4)) 162 = true ∧ Nat.beq (maskOf J5) (getS MB 5) = true ∧
    Nat.beq (lenS J5) 3 = true ∧ allN 3 (fun t => Nat.blt (getS J5 t) 14) = true ∧
    orbRecK e5Act (fun e => e) 3 8 255 (pidn 276 9) 12 E5 E5R = true ∧
    Nat.beq (lenS UE) 12 = true ∧
    allN 12 (fun t => Nat.beq (getS UE t) (pcomp 276 9 511 U4 (getS E5 t))) = true ∧
    ncAllK 276 9 511 (pidn 276 9) (fun _ => xBp) 1 UE = true := by
  have h := ch17370_l4
  simp only [bAnd_iff] at h
  exact h

theorem j5_ok : ∀ j < 3, getS J5 j < 14 ∧ (getS MB 5).testBit (getS J5 j) = true := by
  decide +kernel

@[expose] noncomputable def e5g (j : ℕ) : Equiv.Perm (Fin 276) := sv SB (getS J5 j)

@[expose] noncomputable def E5g : Subgroup (Equiv.Perm (Fin 276)) :=
  closure (Set.range fun j : Fin 3 => e5g j)

theorem prepE {j : ℕ} (hj : j < 3) : PRep 276 9 (getS SB (getS J5 j)) (e5g j) :=
  prep_pv (permS sFacts.2.1 _ (j5_ok j hj).1)

theorem E5g_le : E5g ≤ Gv SB MB 14 5 := by
  rw [E5g, closure_le]
  rintro _ ⟨j, rfl⟩
  exact subset_closure ⟨getS J5 j, lvOk_iff.2 (j5_ok j j.2), rfl⟩

theorem recE : E5.length = 12 ∧ (E5.map (fun e => e)).Nodup ∧ (0 < 12 → pidn 276 9 ∈ E5) ∧
    (∀ e ∈ E5, ∀ j < 3, e5Act j e ∈ E5) ∧ ∀ e ∈ E5, ActReach e5Act 3 (pidn 276 9) e :=
  orbRecK_sound l4Facts.2.2.2.2.2.1

theorem reachE : ∀ e, ActReach e5Act 3 (pidn 276 9) e →
    ∃ t ∈ E5g, PRep 276 9 e t ∧ e >>> (276 * 9) = 0 := by
  intro e he
  induction he with
  | root => exact ⟨1, one_mem _, prep_one, pidn_shr (by norm_num) (by norm_num)⟩
  | @step e j _ hj ih =>
    obtain ⟨t, ht, hp, -⟩ := ih
    exact ⟨e5g j * t, mul_mem (subset_closure ⟨⟨j, hj⟩, rfl⟩) ht,
      prep_pcomp (by norm_num) (prepE hj) hp, pcomp_shr _ _ (by norm_num) (by norm_num)⟩

@[expose] noncomputable def EE : Finset (Fin 276 → Fin 276) := (E5.map (decP 276 9)).toFinset

theorem mem_EE {u : Fin 276 → Fin 276} : u ∈ EE ↔ ∃ p ∈ E5, decP 276 9 p = u := by
  rw [EE, List.mem_toFinset, List.mem_map]

theorem EE_root : (fun i => i) ∈ EE :=
  mem_EE.2 ⟨_, recE.2.2.1 (by norm_num), by rw [decP_of_prep prep_one]; rfl⟩

theorem EE_clos : ∀ e ∈ EE, ∀ r ∈ Set.range (fun j : Fin 3 => e5g j), (fun i => r (e i)) ∈ EE := by
  rintro e he _ ⟨j, rfl⟩
  obtain ⟨p, hp, rfl⟩ := mem_EE.1 he
  obtain ⟨t, -, hpr, -⟩ := reachE p (recE.2.2.2.2 p hp)
  refine mem_EE.2 ⟨e5Act j p, recE.2.2.2.1 p hp j j.2, ?_⟩
  have hq : PRep 276 9 (e5Act j p) (e5g j * t) := prep_pcomp (by norm_num) (prepE j.2) hpr
  rw [decP_of_prep hq, decP_of_prep hpr]
  rfl

theorem card_EE : EE.card = 12 := by
  rw [EE, List.toFinset_card_of_nodup, List.length_map, recE.1]
  have hnd : E5.Nodup := by simpa using recE.2.1
  refine hnd.map_on fun p hp q hq he => ?_
  obtain ⟨t, -, hpt, hps⟩ := reachE p (recE.2.2.2.2 p hp)
  obtain ⟨s, -, hqs, hqs'⟩ := reachE q (recE.2.2.2.2 q hq)
  rw [decP_of_prep hpt, decP_of_prep hqs] at he
  have hts : t = s := Equiv.ext (congrFun he)
  rw [hts] at hpt
  exact eq_of_prep (by norm_num) hpt hqs hps hqs'

theorem card_E5g : Nat.card E5g = 12 := by
  have h := key_orbit (K := ⊤) rfl le_top (fun i => i) (fun g _ h => Equiv.ext h) EE EE_root EE_clos
    (by
      intro e he
      obtain ⟨p, hp, rfl⟩ := mem_EE.1 he
      obtain ⟨t, ht, hpr, -⟩ := reachE p (recE.2.2.2.2 p hp)
      exact ⟨t, ht, by rw [decP_of_prep hpr]⟩)
  have h1 : Nat.card E5g = EE.card := h.1
  rw [h1, card_EE]

theorem prodKB5 : ∏ t ∈ Finset.Ico 5 17, getS KB t = 12 := by decide +kernel

theorem rec_G5
    {y : Equiv.Perm (Fin 276)} (hy : y ∈ Gv SB MB 14 5) : ∃ p ∈ E5, PRep 276 9 p y := by
  have hE : E5g = Gv SB MB 14 5 := Subgroup.eq_of_le_of_card_ge E5g_le (by
    rw [card_E5g, (chainB 5 (by norm_num)).2, prodKB5])
  rw [← hE] at hy
  have hTS : E5g ≤ tupStab EE := by
    rw [E5g, closure_le]
    rintro _ ⟨j, rfl⟩ e he
    exact EE_clos e he _ ⟨j, rfl⟩
  obtain ⟨p, hp, hpe⟩ := mem_EE.1 (hTS hy _ EE_root)
  obtain ⟨t', -, hpr, -⟩ := reachE p (recE.2.2.2.2 p hp)
  rw [decP_of_prep hpr] at hpe
  have htt : t' = y := Equiv.ext (congrFun hpe)
  rw [htt] at hpr
  exact ⟨p, hp, hpr⟩

theorem b4_val : getS BB 4 ≠ 162 := by decide +kernel

@[expose] def p162 : Fin 276 := ⟨162, by norm_num⟩

@[expose] noncomputable def u4 : Equiv.Perm (Fin 276) := wvB WU4

theorem u4_facts : PRep 276 9 U4 u4 ∧ u4 ∈ Gv SB MB 14 4 ∧ u4 (bB 4) = p162 := by
  obtain ⟨hl, hx⟩ := wordEqK_sound l4Facts.1
  have hpr : PRep 276 9 U4 u4 := by
    rw [hx]
    exact wvB_prep hl
  refine ⟨hpr, wvB_mem hl, Fin.ext ?_⟩
  have e : pg 9 (mask 9) U4 (getS BB 4) = 162 := Nat.eq_of_beq_eq_true l4Facts.2.1
  rw [← (hpr (bB 4))]
  exact e

theorem lvl4
    {g : Equiv.Perm (Fin 276)} (hg : g ∈ stabB CB bB 4) : g (bB 4) ≠ p162 := by
  intro h162
  obtain ⟨hU, hU4, hUb⟩ := u4_facts
  have hgP : g ∈ co3P := (mem_CB.1 hg.1).2
  have hU4' := hU4
  rw [GB_eq (by norm_num)] at hU4'
  have he : u4⁻¹ * g ∈ Gv SB MB 14 5 := by
    rw [GB_eq (by norm_num)]
    refine ⟨co3P.mul_mem (co3P.inv_mem hU4'.1) hgP, fun l hl => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
    · rw [Equiv.Perm.mul_apply, hg.2 l hl, Equiv.Perm.inv_eq_iff_eq, hU4'.2 l hl]
    · rw [Equiv.Perm.mul_apply, h162, Equiv.Perm.inv_eq_iff_eq, hUb]
  obtain ⟨p, hp, hpe⟩ := rec_G5 he
  obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hp
  have hs12 : s < 12 := by
    have := recE.1
    omega
  have hps : getS E5 s = E5[s] := by
    rw [getS_eq]
    exact List.getD_eq_getElem _ _ hs
  have hUE : getS UE s = pcomp 276 9 511 U4 (getS E5 s) :=
    Nat.eq_of_beq_eq_true (allN_spec l4Facts.2.2.2.2.2.2.2.1 s hs12)
  have hpg : PRep 276 9 (getS UE s) g := by
    have h1 := prep_pcomp (n := 276) (by norm_num) hU hpe
    rw [mul_inv_cancel_left] at h1
    rw [hUE, hps]
    exact h1
  have hlen : UE.length = 12 := by
    have := Nat.eq_of_beq_eq_true l4Facts.2.2.2.2.2.2.1
    rwa [lenS_eq] at this
  have hmem : getS UE s ∈ UE := getS_mem (by rw [hlen]; exact hs12)
  by_cases hid : getS UE s = pidn 276 9
  · rw [hid] at hpg
    have hg1 : g = 1 := CFSG.KC.OrbRow.prep_unique hpg prep_one
    rw [hg1] at h162
    exact b4_val (congrArg Fin.val h162)
  · have hf := ncAllK_sound l4Facts.2.2.2.2.2.2.2.2 _ hmem hid
    have hc : commOK 276 9 (mask 9) (getS UE s) xBp = true :=
      (commOK_iff hpg prepXB).2 (mem_CB.1 hg.1).1
    have hall : allN 1 (fun _ => commOK 276 9 511 (getS UE s) xBp) = true :=
      allN_iff.2 fun _ _ => hc
    rw [hall] at hf
    exact absurd hf (by decide)

theorem p162_mem :
    p162 ∈ FBs ∩ DelB 4 := by
  refine Finset.mem_inter.2 ⟨?_, ?_⟩
  · simp only [FBs, Finset.mem_filter, Finset.mem_univ, true_and, p162]
    decide +kernel
  · rw [← u4_facts.2.2]
    exact img_Del (by norm_num) _ u4_facts.2.1

theorem prod_caps : ∏ i ∈ Finset.range 6, getS [15, 12, 9, 6, 1, 1] i = 9720 := by decide

theorem card_CB :
    Nat.card CB ≤ 29160 := by
  have hL : Nat.card (stabB CB bB 6) ≤ 3 := by
    have h6 := chainB 6 (by norm_num)
    rw [prodKB6, h6.1] at h6
    rw [← h6.2]
    exact Subgroup.card_le_of_le fun g hg => ⟨(mem_CB.1 hg.1).2, hg.2⟩
  have hcap : ∀ i < 6, ∃ s : Finset (Fin 276), s.card ≤ getS [15, 12, 9, 6, 1, 1] i ∧
      ∀ g ∈ stabB CB bB i, g (bB i) ∈ s := by
    intro i hi
    interval_cases i
    · exact ⟨_, (card_cap (i := 0) (by norm_num)).le, fun g hg => img_cap (by norm_num) hg⟩
    · refine ⟨Finset.univ.filter fun y : Fin 276 => y.val ∈ Q1, (card_le_list Q1).trans
        Q1_len.le, fun g hg => ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact lvl1 hg
    · exact ⟨_, (card_cap (i := 2) (by norm_num)).le, fun g hg => img_cap (by norm_num) hg⟩
    · exact ⟨_, (card_cap (i := 3) (by norm_num)).le, fun g hg => img_cap (by norm_num) hg⟩
    · refine ⟨(FBs ∩ DelB 4).erase p162, ?_, fun g hg =>
        Finset.mem_erase.2 ⟨lvl4 hg, img_cap (by norm_num) hg⟩⟩
      rw [Finset.card_erase_of_mem p162_mem, card_cap (i := 4) (by norm_num)]
      rfl
    · exact ⟨_, (card_cap (i := 5) (by norm_num)).le, fun g hg => img_cap (by norm_num) hg⟩
  have h := CFSG.KC.Co3Cent.bound_of_chain CB bB 6 (getS [15, 12, 9, 6, 1, 1]) 3 hcap hL
  rw [prod_caps] at h
  exact h

theorem xB_eq' : permOfArr 276 (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T.dElts ())[
    CFSG.HardMathSupport.Solomon.Coordinator.Co3Pump.kB]! = xB := xB_eq

theorem caseB :
    xB ^ 3 = 1 ∧ xB ≠ 1 ∧ xB ∈ co3P ∧ Nat.card (closure (permsA 276 (dGens ()))) = 243 ∧
      closure (permsA 276 (dGens ())) ≤ centralizer {xB} ⊓ co3P ∧
      (∀ g ∈ centralizer {xB} ⊓ co3P, ∀ r ∈ closure (permsA 276 (dGens ())),
        g * r * g⁻¹ ∈ closure (permsA 276 (dGens ()))) ∧
      centralizer (closure (permsA 276 (dGens ())) : Set (Equiv.Perm (Fin 276))) ⊓
        (centralizer {xB} ⊓ co3P) ≤ closure (permsA 276 (dGens ())) :=
  ⟨xB_pow, xB_ne, xB_mem, card_DB, DB_le, DB_norm card_CB, DB_cent card_CB⟩

end CertificateChecks.KernelCo3Cent

end
