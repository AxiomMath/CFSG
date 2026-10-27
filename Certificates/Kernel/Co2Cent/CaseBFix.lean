module

public import Certificates.Kernel.Co2Cent.ChainBGlue
public import Certificates.Kernel.Co2Cent.CentBChk
public import CFSG.Certificates.Kernel.OrbRow.CentBSound
public import CFSG.Certificates.Kernel.OrbRow.PRepFacts
public import CFSG.Certificates.Kernel.OrbRow.CentPerm

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelCo2Cent

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KC.OrbRow.CentGrp CFSG.KC.PGrp CFSG.KS CFSG.KS.Raw
  CFSG.KS.Raw.Orb CFSG.KD.Co2Cent Subgroup CFSG.Sporadic.Co2Cert

@[expose] noncomputable def wvB (wd : List ℕ) : Equiv.Perm (Fin 2300) := (wd.map sB).prod

theorem word_repB {lv : ℕ} {wd : List ℕ}
    (hl : ∀ j ∈ wd, j < 17 ∧ Nat.beq fld(lv, j, nat_lit 1) (nat_lit 1) = true) :
    PRep 2300 12 (posWordK 2300 12 (getS SB) wd) (wvB wd) ∧ wvB wd ∈ co2P := by
  refine ⟨posWordK_rep (by norm_num) (by norm_num) fun l hl' => prepB (hl l hl').1, ?_⟩
  apply list_prod_mem
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
  exact sB_mem (hl j hj).1

@[expose] def Orb2 (p q : Fin 2300) : Prop := ∃ h ∈ co2P, h (bB 0) = p ∧ h (bB 1) = q

theorem orb2_map {g : Equiv.Perm (Fin 2300)} (hg : g ∈ co2P) {p q : Fin 2300} (h : Orb2 p q) :
    Orb2 (g p) (g q) := by
  obtain ⟨h, hh, hp, hq⟩ := h
  exact ⟨g * h, co2P.mul_mem hg hh, by rw [Equiv.Perm.mul_apply, hp],
    by rw [Equiv.Perm.mul_apply, hq]⟩

theorem ap_inv (g : Equiv.Perm (Fin 2300)) (q : Fin 2300) : g (g⁻¹ q) = q := g.apply_symm_apply q

theorem inv_ap (g : Equiv.Perm (Fin 2300)) (q : Fin 2300) : g⁻¹ (g q) = q := g.symm_apply_apply q

theorem orb2_iff {g : Equiv.Perm (Fin 2300)} (hg : g ∈ co2P) (p q : Fin 2300) :
    Orb2 (g p) (g q) ↔ Orb2 p q := by
  refine ⟨fun h => ?_, orb2_map hg⟩
  have := orb2_map (co2P.inv_mem hg) h
  rwa [inv_ap, inv_ap] at this

theorem rows1 : rowsK 2300 12 4095 SB 17 (getS MB 1) (getS DB 1) (getS BB 1) (getS KB 1)
    (getLs RB 1) = true := by
  have h : levelK 2300 12 4095 SB 17 BB KB MB DB RB 1 = true := allN_spec ch17351_tB 1 (by norm_num)
  rw [levelK_eq] at h
  exact h

theorem card_D1 : (Finset.univ.filter fun y : Fin 2300 => depD (getS DB 1) y ≠ 255).card =
    getS KB 1 := by
  rw [← (rowsK_dep rows1).1]
  refine Finset.card_bij (fun y _ => y.val) (fun y hy => ?_) (fun y _ z _ h => Fin.ext h)
    (fun y hy => ?_)
  · rw [Finset.mem_filter] at hy ⊢
    exact ⟨Finset.mem_range.2 y.2, hy.2⟩
  · rw [Finset.mem_filter, Finset.mem_range] at hy
    exact ⟨⟨y, hy.1⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hy.2⟩, rfl⟩

theorem reach_D1 {y : Fin 2300} (hy : depD (getS DB 1) y ≠ 255) :
    ∃ h ∈ GB 1, h (bB 1) = y := by
  obtain ⟨hyn, g, hg, hgy⟩ := reach_perm sB (fun j hj z hz => sB_apply (lvOk_iff.1 hj).1 z hz)
    (baseB_lt 1) ((rowsK_dep rows1).2 y y.2 hy)
  exact ⟨g, hg, by rw [bB_def]; exact hgy⟩

theorem D1_iff (y : Fin 2300) :
    (∃ h ∈ stabB co2P bB 1, h (bB 1) = y) ↔ depD (getS DB 1) y ≠ 255 := by
  have hG1 := chainB 1 (by norm_num)
  have hG2 := chainB 2 (by norm_num)
  constructor
  · rintro ⟨h, hh, rfl⟩
    by_contra hy
    classical
    set s := insert (h (bB 1)) (Finset.univ.filter fun y : Fin 2300 => depD (getS DB 1) y ≠ 255)
    have hs : s.card = getS KB 1 + 1 := by
      rw [Finset.card_insert_of_notMem (by simp [hy]), card_D1]
    have hreach : ∀ z ∈ s, ∃ g ∈ GB 1, g (bB 1) = z := by
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact ⟨h, hG1.1 ▸ hh, rfl⟩
      · exact reach_D1 (Finset.mem_filter.1 hz).2
    have hc := card_ge_of_orbit (GB 1) (bB 1) s hreach (GB 2)
      (fun g hg => ⟨GB_dec 1 (by norm_num) hg, GB_fix 2 (by norm_num) g hg 1 (by norm_num)⟩)
    have e : Nat.card (GB 1) = getS KB 1 * Nat.card (GB 2) := by
      rw [hG1.2, hG2.2, Finset.prod_eq_prod_Ico_succ_bot (by norm_num : 1 < 7)]
    rw [hs, e] at hc
    have hpos : 0 < Nat.card (GB 2) := Nat.card_pos
    nlinarith
  · intro hy
    obtain ⟨g, hg, hgy⟩ := reach_D1 hy
    exact ⟨g, hG1.1 ▸ hg, hgy⟩

@[expose] noncomputable def deg (x : Equiv.Perm (Fin 2300)) (p : Fin 2300) : ℕ := by
  classical
  exact (Finset.univ.filter fun q => x q = q ∧ Orb2 p q).card

theorem deg_inv
    {x g : Equiv.Perm (Fin 2300)} (hg : g ∈ centP co2P x) (p : Fin 2300) :
    deg x (g p) = deg x p := by
  classical
  have hc : g * x = x * g := comm_of_mem_centP hg
  have hgP : g ∈ co2P := hg.2
  have hfx : ∀ q, x (g q) = g q ↔ x q = q := by
    intro q
    have e : x (g q) = g (x q) := by
      have := congrArg (fun σ : Equiv.Perm (Fin 2300) => σ q) hc
      simp only [Equiv.Perm.mul_apply] at this
      exact this.symm
    rw [e]
    exact g.injective.eq_iff
  unfold deg
  refine Finset.card_bij' (fun q _ => g⁻¹ q) (fun q _ => g q) (fun q hq => ?_) (fun q hq => ?_)
    (fun q _ => ap_inv g q) (fun q _ => inv_ap g q)
  · rw [Finset.mem_filter] at hq ⊢
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [← hfx, ap_inv]
      exact hq.2.1
    · rw [← orb2_iff hgP, ap_inv]
      exact hq.2.2
  · rw [Finset.mem_filter] at hq ⊢
    exact ⟨Finset.mem_univ _, (hfx q).2 hq.2.1, (orb2_iff hgP p q).2 hq.2.2⟩

theorem bxFacts : fixSetK 2300 12 4095 xB FB = true ∧ FB.length = 41 ∧
    (∀ t < 41, getS FB t < 2300) ∧ FB.Nodup := by
  have h := ch17351_bx
  simp only [bAnd_iff] at h
  refine ⟨h.1, ?_, fun t ht => Nat.le_of_ble_eq_true (allN_spec h.2.2.1 t ht),
    incK_sound h.2.2.2⟩
  rw [← lenS_eq]
  exact Nat.eq_of_beq_eq_true h.2.1

theorem fixB {x : Equiv.Perm (Fin 2300)} (hx : PRep 2300 12 xB x) (q : Fin 2300) :
    x q = q ↔ q.val ∈ FB := by
  have h1 := fixSetK_sound bxFacts.1 q.2
  have e : pg 12 4095 xB q = x q := hx q
  rw [e] at h1
  rw [Fin.ext_iff, h1]

theorem getS_FB {t : ℕ} (ht : t < FB.length) : getS FB t = FB[t] := by
  rw [getS_eq]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]

theorem mem_FB {y : ℕ} : y ∈ FB ↔ ∃ t < 41, getS FB t = y := by
  have hl := bxFacts.2.1
  constructor
  · intro hy
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hy
    exact ⟨t, hl ▸ ht, getS_FB ht⟩
  · rintro ⟨t, ht, rfl⟩
    rw [getS_FB (hl ▸ ht)]
    exact List.getElem_mem _

theorem bdFacts {t : ℕ} (ht : t < 41) :
    (∀ j ∈ getLs UW t, j < 17 ∧ Nat.beq fld(getS MB 0, j, nat_lit 1) (nat_lit 1) = true) ∧
      pg 12 4095 (posWordK 2300 12 (getS SB) (getLs UW t)) (getS BB 0) = getS FB t ∧
      permOK 2300 12 4095 (2300 * 12) (posWordK 2300 12 (getS SB) (getLs UW t))
        (CFSG.KS.pinvS 2300 12 4095 (posWordK 2300 12 (getS SB) (getLs UW t))) = true ∧
      (FB.filter fun q => inD (getS DB 1) (pg 12 4095 (CFSG.KS.pinvS 2300 12 4095
        (posWordK 2300 12 (getS SB) (getLs UW t))) q)).length =
        nIf(Nat.beq (getS FB t) 1, 40, 13) := by
  have h := allN_spec ch17351_bd t ht
  beta_reduce at h
  rw [strictB_apply] at h
  exact degK_sound h

theorem deg_eq
    {x : Equiv.Perm (Fin 2300)} (hx : PRep 2300 12 xB x) {p : Fin 2300} (hp : x p = p) :
    deg x p = nIf(Nat.beq p.val 1, 40, 13) := by
  classical
  obtain ⟨t, ht, htp⟩ := mem_FB.1 ((fixB hx p).1 hp)
  obtain ⟨hl, hb, hperm, hcnt⟩ := bdFacts ht
  obtain ⟨hU, -⟩ := word_repB hl
  set U := wvB (getLs UW t)
  set u := posWordK 2300 12 (getS SB) (getLs UW t)
  have hUi : PRep 2300 12 (CFSG.KS.pinvS 2300 12 4095 u) U⁻¹ := prep_inv hperm hU
  have hU0 : U (bB 0) = p := by
    apply Fin.ext
    rw [← htp, ← hb]
    exact (hU (bB 0)).symm
  have hU0' : U⁻¹ p = bB 0 := by rw [Equiv.Perm.inv_eq_iff_eq, hU0]
  have hUP : U ∈ co2P := (word_repB hl).2
  have horb : ∀ q, Orb2 p q ↔ inD (getS DB 1) (pg 12 4095 (CFSG.KS.pinvS 2300 12 4095 u) q) =
      true := by
    intro q
    have e : pg 12 4095 (CFSG.KS.pinvS 2300 12 4095 u) q = (U⁻¹ q : ℕ) := hUi q
    rw [e, inD_iff, ← D1_iff]
    constructor
    · rintro ⟨h, hh, hp', hq⟩
      refine ⟨U⁻¹ * h, ⟨co2P.mul_mem (co2P.inv_mem hUP) hh, fun s hs => ?_⟩, ?_⟩
      · have : s = 0 := by omega
        subst this
        rw [Equiv.Perm.mul_apply, hp', hU0']
      · rw [Equiv.Perm.mul_apply, hq]
    · rintro ⟨k, hk, hkq⟩
      refine ⟨U * k, co2P.mul_mem hUP hk.1, ?_, ?_⟩
      · rw [Equiv.Perm.mul_apply, hk.2 0 (by norm_num), hU0]
      · rw [Equiv.Perm.mul_apply, hkq, ap_inv]
  rw [← htp, ← hcnt, ← List.toFinset_card_of_nodup (bxFacts.2.2.2.filter _)]
  unfold deg
  refine Finset.card_bij (fun q _ => q.val) (fun q hq => ?_) (fun q _ r _ h => Fin.ext h)
    (fun y hy => ?_)
  · rw [Finset.mem_filter] at hq
    rw [List.mem_toFinset, List.mem_filter]
    exact ⟨(fixB hx q).1 hq.2.1, (horb q).1 hq.2.2⟩
  · rw [List.mem_toFinset, List.mem_filter] at hy
    obtain ⟨s, hs, rfl⟩ := mem_FB.1 hy.1
    refine ⟨⟨getS FB s, bxFacts.2.2.1 s hs⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _,
      (fixB hx _).2 hy.1, (horb _).2 hy.2⟩, rfl⟩

theorem BB1 : getS BB 1 = 1 := by decide +kernel

theorem one_mem_FB : (1 : ℕ) ∈ FB := by
  rw [mem_FB]
  exact ⟨1, by norm_num, by decide +kernel⟩

theorem fix_b1
    {x : Equiv.Perm (Fin 2300)} (hx : PRep 2300 12 xB x) :
    ∀ g ∈ centP co2P x, g (bB 1) = bB 1 := by
  intro g hg
  have hb1 : x (bB 1) = bB 1 := (fixB hx _).2 (by rw [bB_def]; simp only [BB1]; exact one_mem_FB)
  have hc : g * x = x * g := comm_of_mem_centP hg
  have hgb : x (g (bB 1)) = g (bB 1) := by
    have := congrArg (fun σ : Equiv.Perm (Fin 2300) => σ (bB 1)) hc
    simp only [Equiv.Perm.mul_apply, hb1] at this
    exact this.symm
  have h1 := deg_inv hg (bB 1)
  rw [deg_eq hx hgb, deg_eq hx hb1] at h1
  have hv : (bB 1).val = 1 := BB1
  apply Fin.ext
  rw [hv]
  by_contra hne
  have e : Nat.beq (g (bB 1)).val 1 = false := by
    cases h : Nat.beq (g (bB 1)).val 1
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h) hne
  rw [e, hv] at h1
  exact absurd h1 (by decide)

end CertificateChecks.KernelCo2Cent

end
