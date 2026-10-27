module

public import Certificates.Kernel.Co2Cent.CaseBFix

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelCo2Cent

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KC.OrbRow.CentGrp CFSG.KC.PGrp CFSG.KS CFSG.KS.Raw
  CFSG.KS.Raw.Orb CFSG.KD.Co2Cent Subgroup CFSG.Sporadic.Co2Cert

theorem card_le_orbit {α : Type*} [Finite α] (H S : Subgroup (Equiv.Perm α)) (a : α)
    (s : Finset α) (hs : ∀ h ∈ H, h a ∈ s) (hS : ∀ h ∈ H, h a = a → h ∈ S) :
    Nat.card H ≤ s.card * Nat.card S := by
  classical
  have hrep : ∀ y : s, ∃ r : Equiv.Perm α, (∃ h ∈ H, h a = y.1) → r ∈ H ∧ r a = y.1 := by
    intro y
    by_cases hy : ∃ h ∈ H, h a = y.1
    · obtain ⟨h, hh, hy⟩ := hy
      exact ⟨h, fun _ => ⟨hh, hy⟩⟩
    · exact ⟨1, fun h => absurd h hy⟩
  choose r hr using hrep
  let F : H → s × S := fun h => (⟨h.1 a, hs h.1 h.2⟩, ⟨(r ⟨h.1 a, hs h.1 h.2⟩)⁻¹ * h.1, by
    obtain ⟨hrH, hra⟩ := hr ⟨h.1 a, hs h.1 h.2⟩ ⟨h.1, h.2, rfl⟩
    refine hS _ (H.mul_mem (H.inv_mem hrH) h.2) ?_
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq, hra]⟩)
  have hF : Function.Injective F := by
    rintro ⟨h, hh⟩ ⟨h', hh'⟩ he
    simp only [F, Prod.mk.injEq, Subtype.mk.injEq] at he
    obtain ⟨e1, e2⟩ := he
    have e3 : (⟨h a, hs h hh⟩ : s) = ⟨h' a, hs h' hh'⟩ := Subtype.ext e1
    rw [e3] at e2
    exact Subtype.ext (mul_left_cancel e2)
  have := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := s), Fintype.card_coe] at this

theorem rowsB {i : ℕ} (hi : i < 7) : rowsK 2300 12 4095 SB 17 (getS MB i) (getS DB i) (getS BB i)
    (getS KB i) (getLs RB i) = true := by
  have h : levelK 2300 12 4095 SB 17 BB KB MB DB RB i = true := allN_spec ch17351_tB i hi
  rw [levelK_eq] at h
  exact h

theorem card_Di {i : ℕ} (hi : i < 7) :
    (Finset.univ.filter fun y : Fin 2300 => depD (getS DB i) y ≠ 255).card = getS KB i := by
  rw [← (rowsK_dep (rowsB hi)).1]
  refine Finset.card_bij (fun y _ => y.val) (fun y hy => ?_) (fun y _ z _ h => Fin.ext h)
    (fun y hy => ?_)
  · rw [Finset.mem_filter] at hy ⊢
    exact ⟨Finset.mem_range.2 y.2, hy.2⟩
  · rw [Finset.mem_filter, Finset.mem_range] at hy
    exact ⟨⟨y, hy.1⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hy.2⟩, rfl⟩

theorem reach_Di {i : ℕ} (hi : i < 7) {y : Fin 2300} (hy : depD (getS DB i) y ≠ 255) :
    ∃ h ∈ GB i, h (bB i) = y := by
  obtain ⟨hyn, g, hg, hgy⟩ := reach_perm sB (fun j hj z hz => sB_apply (lvOk_iff.1 hj).1 z hz)
    (baseB_lt i) ((rowsK_dep (rowsB hi)).2 y y.2 hy)
  exact ⟨g, hg, by rw [bB_def]; exact hgy⟩

theorem Di_iff {i : ℕ} (hi : i < 7)
    (y : Fin 2300) : (∃ h ∈ stabB co2P bB i, h (bB i) = y) ↔ depD (getS DB i) y ≠ 255 := by
  have hG1 := chainB i hi.le
  have hG2 := chainB (i + 1) hi
  constructor
  · rintro ⟨h, hh, rfl⟩
    by_contra hy
    classical
    set s := insert (h (bB i)) (Finset.univ.filter fun y : Fin 2300 => depD (getS DB i) y ≠ 255)
    have hs : s.card = getS KB i + 1 := by
      rw [Finset.card_insert_of_notMem (by simp [hy]), card_Di hi]
    have hreach : ∀ z ∈ s, ∃ g ∈ GB i, g (bB i) = z := by
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact ⟨h, hG1.1 ▸ hh, rfl⟩
      · exact reach_Di hi (Finset.mem_filter.1 hz).2
    have hc := card_ge_of_orbit (GB i) (bB i) s hreach (GB (i + 1))
      (fun g hg => ⟨GB_dec i hi hg, GB_fix (i + 1) hi g hg i (Nat.lt_succ_self i)⟩)
    have e : Nat.card (GB i) = getS KB i * Nat.card (GB (i + 1)) := by
      rw [hG1.2, hG2.2, Finset.prod_eq_prod_Ico_succ_bot hi]
    rw [hs, e] at hc
    have hpos : 0 < Nat.card (GB (i + 1)) := Nat.card_pos
    nlinarith
  · intro hy
    obtain ⟨g, hg, hgy⟩ := reach_Di hi hy
    exact ⟨g, hG1.1 ▸ hg, hgy⟩

theorem card_fix {x : Equiv.Perm (Fin 2300)} (hx : PRep 2300 12 xB x) (f : ℕ → Bool) :
    (Finset.univ.filter fun y : Fin 2300 => x y = y ∧ f y = true).card = (FB.filter f).length := by
  rw [← List.toFinset_card_of_nodup (bxFacts.2.2.2.filter _)]
  refine Finset.card_bij (fun q _ => q.val) (fun q hq => ?_) (fun q _ r _ h => Fin.ext h)
    (fun y hy => ?_)
  · rw [Finset.mem_filter] at hq
    rw [List.mem_toFinset, List.mem_filter]
    exact ⟨(fixB hx q).1 hq.2.1, hq.2.2⟩
  · rw [List.mem_toFinset, List.mem_filter] at hy
    obtain ⟨s, hs, rfl⟩ := mem_FB.1 hy.1
    exact ⟨⟨getS FB s, bxFacts.2.2.1 s hs⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _,
      (fixB hx _).2 hy.1, hy.2⟩, rfl⟩

theorem FB_ne1 : (FB.filter fun y => !(Nat.beq y 1)).length = 40 := by decide +kernel

theorem BB_FB : ∀ i < 6, getS BB i = getS FB i := by decide +kernel

theorem fix_bB {x : Equiv.Perm (Fin 2300)} (hx : PRep 2300 12 xB x) {i : ℕ} (hi : i < 6) :
    x (bB i) = bB i :=
  (fixB hx _).2 (mem_FB.2 ⟨i, by omega, (BB_FB i hi).symm⟩)

theorem cFactsB : (FB.filter (inD (getS DB 2))).length = 27 ∧
    (FB.filter (inD (getS DB 3))).length = 6 ∧ (FB.filter (inD (getS DB 4))).length = 4 ∧
    (FB.filter (inD (getS DB 5))).length = 2 := by
  have h := ch17351_bc
  simp only [bAnd_iff] at h
  exact ⟨capK_sound h.1, capK_sound h.2.1, capK_sound h.2.2.1, capK_sound h.2.2.2⟩

@[expose] noncomputable def Cs (x : Equiv.Perm (Fin 2300)) (i : ℕ) :
    Subgroup (Equiv.Perm (Fin 2300)) :=
  centP co2P x ⊓ stabB co2P bB i

theorem Cs_step {x : Equiv.Perm (Fin 2300)} (i : ℕ) (s : Finset (Fin 2300))
    (hs : ∀ h ∈ Cs x i, h (bB i) ∈ s) : Nat.card (Cs x i) ≤ s.card * Nat.card (Cs x (i + 1)) :=
  card_le_orbit (Cs x i) (Cs x (i + 1)) (bB i) s hs fun h hh hfix =>
    ⟨hh.1, hh.2.1, fun t ht => by
      rcases Nat.lt_or_ge t i with h1 | h1
      · exact hh.2.2 t h1
      · have : t = i := by omega
        subst this
        exact hfix⟩

theorem regFacts : VQ.length = 6 ∧ VQ.Nodup ∧
    (∀ t < 6, inD (getS DB 6) (getS VQ t) = true ∧
      (∀ j ∈ getLs VW t, j < 17 ∧ Nat.beq fld(getS MB 6, j, nat_lit 1) (nat_lit 1) = true) ∧
      pg 12 4095 (posWordK 2300 12 (getS SB) (getLs VW t)) (getS BB 6) = getS VQ t) ∧
    ((List.range 6).filter fun t =>
      commOK 2300 12 4095 (posWordK 2300 12 (getS SB) (getLs VW t)) xB).length = 3 :=
  regK_sound ch17351_bv

theorem KB6 : getS KB 6 = 6 := by decide +kernel

theorem getS_VQ {t : ℕ} (ht : t < VQ.length) : getS VQ t = VQ[t] := by
  rw [getS_eq]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]

theorem Cs6_le
    {x : Equiv.Perm (Fin 2300)} (hx : PRep 2300 12 xB x) : Nat.card (Cs x 6) ≤ 3 := by
  classical
  obtain ⟨hlen, hnd, hent, hcnt⟩ := regFacts
  set V : ℕ → Equiv.Perm (Fin 2300) := fun t => wvB (getLs VW t)
  have hVr : ∀ t < 6, PRep 2300 12 (posWordK 2300 12 (getS SB) (getLs VW t)) (V t) :=
    fun t ht => (word_repB (hent t ht).2.1).1
  have hVG : ∀ t < 6, V t ∈ stabB co2P bB 6 := by
    intro t ht
    rw [← (chainB 6 (by norm_num)).1]
    apply list_prod_mem
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
    exact subset_closure ⟨j, lvOk_of_letter ((hent t ht).2.1 j hj), rfl⟩
  have hVb : ∀ t (ht : t < 6), (V t (bB 6) : ℕ) = getS VQ t := by
    intro t ht
    rw [← (hent t ht).2.2]
    exact ((hVr t ht) (bB 6)).symm
  have hsub : (Finset.range 6).attach.image (fun t => V t.1 (bB 6)) ⊆
      Finset.univ.filter fun y : Fin 2300 => depD (getS DB 6) y ≠ 255 := by
    intro y hy
    obtain ⟨⟨t, ht⟩, -, rfl⟩ := Finset.mem_image.1 hy
    have ht' := Finset.mem_range.1 ht
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rw [hVb t ht', ← inD_iff]
    exact (hent t ht').1
  have hcard : ((Finset.range 6).attach.image (fun t => V t.1 (bB 6))).card = 6 := by
    rw [Finset.card_image_of_injective _ (fun a b h => ?_), Finset.card_attach, Finset.card_range]
    have e := congrArg Fin.val h
    have ha : a.1 < VQ.length := by rw [hlen]; exact Finset.mem_range.1 a.2
    have hb : b.1 < VQ.length := by rw [hlen]; exact Finset.mem_range.1 b.2
    rw [hVb a.1 (Finset.mem_range.1 a.2), hVb b.1 (Finset.mem_range.1 b.2), getS_VQ ha,
      getS_VQ hb] at e
    exact Subtype.ext ((List.Nodup.getElem_inj_iff hnd).1 e)
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [card_Di (by norm_num), KB6, hcard])
  set T := ((List.range 6).filter fun t =>
    commOK 2300 12 4095 (posWordK 2300 12 (getS SB) (getLs VW t)) xB).toFinset
  have hmem : ∀ g ∈ Cs x 6, g ∈ T.image V := by
    intro g hg
    have hd := (Di_iff (by norm_num) (g (bB 6))).1 ⟨g, hg.2, rfl⟩
    have hy : g (bB 6) ∈ (Finset.range 6).attach.image (fun t => V t.1 (bB 6)) := by
      rw [heq]
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hd⟩
    obtain ⟨⟨t, ht⟩, -, hte⟩ := Finset.mem_image.1 hy
    have ht' := Finset.mem_range.1 ht
    have hgV : g = V t := by
      have h1 : (V t)⁻¹ * g = 1 := by
        refine eq_one_of_fixB (co2P.mul_mem (co2P.inv_mem (hVG t ht').1) hg.2.1) fun s hs => ?_
        rcases Nat.lt_or_ge s 6 with h6 | h6
        · rw [Equiv.Perm.mul_apply, hg.2.2 s h6, Equiv.Perm.inv_eq_iff_eq, (hVG t ht').2 s h6]
        · have : s = 6 := by omega
          subst this
          rw [Equiv.Perm.mul_apply, ← hte, inv_ap]
      rw [← mul_inv_cancel_left (V t) g, h1, mul_one]
    refine Finset.mem_image.2 ⟨t, ?_, hgV.symm⟩
    rw [List.mem_toFinset, List.mem_filter, List.mem_range]
    refine ⟨ht', ?_⟩
    have hc := comm_of_mem_centP hg.1
    rw [hgV] at hc
    exact (commOK_iff (hVr t ht') hx).2 hc
  have hle : Nat.card (Cs x 6) ≤ (T.image V).card := by
    have := Nat.card_le_card_of_injective (fun g : Cs x 6 => (⟨g.1, hmem g.1 g.2⟩ : T.image V))
      (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))
    rwa [Nat.card_eq_fintype_card (α := T.image V), Fintype.card_coe] at this
  refine hle.trans ((Finset.card_image_le).trans ?_)
  rw [← hcnt]
  exact List.toFinset_card_le _

theorem card_centB_le
    {x : Equiv.Perm (Fin 2300)} (hx : PRep 2300 12 xB x) : Nat.card (centP co2P x) ≤ 155520 := by
  classical
  have hfix1 := fix_b1 hx
  have hC : ∀ g ∈ centP co2P x, ∀ {y}, x y = y → x (g y) = g y := by
    intro g hg y hy
    have := congrArg (fun σ : Equiv.Perm (Fin 2300) => σ y) (comm_of_mem_centP hg)
    simp only [Equiv.Perm.mul_apply, hy] at this
    exact this.symm
  have h0 : centP co2P x ≤ Cs x 0 := fun g hg => ⟨hg, hg.2, fun t ht => absurd ht (by omega)⟩
  have s0 := Cs_step (x := x) 0 (Finset.univ.filter fun y : Fin 2300 => x y = y ∧
      (!(Nat.beq y.val 1)) = true) (by
    intro h hh
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hC h hh.1 (fix_bB hx (by norm_num)), ?_⟩
    have hne : h (bB 0) ≠ bB 1 := by
      rw [← hfix1 h hh.1]
      intro e
      have := congrArg Fin.val (h.injective e)
      rw [bB_def, bB_def] at this
      exact absurd this (by decide +kernel)
    have hv : (bB 1).val = 1 := BB1
    cases hb : Nat.beq (h (bB 0)).val 1
    · rfl
    · exact absurd (Fin.ext ((Nat.eq_of_beq_eq_true hb).trans hv.symm)) hne)
  have e0 := card_fix hx (fun y => !(Nat.beq y 1))
  beta_reduce at e0
  rw [e0, FB_ne1] at s0
  have s1 := Cs_step (x := x) 1 {bB 1} (fun h hh => Finset.mem_singleton.2 (hfix1 h hh.1))
  rw [Finset.card_singleton] at s1
  have sL : ∀ i, 2 ≤ i → i < 6 → Nat.card (Cs x i) ≤
      (FB.filter (inD (getS DB i))).length * Nat.card (Cs x (i + 1)) := by
    intro i hi2 hi6
    have := Cs_step (x := x) i (Finset.univ.filter fun y : Fin 2300 => x y = y ∧
        inD (getS DB i) y = true) (by
      intro h hh
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hC h hh.1 (fix_bB hx hi6), ?_⟩
      rw [inD_iff, ← Di_iff (by omega)]
      exact ⟨h, hh.2, rfl⟩)
    rwa [card_fix hx (inD (getS DB i))] at this
  obtain ⟨c2, c3, c4, c5⟩ := cFactsB
  have s2 := sL 2 (by norm_num) (by norm_num)
  have s3 := sL 3 (by norm_num) (by norm_num)
  have s4 := sL 4 (by norm_num) (by norm_num)
  have s5 := sL 5 (by norm_num) (by norm_num)
  rw [c2] at s2
  rw [c3] at s3
  rw [c4] at s4
  rw [c5] at s5
  have s6 := Cs6_le hx
  have hc0 := Subgroup.card_le_of_le h0
  simp only [Nat.reduceAdd, Nat.zero_add] at s0 s1 s2 s3 s4 s5
  omega

end CertificateChecks.KernelCo2Cent

end
