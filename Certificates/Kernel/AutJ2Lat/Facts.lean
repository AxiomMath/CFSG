module

public import Certificates.Kernel.AutJ2Lat.Glue
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.AutJ2Lat

open CFSG.KC.LQT.PW CFSG.KC.SLDc CFSG.KC.E64F CFSG.KC.IdxG CFSG.KC.SLOm
open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.ComponentClassification.J2Cover CFSG.Quasithin.F112R.AJ2L
open CFSG.KD.J2Dc (wW G ga gb)

theorem fa_mem {α β : Type} {Rl : α → β → Prop} {P : α → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ Rl l1 l2 → (∀ a ∈ l1, P a) →
      List.Forall₂ (fun a b => P a ∧ Rl a b) l1 l2
  | _, _, .nil, _ => .nil
  | _, _, .cons r h, hP =>
    .cons ⟨hP _ List.mem_cons_self, r⟩ (fa_mem h fun a ha => hP a (List.mem_cons_of_mem _ ha))

theorem fa_right {α β : Type} {Rl : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ Rl l1 l2 → ∀ b ∈ l2, ∃ a ∈ l1, Rl a b
  | _, _, .nil, _, hb => absurd hb List.not_mem_nil
  | _, _, .cons r h, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, r⟩
    · obtain ⟨a, ha, e⟩ := fa_right h b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, e⟩

theorem fa_left {α β : Type} {Rl : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ Rl l1 l2 → ∀ a ∈ l1, ∃ b ∈ l2, Rl a b
  | _, _, .nil, _, ha => absurd ha List.not_mem_nil
  | _, _, .cons r h, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, r⟩
    · obtain ⟨b, hb, e⟩ := fa_left h a ha
      exact ⟨b, List.mem_cons_of_mem _ hb, e⟩

theorem fa_get {α β : Type} {Rl : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ Rl l1 l2 →
      ∀ i (h1 : i < l1.length) (h2 : i < l2.length), Rl l1[i] l2[i]
  | _, _, .nil, _, h1, _ => absurd h1 (by simp)
  | _, _, .cons r h, 0, _, _ => r
  | _, _, .cons _ h, i + 1, h1, h2 =>
    fa_get h i (by simpa using h1) (by simpa using h2)

theorem codesBelow_codeSetF {f : ℕ → ℕ} (hf : ∀ p < 315, f p < 315) {x : List ℕ}
    (hx : codesBelow 315 x = true) : codesBelow 315 (codeSetF 315 f x) = true := by
  unfold codesBelow codeSetF
  rw [List.all_eq_true]
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 (insN_mem hc)
  have hpd := List.all_eq_true.1 (List.all_eq_true.1 hx d hd)
  have hl : ∀ q ∈ insN ((decodeSet 315 d d).map f), q < 315 := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (insN_mem hq)
    exact hf p (by simpa using hpd p hp)
  unfold codeF
  rw [decodeSet_encodeSet 315 _ hl _ (encodeSet_ge 315 _)]
  exact List.all_eq_true.2 fun q hq => decide_eq_true (hl q hq)

theorem delta_eq : rDelta = Δc := by decide


theorem mw_eq : AutJ2Lat.RL.mw = mwR := eq_of_beq mw_ok

theorem MC_eq : K.MC = ORD.map fun j =>
    (J2Dc.J.mw.getD j []).map fun w => mulW 315 9 K.CC (mulW 315 9 (wW w) K.CI) :=
  eq_of_beq mc_ok

theorem mw_getD {k : ℕ} (hk : k < 5) : AutJ2Lat.RL.mw.getD k [] =
    (J2Dc.J.mw.getD (ORD.getD k 0) []).map fun w => trW K.cw ++ trW w ++ trW K.ciw := by
  rw [mw_eq]
  interval_cases k <;> rfl

theorem MC_getD {k : ℕ} (hk : k < 5) : K.MC.getD k [] =
    (J2Dc.J.mw.getD (ORD.getD k 0) []).map fun w => mulW 315 9 K.CC (mulW 315 9 (wW w) K.CI) := by
  rw [MC_eq]
  interval_cases k <;> rfl

theorem rmw_len : AutJ2Lat.RL.mw.length = 5 := by
  rw [mw_eq]
  rfl

theorem rmw_lt2 {k : ℕ} : ∀ w ∈ AutJ2Lat.RL.mw.getD k [], ∀ l ∈ w, l < 2 := by
  intro w hw l hl
  rcases Nat.lt_or_ge k AutJ2Lat.RL.mw.length with hk | hk
  · rw [List.getD_eq_getElem _ _ hk] at hw
    have h1 := List.all_eq_true.1 mw_lt2 _ (List.getElem_mem hk)
    have h2 := List.all_eq_true.1 (List.all_eq_true.1 h1 w hw) l hl
    simpa using h2
  · rw [List.getD_eq_default _ _ hk] at hw
    simp at hw

theorem member_word {w : List ℕ} (hw : ∀ l ∈ w, l < 2) :
    wordElt xR yR (trW K.cw ++ trW w ++ trW K.ciw) = φ (cJ * wordElt ga gb w * cJ⁻¹) := by
  have hc := lt_of_all (Bool.and_eq_true _ _ ▸ cw_lt).1
  have hci := lt_of_all (Bool.and_eq_true _ _ ▸ cw_lt).2
  change evalElt #[xR, yR] (trW K.cw ++ trW w ++ trW K.ciw) = _
  rw [evalElt_app, evalElt_app]
  change wordElt xR yR (trW K.cw) * wordElt xR yR (trW w) * wordElt xR yR (trW K.ciw) = _
  rw [wordElt_trW _ hc, wordElt_trW _ hw, wordElt_trW _ hci, ciw_eq, map_mul, map_mul]
  rfl

theorem mem_fa {k : ℕ} (hk : k < 5) :
    List.Forall₂ (fun v c => PI ((wordElt xR yR v : R) : Equiv.Perm (Fin 315)) (imgW 9 c))
      (AutJ2Lat.RL.mw.getD k []) (K.MC.getD k []) := by
  rw [mw_getD hk, MC_getD hk, List.forall₂_map_left_iff, List.forall₂_map_right_iff,
    List.forall₂_same]
  intro w hw
  rw [member_word (CFSG.KD.J2Dc.mw_lt2 w hw)]
  exact pi_conj (piJ_word (CFSG.KD.J2Dc.mw_lt2 w hw))

theorem rD_mw_size : rLatD.mw.size = 5 := by
  change AutJ2Lat.RL.mw.toArray.size = 5
  rw [List.size_toArray]
  exact rmw_len

theorem rD_mw_get (k : ℕ) : rLatD.mw[k]! = AutJ2Lat.RL.mw.getD k [] := by
  change AutJ2Lat.RL.mw.toArray[k]! = _
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]
  rfl

theorem rD_mt_get {k : ℕ} (hk : k < 5) : rLatD.mt[k]! =
    (rLatD.mw[k]!).map (wordTabA #[(tab 315 xR).toArray, (tab 315 yR).toArray] 315) := by
  change (AutJ2Lat.RL.mw.toArray.map _)[k]! = (AutJ2Lat.RL.mw.toArray[k]!).map _
  rw [getElem!_pos _ k (by simp [rmw_len, hk]),
    getElem!_pos AutJ2Lat.RL.mw.toArray k (by simp [rmw_len, hk])]
  simp

theorem rD_Om_get {k : ℕ} (hk : k < 5) : rLatD.Om[k]! = Om k := by
  interval_cases k <;> rfl

theorem otD_get {k : ℕ} (hk : k < 5) : rOtD[k]! = OtD k := by
  interval_cases k <;> rfl

theorem hel : ∀ l < (#[xR, yR] : Array R).size,
    (#[(tab 315 xR).toArray, (tab 315 yR).toArray] : Array (Array ℕ)).getD l #[] =
      (tab 315 ((#[xR, yR] : Array R).getD l 1)).toArray
  | 0, _ => rfl
  | 1, _ => rfl
  | _ + 2, h => absurd h (by simp)

theorem tab_word {w : List ℕ} (hw : ∀ l ∈ w, l < 2) :
    wordTabA #[(tab 315 xR).toArray, (tab 315 yR).toArray] 315 w =
      (tab 315 (wordElt xR yR w)).toArray :=
  wordTabA_eq #[xR, yR] _ hel w (by simpa using hw)

theorem SC_eq : K.SC = [K.SC.getD 0 0, K.SC.getD 1 0, K.SC.getD 2 0] :=
  eq_of_beq (by quickRfl : (K.SC == [K.SC.getD 0 0, K.SC.getD 1 0, K.SC.getD 2 0]) = true)

theorem sT_fa : List.Forall₂ (fun t c => Good 315 t (imgW 9 c)) rLatD.sTabs K.SC := by
  rw [SC_eq]
  exact .cons (good_of_pi (piS (i := 0) (by norm_num)))
    (.cons (good_of_pi (piS (i := 1) (by norm_num)))
      (.cons (good_of_pi (piS (i := 2) (by norm_num))) .nil))

theorem lets_fa {k : ℕ} (hk : k < 5) :
    List.Forall₂ (fun t c => Good 315 t (imgW 9 c)) (rLatD.sTabs ++ rLatD.mt[k]!) (lets k) := by
  unfold lets
  refine fa_append sT_fa ?_
  rw [rD_mt_get hk, rD_mw_get, List.forall₂_map_left_iff]
  refine (fa_mem (mem_fa hk) rmw_lt2).imp fun v c h => ?_
  rw [tab_word h.1]
  exact good_of_pi h.2

theorem om_spec {k : ℕ} (hk : k < 5) :
    OmegaSpec (codeSetAct 315) (rLatD.sTabs ++ rLatD.mt[k]!).toArray rDelta (rLatD.Om[k]!) ∧
      ∀ i < (Om k).lbl.size, codesBelow 315 (Om k).lbl[i]! = true := by
  have hfa := lets_fa hk
  have hlen := hfa.length_eq
  have hom := List.all_eq_true.1 oms k (List.mem_range.2 hk)
  rw [rD_Om_get hk, delta_eq]
  unfold omOK at hom
  refine omOKG_sound (act := codeSetAct 315) (letters := (rLatD.sTabs ++ rLatD.mt[k]!).toArray)
    (actF := fun l x => codeSetF 315 (imgW 9 ((lets k).getD l 0)) x)
    (fun x => codesBelow 315 x = true) codes_ok ?_ (by rw [List.size_toArray, hlen]; exact hom)
  intro l hl x hx
  have hl' : l < (rLatD.sTabs ++ rLatD.mt[k]!).length := by simpa using hl
  have hg : Good 315 ((rLatD.sTabs ++ rLatD.mt[k]!).toArray[l]!) (imgW 9 ((lets k).getD l 0)) := by
    rw [getElem!_pos _ l hl, List.getElem_toArray, List.getD_eq_getElem _ _ (hlen ▸ hl')]
    exact fa_get hfa l hl' (hlen ▸ hl')
  exact ⟨codesBelow_codeSetF (fun p hp => (hg.2 p hp).2) hx, codeSetAct_eq_codeSetF hx hg⟩

theorem rK_membersOK :
    MembersOK (codeSetAct 315) 315 (tab 315 xR).toArray (tab 315 yR).toArray rDelta rLatD := by
  refine ⟨by rw [rD_mw_size]; decide, ?_, by simp [rLatD], by rw [rD_mw_size]; rfl,
    fun j hj => ?_⟩
  · rw [rD_mw_get]
    exact eq_of_beq (by quickRfl : (AutJ2Lat.RL.mw.getD 0 [] == []) = true)
  have hj' : j < 5 := by rwa [rD_mw_size] at hj
  exact ⟨by rw [rD_mw_get]; exact rmw_lt2, rD_mt_get hj', (om_spec hj').1⟩

end CFSG.KD.AutJ2Lat

end
