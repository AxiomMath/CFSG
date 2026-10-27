module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificate
public import Certificates.Kernel.A312He.Checks
public import Certificates.Kernel.He7149.Final
public import CFSG.Certificates.Kernel.A312HeKSound
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312WordsIdx
public import CFSG.Quasithin.Background.A3StructureDefs
import CFSG.Certificates.Kernel.Common.ForallTree
public import Certificates.Certificate4167Base

set_option maxRecDepth 100000

public section

namespace CFSG.KD.A312He

open CFSG.KC.E64F CFSG.KC.A312HeK CFSG.Quasithin.A312He CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.He CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Quasithin.H13.KGE64

#kc_forall_tree w3_all
  (fun c => chunkAll 8330 (fun p => Nat.beq (LF3 4 p) (wordF LAB (mw 3) p)) c = true) 9
  CFSG.KD.A312He.ch4167w3_

#kc_forall_tree w4_all
  (fun c => chunkAll 8330 (fun p => Nat.beq (LF4 4 p) (wordF LAB (mw 4) p)) c = true) 9
  CFSG.KD.A312He.ch4167w4_

#kc_forall_tree i3_all (fun i => invChk LF3 8330 5 (i / 9) (i % 9) = true) 45
  CFSG.KD.A312He.ch4167i3_

#kc_forall_tree i4_all (fun i => invChk LF4 8330 5 (i / 9) (i % 9) = true) 45
  CFSG.KD.A312He.ch4167i4_

#kc_forall_tree i7_all (fun i => invChk LF7 8330 5 (i / 9) (i % 9) = true) 45
  CFSG.KD.A312He.ch4167i7_

#kc_forall_tree h3_all (fun k => hatPart LF3 8330 heB 5 (heHat3Xs.map qg) (qg heHat3T)
  heHat3Ws heHat3Pts heHat3W1 heHat3W2 heHat3V h3wit h3ex k = true) 11 CFSG.KD.A312He.ch4167h3_

#kc_forall_tree h4_all (fun k => hatPart LF4 8330 heB 5 (heHat4Xs.map qg) (qg heHat4T)
  heHat4Ws heHat4Pts heHat4W1 heHat4W2 heHat4V h4wit h4ex k = true) 7 CFSG.KD.A312He.ch4167h4_

#kc_forall_tree e7_all (fun k => extPart LF7 heB 5 (heExt7Xs.map qg) (qg heExt7T)
  heExt7Ws heExt7W heExt7Z e7sq e7C e7idx e7ex k = true) 8 CFSG.KD.A312He.ch4167e7_

theorem inv_of {L : ℕ → ℕ → ℕ} (h : ∀ i < 45, invChk L 8330 5 (i / 9) (i % 9) = true) :
    ∀ l < 5, ∀ c < 9, invChk L 8330 5 l c = true := by
  intro l hl c hc
  have e := h (9 * l + c) (by omega)
  have e1 : (9 * l + c) / 9 = l := by omega
  have e2 : (9 * l + c) % 9 = c := by omega
  rwa [e1, e2] at e

theorem hab : ∀ l < (#[heTa, heTb] : Array (Array Nat)).size,
    Good 8330 ((#[heTa, heTb] : Array (Array Nat)).getD l #[]) (LAB l) := by
  intro l hl
  have e0 : heSLP[0]! = heTa := by
    unfold heSLP slpTabsA
    rw [He7149.slp_get heProg _ 0 (by simp)]
    rfl
  have e1 : heSLP[1]! = heTb := by
    unfold heSLP slpTabsA
    rw [He7149.slp_get heProg _ 1 (by simp)]
    rfl
  rcases l with _ | _ | l
  · change Good 8330 heTa (CFSG.KC.LQT.PW.imgW 14 (CFSG.KD.LQT.C4141.TF 0))
    rw [← e0]
    exact He7149.good_of_rep (He7149.rep_he (by decide))
  · change Good 8330 heTb (CFSG.KC.LQT.PW.imgW 14 (CFSG.KD.LQT.C4141.TF 1))
    rw [← e1]
    exact He7149.good_of_rep (He7149.rep_he (by decide))
  · exact absurd hl (by simp)

theorem good_hat {LF : ℕ → ℕ → ℕ} {TF : ℕ → ℕ} {j : ℕ}
    (hLF : ∀ l p, LF l p = CFSG.KC.LQT.PW.imgW 14 (TF l) p)
    (hlt : (Nat.beq (TF 0) (CFSG.KD.LQT.C4141.TF 197) &&
      Nat.beq (TF 1) (CFSG.KD.LQT.C4141.TF 207) && Nat.beq (TF 2) (CFSG.KD.LQT.C4141.TF 226) &&
      Nat.beq (TF 3) (CFSG.KD.LQT.C4141.TF 247)) = true)
    (hw : ∀ c < 9, chunkAll 8330 (fun p => Nat.beq (LF 4 p) (wordF LAB (mw j) p)) c = true)
    (hm : heMwLit[j]! = [mw j]) (hwb : ∀ l ∈ mw j, l < 2) :
    ∀ l < 5, Good 8330 ((heLetters j).getD l #[]) (LF l) := by
  simp only [Bool.and_eq_true] at hlt
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := hlt
  have hcode : ∀ {l k : Nat}, Nat.beq (TF l) (CFSG.KD.LQT.C4141.TF k) = true →
      k < heProg.length + 2 → Good 8330 heSLP[k]! (LF l) := by
    intro l k e hk
    have eL : LF l = CFSG.KC.LQT.PW.imgW 14 (CFSG.KD.LQT.C4141.TF k) := funext fun p => by
      rw [hLF, Nat.eq_of_beq_eq_true e]
    rw [eL]
    exact He7149.good_of_rep (He7149.rep_he hk)
  have hw4 : ∀ p < 8330, LF 4 p = wordF LAB (mw j) p := fun p hp =>
    Nat.eq_of_beq_eq_true (chunkAll_sound (m := 9) (by norm_num) hw p hp)
  have hL : heLetters j = [heSLP[197]!, heSLP[207]!, heSLP[226]!, heSLP[247]!,
      wordTabA #[heTa, heTb] 8330 (mw j)] := by
    simp only [heLetters, hm, heQp, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append]
  rw [hL]
  intro l hl
  rcases l with _ | _ | _ | _ | _ | l
  · rw [List.getD_cons_zero]
    exact hcode h0 (by decide)
  · rw [List.getD_cons_succ, List.getD_cons_zero]
    exact hcode h1 (by decide)
  · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero]
    exact hcode h2 (by decide)
  · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero]
    exact hcode h3 (by decide)
  · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ,
      List.getD_cons_zero]
    have g := good_word hab (w := mw j) (fun l hl => by have := hwb l hl; simpa using this)
    exact ⟨g.1, fun p hp => by rw [hw4 p hp]; exact g.2 p hp⟩
  · omega

theorem good7 : ∀ l < 5, Good 8330 ((heLetters 7).getD l #[]) (LF7 l) := by
  have hm : heMwLit[7]! = [He7149.w7] := by decide
  have hL : heLetters 7 = heE64Lt.toList := by
    rw [He7149.lt_eq]
    simp only [heLetters, hm, heQp, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.toList_toArray]
  intro l hl
  have hs : l < heE64Lt.size := by
    rw [He7149.lt_eq]
    simpa using hl
  have g := He7149.good_lt l hs
  have e : LF7 l = He7149.LF l := funext fun p => by
    have hb : Nat.blt l 5 = true := Nat.blt_eq.mpr hl
    unfold LF7 He7149.LF
    rw [hb]
    rfl
  have ea : heE64Lt.toList.getD l #[] = heE64Lt.getD l #[] := by
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  rw [e, hL, ea]
  exact g

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem letters_of_good {E : List Γ} {T : List (Array ℕ)} (hT : genTabs n E = T)
    {L : ℕ → ℕ → ℕ} (hg : ∀ l < E.length, Good n (T.getD l #[]) (L l)) :
    ∀ l < E.length, ∀ p < n, L l p = act n (E.getD l 1) p := by
  intro l hl p hp
  rw [← ((hg l hl).2 p hp).1, ← hT]
  unfold genTabs
  rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map,
    List.getD_eq_getElem _ _ hl]
  simp [act, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem he_letters
    {j : ℕ} (hj : j < 11) :
    heCtx.D.sTabs ++ heCtx.D.mt[j]! = heLetters j := by
  have hJ : j < heCtx.J := by rw [he_J]; exact hj
  have hsT : heCtx.D.sTabs = heQp.map (fun p => heSLP[p.1]!) := by
    rw [← heCtx.hsg]
    exact he_sGens.1
  have hmt : heCtx.D.mt[j]! = (heMwLit[j]!).map (fun w => wordTabA #[heTa, heTb] 8330 w) := by
    have h := (heCtx.membersOK.2.2.2.2 j hJ).2.1
    have hmw : heCtx.D.mw = heMwLit := he_mw_lit
    rw [hmw] at h
    exact h
  rw [hsT, hmt]
  rfl

theorem gen_tabs
    {j : ℕ} (hj : j < 11) :
    genTabs 8330 (heCtx.sg ++ heCtx.gens j) = heLetters j :=
  (heCtx.Y_letters (by rw [he_J]; exact hj)).trans (he_letters hj)

theorem baseLetters
    {j : ℕ} (hj : j < 11) {L : ℕ → ℕ → ℕ}
    (hlen : (heLetters j).length = 5)
    (hg : ∀ l < 5, Good 8330 ((heLetters j).getD l #[]) (L l))
    (hinv : ∀ l < 5, ∀ c < 9, invChk L 8330 5 l c = true) :
    (heCtx.sg ++ heCtx.gens j).length = 5 ∧
      BaseLetters 8330 heB L (heCtx.sg ++ heCtx.gens j) := by
  have hT := gen_tabs hj
  have hE : (heCtx.sg ++ heCtx.gens j).length = 5 := by
    rw [← hlen, ← hT]
    simp [genTabs]
  refine ⟨hE, ⟨he_base_lt, he_base_property, ?_, ?_⟩⟩
  · rw [hE]
    have := letters_of_good hT (L := L) (by rw [hE]; exact hg)
    rwa [hE] at this
  · rw [hE]
    exact invChk_sound (m := 9) (by norm_num) hinv

theorem hat_facts
    {j : ℕ} (hj : j < 11) {L : ℕ → ℕ → ℕ}
    (hlen : (heLetters j).length = 5)
    (hg : ∀ l < 5, Good 8330 ((heLetters j).getD l #[]) (L l))
    (hinv : ∀ l < 5, ∀ c < 9, invChk L 8330 5 l c = true)
    {xs : List (List ℕ × ℕ × ℕ)} {t : List ℕ × ℕ × ℕ} {ws : List (List ℕ)}
    {pts w1 w2 : List ℕ} {vws : List (List ℕ)} {wit ex : List ℕ}
    (hc : hatChk L 8330 heB 5 xs t ws pts w1 w2 vws wit ex = true) : HeHatFacts (heCtx.Y j) := by
  obtain ⟨hE, hB⟩ := baseLetters hj hlen hg hinv
  rw [← hE] at hc
  exact ⟨_, _, hat_sound hB hc⟩

theorem ext_facts
    {j : ℕ} (hj : j < 11) {L : ℕ → ℕ → ℕ}
    (hlen : (heLetters j).length = 5)
    (hg : ∀ l < 5, Good 8330 ((heLetters j).getD l #[]) (L l))
    (hinv : ∀ l < 5, ∀ c < 9, invChk L 8330 5 l c = true)
    {xs : List (List ℕ × ℕ × ℕ)} {t : List ℕ × ℕ × ℕ} {ws : List (List ℕ)}
    {W : List (List ℕ)} {zw : List ℕ} {sq C idx ex : List ℕ}
    (hc : extChk L heB 5 xs t ws W zw sq C idx ex = true) (ht : t.1 = [])
    (hidx6 : idx.length = 6) : HeExtFacts (heCtx.Y j) := by
  obtain ⟨hE, hB⟩ := baseLetters hj hlen hg hinv
  rw [← hE] at hc
  exact ext_sound hB hc ht hidx6

theorem hat_ok {L : ℕ → ℕ → ℕ} {xs : List (List ℕ × ℕ × ℕ)} {t : List ℕ × ℕ × ℕ}
    {ws : List (List ℕ)} {pts w1 w2 : List ℕ} {vws : List (List ℕ)} {wit ex : List ℕ} {N : ℕ}
    (hN : 2 * xs.length + 3 = N)
    (h : ∀ k < N, hatPart L 8330 heB 5 xs t ws pts w1 w2 vws wit ex k = true) :
    hatChk L 8330 heB 5 xs t ws pts w1 w2 vws wit ex = true := by
  unfold hatChk
  rw [List.all_eq_true, hN]
  exact fun k hk => h k (List.mem_range.mp hk)

theorem ext_ok {L : ℕ → ℕ → ℕ} {xs : List (List ℕ × ℕ × ℕ)} {t : List ℕ × ℕ × ℕ}
    {ws : List (List ℕ)} {W : List (List ℕ)} {zw : List ℕ} {sq C idx ex : List ℕ} {N : ℕ}
    (hN : 2 * xs.length + 2 = N)
    (h : ∀ k < N, extPart L heB 5 xs t ws W zw sq C idx ex k = true) :
    extChk L heB 5 xs t ws W zw sq C idx ex = true := by
  unfold extChk
  rw [List.all_eq_true, hN]
  exact fun k hk => h k (List.mem_range.mp hk)

theorem he4167 :
    HeHatFacts (heCtx.Y 3) ∧ HeHatFacts (heCtx.Y 4) ∧ HeExtFacts (heCtx.Y 7) := by
  have l3 : (heLetters 3).length = 5 := by decide
  have l4 : (heLetters 4).length = 5 := by decide
  have l7 : (heLetters 7).length = 5 := by decide
  refine ⟨hat_facts (L := LF3) (by norm_num) l3
      (good_hat (fun _ _ => rfl) lt3_ok w3_all (by decide) (by decide)) (inv_of i3_all)
      (hat_ok (by decide) h3_all),
    hat_facts (L := LF4) (by norm_num) l4
      (good_hat (fun _ _ => rfl) lt4_ok w4_all (by decide) (by decide)) (inv_of i4_all)
      (hat_ok (by decide) h4_all),
    ext_facts (L := LF7) (by norm_num) l7 good7 (inv_of i7_all) (ext_ok (by decide) e7_all)
      (by decide) (by decide)⟩

end CFSG.KD.A312He

end
