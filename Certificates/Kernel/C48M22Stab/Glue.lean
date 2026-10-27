module

public import Certificates.Kernel.C48M22Stab.All
public import Certificates.Kernel.C48M22Stab.ChainChecks
public import Certificates.Kernel.KGC31M22.Facts
public import CFSG.Certificates.Kernel.Misc.Coset.StabSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelC48M22

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P CFSG.KS.SporSch.MOC CFSG.KC.Child3
open CFSG.Quasithin.KGC31.Native CFSG.Certificates.CosetEnumeration
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu
open CFSG.Sporadic.Recognition.M22Multiplier CFSG.Quasithin.C48Cover CFSG.Quasithin.KGC31.M22
open CFSG.Monster.B.Mathieu CFSG.CosetTable CertificateChecks.KernelSporSch
open CertificateChecks.KernelKGC31M22

theorem evalCodes_append' (S : List (Equiv.Perm (Fin 22))) (a b : List ℤ) :
    evalCodes S (a ++ b) = evalCodes S a * evalCodes S b := by
  induction a with
  | nil => simp [evalCodes]
  | cons z a ih => rw [List.cons_append, evalCodes, evalCodes, ih, mul_assoc]

theorem getD_AB (i : Fin 2) :
    [m22gA, m22gB].getD i.val 1 = if i = 0 then m22gA else m22gB := by
  fin_cases i <;> rfl

theorem letterAB_eq (l : Fin 2 × Bool) : letterAB l = evalCodes [m22gA, m22gB] [zOf l] := by
  obtain ⟨i, b⟩ := l
  rw [evalCodes, evalCodes, mul_one]
  cases b
  · have h1 : ¬ (0 < zOf (i, false)) := Int.not_lt.2 (Int.negSucc_lt_zero _).le
    have h2 : (-zOf (i, false)).toNat - 1 = i.val := rfl
    rw [if_neg h1, h2, getD_AB]
    by_cases h : i = 0 <;> simp only [letterAB, h, Bool.false_eq_true, ↓reduceIte]
  · have h1 : 0 < zOf (i, true) := Int.ofNat_succ_pos _
    have h2 : (zOf (i, true)).toNat - 1 = i.val := rfl
    rw [if_pos h1, h2, getD_AB]
    by_cases h : i = 0 <;> simp only [letterAB, h, ↓reduceIte]

theorem letterAB_not (l : Fin 2 × Bool) : letterAB (l.1, !l.2) = (letterAB l)⁻¹ := by
  obtain ⟨i, b⟩ := l
  cases b <;> by_cases h : i = 0 <;>
    simp only [letterAB, h, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, inv_inv]

theorem permAB_append (u v : List (Fin 2 × Bool)) : permAB (u ++ v) = permAB u * permAB v := by
  rw [permAB, permAB, permAB, List.map_append, List.prod_append]

theorem permAB_cons (l : Fin 2 × Bool) (w : List (Fin 2 × Bool)) :
    permAB (l :: w) = letterAB l * permAB w := by
  rw [permAB, permAB, List.map_cons, List.prod_cons]

theorem permAB_eq (w : List (Fin 2 × Bool)) : permAB w = evalCodes [m22gA, m22gB] (w.map zOf) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [permAB_cons, ih, letterAB_eq, ← evalCodes_append']
    rfl

theorem permAB_invRev (w : List (Fin 2 × Bool)) : permAB (FreeGroup.invRev w) = (permAB w)⁻¹ := by
  induction w with
  | nil => exact inv_one.symm
  | cons l w ih =>
    have e : FreeGroup.invRev [l] = [(l.1, !l.2)] := rfl
    have e1 : permAB [(l.1, !l.2)] = letterAB (l.1, !l.2) := by
      rw [permAB_cons]
      exact mul_one _
    rw [FreeGroup.invRev_cons, permAB_append, ih, e, e1, letterAB_not, permAB_cons l w, mul_inv_rev]

theorem permGen_eq (w : List (Fin 2 × Bool)) : permGen w = permAB (substWord m22GenWords w) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [substWord, List.flatMap_cons, permAB_append, ← substWord, ← ih, permGen, List.map_cons,
      List.prod_cons, ← permGen]
    congr 1
    obtain ⟨i, b⟩ := l
    cases b <;> simp [genPerm, tab_eq, permAB_invRev]

theorem img_eW (j : ℕ) {P : ℕ} (hw : abOK (eW j) = true)
    (h : Nat.beq (abWordK 22 5 (mask 5) (pidn 22 5) (M22Q.S 0) (M22Q.SI 0) (M22Q.S 1) (M22Q.SI 1)
      (eW j)) P = true) :
    imageList (tab (permGen (m22Word (e8NormW.getD j [])))) = (unpack 22 5 P).toList := by
  rw [tab_eq, permGen_eq, permAB_eq]
  exact M22OC.img_word hw h

theorem img_e8Gen : ∀ j < e8Gen.length, imageList (e8Gen.getD j 1) = (unpack 22 5 (CE8.S j)).toList := by
  intro j hj
  have hj2 : j < 2 := hj
  interval_cases j
  · exact img_eW 0 kA0 kW0
  · exact img_eW 1 kA1 kW1

theorem chainE8 : ChainK 22 5 e8Gen e8ChainW (#v[0, 1, 2] : Vector (Fin 22) 3)
    CE8.S CE8.SI CE8.LR CE8.TR CE8.TRI 5 CE8.BP 2 16 :=
  ⟨by norm_num, by norm_num, by norm_num, img_e8Gen, by decide, CE8.head, CE8.hl, by norm_num,
    CE8.hs⟩

theorem card8 : Nat.card (Subgroup.closure {g : Equiv.Perm (Fin 22) | g ∈ e8Gen}) = 1344 := by
  obtain ⟨hc, ho⟩ := chainK_check (by decide) (by decide) chainE8
  have hQ : e8Chain.originalSubgroup = Subgroup.closure {g | g ∈ e8Gen} :=
    certificate_originalSubgroup _ _ _ _ _
  rw [← hQ, ← e8Chain.orderCertificate_eq_card hc]
  exact ho.trans (Nat.eq_of_beq_eq_true kOrd)

theorem toTable_e8Gen (j : ℕ) (hj : j < 2) : toTable (e8Gen.getD j 1) = tabP 22 5 (CE8.S j) :=
  CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img (img_e8Gen j hj)

theorem masks8 : ((e8Gen.zip e8Masks).all fun p => masksOK 22 e8T (toTable p.1) p.2) = true := by
  have e : e8Gen.zip e8Masks = [(e8Gen.getD 0 1, [1, 4, 2]), (e8Gen.getD 1 1, [5, 3, 7])] := rfl
  rw [e, List.all_cons, List.all_cons, List.all_nil, Bool.and_true, toTable_e8Gen 0 (by norm_num),
    toTable_e8Gen 1 (by norm_num), e8T, mapW,
    masksOK_tabP hsz (ppL e8W) (CFSG.KC.HeGlueK.PP_of_permOK2 hsz kP0),
    masksOK_tabP hsz (ppL e8W) (CFSG.KC.HeGlueK.PP_of_permOK2 hsz kP1)]
  exact Bool.and_eq_true_iff.2 ⟨kM0, kM1⟩

theorem stab8 :
    ∃ S : Subgroup (PresentedGroup {r : FreeGroup (Fin 2) | r ∈ m22Cover.map FreeGroup.mk}),
      (∀ u ∈ e8SubW, PresentedGroup.mk _ (FreeGroup.mk u) ∈ S) ∧
        PresentedGroup.mk _ (FreeGroup.mk m22B11) ∉ S := by
  have hr : codes m22Cover = CFSG.KAct.C48M22.rels := by decide +kernel
  have hf : codes e8SubW = CFSG.KAct.C48M22.fix := by decide +kernel
  have hm : codes [m22B11] = CFSG.KAct.C48M22.move := by decide +kernel
  obtain ⟨S, h1, h2⟩ := CFSG.KC.MiscCoset.Act.stab_sound m22Cover hr (N := 660) (by norm_num)
    (CFSG.KC.MiscCoset.Act.pointOK_of_allR CFSG.KAct.C48M22.all) e8SubW [m22B11] hf hm
    CFSG.KAct.C48M22.fix0 CFSG.KAct.C48M22.moves
  exact ⟨S, h1, h2 m22B11 (List.mem_singleton_self _)⟩

open CFSG.Sporadic.Th.Native CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.M22
  CFSG.Sporadic.Recognition.M22Multiplier CFSG.Sporadic.Schreier in
open Certificates in
theorem cert7221 : Nat.card (Subgroup.closure {g : Equiv.Perm (Fin 22) | g ∈ CFSG.Quasithin.C48Cover.e8Gen}) =
      1344 ∧
    ((CFSG.Quasithin.C48Cover.e8Gen.zip CFSG.Quasithin.C48Cover.e8Masks).all
      fun p => masksOK 22 e8T (toTable p.1) p.2) = true ∧
    ∃ S : Subgroup (PresentedGroup {r : FreeGroup (Fin 2) | r ∈ m22Cover.map FreeGroup.mk}),
      (∀ u ∈ CFSG.Quasithin.C48Cover.e8SubW, PresentedGroup.mk _ (FreeGroup.mk u) ∈ S) ∧
        PresentedGroup.mk _ (FreeGroup.mk m22B11) ∉ S := ⟨card8, masks8, stab8⟩

end CertificateChecks.KernelC48M22

end
