module

public import Certificates.Kernel.AE6C2.Checks
public import Certificates.Kernel.AE6ModC.Final
public import Certificates.Kernel.AE6Sm.Facts
public import CFSG.Certificates.Kernel.AE6C2Sound
public import CFSG.Certificates.Kernel.AE6C2TSound
public import CFSG.Certificates.Kernel.Ivk8TwoNSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAE6C2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.YoshQ CFSG.KC.KGC31P CFSG.KC.AE6F CFSG.KC.AE6C2
  CFSG.KC.HeGlueK CFSG.KC.BfsPin Certificates.AE6Model Certificates.S7Twin CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.KC.Child3 (tabP)
open CFSG.KC.Ivk8N (invOK_tabN)
open CertificateChecks.KernelAE6F (RG gensRG hsz tabP_eq_tabN)
open CertificateChecks.KernelAE6ModC (PLL ppTLP allTables_plQ)
open CertificateChecks.KernelAE6Sm (chainCZ)

theorem hTLP : TLP = [TLP.getD 0 [], TLP.getD 1 [], TLP.getD 2 [], TLP.getD 3 []] := rfl

theorem rngTLP : ∀ T ∈ [TLP.getD 0 [], TLP.getD 1 [], TLP.getD 2 [], TLP.getD 3 []], ∀ t ∈ T,
    Rng t := by
  rw [← hTLP]
  intro L hL t ht
  have h := List.all_eq_true.1 (List.all_eq_true.1 CertificateChecks.KernelAE6ModC.kTRP L hL) t ht
  exact fun i hi => ((Orb.permOK_facts h).2.2 i hi).1

theorem kBasic : (c2BasicN RG PLL QS LSP && lsN QS (l3N (QS.getD 3 []) BZ CZL) == LSP) = true :=
  basicT_sound kBasicT (by rw [← hTLP] <;> rfl) rngTLP

theorem ppPLL : ∀ x ∈ PLL, PP 360 9 x :=
  PP_pfilterProducts hsz _ ppTLP _ [] (PP.id hsz) (fun _ h => absurd h List.not_mem_nil)

theorem ppCZ : ∀ L ∈ CZL, ∀ t ∈ L, PP 360 9 t := by
  have h := kTRZ
  unfold CZL CZIL trPL at *
  rw [List.zip_map', List.all_eq_true] at h
  intro L hL t ht
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hL
  have hi' := h _ (List.mem_map.2 ⟨i, hi, rfl⟩)
  rw [List.zip_map', List.all_eq_true] at hi'
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 ht
  exact PP_of_permOK2 hsz (hi' _ (List.mem_map.2 ⟨a, ha, rfl⟩))

theorem ppQS : ∀ Q ∈ QS, ∀ x ∈ Q, PP 360 9 x := by
  intro Q hQ x hx
  unfold QS qsAllN at hQ
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hQ
  exact ppPLL x (List.mem_filter.1 hx).1

theorem mem_of_getD {L : List (List Nat)} {i x : Nat} (h : x ∈ L.getD i []) : ∃ Q ∈ L, x ∈ Q := by
  rw [List.getD_eq_getElem?_getD] at h
  cases e : L[i]? with
  | none =>
    rw [e] at h
    exact absurd h List.not_mem_nil
  | some Q =>
    rw [e] at h
    exact ⟨Q, List.mem_of_getElem? e, h⟩

theorem ppQ3 : ∀ x ∈ QS.getD 3 [], PP 360 9 x := fun x hx => by
  obtain ⟨Q, hQ, hx⟩ := mem_of_getD hx
  exact ppQS Q hQ x hx

theorem hBZ : ∀ u ∈ BZ, u < 360 := by decide

theorem ppL3 : ∀ x ∈ l3N (QS.getD 3 []) BZ CZL, PP 360 9 x := by
  rw [l3N_eq hBZ kFix]
  exact PP_pfilterProducts hsz _ ppCZ _ [] (PP.id hsz) (fun _ h => absurd h List.not_mem_nil)

theorem all_congr_mem {α : Type} {p q : α → Bool} :
    ∀ (l : List α), (∀ a ∈ l, p a = q a) → l.all p = l.all q
  | [], _ => rfl
  | a :: l, h => by
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      all_congr_mem l fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem getD_map_nil (L : List (List Nat)) (i : Nat) :
    (L.map (List.map (tabN 360 9))).getD i [] = (L.getD i []).map (tabN 360 9) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[i]? <;> rfl

theorem getD_map_tabN (L : List Nat) (i d : Nat) :
    (L.map (tabN 360 9)).getD i (tabN 360 9 d) = tabN 360 9 (L.getD i d) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[i]? <;> rfl

theorem getD_map_tabN' {α : Type} (L : List α) (h : α → Nat) (i d : Nat) :
    (L.map fun a => tabN 360 9 (h a)).getD i (tabN 360 9 d) = tabN 360 9 ((L.map h).getD i d) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_map]
  cases L[i]? <;> rfl

theorem sections_map {α β : Type} (f : α → β) :
    ∀ L : List (List α), (L.map (List.map f)).sections = L.sections.map (List.map f)
  | [] => rfl
  | l :: L => by
    simp only [List.map_cons, List.sections, sections_map f L, List.flatMap_map, List.map_flatMap,
      List.map_map, Function.comp_def]

theorem c2Qs_eq : c2Qs () = QS.map (List.map (tabN 360 9)) := by
  unfold c2Qs QS qsAllN qsN
  simp only [allTables_plQ, List.map_map, Function.comp_def, List.filter_map, conjT,
    toTable_inv (by norm_num : (360 : Nat) < 2 ^ 32), gensRG.get, invT_tabN' dims,
    compT_tabN' dims, memT_tabN, conjN]

theorem commT_tabN {x q : Nat} (hx : PP 360 9 x) (hq : PP 360 9 q) :
    commT 360 (tabN 360 9 x) (tabN 360 9 q) = Nat.beq (pc 360 9 x q) (pc 360 9 q x) := by
  rw [← tabP_eq_tabN hx, ← tabP_eq_tabN hq, commT_tabP hx hq]

theorem allComm_tabN {Q : List Nat} (hQ : ∀ q ∈ Q, PP 360 9 q) {x : Nat} (hx : PP 360 9 x) :
    ((Q.map (tabN 360 9)).all fun q => commT 360 (tabN 360 9 x) q) = commAllN Q x := by
  rw [List.all_map]
  unfold commAllN
  exact all_congr_mem Q fun q hq => commT_tabN hx (hQ q hq)

theorem c2L3_eq : c2L3 () = (l3N (QS.getD 3 []) BZ CZL).map (tabN 360 9) := by
  have hL : levelTables (czQ ()) = CZL.map (List.map (tabP 360 9)) :=
    levelTables_eq chainCZ (by decide) (by decide)
  have h := filterProducts_tabP (n := 360) (w := 9)
    (f := fun T => ((QS.getD 3 []).map (tabN 360 9)).all fun q => commT 360 T q)
    (fk := commAllN (QS.getD 3 [])) (fun X hX => by
      rw [tabP_eq_tabN hX]
      exact allComm_tabN ppQ3 hX) CZL ppCZ (pidn 360 9) [] (PP.id hsz)
  rw [List.map_nil] at h
  unfold c2L3
  simp only [c2Qs_eq, getD_map_nil]
  rw [hL, idT_tabP hsz, h, ← l3N_eq hBZ kFix]
  exact List.map_congr_left fun x hx => tabP_eq_tabN (ppL3 x hx)

theorem c2Ls_eq : c2Ls () = LSP.map (List.map (tabN 360 9)) := by
  have hk : lsN QS (l3N (QS.getD 3 []) BZ CZL) = LSP :=
    eq_of_beq ((Bool.and_eq_true _ _).mp kBasic).2
  rw [← hk]
  unfold c2Ls lsN
  simp only [c2Qs_eq, c2L3_eq, List.map_map, Function.comp_def, List.filter_map]
  refine List.map_congr_left fun Q hQ => congrArg _ (List.filter_congr fun x hx => ?_)
  exact allComm_tabN (ppQS Q hQ) (ppL3 x hx)

theorem c2Basic_eq : c2Basic () = c2BasicN RG PLL QS LSP := by
  unfold c2Basic c2BasicN z0
  simp only [allTables_plQ, c2Qs_eq, c2Ls_eq, toTable_aeWord gensRG.get, memT_tabN, List.all_map,
    Function.comp_def, List.length_map, getD_map_nil, invT_tabN' dims, invOK_tabN dims]

theorem GT_eq : ((curtisPerms ()).map fun g => (toTable g, toTable g⁻¹)) =
    RG.map fun g => (tabN 360 9 g, tabN 360 9 (invN 360 9 g)) := by
  have e : ((curtisPerms ()).map fun g => (toTable g, toTable g⁻¹)) =
      ((curtisPerms ()).map toTable).map fun T => (T, invT 360 T) := by
    rw [List.map_map]
    exact List.map_congr_left fun g _ => by
      rw [Function.comp_apply, toTable_inv (by norm_num : (360 : Nat) < 2 ^ 32)]
  rw [e, gensRG.all, List.map_map]
  exact List.map_congr_left fun g _ => by rw [Function.comp_apply, invT_tabN' dims]

theorem c2Search_eq : c2Search () = (List.sections LSP).all (c2PN GTN TGN ZCN) := by
  unfold c2Search
  simp only [GT_eq, c2Ls_eq, sections_map, List.all_map]
  refine all_congr_mem _ fun cs _ => ?_
  unfold c2PN wordsN relsN idZN c2HT c2HTN wordTable wordHN GTN TGN ZCN z0
  simp only [Function.comp_apply, idT_tabN' dims, getD_map_pair, getD_map_tabN, invT_tabN' dims,
    compT_tabN' dims, foldl_tabN, toTable_aeWord gensRG.get, tblEq_tabN' dims, List.all_map,
    Function.comp_def, tableEval_tabN, toTable_mul (by norm_num : (360 : Nat) < 2 ^ 32),
    toTable_inv (by norm_num : (360 : Nat) < 2 ^ 32), gensRG.get, getD_map_tabN', Bool.or_assoc]

theorem hTG : ∀ wt ∈ TGN, ∀ i ∈ wt.1, i = 0 ∨ i = 2 ∨ i = 4 ∨ i = 6 := by
  unfold TGN
  simp only [List.forall_mem_map]
  decide

theorem c2Basic_k : c2Basic () = true :=
  c2Basic_eq.trans ((Bool.and_eq_true _ _).mp kBasic).1

theorem c2Search_k : c2Search () = true := by
  rw [c2Search_eq]
  have h := kSearch
  unfold LSP at h ⊢
  exact sections_of_treeN hTG h

end CertificateChecks.KernelAE6C2

end
