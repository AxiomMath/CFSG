module

public import Certificates.Kernel.AE6FW.Checks
public import Certificates.Kernel.AE6Core.Final
public import CFSG.Certificates.Kernel.AE6FWSound
public import Certificates.Data.AE6ModelFW

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAE6FW

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.YoshQ CFSG.KC.KGC31P CFSG.KC.BfsPin
  CFSG.KC.HeGlueK CFSG.KC.AE6F CFSG.KC.AE6Core CFSG.KC.AE6FW CFSG.KS.SporSch.MOC
  Certificates.AE6Model Certificates.S7Twin Certificates.S5Rows CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Monster.B.Mathieu CFSG.Monster.B.Co2.Native
open CFSG.KC.Child3 (tabP)
open CertificateChecks.KernelAE6F (RG WL gensRG allTables_wQ hsz tabP_eq_tabN toTable_eq_tabN
  prep_curtis imageList_of_tabN)
open CertificateChecks.KernelAE6Core (cPerms_eq tab_conj hn32)
open CertificateChecks.KernelAE6Q8

theorem sc_gen : ∀ l < 4, SC.S l = CertificateChecks.KernelO8.AP.S (2 * l) := by
  intro l hl
  interval_cases l <;> decide

theorem sGens_img : ∀ j < (sGens ()).length,
    imageList ((sGens ()).getD j 1) = (unpack 360 9 (SC.S j)).toList := by
  intro j hj
  have hl : (sGens ()).length = 4 := by
    unfold sGens
    simp only [List.length_map]
    rfl
  have hj4 : j < 4 := hl ▸ hj
  have e : (sGens ()).getD j 1 = (curtisPerms ()).getD (2 * j) 1 := by
    rw [List.getD_eq_getElem _ _ hj]
    unfold sGens
    simp only [List.getElem_map]
    congr 1
    interval_cases j <;> rfl
  rw [e, sc_gen j hj4]
  exact imageList_of_tabN (toTable_eq_tabN (prep_curtis (by omega)))

theorem chainS : ChainK 360 9 (sGens ()) sDerive (#v[0, 2, 4, 24, 8] : Vector (Fin 360) 5)
    SC.S SC.SI SC.LR SC.TR SC.TRI 7 SC.BP SC.NS 24 :=
  ⟨by norm_num, by norm_num, by norm_num, sGens_img, by decide, SC.head, SC.hl, by decide, SC.hs⟩

theorem ppTLS : ∀ L ∈ trPL 360 9 SC.LR SC.TR 5, ∀ t ∈ L, PP 360 9 t := fun L hL t ht =>
  PP_of_permOK hsz (List.all_eq_true.1 (List.all_eq_true.1 kTRS L hL) t ht)

theorem allTables_sQ : allTables (sQ ()) = SL.map (tabN 360 9) := by
  have hL : levelTables (sQ ()) = (trPL 360 9 SC.LR SC.TR 5).map (List.map (tabP 360 9)) :=
    levelTables_eq chainS (by decide) (by decide)
  have h := filterProducts_tabP (n := 360) (w := 9) (f := allTrue) (fk := fun _ => true)
    (fun _ _ => rfl) _ ppTLS (pidn 360 9) [] (PP.id hsz)
  rw [List.map_nil] at h
  rw [allTables, hL, idT_tabP hsz, h]
  unfold SL
  exact List.map_congr_left fun x hx => tabP_eq_tabN (PP_pfilterProducts hsz _ ppTLS _ []
    (PP.id hsz) (fun _ h => absurd h List.not_mem_nil) x hx)

theorem twinPairs_eq : twinPairs () = (cwN CertificateChecks.KernelAE6Core.CW.chars).map fun c =>
    (aeWord (curtisPerms ()) c * aeWord (curtisPerms ()) (kWords.getD 0 []) *
        (aeWord (curtisPerms ()) c)⁻¹,
      aeWord (curtisPerms ()) c * aeWord (curtisPerms ()) (kWords.getD 1 []) *
        (aeWord (curtisPerms ()) c)⁻¹) := by
  unfold twinPairs k0Gens
  simp only
  rw [cPerms_eq, List.map_map]
  rfl

theorem getD_map_tab {γ : Type} (L : List γ)
    (F : γ → Equiv.Perm (Fin 360) × Equiv.Perm (Fin 360)) (G : γ → Nat × Nat) (k : Nat)
    (h : ∀ c, toTable (F c).1 = tabN 360 9 (G c).1 ∧ toTable (F c).2 = tabN 360 9 (G c).2) :
    toTable ((L.map F).getD k (1, 1)).1 = tabN 360 9 ((L.map G).getD k (pidn 360 9, pidn 360 9)).1 ∧
      toTable ((L.map F).getD k (1, 1)).2 =
        tabN 360 9 ((L.map G).getD k (pidn 360 9, pidn 360 9)).2 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_map]
  cases L[k]? with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    exact ⟨(toTable_one hn32).trans (idT_tabN' dims), (toTable_one hn32).trans (idT_tabN' dims)⟩
  | some c =>
    simp only [Option.map_some, Option.getD_some]
    exact h c

theorem tp_getD (k : Nat) :
    toTable ((twinPairs ()).getD k (1, 1)).1 = tabN 360 9 (TPN.getD k (pidn 360 9, pidn 360 9)).1 ∧
      toTable ((twinPairs ()).getD k (1, 1)).2 =
        tabN 360 9 (TPN.getD k (pidn 360 9, pidn 360 9)).2 := by
  rw [twinPairs_eq, TPN, twinPairsN]
  exact getD_map_tab _ _ _ k fun c => ⟨tab_conj c _, tab_conj c _⟩

theorem q8Span_tab {i j : Equiv.Perm (Fin 360)} {a b : Nat} (hi : toTable i = tabN 360 9 a)
    (hj : toTable j = tabN 360 9 b) :
    (q8Span i j).map toTable = (q8SpanN a b).map (tabN 360 9) := by
  simp only [q8Span, q8SpanN, List.map_cons, List.map_nil, pow_two, toTable_mul hn32,
    toTable_inv hn32, toTable_one hn32, hi, hj, compT_tabN' dims, invT_tabN' dims,
    idT_tabN' dims]

theorem filter_tab (L : List Nat) :
    ((L.map (tabN 360 9)).filter fun X => !sqOneT 360 X) =
      (L.filter fun X => !sqOneN X).map (tabN 360 9) := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro x _
  simp only [Function.comp_apply, sqOneT, sqOneN, compT_tabN' dims, idT_tabN' dims,
    tblEq_tabN' dims]

theorem frameCands_eq (k : Nat) :
    frameCands (twinPairs ()) k = (frameCandsN TPN k).map (tabN 360 9) := by
  unfold frameCands frameCandsN
  simp only
  rw [q8Span_tab (tp_getD k).1 (tp_getD k).2, filter_tab]

theorem fwComm_eq : fwComm () = fwCommN WL := by
  unfold fwComm fwCommN
  simp only [allTables_wQ, List.all_map, Function.comp_def, commT_tabN]

theorem fwInS_eq : fwInS () = fwInSN SL WL := by
  unfold fwInS fwInSN
  simp only [allTables_sQ, allTables_wQ, List.all_map, Function.comp_def, memT_tabN]

theorem fwNorm_eq : fwNorm () = fwNormN TPN WL := by
  unfold fwNorm fwNormN TPN twinPairsN
  simp only [allTables_wQ, twinPairs_eq, List.all_map, Function.comp_def, q8Span, q8SpanN,
    List.all_cons, List.all_nil, pow_two, toTable_mul hn32, toTable_inv hn32, toTable_one hn32,
    toTable_aeWord gensRG.get, conjT, conjN, memT_tabN, compT_tabN' dims, invT_tabN' dims,
    idT_tabN' dims]

theorem fwMeet_eq : fwMeet () = fwMeetN TPN WL := by
  unfold fwMeet fwMeetN TPN twinPairsN sqOneN
  simp only [allTables_wQ, twinPairs_eq, List.all_map, List.any_map, Function.comp_def, q8Span,
    q8SpanN, List.all_cons, List.all_nil, List.any_cons, List.any_nil, pow_two,
    toTable_mul hn32, toTable_inv hn32, toTable_one hn32, toTable_aeWord gensRG.get, memT,
    CFSG.KC.AE6F.memN,
    sqOneT, compT_tabN' dims, invT_tabN' dims, idT_tabN' dims, tblEq_tabN' dims]

theorem fwFrames_tab : fwFrames () = framesG (SL.map (tabN 360 9))
    ((frameCandsN TPN 0).map (tabN 360 9)) ((frameCandsN TPN 1).map (tabN 360 9))
    ((frameCandsN TPN 2).map (tabN 360 9)) ((frameCandsN TPN 3).map (tabN 360 9))
    (fun T X => commT 360 T X) (fun T X => commT 360 T X) (fun T X => commT 360 T X)
    (fun T X => commT 360 T X) (fun X => (WL.map (tabN 360 9)).all fun T => commT 360 T X)
    (fun X => (WL.map (tabN 360 9)).all fun T => commT 360 T X)
    (fun X => (WL.map (tabN 360 9)).all fun T => commT 360 T X)
    (fun X => (WL.map (tabN 360 9)).all fun T => commT 360 T X) := by
  unfold fwFrames framesG
  simp only [allTables_sQ, allTables_wQ, frameCands_eq, all_and2]

theorem KA_length : KA.length = (frameCandsN TPN 0).length + (frameCandsN TPN 1).length +
    (frameCandsN TPN 2).length + (frameCandsN TPN 3).length := by
  simp only [KA, List.length_append]
  omega

theorem hK0 : frameCandsN TPN 0 =
    (List.range' 0 (frameCandsN TPN 0).length).map fun i => KA.getD i 0 := by
  unfold KA
  have h := range'_getD [] (frameCandsN TPN 0) (frameCandsN TPN 1 ++ (frameCandsN TPN 2 ++
    frameCandsN TPN 3))
  rw [List.nil_append, List.length_nil] at h
  exact h.symm

theorem hK1 : frameCandsN TPN 1 =
    (List.range' (frameCandsN TPN 0).length (frameCandsN TPN 1).length).map
      fun i => KA.getD i 0 := by
  unfold KA
  exact (range'_getD (frameCandsN TPN 0) (frameCandsN TPN 1)
    (frameCandsN TPN 2 ++ frameCandsN TPN 3)).symm

theorem hK2 : frameCandsN TPN 2 =
    (List.range' ((frameCandsN TPN 0).length + (frameCandsN TPN 1).length)
      (frameCandsN TPN 2).length).map fun i => KA.getD i 0 := by
  unfold KA
  have h := range'_getD (frameCandsN TPN 0 ++ frameCandsN TPN 1) (frameCandsN TPN 2)
    (frameCandsN TPN 3)
  rw [List.length_append, List.append_assoc] at h
  exact h.symm

theorem hK3 : frameCandsN TPN 3 =
    (List.range' ((frameCandsN TPN 0).length + (frameCandsN TPN 1).length +
      (frameCandsN TPN 2).length) (frameCandsN TPN 3).length).map fun i => KA.getD i 0 := by
  unfold KA
  have h := range'_getD (frameCandsN TPN 0 ++ frameCandsN TPN 1 ++ frameCandsN TPN 2)
    (frameCandsN TPN 3) []
  rw [List.length_append, List.length_append, List.append_nil, List.append_assoc,
    List.append_assoc] at h
  exact h.symm

theorem fwFrames_eq : fwFrames () = fwFramesI SIG WB (frameCandsN TPN 0).length
    (frameCandsN TPN 1).length (frameCandsN TPN 2).length (frameCandsN TPN 3).length := by
  rw [fwFrames_tab, framesG_mapS, framesG_mapK]
  simp only [commT_tabN, List.all_map, Function.comp_def]
  rw [fwFramesI, SIG, framesG_mapS]
  conv_lhs => rw [hK0, hK1, hK2, hK3]
  rw [framesG_mapK]
  have hlt : ∀ {s n i : Nat}, s + n ≤ KA.length → i ∈ List.range' s n → i < KA.length :=
    fun h hi => lt_of_mem_range' KA h hi
  apply framesG_congr <;> intro i hi <;> refine ⟨funext fun T => ?_, ?_⟩ <;>
    simp only [WB, testBit_bitsOf] <;>
    rw [getD_map_lt _ (hlt (by have := KA_length; omega) hi)]

theorem fwComm_k : fwComm () = true := fwComm_eq.trans kComm

theorem fwInS_k : fwInS () = true :=
  fwInS_eq.trans (Bool.and_eq_true_iff.1 kInSFrames).1

theorem fwNorm_k : fwNorm () = true := fwNorm_eq.trans kNorm

theorem fwMeet_k : fwMeet () = true := fwMeet_eq.trans kMeet

theorem fwFrames_k : fwFrames () = true :=
  fwFrames_eq.trans (Bool.and_eq_true_iff.1 kInSFrames).2

end CertificateChecks.KernelAE6FW

end
