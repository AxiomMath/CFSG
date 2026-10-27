module

public import Certificates.Kernel.AE6Core.Checks
public import Certificates.Kernel.AE6F.Final
public import CFSG.Certificates.Kernel.AE6CoreParse
public import CFSG.Certificates.Kernel.AE6TriSound
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.TwinFactsQ8Spec

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAE6Core

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.YoshQ CFSG.KC.KGC31P CFSG.KC.BfsPin
  CFSG.KC.HeGlueK CFSG.KC.AE6F CFSG.KC.AE6Tri CFSG.KC.AE6Core CFSG.KS.SporSch.MOC
  Certificates.AE6Model Certificates.S7Twin CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Co2.Native CertificateChecks.KernelAE6F
open CFSG.KC.Child3 (tabP)

theorem hn32 : (360 : Nat) < 2 ^ 32 := by norm_num

theorem gens_ok : ae6Gens () = true := by
  unfold ae6Gens
  rw [List.all_eq_true]
  intro l hl
  have hl8 : l < 8 := List.mem_range.1 hl
  have hp := ppS (j := l) (by omega)
  have ht : curtisArr l = unpack 360 9 (CertificateChecks.KernelO8.AP.S l) :=
    CertificateChecks.KernelO8.genAP.2 l (by omega)
  rw [ht, invCand_PP hp]
  exact invPairB_of (rep_sg hp) (rep_sg_inv hp)

theorem curtis_sq (l : Nat) : (curtisPerms ()).getD l 1 * (curtisPerms ()).getD l 1 = 1 := by
  by_cases hl : l < 8
  · apply (CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Twin.sqOneT_iff hn32
      (rep_toTable hn32 _)).1
    unfold sqOneT
    rw [gensRG.get, compT_tabN' dims, idT_tabN' dims, tblEq_tabN' dims]
    have hm : RG.getD l (pidn 360 9) ∈ RG := by
      rw [List.getD_eq_getElem _ _ (by simp [RG]; omega)]
      exact List.getElem_mem _
    exact List.all_eq_true.1 kInv _ hm
  · rw [List.getD_eq_default _ _ (by simp [curtisPerms]; omega), mul_one]

theorem curtis_inv (l : Nat) : ((curtisPerms ()).getD l 1)⁻¹ = (curtisPerms ()).getD l 1 :=
  inv_eq_of_mul_eq_one_right (curtis_sq l)

theorem evalCodes_eq : ∀ w : List ℤ,
    evalCodes (curtisPerms ()) w = aeWord (curtisPerms ()) (w.map fun z => z.natAbs - 1)
  | [] => by simp [evalCodes, aeWord]
  | z :: w => by
    rw [evalCodes, evalCodes_eq w]
    unfold aeWord
    rw [List.map_cons, List.map_cons, List.prod_cons]
    congr 1
    split_ifs with hz
    · congr 1
      omega
    · rw [curtis_inv]
      congr 1
      omega

theorem cWords_map : (cWords ()).map (List.map fun z => z.natAbs - 1) = cwN CW.chars := by
  rw [CW.eq, parseWords_ofList _ kToks]
  rfl

theorem cPerms_eq : cPerms () = (cwN CW.chars).map (aeWord (curtisPerms ())) := by
  unfold cPerms
  simp only
  rw [← cWords_map, List.map_map]
  exact List.map_congr_left fun w _ => evalCodes_eq w

theorem comm_ok : ae6CComm () = true := by
  unfold ae6CComm z0
  simp only
  rw [cPerms_eq, List.all_map, List.all_eq_true]
  intro c hc
  have h := kComm
  unfold commAllN at h
  rw [Orb.strictB_eq] at h
  obtain ⟨i, hi⟩ := allIx_mem h c hc
  rw [Orb.strictB_eq] at hi
  simp only [Function.comp_apply]
  unfold commT
  rw [toTable_aeWord gensRG.get, toTable_aeWord gensRG.get, compT_tabN' dims, compT_tabN' dims,
    tblEq_tabN' dims]
  exact hi

theorem tab_conj (c x : List Nat) :
    toTable (aeWord (curtisPerms ()) c * aeWord (curtisPerms ()) x * (aeWord (curtisPerms ()) c)⁻¹) =
      tabN 360 9 (pmN 360 9 (pmN 360 9 (awN RG c) (awN RG x)) (invN 360 9 (awN RG c))) := by
  rw [toTable_mul hn32, toTable_mul hn32, toTable_inv hn32, toTable_aeWord gensRG.get,
    toTable_aeWord gensRG.get, compT_tabN' dims, invT_tabN' dims, compT_tabN' dims]

@[expose] noncomputable def conjL (C : List (List Nat)) : List (Equiv.Perm (Fin 360)) :=
  (C.map (aeWord (curtisPerms ()))).flatMap fun c =>
    (kWords.map (aeWord (curtisPerms ()))).map fun x => c * x * c⁻¹

@[expose] noncomputable def plF (PS : Nat → Nat) (i : Nat) (c : List Nat) : Bool :=
  strictB (awN RG c) fun X => strictB (invN 360 9 X) fun XI =>
    allIx kWords (fun t x =>
      Nat.beq (PS (Nat.add (Nat.mul 2 i) t)) (pmN 360 9 (pmN 360 9 X (awN RG x)) XI)) 0

theorem conjL_length : ∀ C : List (List Nat), (conjL C).length = 2 * C.length
  | [] => by simp [conjL]
  | c :: C => by
    have ih := conjL_length C
    simp only [conjL, List.map_cons, List.flatMap_cons, List.length_append, List.length_map,
      List.length_cons] at ih ⊢
    rw [ih]
    simp [kWords]
    omega

theorem conjL_img (PS : Nat → Nat) : ∀ (C : List (List Nat)) (i₀ : Nat),
    allIx C (plF PS) i₀ = true →
    ∀ j < (conjL C).length, toTable ((conjL C).getD j 1) = tabN 360 9 (PS (2 * i₀ + j))
  | [], _, _, j, hj => by simp [conjL] at hj
  | c :: C, i₀, h, j, hj => by
    have hall := (allIx_iff _ _ i₀).1 h
    have h0 : plF PS i₀ c = true := by
      have := hall 0 (by simp)
      rwa [Nat.add_zero, List.getElem_cons_zero] at this
    have hC : allIx C (plF PS) (i₀ + 1) = true := (allIx_iff _ _ (i₀ + 1)).2 fun i hi => by
      have := hall (i + 1) (by simp; omega)
      rwa [List.getElem_cons_succ, show i₀ + (i + 1) = i₀ + 1 + i by omega] at this
    have hA : conjL (c :: C) = ((kWords.map (aeWord (curtisPerms ()))).map fun x =>
        aeWord (curtisPerms ()) c * x * (aeWord (curtisPerms ()) c)⁻¹) ++ conjL C := by
      simp only [conjL, List.map_cons, List.flatMap_cons]
    have hlen : ((kWords.map (aeWord (curtisPerms ()))).map fun x =>
        aeWord (curtisPerms ()) c * x * (aeWord (curtisPerms ()) c)⁻¹).length = 2 := by
      simp [kWords]
    rw [hA] at hj ⊢
    by_cases hj2 : j < 2
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_eq_getElem _ _ (by omega),
        List.getElem_map, List.getElem_map, tab_conj]
      unfold plF at h0
      rw [Orb.strictB_eq, Orb.strictB_eq] at h0
      have ht := (allIx_iff _ _ 0).1 h0 j (by simp [kWords]; omega)
      rw [Nat.zero_add] at ht
      exact congrArg (tabN 360 9) (Nat.eq_of_beq_eq_true ht).symm
    · rw [List.getD_append_right _ _ _ _ (by omega), hlen]
      rw [List.length_append, hlen] at hj
      rw [conjL_img PS C (i₀ + 1) hC (j - 2) (by omega)]
      congr 2
      omega

theorem plGens_eq : plGens () = conjL (cwN CW.chars) := by
  unfold plGens k0Gens
  simp only
  rw [cPerms_eq]
  rfl

theorem plGens_img : ∀ j < (plGens ()).length,
    imageList ((plGens ()).getD j 1) = (unpack 360 9 (PL.S j)).toList := by
  intro j hj
  rw [plGens_eq] at hj ⊢
  apply imageList_of_tabN
  have := conjL_img PL.S (cwN CW.chars) 0 kPL j hj
  rwa [Nat.mul_zero, Nat.zero_add] at this

theorem cwN_length : (cwN CW.chars).length = 4 :=
  Nat.eq_of_beq_eq_true kLen

theorem plGens_length : (plGens ()).length = 8 := by
  rw [plGens_eq, conjL_length, cwN_length]

theorem chainPL : ChainK 360 9 (plGens ()) plDerive (#v[0, 2, 4, 8] : Vector (Fin 360) 4)
    PL.S PL.SI PL.LR PL.TR PL.TRI 12 PL.BP PL.NS 24 :=
  ⟨by norm_num, by norm_num, by norm_num, plGens_img, by decide,
    by rw [plGens_length]; exact PL.head, PL.hl, by decide, PL.hs⟩

theorem ordPL : ordK PL.LR 4 = 512 := by decide +kernel

theorem ordW : ordK W.LR 1 = 64 := by decide +kernel

theorem plQ_ok : (plQ ()).check = true ∧ (plQ ()).orderCertificate = 512 := by
  unfold plQ
  rw [← ordPL]
  exact chainK_check (by norm_num) (by decide) chainPL

theorem wQ_ok : (wQ ()).check = true ∧ (wQ ()).orderCertificate = 64 := by
  unfold wQ
  rw [← ordW]
  exact chainK_check (by norm_num) (by decide) chainW

theorem chains_ok : ae6CChains () = true := by
  unfold ae6CChains
  simp only
  rw [plQ_ok.1, plQ_ok.2, wQ_ok.1, wQ_ok.2]
  rfl

end CertificateChecks.KernelAE6Core

end
