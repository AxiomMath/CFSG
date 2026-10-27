module

public import Certificates.Kernel.AE6F.Checks
public import Certificates.Kernel.OmegaEight.Aut
public import CFSG.Certificates.Kernel.AE6FSound
public import CFSG.Certificates.Kernel.KGC31PBSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAE6F

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.YoshQ CFSG.KC.KGC31P CFSG.KC.BfsPin
  CFSG.KC.HeGlueK CFSG.KC.AE6F CFSG.KS.SporSch.MOC Certificates.AE6Model Certificates.S7Twin
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Monster.B.Mathieu CFSG.Monster.B.Co2.Native
open CFSG.KC.Child3 (tabP)

theorem hsz : szOK 360 9 = true := by decide

theorem perm_head {n w kS kO nb BP : Nat} {PS PSI : Nat → Nat} {D : List (List Int)}
    (h : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true) :
    allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true := by
  unfold headK at h
  simp only [bAnd_iff] at h
  exact h.2.2.2.2.1

theorem ppS {j : Nat} (hj : j < 18) : PP 360 9 (CertificateChecks.KernelO8.AP.S j) :=
  PP_of_permOK2 hsz (allN_spec (perm_head CertificateChecks.KernelO8.AP.head) j hj)

theorem toTable_eq_tabN {X : Nat} {g : Equiv.Perm (Fin 360)} (h : Orb.PRep 360 9 X g) :
    toTable g = tabN 360 9 X := by
  apply Array.ext (by simp [toTable, tabN])
  intro i h1 _
  have hi : i < 360 := by simpa [toTable] using h1
  simp only [toTable, tabN, Array.getElem_ofFn]
  rw [pg_mod hi]
  exact congrArg UInt32.ofNat (h ⟨i, hi⟩).symm

theorem prep_sg {X : Nat} (hX : PP 360 9 X) : Orb.PRep 360 9 X (sg 360 9 X) := fun x =>
  (Orb.unpack_get x.isLt).symm.trans (rep_sg hX x)

theorem tabP_eq_tabN {X : Nat} (hX : PP 360 9 X) : tabP 360 9 X = tabN 360 9 X := by
  rw [tabP_eq hX]
  exact toTable_eq_tabN (prep_sg hX)

theorem invPairB_of {t r : Array Nat} {g : Equiv.Perm (Fin 360)}
    (ht : CFSG.Monster.B.Co2.Rep 360 t g) (hr : CFSG.Monster.B.Co2.Rep 360 r g⁻¹) :
    invPairB 360 t r = true := by
  simp only [invPairB, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    beq_iff_eq]
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have e : t[i]! = g ⟨i, hi⟩ := ht ⟨i, hi⟩
    rw [e, hr (g ⟨i, hi⟩)]
    exact ⟨(g _).isLt, by simp⟩
  · have e : r[i]! = g⁻¹ ⟨i, hi⟩ := hr ⟨i, hi⟩
    rw [e, ht (g⁻¹ ⟨i, hi⟩)]
    exact ⟨(g⁻¹ _).isLt, by simp⟩

theorem getD_curtis {l : Nat} (hl : l < 8) :
    (curtisPerms ()).getD l 1 = permOfInv 360 (curtisArr l) (invCand 360 (curtisArr l)) := by
  rw [curtisPerms, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl]
  rfl

theorem prep_curtis {l : Nat} (hl : l < 8) :
    Orb.PRep 360 9 (CertificateChecks.KernelO8.AP.S l) ((curtisPerms ()).getD l 1) := by
  have hp := ppS (j := l) (by omega)
  have ht : curtisArr l = unpack 360 9 (CertificateChecks.KernelO8.AP.S l) :=
    CertificateChecks.KernelO8.genAP.2 l (by omega)
  have hinv : invPairB 360 (curtisArr l) (invCand 360 (curtisArr l)) = true := by
    rw [ht, invCand_PP hp]
    exact invPairB_of (rep_sg hp) (rep_sg_inv hp)
  rw [getD_curtis hl]
  intro x
  unfold permOfInv
  rw [dif_pos hinv]
  change _ = (curtisArr l)[x.val]!
  rw [ht, Orb.unpack_get x.isLt]

theorem getD_RG {l : Nat} (hl : l < 8) : RG.getD l (pidn 360 9) = CertificateChecks.KernelO8.AP.S l := by
  rw [RG, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl]
  rfl

theorem gensRG : Gens RG where
  get l := by
    by_cases hl : l < 8
    · rw [toTable_eq_tabN (prep_curtis hl), getD_RG hl]
    · have e1 : (curtisPerms ()).getD l 1 = 1 := by
        rw [List.getD_eq_default]
        simp [curtisPerms]
        omega
      have e2 : RG.getD l (pidn 360 9) = pidn 360 9 := by
        rw [List.getD_eq_default]
        simp [RG]
        omega
      rw [e1, e2, toTable_one (by norm_num), idT_tabN' dims]
  all := by
    apply List.ext_getElem (by simp [curtisPerms, RG])
    intro l h1 h2
    have hl : l < 8 := by simpa [curtisPerms] using h1
    rw [List.getElem_map, List.getElem_map, ← List.getD_eq_getElem _ 1,
      toTable_eq_tabN (prep_curtis hl), ← getD_RG hl, List.getD_eq_getElem]

theorem imageList_of_tabN {X : Nat} {g : Equiv.Perm (Fin 360)} (h : toTable g = tabN 360 9 X) :
    imageList g = (unpack 360 9 X).toList := by
  unfold imageList unpack
  rw [Array.toList_ofFn]
  congr 1
  funext i
  have e := rep_toTable (n := 360) (by norm_num) g i.val i.isLt
  rw [h, ap_tabN (by norm_num), pg_mod i.isLt, idx_of_lt _ i.isLt] at e
  exact e.symm

theorem w0Gens_length : (w0Gens ()).length = 5 := by simp [w0Gens, wWords]

theorem wGens_img : ∀ j < (w0Gens ()).length,
    imageList ((w0Gens ()).getD j 1) = (unpack 360 9 (W.S j)).toList := by
  intro j hj
  have hj5 : j < 5 := w0Gens_length ▸ hj
  apply imageList_of_tabN
  have e : (w0Gens ()).getD j 1 = aeWord (curtisPerms ()) (wWords.getD j []) := by
    rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ (by simp [wWords]; omega)]
    simp [w0Gens]
  rw [e, toTable_aeWord gensRG.get,
    Nat.eq_of_beq_eq_true (List.all_eq_true.1 kGensW j (List.mem_range.2 hj5))]

theorem chainW : ChainK 360 9 (w0Gens ()) wDerive (#v[0] : Vector (Fin 360) 1)
    W.S W.SI W.LR W.TR W.TRI 5 W.BP W.NS 24 :=
  ⟨by norm_num, by norm_num, by norm_num, wGens_img, by decide, W.head, W.hl, by decide, W.hs⟩

theorem ppTL : ∀ L ∈ trPL 360 9 W.LR W.TR 1, ∀ t ∈ L, PP 360 9 t := fun L hL t ht =>
  PP_of_permOK hsz (List.all_eq_true.1 (List.all_eq_true.1 kTRW L hL) t ht)

theorem allTables_wQ : allTables (wQ ()) = WL.map (tabN 360 9) := by
  have hL : levelTables (wQ ()) = (trPL 360 9 W.LR W.TR 1).map (List.map (tabP 360 9)) :=
    levelTables_eq chainW (by decide) (by decide)
  have h := filterProducts_tabP (n := 360) (w := 9) (f := allTrue) (fk := fun _ => true)
    (fun _ _ => rfl) _ ppTL (pidn 360 9) [] (PP.id hsz)
  rw [List.map_nil] at h
  rw [allTables, hL, idT_tabP hsz, h]
  unfold WL
  exact List.map_congr_left fun x hx => tabP_eq_tabN (PP_pfilterProducts hsz _ ppTL _ []
    (PP.id hsz) (fun _ h => absurd h List.not_mem_nil) x hx)

open Certificates in
open Certificates.AE6Model in
theorem cert517507 : fBasic () = true ∧ fTwinChecks () = true ∧ fCycChecks () = true ∧
    fDiagChecks () = true :=
  ⟨(fBasic_eq gensRG).trans kBasic, (fTwinChecks_eq gensRG).trans kTwin,
    (fCycChecks_eq gensRG).trans kCyc, (fDiagChecks_eq gensRG allTables_wQ).trans kDiag⟩

end CertificateChecks.KernelAE6F

end
