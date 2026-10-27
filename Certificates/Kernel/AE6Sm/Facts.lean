module

public import Certificates.Kernel.AE6Sm.Pairs
public import Certificates.Kernel.AE6Sm.Comm
public import Certificates.Kernel.AE6Sm.Chain
public import Certificates.Kernel.AE6Sm.Z
public import Certificates.Kernel.AE6Q8.Facts
public import Certificates.Kernel.AE6Core.Final
public import Certificates.Kernel.OmegaEight.E4O8CentGlue
public import CFSG.Certificates.Kernel.RootPairZSound
public import CFSG.Certificates.Kernel.SporSch.MOCChain
public import CFSG.Certificates.Kernel.SporSch.ChainKPack
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5.RowsBasic
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAE6Sm

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.MOC CFSG.KS.SporSch.CIdx CFSG.KS.SporSch.CAll
  CFSG.KS.SporSch.RPair CFSG.KC.YoshQ CFSG.KC.AE6F CFSG.KC.AE6Tri CFSG.KC.AE6Core CFSG.KC.AE6Sm
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  Certificates.AE6Model Certificates.S7Twin CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu
open CFSG.Sporadic.Schreier (toTable rep_toTable)
open CFSG.KS.Raw.Orb (Gen)
open CertificateChecks.KernelAE6Q8 CertificateChecks.KernelAE6Core CertificateChecks.KernelAE6F
open CFSG.EvenSmallLie.OmegaEight (omegaT mainPerm)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5 (Q8Rel)

theorem czS_eq : ∀ l < 7, CZ.S l = CertificateChecks.KernelO8.AP.S (czLetters.getD l 0) := by
  intro l hl
  interval_cases l <;> decide

theorem sGens_len : (sGens ()).length = 4 := by simp [sGens, sLetters]

theorem czGens_len : (czGens ()).length = 7 := by simp [czGens, czLetters]

theorem sGens_get {j : Nat} (hj : j < 4) : (sGens ()).getD j 1 = (curtisPerms ()).getD (2 * j) 1 := by
  rw [List.getD_eq_getElem _ _ (by rw [sGens_len]; exact hj)]
  simp only [sGens, List.getElem_map]
  congr 1
  interval_cases j <;> rfl

theorem czGens_get {j : Nat} (hj : j < 7) :
    (czGens ()).getD j 1 = (curtisPerms ()).getD (czLetters.getD j 0) 1 := by
  rw [List.getD_eq_getElem _ _ (by rw [czGens_len]; exact hj)]
  simp only [czGens, List.getElem_map]
  congr 1
  interval_cases j <;> rfl

theorem sGens_img : ∀ j < (sGens ()).length,
    imageList ((sGens ()).getD j 1) = (unpack 360 9 (SC.S j)).toList := by
  intro j hj
  rw [sGens_len] at hj
  rw [sGens_get hj, gen_eq_AP j hj]
  exact CFSG.KS.SporSch.MOC.imageList_of_prep (prep_curtis (by omega))

theorem czGens_img : ∀ j < (czGens ()).length,
    imageList ((czGens ()).getD j 1) = (unpack 360 9 (CZ.S j)).toList := by
  intro j hj
  rw [czGens_len] at hj
  rw [czGens_get hj, czS_eq j hj]
  have h8 : czLetters.getD j 0 < 8 := by interval_cases j <;> decide
  exact CFSG.KS.SporSch.MOC.imageList_of_prep (prep_curtis h8)

theorem chainS : ChainK 360 9 (sGens ()) sDerive (#v[0, 2, 4, 24, 8] : Vector (Fin 360) 5)
    SC.S SC.SI SC.LR SC.TR SC.TRI 7 SC.BP 15 24 :=
  ⟨by norm_num, by norm_num, by norm_num, sGens_img, by decide, SC.head, SC.hl, by norm_num,
    SC.hs⟩

theorem chainCZ : ChainK 360 9 (czGens ()) czDerive (#v[0, 2, 4, 24, 8] : Vector (Fin 360) 5)
    CZ.S CZ.SI CZ.LR CZ.TR CZ.TRI 11 CZ.BP 15 24 :=
  ⟨by norm_num, by norm_num, by norm_num, czGens_img, by decide, CZ.head, CZ.hl, by norm_num,
    CZ.hs⟩

theorem ordS : ordK SC.LR 5 = 4096 := by decide +kernel

theorem ordCZ : ordK CZ.LR 5 = 110592 := by decide +kernel

theorem sQ_ok : (sQ ()).check = true ∧ (sQ ()).orderCertificate = 4096 := by
  unfold sQ
  rw [← ordS]
  exact chainK_check (by norm_num) (by decide) chainS

theorem czQ_ok : (czQ ()).check = true ∧ (czQ ()).orderCertificate = 110592 := by
  unfold czQ
  rw [← ordCZ]
  exact chainK_check (by norm_num) (by decide) chainCZ

theorem card_S : Nat.card (Subgroup.closure {g | g ∈ sGens ()}) = 4096 := by
  have e : (sQ ()).originalSubgroup = Subgroup.closure {g | g ∈ sGens ()} := by
    rw [sQ, CFSG.Sporadic.Schreier.certificate_originalSubgroup]
  rw [← e, ← (sQ ()).orderCertificate_eq_card sQ_ok.1, sQ_ok.2]

theorem card_CZ : Nat.card (Subgroup.closure {g | g ∈ czGens ()}) = 110592 := by
  have e : (czQ ()).originalSubgroup = Subgroup.closure {g | g ∈ czGens ()} := by
    rw [czQ, CFSG.Sporadic.Schreier.certificate_originalSubgroup]
  rw [← e, ← (czQ ()).orderCertificate_eq_card czQ_ok.1, czQ_ok.2]

theorem tab_word (w : List Nat) : toTable (aeWord (curtisPerms ()) w) = tabN 360 9 (awN RG w) :=
  toTable_aeWord gensRG.get w

theorem tab_mul {g h : Equiv.Perm (Fin 360)} {X Y : Nat} (hg : toTable g = tabN 360 9 X)
    (hh : toTable h = tabN 360 9 Y) : toTable (g * h) = tabN 360 9 (pmN 360 9 X Y) := by
  rw [toTable_mul hn32, hg, hh, compT_tabN' dims]

theorem tab_inv {g : Equiv.Perm (Fin 360)} {X : Nat} (hg : toTable g = tabN 360 9 X) :
    toTable g⁻¹ = tabN 360 9 (invN 360 9 X) := by
  rw [toTable_inv hn32, hg, invT_tabN' dims]

theorem tab_one : toTable (1 : Equiv.Perm (Fin 360)) = tabN 360 9 (pidn 360 9) := by
  rw [toTable_one hn32, idT_tabN' dims]

theorem eq_of_eqN {g h : Equiv.Perm (Fin 360)} {X Y : Nat} (hg : toTable g = tabN 360 9 X)
    (hh : toTable h = tabN 360 9 Y) (e : eqN 360 9 X Y = true) : g = h := by
  have h1 : tblEq 360 (toTable g) (toTable h) = true := by
    rw [hg, hh, tblEq_tabN' dims]
    exact e
  exact (CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Twin.tblEq_iff_eq
    (rep_toTable hn32 g) (rep_toTable hn32 h)).1 h1

theorem eqN_of_eq {g h : Equiv.Perm (Fin 360)} {X Y : Nat} (hg : toTable g = tabN 360 9 X)
    (hh : toTable h = tabN 360 9 Y) (e : g = h) : eqN 360 9 X Y = true := by
  rw [← tblEq_tabN' dims, ← hg, ← hh]
  exact (CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Twin.tblEq_iff_eq
    (rep_toTable hn32 g) (rep_toTable hn32 h)).2 e

theorem comm_of {C : List (List Nat)} (h : commAllN RG zWord C = true) {c : List Nat}
    (hc : c ∈ C) : aeWord (curtisPerms ()) c * z0 () = z0 () * aeWord (curtisPerms ()) c := by
  unfold commAllN at h
  rw [Orb.strictB_eq] at h
  obtain ⟨i, hi⟩ := allIx_mem h c hc
  rw [Orb.strictB_eq] at hi
  exact eq_of_eqN (tab_mul (tab_word c) (tab_word zWord)) (tab_mul (tab_word zWord) (tab_word c))
    hi

theorem aeWord_single (l : Nat) : aeWord (curtisPerms ()) [l] = (curtisPerms ()).getD l 1 := by
  simp [aeWord]

theorem comm_cz {l : Nat} (hl : l ∈ czLetters) :
    (curtisPerms ()).getD l 1 * z0 () = z0 () * (curtisPerms ()).getD l 1 := by
  rw [← aeWord_single]
  refine comm_of ch517503c1 ?_
  simp only [czLetters, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem comm_fact : (∀ g ∈ czGens (), g * z0 () = z0 () * g ∧ g * g = 1) ∧
    (∀ g ∈ sGens (), g * z0 () = z0 () * g) ∧ cutPerm () * z0 () = z0 () * cutPerm () ∧
    ∀ c ∈ conjPerms (), c * z0 () = z0 () * c := by
  refine ⟨fun g hg => ?_, fun g hg => ?_, comm_of (c := cutWord) ch517503c2 List.mem_cons_self,
    fun c hc => ?_⟩
  · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hg
    exact ⟨comm_cz hl, curtis_sq l⟩
  · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hg
    refine comm_cz ?_
    simp only [sLetters, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl <;> simp [czLetters]
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc
    exact comm_of ch517503c2 (List.mem_cons_of_mem _ hw)

theorem z0_eq : z0 () = mainPerm 0 := by
  rw [← CertificateChecks.KernelO8.E4C.e4c_x0]
  obtain ⟨-, -, -, -, -, hpx, -, -⟩ := CertificateChecks.KernelO8.E4C.e4c_pm
  have hz := prep_zK zWord (by decide)
  rw [← Z_eq, Nat.eq_of_beq_eq_true ch517503z] at hz
  exact Equiv.ext fun i => Fin.ext ((hz i).symm.trans (CFSG.KC.PCent.toPerm_apply hpx i).symm)

theorem z0_sq : z0 () * z0 () = 1 := by
  rw [z0_eq, ← CertificateChecks.KernelO8.E4C.e4c_x0]
  exact CertificateChecks.KernelO8.E4C.e4c_x0_facts.2.1

theorem z0_ne : z0 () ≠ 1 := by
  rw [z0_eq, ← CertificateChecks.KernelO8.E4C.e4c_x0]
  exact CertificateChecks.KernelO8.E4C.e4c_x0_facts.2.2

theorem class_ge :
    1575 ≤ (CFSG.Sporadic.Schreier.conjClass omegaT (z0 ())).ncard := by
  have hos := CFSG.Sporadic.Schreier.ncard_conjClass_mul_card omegaT (z0 ())
  obtain ⟨he, hc⟩ := CertificateChecks.KernelO8.E4C.e4c_H0
  have e : CFSG.Sporadic.Schreier.centralizerIn omegaT (z0 ()) =
      CertificateChecks.KernelO8.E4C.e4H0 := by
    rw [he, z0_eq]
    rfl
  rw [e, hc, CFSG.EvenSmallLie.OmegaEight.card_omegaT] at hos
  omega

theorem k0_fact : Q8Rel ((k0Gens ()).getD 0 1) ((k0Gens ()).getD 1 1) ∧
    (k0Gens ()).getD 0 1 * (k0Gens ()).getD 0 1 = z0 () ∧ (twinPairs ()).length = 4 := by
  have h := ch517503k
  unfold k0N at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, -⟩, h7⟩ := h
  have tx : toTable ((k0Gens ()).getD 0 1) = tabN 360 9 (awN RG (kWords.getD 0 [])) :=
    tab_word _
  have ty : toTable ((k0Gens ()).getD 1 1) = tabN 360 9 (awN RG (kWords.getD 1 [])) :=
    tab_word _
  set x := (k0Gens ()).getD 0 1
  set y := (k0Gens ()).getD 1 1
  have txx := tab_mul tx tx
  have e2 : x * x * (x * x) = 1 := eq_of_eqN (tab_mul txx txx) tab_one h2
  have e3 : y * y = x * x := eq_of_eqN (tab_mul ty ty) txx h3
  have e4 : x * y * (x * y) = x * x :=
    eq_of_eqN (tab_mul (tab_mul tx ty) (tab_mul tx ty)) txx h4
  have e7 : x * x = z0 () := eq_of_eqN txx (tab_word zWord) h7
  have n1 : x * x ≠ 1 := fun e => Bool.false_ne_true (h1.symm.trans (eqN_of_eq txx tab_one e))
  have e5 : y * x * y = x := mul_left_cancel (a := x) (by simpa only [mul_assoc] using e4)
  have hx3 : x * (x * (x * x)) = 1 := by simpa only [mul_assoc] using e2
  have h4' : x ^ 4 = x * x * (x * x) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hlen : (twinPairs ()).length = 4 := by
    unfold twinPairs
    simp only [List.length_map]
    rw [cPerms_eq, List.length_map, cwN_length]
  refine ⟨⟨by rw [h4']; exact e2, by rw [sq]; exact n1, by rw [sq, sq, e3], ?_⟩, e7, hlen⟩
  calc y⁻¹ * x * y = y⁻¹ * (y * x * y) * y := by rw [e5]
    _ = x * (y * y) := by group
    _ = x * (x * x) := by rw [e3]
    _ = x⁻¹ := (inv_eq_of_mul_eq_one_right hx3).symm

@[expose] noncomputable def PP (j : Nat) : Equiv.Perm (Fin 360) := (plGens ()).getD j 1

theorem prep_PL {j : Nat} (hj : j < 8) : Orb.PRep 360 9 (PL.S j) (PP j) :=
  Orb.prep_of_rep (CFSG.KS.SporSch.MOC.rep_of_imageList
    (plGens_img j (by rw [plGens_length]; exact hj)))

theorem tab_PL {j : Nat} (hj : j < 8) : toTable (PP j) = tabN 360 9 (PL.S j) :=
  toTable_eq_tabN (prep_PL hj)

theorem twinPairs_eq : twinPairs () = [(PP 0, PP 1), (PP 2, PP 3), (PP 4, PP 5), (PP 6, PP 7)] := by
  have hl : (cPerms ()).length = 4 := by rw [cPerms_eq, List.length_map, cwN_length]
  unfold twinPairs PP plGens
  dsimp only
  generalize cPerms () = L at hl ⊢
  match L, hl with
  | [_, _, _, _], _ => rfl

theorem mem_twinPairs' {p : Equiv.Perm (Fin 360) × Equiv.Perm (Fin 360)} :
    p ∈ twinPairs () ↔ ∃ i < 4, p = (PP (2 * i), PP (2 * i + 1)) := by
  rw [twinPairs_eq]
  constructor
  · intro h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl
    exacts [⟨0, by norm_num, rfl⟩, ⟨1, by norm_num, rfl⟩, ⟨2, by norm_num, rfl⟩,
      ⟨3, by norm_num, rfl⟩]
  · rintro ⟨i, hi, rfl⟩
    interval_cases i <;> simp

theorem mem_twinPN {PS : Nat → Nat} {q : Nat × Nat} :
    q ∈ twinPN PS ↔ ∃ i < 4, q = (PS (2 * i), PS (2 * i + 1)) := by
  unfold twinPN
  constructor
  · intro h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl
    exacts [⟨0, by norm_num, rfl⟩, ⟨1, by norm_num, rfl⟩, ⟨2, by norm_num, rfl⟩,
      ⟨3, by norm_num, rfl⟩]
  · rintro ⟨i, hi, rfl⟩
    interval_cases i <;> simp

theorem mem_of_memN {r y u : Equiv.Perm (Fin 360)} {R Y U : Nat} (hr : toTable r = tabN 360 9 R)
    (hy : toTable y = tabN 360 9 Y) (hu : toTable u = tabN 360 9 U)
    (h : CFSG.KC.AE6F.memN (spanQN R Y) U = true) : u ∈ Subgroup.closure {r, y} := by
  unfold CFSG.KC.AE6F.memN spanQN at h
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at h
  have hrM : r ∈ Subgroup.closure ({r, y} : Set (Equiv.Perm (Fin 360))) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hyM : y ∈ Subgroup.closure ({r, y} : Set (Equiv.Perm (Fin 360))) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have trr := tab_mul hr hr
  have m := fun a b => Subgroup.mul_mem (Subgroup.closure ({r, y} : Set (Equiv.Perm (Fin 360))))
    (x := a) (y := b)
  rcases h with h | h | h | h | h | h | h | h
  · rw [eq_of_eqN hu tab_one h]
    exact Subgroup.one_mem _
  · rw [eq_of_eqN hu trr h]
    exact m _ _ hrM hrM
  · rw [eq_of_eqN hu hr h]
    exact hrM
  · rw [eq_of_eqN hu (tab_mul hr trr) h]
    exact m _ _ hrM (m _ _ hrM hrM)
  · rw [eq_of_eqN hu hy h]
    exact hyM
  · rw [eq_of_eqN hu (tab_mul hy trr) h]
    exact m _ _ hyM (m _ _ hrM hrM)
  · rw [eq_of_eqN hu (tab_mul hr hy) h]
    exact m _ _ hrM hyM
  · rw [eq_of_eqN hu (tab_mul hy hr) h]
    exact m _ _ hyM hrM

theorem twins_fact : ∀ g ∈ czGens (), ∀ p ∈ twinPairs (), ∃ q ∈ twinPairs (),
    g * p.1 * g⁻¹ ∈ Subgroup.closure {q.1, q.2} ∧ g * p.2 * g⁻¹ ∈ Subgroup.closure {q.1, q.2} := by
  intro g hg p hp
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hg
  obtain ⟨i, hi, rfl⟩ := mem_twinPairs'.1 hp
  have h := ch517503t
  simp only [twinsN, List.all_eq_true, List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨sp, hsp, h2⟩ := h l hl _ (mem_twinPN.2 ⟨i, hi, rfl⟩)
  obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hsp
  obtain ⟨i', hi', rfl⟩ := mem_twinPN.1 hq'
  have tg := gensRG.get l
  have tgi := tab_inv tg
  refine ⟨_, mem_twinPairs'.2 ⟨i', hi', rfl⟩, ?_, ?_⟩
  · exact mem_of_memN (tab_PL (by omega)) (tab_PL (by omega))
      (tab_mul (tab_mul tg (tab_PL (by omega))) tgi) h2.1
  · exact mem_of_memN (tab_PL (by omega)) (tab_PL (by omega))
      (tab_mul (tab_mul tg (tab_PL (by omega))) tgi) h2.2

@[expose] def xW (t : Nat) : List Nat := (cutWord :: conjWords).getD t []

@[expose] noncomputable def xg (t : Nat) : Equiv.Perm (Fin 360) := aeWord (curtisPerms ()) (xW t)

theorem ch517503xe : allN 9 (fun t => Nat.beq (ZR.X t) (zK (xW t))) = true := by decide +kernel

theorem ch517503nx : Nat.beq ZR.nx 9 = true := by decide +kernel

theorem xW_lt : ∀ t < 9, ∀ i ∈ xW t, i < 8 := by decide

theorem prepX {t : Nat} (ht : t < ZR.nx) :
    Orb.PRep 360 9 (ZR.X t) (xg t) ∧ Orb.PRep 360 9 (ZR.XI t) (xg t)⁻¹ := by
  have h9 : t < 9 := by
    rw [← Nat.eq_of_beq_eq_true ch517503nx]
    exact ht
  have hx := prep_zK (xW t) (xW_lt t h9)
  rw [← Nat.eq_of_beq_eq_true ((Orb.allN_iff.1 ch517503xe) t h9)] at hx
  obtain ⟨-, b⟩ := (CFSG.KS.SporSch.CIdx.bAnd_iff' _ _).1 ((Orb.allN_iff.1 ch517503x) t ht)
  exact ⟨hx, CFSG.KS.SporSch.MOC.prep_inv_of_permOK hx b⟩

theorem xg_mem {t : Nat} (h1 : 1 ≤ t) (h9 : t < 9) : xg t ∈ conjPerms () := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have hs : s < conjWords.length := by
    simp only [conjWords, List.length_cons, List.length_nil]
    omega
  refine List.mem_map.2 ⟨conjWords.getD s [], ?_, rfl⟩
  rw [List.getD_eq_getElem _ _ hs]
  exact List.getElem_mem hs

theorem zrep : el 360 SA baseA 5 (SK.E (SR.RP SR.zc)) = z0 () := by
  rw [Nat.eq_of_beq_eq_true kZc]
  exact el_zp

theorem zc_lt : SR.zc < SK.ncl := by decide +kernel

theorem ch517503rl : allN nrZ (fun d => Nat.blt (rlZ d) SK.N) = true := by decide +kernel

theorem rl_lt : ∀ d < nrZ, rlZ d < SK.N := fun d hd =>
  blt_iff.1 ((Orb.allN_iff.1 ch517503rl) d hd)

theorem root_idx {x : Equiv.Perm (Fin 360)} (hx : x ∈ Gen 360 SA 4) (hxx : x * x = z0 ()) :
    ∃ d < nrZ, el 360 SA baseA 5 (rlZ d) = x := by
  obtain ⟨p, hp, hpc, hpx⟩ := root_complete chainCK SK.hN clsF kRootHd sqB
    (Orb.allN_iff.1 kRoot) zc_lt hx (hxx.trans zrep.symm)
  obtain ⟨-, -, -, h1, h2⟩ := rootK_facts ((Orb.allN_iff.1 kRoot) p hp)
  rw [hpc] at h1 h2
  refine ⟨p - SR.RO SR.zc, ?_, ?_⟩
  · unfold nrZ
    change p - SR.RO SR.zc < SR.RO (SR.zc + 1) - SR.RO SR.zc
    omega
  · unfold rlZ
    have e : Nat.add (SR.RO SR.zc) (p - SR.RO SR.zc) = p := by
      change SR.RO SR.zc + (p - SR.RO SR.zc) = p
      omega
    rw [e]
    exact hpx

theorem pairAll : ∀ d < nrZ, pairQK 360 9 (mask 9) (360 * 9) SC.BP 5 SC.LR SC.TR rlZ ZR.CT ZR.PQ
    ZR.QJ nrZ ZR.nq d = true := by
  intro d hd
  have hn : nrZ = 240 := Nat.eq_of_beq_eq_true ch517503nr
  have key : ∀ b < 4, pairB (60 * b) = true := by
    intro b hb
    interval_cases b
    exacts [ch517503p0, ch517503p1, ch517503p2, ch517503p3]
  have hk := key (d / 60) (by omega)
  unfold pairB at hk
  have := CFSG.KS.allBlk_spec hk (d % 60) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (60 * (d / 60)) (d % 60) = d := by
    change 60 * (d / 60) + d % 60 = d
    omega
  rwa [e] at this

theorem nq_eq : ZR.ntw = 4 ∧ ZR.nq = 1120 := by
  have h := ch517503nq
  cases ha : Nat.beq ZR.ntw 4 <;> rw [ha] at h
  · exact absurd h Bool.false_ne_true
  · exact ⟨Nat.eq_of_beq_eq_true ha, Nat.eq_of_beq_eq_true h⟩

theorem subAll {mm : Nat} (h4 : 4 ≤ mm) (hmm : mm < ZR.nq) :
    subAK 360 9 (mask 9) (360 * 9) SC.BP 5 SK.N ZR.nx (SK.E (SR.RP SR.zc)) SC.LR SC.TR ZR.X ZR.XI
      ZR.QJ ZR.QA ZR.QW ZR.QP mm = true := by
  rw [nq_eq.2] at hmm
  have key : ∀ b < 4, subB (4 + 279 * b) = true := by
    intro b hb
    interval_cases b
    exacts [ch517503s0, ch517503s1, ch517503s2, ch517503s3]
  have hk := key ((mm - 4) / 279) (by omega)
  unfold subB at hk
  have := CFSG.KS.allBlk_spec hk ((mm - 4) % 279) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (4 + 279 * ((mm - 4) / 279)) ((mm - 4) % 279) = mm := by
    change 4 + 279 * ((mm - 4) / 279) + (mm - 4) % 279 = mm
    omega
  rwa [e] at this

theorem five_le_conjL {M : Type*} [Group M] [Finite M] {A B x y : M} {c : Nat → M} {L : List M}
    (hJ : Subgroup.closure {x, y} = Subgroup.closure {A, B})
    (hW : ∀ z ∈ Subgroup.closure {A, B}, ∃ k < 8, q8G A B k = z)
    (hcL : ∀ a < 5, c a ∈ L)
    (hd : ∀ a < 5, ∀ b < 5, a < b → ∃ k < 8, ∀ k' < 8,
      (c b)⁻¹ * c a * q8G A B k * (c a)⁻¹ * c b ≠ q8G A B k') :
    5 ≤ Set.ncard {J | ∃ g ∈ L,
      J = (Subgroup.closure {x, y}).map (MulAut.conj g).toMonoidHom} := by
  set K := Subgroup.closure ({x, y} : Set M)
  let F : Nat → Subgroup M := fun a => K.map (MulAut.conj (c a)).toMonoidHom
  have hinj : Set.InjOn F {a | a < 5} := by
    intro a ha b hb e
    by_contra hne
    have key : ∀ a < 5, ∀ b < 5, a < b → F a ≠ F b := by
      intro a ha b hb hab e
      obtain ⟨k, hk, hk'⟩ := hd a ha b hb hab
      have hmem : c a * q8G A B k * (c a)⁻¹ ∈ F b := by
        rw [← e]
        refine Subgroup.mem_map.2 ⟨q8G A B k, ?_, rfl⟩
        rw [hJ]
        exact q8G_mem hk
      obtain ⟨z, hz, ez⟩ := Subgroup.mem_map.1 hmem
      change c b * z * (c b)⁻¹ = _ at ez
      rw [hJ] at hz
      obtain ⟨k', hk'', rfl⟩ := hW z hz
      refine hk' k' hk'' ?_
      have e2 : (c b)⁻¹ * c a * q8G A B k * (c a)⁻¹ * c b =
          (c b)⁻¹ * (c a * q8G A B k * (c a)⁻¹) * c b := by group
      rw [e2, ← ez]
      group
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key a ha b hb h e
    · exact key b hb a ha h e.symm
  have hsub : F '' {a | a < 5} ⊆ {J | ∃ g ∈ L, J = K.map (MulAut.conj g).toMonoidHom} := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨c a, hcL a ha, rfl⟩
  have hfin : {J | ∃ g ∈ L, J = K.map (MulAut.conj g).toMonoidHom}.Finite := by
    refine (Set.finite_univ.image fun g : M => K.map (MulAut.conj g).toMonoidHom).subset ?_
    rintro _ ⟨g, -, rfl⟩
    exact ⟨g, Set.mem_univ _, rfl⟩
  have := Set.ncard_le_ncard hsub hfin
  rwa [hinj.ncard_image, show {a | a < 5} = ((Finset.range 5 : Finset Nat) : Set Nat) by
    ext; simp, Set.ncard_coe_finset, Finset.card_range] at this

theorem pairs_gen {x y : Equiv.Perm (Fin 360)} (hx : x ∈ Gen 360 SA 4) (hy : y ∈ Gen 360 SA 4)
    (hxx : x * x = z0 ()) (hyy : y * y = z0 ())
    (hcx : (cutPerm ())⁻¹ * x * cutPerm () ∈ Gen 360 SA 4)
    (hcy : (cutPerm ())⁻¹ * y * cutPerm () ∈ Gen 360 SA 4) (hxy : x * y * x = y) :
    (∃ p ∈ twinPairs (), x ∈ Subgroup.closure {p.1, p.2} ∧ y ∈ Subgroup.closure {p.1, p.2}) ∨
      5 ≤ Set.ncard {J | ∃ c ∈ conjPerms (),
        J = (Subgroup.closure {x, y}).map (MulAut.conj c).toMonoidHom} := by
  obtain ⟨d, hd, rfl⟩ := root_idx hx hxx
  obtain ⟨e, he, rfl⟩ := root_idx hy hyy
  have h0 := prepX (t := 0) (by rw [Nat.eq_of_beq_eq_true ch517503nx]; norm_num)
  have hkeep : ∀ d < nrZ, (cutPerm ())⁻¹ * el 360 SA baseA 5 (rlZ d) * cutPerm () ∈
      Gen 360 SA 4 → ZR.CT d = 0 := by
    intro d hd hm
    by_contra hct
    exact cutZ_sound chainCK h0.1 h0.2 ((Orb.allN_iff.1 ch517503cut) d hd) hct hm
  obtain ⟨hmm, ⟨k1, hk1, e1⟩, ⟨k2, hk2, e2⟩⟩ := pairQ_sound chainCK SK.hN rl_lt pairAll hd he
    (hkeep d hd hcx) (hkeep e he hcy) hxy
  by_cases htw : ZR.PQ (d * nrZ + e) < 4
  · left
    have htf := twin_facts chainCK (prep_PL (j := 2 * ZR.PQ (d * nrZ + e)) (by omega))
      (prep_PL (j := 2 * ZR.PQ (d * nrZ + e) + 1) (by omega))
      ((Orb.allN_iff.1 ch517503tw) _ (by rw [nq_eq.1]; exact htw))
    refine ⟨_, mem_twinPairs'.2 ⟨_, htw, rfl⟩, ?_, ?_⟩
    · rw [← e1, htf k1 hk1 (by rw [e1]; exact rl_lt d hd)]
      exact q8G_mem hk1
    · rw [← e2, htf k2 hk2 (by rw [e2]; exact rl_lt e he)]
      exact q8G_mem hk2
  · right
    obtain ⟨-, hzj, hQw, hBB, hABA, hQA, hdist⟩ := subA_facts chainCK SK.hN
      (fun t ht => prepX ht) (subAll (by omega) hmm)
    set mm := ZR.PQ (d * nrZ + e)
    set A := el 360 SA baseA 5 (ZR.QJ (8 * mm + 2))
    set B := el 360 SA baseA 5 (ZR.QJ (8 * mm + 4))
    have hJ1 : el 360 SA baseA 5 (ZR.QJ (8 * mm + 1)) = z0 () := by
      rw [hzj]
      exact zrep
    have hq1 : q8G A B 1 = A * A := by simp [q8G]
    have hAA : A * A = z0 () := by rw [← hq1, ← hQw 1 (by norm_num), hJ1]
    have h4 : A * (A * (A * A)) = 1 := by rw [← mul_assoc, hAA, z0_sq]
    have hBB' : B * B = A * A := by rw [hBB, hJ1, hAA]
    have hA1 : A * A ≠ 1 := by
      rw [hAA]
      exact z0_ne
    have hx : ∃ k < 8, q8G A B k = el 360 SA baseA 5 (rlZ d) :=
      ⟨k1, hk1, by rw [← hQw k1 hk1, e1]⟩
    have hy : ∃ k < 8, q8G A B k = el 360 SA baseA 5 (rlZ e) :=
      ⟨k2, hk2, by rw [← hQw k2 hk2, e2]⟩
    have hJ := q8_pair_closure h4 hBB' hABA hA1 hx hy (hxx.trans hAA.symm) hxy
    have hnx : ZR.nx = 9 := Nat.eq_of_beq_eq_true ch517503nx
    exact five_le_conjL (c := fun a => xg (ZR.QA (5 * mm + a))) hJ
      (fun z hz => q8_closure h4 hBB' hABA hz)
      (fun a ha => xg_mem (hQA a ha).1 (hnx ▸ (hQA a ha).2))
      (fun a ha b hb hab => by
        obtain ⟨k, hk, hk'⟩ := hdist a ha b hb hab
        refine ⟨k, hk, fun k' hk'' => ?_⟩
        rw [← hQw k hk, ← hQw k' hk'']
        exact hk' k' hk'')

theorem facts517503 :
    (ValidSchreier (sQ ()) ∧ ValidSchreier (czQ ())) ∧
    Nat.card (Subgroup.closure {g | g ∈ sGens ()}) = 4096 ∧
    Nat.card (Subgroup.closure {g | g ∈ czGens ()}) = 110592 ∧
    ((∀ g ∈ czGens (), g * z0 () = z0 () * g ∧ g * g = 1) ∧
      (∀ g ∈ sGens (), g * z0 () = z0 () * g) ∧ cutPerm () * z0 () = z0 () * cutPerm () ∧
      ∀ c ∈ conjPerms (), c * z0 () = z0 () * c) ∧
    1575 ≤ (CFSG.Sporadic.Schreier.conjClass omegaT (z0 ())).ncard ∧
    (Q8Rel ((k0Gens ()).getD 0 1) ((k0Gens ()).getD 1 1) ∧
      (k0Gens ()).getD 0 1 * (k0Gens ()).getD 0 1 = z0 () ∧ (twinPairs ()).length = 4) ∧
    (∀ g ∈ czGens (), ∀ p ∈ twinPairs (), ∃ q ∈ twinPairs (),
      g * p.1 * g⁻¹ ∈ Subgroup.closure {q.1, q.2} ∧
        g * p.2 * g⁻¹ ∈ Subgroup.closure {q.1, q.2}) ∧
    ∀ x ∈ Subgroup.closure {g | g ∈ sGens ()}, ∀ y ∈ Subgroup.closure {g | g ∈ sGens ()},
      x * x = z0 () → y * y = z0 () →
      (cutPerm ())⁻¹ * x * cutPerm () ∈ Subgroup.closure {g | g ∈ sGens ()} →
      (cutPerm ())⁻¹ * y * cutPerm () ∈ Subgroup.closure {g | g ∈ sGens ()} → x * y * x = y →
      (∃ p ∈ twinPairs (), x ∈ Subgroup.closure {p.1, p.2} ∧ y ∈ Subgroup.closure {p.1, p.2}) ∨
        5 ≤ Set.ncard {J | ∃ c ∈ conjPerms (),
          J = (Subgroup.closure {x, y}).map (MulAut.conj c).toMonoidHom} := by
  refine ⟨⟨sQ_ok.1, czQ_ok.1⟩, card_S, card_CZ, comm_fact, class_ge, k0_fact, twins_fact, ?_⟩
  intro x hx y hy hxx hyy hcx hcy hxy
  rw [← gen_eq_S] at hx hy hcx hcy
  exact pairs_gen hx hy hxx hyy hcx hcy hxy

end CertificateChecks.KernelAE6Sm

end
