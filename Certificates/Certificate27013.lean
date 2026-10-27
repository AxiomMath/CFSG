module

public import Certificates.Data.TitsAschbacherParrott
public import Certificates.Kernel.EvenBN.Table4
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.EvenBN.Bind

public section

set_option maxRecDepth 400000

namespace CertificateChecks.Batch27013

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits CFSG.Quasithin
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2268
open CertificateChecks.KernelSporSch.TitsHelp CertificateChecks.KernelSporSch.TitsCentral
open CertificateChecks.KernelEvenBN Certificates.TitsAschbacherParrott

@[expose] noncomputable def X : Nat := wP TitsH.S hatXWord

@[expose] noncomputable def V512 : Nat := pcomp 1755 11 (mask 11) (V 5) (V 12)

@[expose] noncomputable def gK (t0 t1 t2 t3 t4 : Nat) : Bool :=
  !commPts 1755 11 (mask 11) X t0 t1 t2 t3 t4 ||
    (eqPts 1755 11 (mask 11) (pidn 1755 11) t0 t1 t2 t3 t4 ||
      (eqPts 1755 11 (mask 11) (V 5) t0 t1 t2 t3 t4 ||
        (eqPts 1755 11 (mask 11) (V 12) t0 t1 t2 t3 t4 ||
          (eqPts 1755 11 (mask 11) V512 t0 t1 t2 t3 t4 || false))))

@[expose] noncomputable def tK (a b c d : Nat) : Bool :=
  gK (trAt 1755 (1755 * 11) TitsJ.LR TitsJ.TR 0 a) (trAt 1755 (1755 * 11) TitsJ.LR TitsJ.TR 1 b)
      (trAt 1755 (1755 * 11) TitsJ.LR TitsJ.TR 2 c) (trAt 1755 (1755 * 11) TitsJ.LR TitsJ.TR 3 d)
      (pidn 1755 11) &&
    gK (trAt 1755 (1755 * 11) TitsJ.LR TitsJ.TR 0 a) (trAt 1755 (1755 * 11) TitsJ.LR TitsJ.TR 1 b)
      (trAt 1755 (1755 * 11) TitsJ.LR TitsJ.TR 2 c) (trAt 1755 (1755 * 11) TitsJ.LR TitsJ.TR 3 d) Pi

theorem sizeK : Nat.beq (rcnt (TitsJ.LR 0) * rcnt (TitsJ.LR 1) * rcnt (TitsJ.LR 2) *
    rcnt (TitsJ.LR 3)) 512 = true := by quickRfl

theorem enumK : allN (rcnt (TitsJ.LR 0)) (fun a => allN (rcnt (TitsJ.LR 1)) fun b =>
    allN (rcnt (TitsJ.LR 2)) fun c => allN (rcnt (TitsJ.LR 3)) fun d => tK a b c d) = true := by
  quickRfl

theorem relK : (Nat.beq (ppw X 5) (pidn 1755 11) && !Nat.beq X (pidn 1755 11) &&
    Nat.beq (pcomp 1755 11 (mask 11) (V 1) X) (pcomp 1755 11 (mask 11) (ppw X 3) (V 1)) &&
    Nat.beq (pcomp 1755 11 (mask 11) (V 5) X) (pcomp 1755 11 (mask 11) X (V 5))) = true := by
  quickRfl

theorem get_mem {a : Array (Array Nat)} {i : Nat} (h : i < a.size) : a[i]! ∈ a.toList := by
  rw [getElem!_pos a i h, Array.mem_toList_iff]
  exact Array.getElem_mem h

theorem compA_idG {n : Nat} {a : Array Nat} (ha : a.size = n) : compA n a (idA n) = a := by
  apply Array.ext
  · rw [ha]
    exact Array.size_ofFn
  · intro i h1 h2
    have hi : i < n := by simpa [compA] using h1
    rw [← getElem!_pos _ i h1, ← getElem!_pos _ i h2, CFSG.Monster.B.Co2.compA_get hi,
      CFSG.Monster.B.Co2.idA_get hi]

theorem compA_idR {a : Array Nat} (ha : a.size = 1755) : compA 1755 a (idA 1755) = a :=
  compA_idG ha

theorem f_eq {t0 t1 t2 t3 t4 : Nat} (k0 : C t0) (k1 : C t1) (k2 : C t2) (k3 : C t3) (k4 : C t4)
    (cX : C X) (h : gK t0 t1 t2 t3 t4 = true) :
    (!commEqA (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) xArr (idA 1755) ||
      [idA 1755, vA 5, vA 12, compA 1755 (vA 5) (vA 12)].any
        (eqA 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)))) = true := by
  have hx : xArr = unpack 1755 11 X := (chain_gen bindsH canH (w := hatXWord) (by decide)).1
  have c5 := cV (i := 5) (by decide)
  have c12 := cV (i := 12) (by decide)
  have h512 : compA 1755 (vA 5) (vA 12) = unpack 1755 11 V512 := by
    rw [vA_eq (i := 5) (by decide), vA_eq (i := 12) (by decide), cmpU c5 c12]
    rfl
  unfold commEqA
  rw [compA_idR (a := compA 1755 xArr _) Array.size_ofFn, hx, ← commPts_sound k0 k1 k2 k3 k4 cX,
    List.any_cons,
    List.any_cons, List.any_cons, List.any_cons, List.any_nil, h512,
    vA_eq (i := 5) (by decide), vA_eq (i := 12) (by decide),
    CertificateChecks.KernelSporSch.TitsCentral.id_eq, ← eqPts_sound k0 k1 k2 k3 k4 canId,
    ← eqPts_sound k0 k1 k2 k3 k4 c5, ← eqPts_sound k0 k1 k2 k3 k4 c12,
    ← eqPts_sound (Z := V512) k0 k1 k2 k3 k4 (cmpC c5 c12)]
  exact h

theorem table_ok : ∀ y ∈ jPel.toList,
    (!commEqA y xArr (idA 1755) || [idA 1755, vA 5, vA 12, compA 1755 (vA 5) (vA 12)].any (eqA 1755 y)) =
      true ∧
    (!commEqA (compA 1755 y titsPiArr) xArr (idA 1755) ||
      [idA 1755, vA 5, vA 12, compA 1755 (vA 5) (vA 12)].any (eqA 1755 (compA 1755 y titsPiArr))) =
      true := by
  have cX : C X := (chain_gen bindsH canH (w := hatXWord) (by decide)).2
  rw [pi_eq]
  refine table4_all bindsJ permJ TitsJ.hl cPi fun a ha b hb c hc d hd k0 k1 k2 k3 => ?_
  have e := allN_spec (allN_spec (allN_spec (allN_spec enumK a ha) b hb) c hc) d hd
  unfold tK at e
  rw [Bool.and_eq_true] at e
  exact ⟨f_eq k0 k1 k2 k3 canId cX e.1, f_eq k0 k1 k2 k3 cPi cX e.2⟩

theorem tits_x_check_0 : xCheck = true := by
  obtain ⟨hx, cX⟩ := chain_gen bindsH canH (w := hatXWord) (by decide)
  have hx' : xArr = unpack 1755 11 X := hx
  have cX' : C X := cX
  have k := relK
  simp only [Bool.and_eq_true] at k
  obtain ⟨⟨⟨r1, r2⟩, r3⟩, r4⟩ := k
  have hsz : jPel.size = 512 := by
    unfold jPel jLevels
    rw [table4_size bindsJ permJ TitsJ.hl]
    exact Nat.eq_of_beq_eq_true sizeK
  unfold xCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, CFSG.Monster.B.Co2.allLt_iff.2 fun i hi => ?_⟩
  · rw [hx', powU cX', CertificateChecks.KernelSporSch.TitsCentral.id_eq, eqU (powC cX') canId]
    exact r1
  · rw [hx', CertificateChecks.KernelSporSch.TitsCentral.id_eq, eqU cX' canId]
    exact r2
  · rw [hx', vA_eq (i := 1) (by decide), cmpU (cV (i := 1) (by decide)) cX', powU cX',
      cmpU (powC cX') (cV (i := 1) (by decide)),
      eqU (cmpC (cV (i := 1) (by decide)) cX') (cmpC (powC cX') (cV (i := 1) (by decide)))]
    exact r3
  · unfold commEqA
    rw [compA_idR (a := compA 1755 xArr (vA 5)) Array.size_ofFn, hx', vA_eq (i := 5) (by decide), cmpU (cV (i := 5) (by decide)) cX',
      cmpU cX' (cV (i := 5) (by decide)),
      eqU (cmpC (cV (i := 5) (by decide)) cX') (cmpC cX' (cV (i := 5) (by decide)))]
    exact r4
  · have hp : pPel[i]! = if i < 512 then jPel[i]! else compA 1755 jPel[i - 512]! titsPiArr := by
      rw [pPel, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
    rw [hp]
    split_ifs with h
    · exact (table_ok _ (get_mem (by omega))).1
    · exact (table_ok _ (get_mem (by omega))).2

end CertificateChecks.Batch27013

namespace Certificates

open CertificateChecks

theorem certificate27013 : Certificates.TitsAschbacherParrott.xCheck = true := by
  exact CertificateChecks.Batch27013.tits_x_check_0

end Certificates
