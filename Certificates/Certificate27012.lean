module

public import Certificates.Data.TitsAschbacherParrott
public import Certificates.Kernel.EvenBN.Bind
public import CFSG.Certificates.Kernel.Spor.SiftEq
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.Batch27012

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier.Tits CFSG.Quasithin CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.Tits2268 CertificateChecks.KernelSporSch.TitsHelp
open CertificateChecks.KernelSporSch.TitsCentral CertificateChecks.KernelEvenBN
open Certificates.TitsAschbacherParrott

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 1755 11 (mask 11) p q

@[expose] noncomputable def VW (w j : Nat) : Nat := Bool.rec (motive := fun _ => Nat) w (V j) (Nat.blt j 13)

@[expose] noncomputable def sS (g : Nat) : Bool :=
  siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsS.LR TitsS.TRI TitsS.BP 5 0 g

@[expose] noncomputable def outT (g : Nat) : Bool := !sS g && !sS (pc g PiI)

theorem conjK : (reeConj₁.all (fun p => Nat.beq (pc (V p.1) W1) (pc W1 (V p.2))) &&
    reeConj₂.all (fun p => Nat.beq (pc (V p.1) W2) (pc W2 (V p.2)))) = true := by quickRfl

theorem ordK : (Nat.beq (pc W1 W1) (pidn 1755 11) && !Nat.beq W1 (pidn 1755 11) &&
    Nat.beq (pc W2 W2) (pidn 1755 11) && !Nat.beq W2 (pidn 1755 11) &&
    !Nat.beq (ppw (pc W1 W2) 4) (pidn 1755 11) && Nat.beq (ppw (pc W1 W2) 8) (pidn 1755 11)) = true := by
  quickRfl

theorem outK : allN 8 (fun k => (Nat.beq k 0 || outT (ppw (pc W1 W2) k)) &&
    outT (pc (ppw (pc W1 W2) k) W1)) = true := by quickRfl

theorem hK : allN 3 (fun k => Nat.beq (TitsH.S k) (wP (VW W1) (hInTW.getD k []))) = true := by quickRfl

theorem nK : allN 4 (fun k => Nat.beq (TitsN.S k) (wP (VW W2) (nInTW.getD k []))) = true := by quickRfl

theorem tab_eq {w : Array Nat} {W : Nat} (hw : w = unpack 1755 11 W) (cw : C W) :
    ∀ j ∈ List.range 14, (vArrs.push w)[j]! = unpack 1755 11 (VW W j) ∧ C (VW W j) := by
  intro j hj
  have hj' := List.mem_range.1 hj
  have hs : vArrs.size = 13 := by simp [vArrs]
  by_cases h : j < 13
  · have e : VW W j = V j := by
      unfold VW
      rw [Nat.blt_eq.mpr h]
    rw [e, getElem!_pos _ j (by simp; omega), Array.getElem_push_lt (by omega),
      ← getElem!_pos vArrs j (by omega)]
    exact v_eq h
  · have hj13 : j = 13 := by omega
    subst hj13
    have e : VW W 13 = W := rfl
    rw [e, getElem!_pos _ 13 (by simp; omega)]
    simp only [Array.getElem_push, hs, Nat.lt_irrefl, dite_false]
    exact ⟨hw, cw⟩

theorem sS_eq {g : Array Nat} {G : Nat} (hg : g = unpack 1755 11 G) (cG : C G) :
    inS g = sS G :=
  siftK_eq bindsS permS TitsS.hl hg (hi_of cG) (range_of_canonK cG)

theorem outT_eq {g : Array Nat} {G : Nat} (hg : g = unpack 1755 11 G) (cG : C G) :
    notInT g = outT G := by
  unfold notInT outT
  rw [sS_eq hg cG, hg, piInv_eq, cmpU cG cPiI, sS_eq rfl (cmpC cG cPiI)]
  rfl

theorem gen_eq {A : Array (Array Nat)} {PS : Nat → Nat} {kS nb BP k : Nat} {base : Array Nat}
    {w : Array Nat} {W : Nat} (hw : w = unpack 1755 11 W) (cw : C W)
    (hb : Binds 1755 11 PS kS nb BP A base)
    (hc : allN kS (fun j => canonK 1755 11 (mask 11) (1755 * 11) (PS j)) = true)
    {L : List (List Nat)} (hk : k ≤ kS) (hL : ∀ j < k, ∀ i ∈ L.getD j [], i ∈ List.range 14)
    (h : allN k (fun j => Nat.beq (PS j) (wP (VW W) (L.getD j []))) = true) :
    (List.range k).all (fun j => eqA 1755 A[j]! (prodArr (vArrs.push w) (L.getD j []))) = true := by
  refine List.all_eq_true.2 fun j hj => ?_
  have hj' := List.mem_range.1 hj
  obtain ⟨e, c⟩ := prod_eq (G := VW W) fun i hi => tab_eq hw cw i (hL j hj' i hi)
  rw [hb.2.2.2.2.1 j (by omega), e, eqU (allN_spec hc j (by omega)) c]
  exact allN_spec h j hj'

theorem conjPart (w : Array Nat) {W : Nat} (hw : w = unpack 1755 11 W) (cw : C W)
    (L : List (Nat × Nat)) (hL : ∀ p ∈ L, p.1 < 13 ∧ p.2 < 13)
    (h : L.all (fun p => Nat.beq (pc (V p.1) W) (pc W (V p.2))) = true) :
    L.all (fun p => conjEqA w (vA p.1) (vA p.2)) = true := by
  refine List.all_eq_true.2 fun p hp => ?_
  obtain ⟨l1, l2⟩ := hL p hp
  unfold conjEqA
  rw [hw, vA_eq l1, vA_eq l2, cmpU (cV l1) cw, cmpU cw (cV l2), eqU (cmpC (cV l1) cw) (cmpC cw (cV l2))]
  exact List.all_eq_true.1 h p hp

theorem tits_parrott_check_1 : reeCheck = true := by
  obtain ⟨h1, c1⟩ := w1_eq
  obtain ⟨h2, c2⟩ := w2_eq
  have c12 : C (pc W1 W2) := cmpC c1 c2
  have hx : compA 1755 w1Arr w2Arr = unpack 1755 11 (pc W1 W2) := by rw [h1, h2, cmpU c1 c2]; rfl
  have kk := conjK
  simp only [Bool.and_eq_true] at kk
  obtain ⟨k1, k2⟩ := kk
  have ord := ordK
  simp only [Bool.and_eq_true] at ord
  obtain ⟨⟨⟨⟨⟨o1, o2⟩, o3⟩, o4⟩, o5⟩, o6⟩ := ord
  have outPart : (List.range 8).all (fun k => (k == 0 || notInT (powA (compA 1755 w1Arr w2Arr) k)) &&
      notInT (compA 1755 (powA (compA 1755 w1Arr w2Arr) k) w1Arr)) = true := by
    refine List.all_eq_true.2 fun k hk => ?_
    have hk' := List.mem_range.1 hk
    have cp : C (ppw (pc W1 W2) k) := powC c12
    have hp : powA (compA 1755 w1Arr w2Arr) k = unpack 1755 11 (ppw (pc W1 W2) k) := by
      rw [hx, powU c12]
    rw [outT_eq hp cp, hp, h1, cmpU cp c1, outT_eq rfl (cmpC cp c1)]
    have := allN_spec outK k hk'
    simpa [pc] using this
  unfold reeCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨conjPart _ h1 c1 _ (by decide) k1, conjPart _ h2 c2 _ (by decide) k2⟩, ?_⟩, ?_⟩,
    ?_⟩, ?_⟩, ?_⟩, ?_⟩, outPart⟩,
    gen_eq h1 c1 bindsH canH (by norm_num) (by decide) hK⟩,
    gen_eq h2 c2 bindsN canN (by norm_num) (by decide) nK⟩, by decide⟩, by decide⟩
  · rw [h1, cmpU c1 c1, CertificateChecks.KernelSporSch.TitsCentral.id_eq, eqU (cmpC c1 c1) canId]
    exact o1
  · rw [h1, CertificateChecks.KernelSporSch.TitsCentral.id_eq, eqU c1 canId]
    simpa using o2
  · rw [h2, cmpU c2 c2, CertificateChecks.KernelSporSch.TitsCentral.id_eq, eqU (cmpC c2 c2) canId]
    exact o3
  · rw [h2, CertificateChecks.KernelSporSch.TitsCentral.id_eq, eqU c2 canId]
    simpa using o4
  · rw [hx, powU c12, CertificateChecks.KernelSporSch.TitsCentral.id_eq, eqU (powC c12) canId]
    simpa using o5
  · rw [hx, powU c12, CertificateChecks.KernelSporSch.TitsCentral.id_eq, eqU (powC c12) canId]
    exact o6

end CertificateChecks.Batch27012

namespace Certificates

open CertificateChecks

theorem certificate27012 : Certificates.TitsAschbacherParrott.reeCheck = true := by
  exact CertificateChecks.Batch27012.tits_parrott_check_1

end Certificates
