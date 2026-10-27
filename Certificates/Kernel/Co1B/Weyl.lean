module

public import Certificates.Kernel.Co1B.WeylData
public import CFSG.Certificates.Kernel.Co1BSound
public import CFSG.Sporadic.Co1Patterson.TwistNativeInputs
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylData
public import CFSG.Sporadic.Co1Block.Iota

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo1B

open CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KD.Co1B CFSG.EvenSmallLie.OmegaEight.Weyl
  CFSG.Sporadic.Co1Patterson.TwistNative CFSG.KC.Loop CFSG.KLie.CT

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

@[expose] noncomputable def rfK (i : Nat) : Bool :=
  (fun r => andB ((reflArr r).toList == (List.range 240).map (pget (getL 0 REFL r)))
    ((List.range 240).all fun j => Nat.blt (pget (getL 0 REFL r) j) 240)) (getL 0 OML i)

#j4q_all CFSG.KD.Co1B.RF CertificateChecks.KernelCo1B.rfK 20

theorem oml_len : OML.length = 20 := rfl

theorem andB_t {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem getL_mem (x : Nat) : ∀ {l : List Nat} {r : Nat}, r ∈ l → ∃ i < l.length, getL x l i = r
  | [], _, h => absurd h List.not_mem_nil
  | y :: l, r, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨0, by simp, rfl⟩
    · obtain ⟨i, hi, he⟩ := getL_mem x h
      exact ⟨i + 1, by simp; omega, he⟩

theorem refl_eq {r : Nat} (hr : r ∈ OML) :
    (reflArr r).toList = (List.range 240).map (pget (getL 0 REFL r)) := by
  obtain ⟨i, hi, rfl⟩ := getL_mem 0 hr
  have hi' : i < 20 := by
    have := hi
    rwa [oml_len] at this
  have h := RF.all i hi'
  unfold rfK at h
  exact eq_of_beq (andB_t h).1

theorem refl_lt {r : Nat} (hr : r ∈ OML) : ∀ j < 240, pget (getL 0 REFL r) j < 240 := by
  obtain ⟨i, hi, rfl⟩ := getL_mem 0 hr
  have hi' : i < 20 := by
    have := hi
    rwa [oml_len] at this
  have h := RF.all i hi'
  unfold rfK at h
  intro j hj
  exact Nat.le_of_ble_eq_true (List.all_eq_true.1 (andB_t h).2 j (List.mem_range.2 hj))

theorem lift_chk : ([1, 2].all fun k => (List.range 64).all fun c =>
    (liftRoots k c).all fun r => OML.contains r) = true := by quickRfl

theorem neg_chk : andB ((negArr.toList == (List.range 240).map (pget NEGP)) &&
    ((CFSG.Monster.B.Co2.Native.idA 240).toList == (List.range 240).map (pget pidK)))
    (andB (Nat.blt NEGP (Nat.shiftLeft 1 1920)) (Nat.blt pidK (Nat.shiftLeft 1 1920))) = true := by
  quickRfl

theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem pword_lt (R : List Nat) : ∀ l : List Nat, pword R l < Nat.shiftLeft 1 1920
  | [] => Nat.le_of_ble_eq_true (andB_t (andB_t neg_chk).2).2
  | _ :: _ => pcomp_lt _ _

theorem lt1920 {n : Nat} (h : Nat.blt n (Nat.shiftLeft 1 1920) = true) : n < Nat.shiftLeft 1 1920 :=
  Nat.le_of_ble_eq_true h

@[expose] noncomputable def sqK (k c : Nat) : Nat :=
  strictN (pword REFL (liftRoots k c)) fun W => pcomp W W

theorem liftSq_eq {k c : Nat} (hk : k = 1 ∨ k = 2) (hc : c < 64) : liftSq k c = unpackP (sqK k c) := by
  have hl := lift_chk
  have hm : ∀ r ∈ liftRoots k c, r ∈ OML := by
    intro r hr
    rw [List.all_eq_true] at hl
    have h1 := hl k (by rcases hk with rfl | rfl <;> simp)
    rw [List.all_eq_true] at h1
    have h2 := h1 c (List.mem_range.2 hc)
    rw [List.all_eq_true] at h2
    exact List.contains_iff_mem.1 (h2 r hr)
  rw [liftSq, wordArr_sound REFL _ (fun r hr => refl_eq (hm r hr)) (fun r hr => refl_lt (hm r hr)),
    compA_sound _ (pword_lt REFL _), sqK, strictN_eq']

theorem sgn_eq {k c : Nat} (hk : k = 1 ∨ k = 2) (hc : c < 64) :
    (CFSG.Monster.B.Co2.Native.eqA 240 (liftSq k c) negArr ||
      CFSG.Monster.B.Co2.Native.eqA 240 (liftSq k c) (CFSG.Monster.B.Co2.Native.idA 240)) =
      (Nat.beq (sqK k c) NEGP || Nat.beq (sqK k c) pidK) := by
  have hn := neg_chk
  obtain ⟨h1, h2⟩ := andB_true hn
  rw [Bool.and_eq_true] at h1
  obtain ⟨h3, h4⟩ := andB_true h2
  have hs : sqK k c < Nat.shiftLeft 1 1920 := by
    rw [sqK, strictN_eq']
    exact pcomp_lt _ _
  rw [liftSq_eq hk hc, eqA_sound hs (lt1920 h3) (eq_of_beq h1.1),
    eqA_sound hs (lt1920 h4) (eq_of_beq h1.2)]

@[expose] noncomputable def negK (k c : Nat) : Bool := Nat.beq (sqK k c) NEGP

theorem negSq_eq {k c : Nat} (hk : k = 1 ∨ k = 2) (hc : c < 64) :
    CFSG.Monster.B.Co2.Native.eqA 240 (liftSq k c) negArr = negK k c := by
  have hn := neg_chk
  obtain ⟨h1, h2⟩ := andB_true hn
  rw [Bool.and_eq_true] at h1
  obtain ⟨h3, -⟩ := andB_true h2
  have hs : sqK k c < Nat.shiftLeft 1 1920 := by
    rw [sqK, strictN_eq']
    exact pcomp_lt _ _
  rw [liftSq_eq hk hc, eqA_sound hs (lt1920 h3) (eq_of_beq h1.1)]
  rfl

end CertificateChecks.KernelCo1B

end
