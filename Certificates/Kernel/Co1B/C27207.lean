module

public import Certificates.Kernel.Co1B.Chk27207
public import Certificates.Kernel.Co1B.Text27207
public import Certificates.Kernel.EvenSporG24.TblText
public import CFSG.Certificates.Kernel.Co1BSpinSound
import all Init.Data.List.SplitOn.Basic
public import Certificates.Kernel.Co1B.Tri2045Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Cent27207

open CFSG.KC.Co1BSpin CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.F2W CFSG.EvenSporadicStandard.Co1Cent
  CFSG.EvenSporadicStandard.Co1Pair CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block
  CFSG.EvenSporadicStandard.Induction.AutBound.Spin

set_option maxHeartbeats 0 in
theorem good_all : (CT.chars.splitOn ' ').all CertificateChecks.EvenSporG24.goodK = true := by
  decide +kernel

theorem centNums_eq :
    centNums = ((CT.chars.splitOn ' ').map CertificateChecks.EvenSporG24.tokV).toArray := by
  have h : centNums = CFSG.EvenSporadicStandard.G24Model.parseNums centText := rfl
  rw [h, CT.eq]
  exact CertificateChecks.EvenSporG24.parseNums_ofList _ good_all

set_option maxHeartbeats 0 in
theorem sWords_eq : sWords = K.SW.map (·.map decLetter) := by
  have h : sWords = readWordsD centNums 6 0 := rfl
  have key : ∀ (L : List Nat) (m p : Nat), readWordsD L.toArray m p =
      Nat.rec (motive := fun _ => List Nat → List (List Int)) (fun _ => [])
        (fun _ ih l => Nat.rec (motive := fun _ => List Nat → List Int) (fun _ => [])
            (fun _ ih' l' => decLetter (l'.headD 0) :: ih' l'.tail) (l.headD 0) (l.drop 1) ::
          ih (l.drop (1 + l.headD 0))) m (L.drop p) := by
    have tk : ∀ (k : Nat) (L : List Nat), (List.range k).map (fun i => decLetter (L.getD i 0)) =
        Nat.rec (motive := fun _ => List Nat → List Int) (fun _ => [])
          (fun _ ih' l' => decLetter (l'.headD 0) :: ih' l'.tail) k L := by
      intro k
      induction k with
      | zero => intro L; rfl
      | succ k ih =>
        intro L
        have e : (fun i => decLetter (L.getD i 0)) ∘ Nat.succ =
            fun i => decLetter (L.tail.getD i 0) := by
          funext i
          cases L <;> simp
        rw [List.range_succ_eq_map, List.map_cons, List.map_map, e, ih]
        cases L <;> rfl
    intro L m
    induction m with
    | zero => intro p; rfl
    | succ m ih =>
      intro p
      have e1 : L.toArray[p]! = (L.drop p).headD 0 := by
        rw [List.headD_eq_head?_getD, List.head?_drop, getElem!_def, List.getElem?_toArray]
        cases L[p]? <;> rfl
      have e2 : ∀ i, L.toArray[p + 1 + i]! = ((L.drop p).drop 1).getD i 0 := by
        intro i
        rw [List.drop_drop, List.getD_eq_getElem?_getD, List.getElem?_drop, getElem!_def,
          List.getElem?_toArray, Nat.add_comm p 1]
        cases L[1 + p + i]? <;> rfl
      have e3 : ∀ x, L.drop (p + 1 + x) = (L.drop p).drop (1 + x) := by
        intro x
        rw [List.drop_drop, Nat.add_assoc]
      rw [readWordsD, ih, e3, e1]
      simp only [e2]
      rw [tk]
  rw [h, centNums_eq, key, List.drop_zero]
  decide +kernel

theorem cpX_eq : cpX = unpackR 24 K.X := by
  rw [cpX, Tri2045.rx_eq, Tri2045.ry_eq, CFSG.KC.Co1T.unpack_eq_unpackR,
    CFSG.KC.Co1T.unpack_eq_unpackR, mul_unpackW, pow_unpack', mul_unpackW]
  exact (beq_of_eqK kX).symm

theorem cpY_eq : cpY = unpackR 24 K.Y := by
  rw [cpY, Tri2045.ry_eq, CFSG.KC.Co1T.unpack_eq_unpackR]
  exact (beq_of_eqK kY).symm

theorem cpXI_eq : inv cpX = unpackR 24 K.XI := by
  rw [cpX_eq]
  exact inv_unpackR (Nat.eq_of_beq_eq_true kXI)

theorem cpYI_eq : inv cpY = unpackR 24 K.YI := by
  rw [cpY_eq]
  exact inv_unpackR (Nat.eq_of_beq_eq_true kYI)

theorem sRows_eq : sRows = K.RS.map (unpackR 24) := by
  have h : sRows = sWords.map (word [cpX, cpY] [inv cpX, inv cpY]) := rfl
  have e1 : [cpX, cpY] = [K.X, K.Y].map (unpackR 24) := by rw [cpX_eq, cpY_eq]; rfl
  have e2 : [inv cpX, inv cpY] = [K.XI, K.YI].map (unpackR 24) := by rw [cpXI_eq, cpYI_eq]; rfl
  rw [h, sWords_eq, e1, e2, leqK_sound kRS, List.map_map, List.map_map]
  refine List.map_congr_left fun w _ => ?_
  rw [Function.comp_apply, Function.comp_apply, word_sound]

theorem sInv_eq : sInv = K.RIS.map (unpackR 24) := by
  have h : sInv = sRows.map inv := rfl
  rw [h, sRows_eq]
  exact invsK_map (spinK_invs kSpin)

theorem hC : centData.C = unpackR 24 K.CP := by decide +kernel
theorem hLam : centData.lam = unpackR 24 K.LP := by decide +kernel
theorem hW : centData.wcolsArr = unpackR 24 K.WC := by decide +kernel
theorem hP : centData.Pp = unpackR 24 K.PP := by decide +kernel

theorem spin_ok : spinOK centData = true :=
  spinOK_of rfl sRows_eq sInv_eq hC hLam hW hP kSpin

theorem one_mul_inv {A AI : Nat} (h : Nat.beq (mulK A AI) oneK = true) :
    (mul (unpackR 24 A) (unpackR 24 AI) == one) = true := by
  rw [mul_unpack, Nat.eq_of_beq_eq_true h, one_eq]
  exact beq_self_eq_true _

open Certificates in
open CFSG.EvenSporadicStandard.Co1Cent in
theorem c27207 : centOK = true := by
  have hl : sWords.length = 6 := by rw [sWords_eq]; rfl
  rw [centOK, hl, cpXI_eq, cpYI_eq, cpX_eq, cpY_eq, one_mul_inv kXI, one_mul_inv kYI, spin_ok]
  rfl

end CertificateChecks.KernelCo1B.Cent27207

end
