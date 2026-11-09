module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BInvCentData
public import CFSG.Certificates.Kernel.Cnum.XorCols

public section

open CFSG.Monster.B.CTIB.Native

namespace CertificateChecks.Batch27200

open CFSG.Monster.B.CTIB.Native CFSG.Certificates.Kernel.Cnum

def cw (w : List Nat) (j : Nat) : Nat := censusWord w (2 ^ j)

theorem act22_xor (R : Array Nat) (a b : Nat) :
    CFSG.Monster.B.Max2.Native.act22 R (a ^^^ b) =
      CFSG.Monster.B.Max2.Native.act22 R a ^^^ CFSG.Monster.B.Max2.Native.act22 R b := by
  unfold CFSG.Monster.B.Max2.Native.act22
  rw [actGo_eq_ca, actGo_eq_ca, actGo_eq_ca]
  exact ca_xor0 _ _ _ _

theorem act22_lt (R : Array Nat) (hR : ∀ i < 22, R[i]! < 2 ^ 22) (v : Nat) :
    CFSG.Monster.B.Max2.Native.act22 R v < 2 ^ 22 := by
  unfold CFSG.Monster.B.Max2.Native.act22
  rw [actGo_eq_ca]
  exact ca_lt 22 0 hR (by decide)

theorem censusAct_xor (k a b : Nat) : censusAct k (a ^^^ b) = censusAct k a ^^^ censusAct k b := by
  unfold censusAct
  exact act22_xor _ _ _

theorem r1Rows_lt : ∀ i < 22, CFSG.Monster.B.Max2.Native.r1Rows[i]! < 2 ^ 22 := by
  decide +kernel

theorem r2Rows_lt : ∀ i < 22, CFSG.Monster.B.Max2.Native.r2Rows[i]! < 2 ^ 22 := by
  decide +kernel

theorem censusAct_lt (k v : Nat) : censusAct k v < 2 ^ 22 := by
  unfold censusAct
  split
  · exact act22_lt _ r1Rows_lt v
  · exact act22_lt _ r2Rows_lt v

theorem censusWord_xor : ∀ (w : List Nat) (a b : Nat),
    censusWord w (a ^^^ b) = censusWord w a ^^^ censusWord w b
  | [], _, _ => rfl
  | k :: w, a, b => by
    show censusWord w (censusAct k (a ^^^ b)) = censusWord w (censusAct k a) ^^^
      censusWord w (censusAct k b)
    rw [censusAct_xor, censusWord_xor w]

theorem censusWord_append : ∀ (w1 w2 : List Nat) (v : Nat),
    censusWord (w1 ++ w2) v = censusWord w2 (censusWord w1 v)
  | [], _, _ => rfl
  | k :: w, w2, v => censusWord_append w w2 (censusAct k v)

theorem censusWord_lt : ∀ (w : List Nat) (v : Nat), v < 2 ^ 22 → censusWord w v < 2 ^ 22
  | [], _, h => h
  | k :: w, v, _ => censusWord_lt w (censusAct k v) (censusAct_lt k v)

theorem censusWord_lt_of_ne : ∀ (w : List Nat) (v : Nat), w ≠ [] → censusWord w v < 2 ^ 22
  | [], _, h => absurd rfl h
  | k :: w, v, _ => censusWord_lt w (censusAct k v) (censusAct_lt k v)

theorem comp_ne (w1 w2 : List Nat) (u : Nat) (h : w1 ≠ []) :
    censusWord (w1 ++ w2) u = ca (cw w2) (censusWord w1 u) 22 0 := by
  rw [censusWord_append]
  exact lin_eq (censusWord_xor w2) (censusWord_lt_of_ne w1 u h)

theorem hA : ∀ u, censusWord (a5WordA ++ a5WordA) u =
    ca (cw a5WordA) (censusWord a5WordA u) 22 0 :=
  fun u => comp_ne _ _ u (by decide)

theorem hB2 : ∀ u, censusWord (a5WordB ++ a5WordB) u =
    ca (cw a5WordB) (censusWord a5WordB u) 22 0 :=
  fun u => comp_ne _ _ u (by decide)

theorem hB3 : ∀ u, censusWord (a5WordB ++ a5WordB ++ a5WordB) u =
    ca (cw a5WordB) (censusWord (a5WordB ++ a5WordB) u) 22 0 :=
  fun u => comp_ne _ _ u (by decide)

theorem hC2 : ∀ u, censusWord (a5Cycle ++ a5Cycle) u =
    ca (cw a5Cycle) (censusWord a5Cycle u) 22 0 :=
  fun u => comp_ne _ _ u (by decide)

theorem hC3 : ∀ u, censusWord (a5Cycle ++ a5Cycle ++ a5Cycle) u =
    ca (cw a5Cycle) (censusWord (a5Cycle ++ a5Cycle) u) 22 0 :=
  fun u => comp_ne _ _ u (by decide)

theorem hC4 : ∀ u, censusWord (a5Cycle ++ a5Cycle ++ a5Cycle ++ a5Cycle) u =
    ca (cw a5Cycle) (censusWord (a5Cycle ++ a5Cycle ++ a5Cycle) u) 22 0 :=
  fun u => comp_ne _ _ u (by decide)

theorem hC5 : ∀ u, censusWord (a5Cycle ++ a5Cycle ++ a5Cycle ++ a5Cycle ++ a5Cycle) u =
    ca (cw a5Cycle) (censusWord (a5Cycle ++ a5Cycle ++ a5Cycle ++ a5Cycle) u) 22 0 :=
  fun u => comp_ne _ _ u (by decide)

theorem hCyc : ∀ u, censusWord a5Cycle u = ca (cw a5WordA) (censusWord a5WordB u) 22 0 :=
  fun u => comp_ne _ _ u (by decide)

theorem cwC : cw a5Cycle = fun j => ca (cw a5WordA) (cw a5WordB j) 22 0 :=
  funext fun j => hCyc (2 ^ j)

theorem a5_0 : a5OK () = true := by
  unfold a5OK fixesBasis
  simp only [hA, hB3, hB2, hC5, hC4, hC3, hC2, hCyc, cwC]
  decide +kernel

end CertificateChecks.Batch27200

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.CTIB.Native in
theorem certificate27200 : a5OK () = true := CertificateChecks.Batch27200.a5_0

end Certificates
