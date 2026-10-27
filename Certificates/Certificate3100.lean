module

public import Certificates.Data.CFSGNative.CTIB.Coset
public import CFSG.Monster.B.Dyadic.CTIBK
public import Certificates.Kernel.BabyMonster.CTIB.CosetQBind
public import CFSG.Certificates.Kernel.BabyMonster.CTIBNatsSound
import Certificates.Kernel.BabyMonster.CTIB.Delta
import CFSG.Certificates.Kernel.BabyMonster.CTIBWordsSound
import CFSG.Certificates.Kernel.Common.StrLits
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.List.SplitOn.Basic
import all Init.Data.Nat.ToString

public section

open CFSG.Monster.B.CTIB CFSG.KC.BM.CosetQ CertificateChecks.KernelBM.CTIB.CosetQ

set_option maxRecDepth 400000

namespace CertificateChecks.Batch3100

open CFSG.Monster.B.CTIB CFSG.KC.BM.CosetQ CertificateChecks.KernelBM.CTIB.CosetQ

theorem parseWords_eq : Native.parseWords Native.centWordStr = Native.centWordsL := by
  str_lits Native.centWordStr
  exact (Native.parseWords_ofList _).trans (eq_of_beq (by quickRfl))

@[expose] noncomputable def natsChk (L : List Char) (R : List ℕ) : Bool :=
  (List.splitOnPPrepend (· == ' ') L []).all (fun p => p.all Char.isDigit) &&
    (List.splitOnPPrepend (· == ' ') L []).filterMap Native.pieceVal == R

theorem nats_of {L : List Char} {R : List ℕ} (h : natsChk L R = true) :
    Native.parseNats (String.ofList L) = R := by
  unfold natsChk at h
  rw [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  rw [Native.parseNats_ofList L fun p hp c hc => List.all_eq_true.1 (h.1 p hp) c hc, h.2]

@[expose] noncomputable def recsL (k PT npts : ℕ) : List ℕ :=
  (List.range npts).flatMap fun p => [repOf PT p, sizeOf k PT p]

theorem pairs_flatMap (a b : ℕ → ℕ) : ∀ l : List ℕ,
    Native.orbitRecs.pairs (l.flatMap fun p => [a p, b p]) = l.map fun p => (a p, b p)
  | [] => rfl
  | p :: l => by
    rw [List.flatMap_cons, List.cons_append, List.cons_append, List.nil_append,
      Native.orbitRecs.pairs, pairs_flatMap a b l, List.map_cons]

theorem orbit6 : Native.orbitRecs 6 = qrecs 6 PT6 529 := by
  simp only [Native.orbitRecs, ↓reduceIte]
  str_lits Native.orbitStr6
  rw [nats_of (R := recsL 6 PT6 529) (by quickRfl), recsL, pairs_flatMap]
  rfl

theorem orbit8 : Native.orbitRecs 8 = qrecs 8 PT8 37 := by
  simp only [Native.orbitRecs, Nat.reduceEqDiff, ↓reduceIte]
  str_lits Native.orbitStr8
  rw [nats_of (R := recsL 8 PT8 37) (by quickRfl), recsL, pairs_flatMap]
  rfl

theorem orbit10 : Native.orbitRecs 10 = qrecs 10 PT10 3 := by
  simp only [Native.orbitRecs, Nat.reduceEqDiff, ↓reduceIte]
  str_lits Native.orbitStr10
  rw [nats_of (R := recsL 10 PT10 3) (by quickRfl), recsL, pairs_flatMap]
  rfl

theorem imgs_eq : Native.parseNats Native.centImgsStr = imgsL := by
  str_lits Native.centImgsStr
  exact nats_of (by quickRfl)

theorem neg_orbit6 : (!natsChk ((Native.orbitStr6.toList).set 0 '5') (recsL 6 PT6 529)) = true := by
  str_lits Native.orbitStr6
  rw [String.toList_ofList]
  quickRfl

theorem neg_imgs : (!natsChk ((Native.centImgsStr.toList).set 0 '3') imgsL) = true := by
  str_lits Native.centImgsStr
  rw [String.toList_ofList]
  quickRfl

theorem cosetCheck_eq_true_0 : Native.cosetCheck () = true :=
  cosetCheck_of parseWords_eq orbit6 orbit8 orbit10 imgs_eq

end CertificateChecks.Batch3100

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.CTIB in
theorem certificate3100 : (Native.cosetCheck () = true) ∧ CFSG.Monster.B.Dyadic.FactDelta :=
  ⟨CertificateChecks.Batch3100.cosetCheck_eq_true_0, KernelBM.CTIB.factDelta⟩

end Certificates
