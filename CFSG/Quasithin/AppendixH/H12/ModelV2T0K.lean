module

public import CFSG.Quasithin.AppendixH.H12.ModelM0K
public import CFSG.Quasithin.AppendixH.H12.ModelV2K

public section

namespace CFSG.Quasithin.AppendixH.H12.ModelV2T0K

open CFSG.Quasithin.AppendixH.H12.Model CFSG.Quasithin.H.Mathieu.H12Cert CFSG.Quasithin.H13.MatNCert
  CFSG.KC.Mat12P CFSG.Quasithin.AppendixH.H12.ModelM0K CFSG.Quasithin.AppendixH.H12.ModelV2K

theorem all_comm_eq (B w : List ℕ) :
    (List.range 4096).all (fun c => (spanN B).contains (mvN (tW w) c ^^^ c)) =
      forceM (spanMask B) (fun m => forceM (evalQ w) (fun X =>
        (List.range 4096).all (fun c => bitM m (Nat.xor (mvNR (unpackQ X) c) c)))) := by
  rw [forceM_apply, forceM_apply]
  congr 1
  funext c
  rw [bitM_eq, spanMask, testBit_maskOf, ← mvN_toR]
  change (spanN B).contains (mvN (evalW 12 gG w) c ^^^ c) =
    decide (mvN (unpackQ (evalQ w)) c ^^^ c ∈ spanN B)
  rw [tW_eq]
  exact Bool.eq_iff_iff.2 (by simp [List.contains_iff_mem])

theorem all_any_comm_eq (B w : List ℕ) :
    B.all (fun x => (List.range 4096).any (fun c => (mvN (tW w) c ^^^ c) == x)) =
      forceM (evalQ w) (fun X =>
        B.all (fun x => (List.range 4096).any fun c =>
          Nat.beq (Nat.xor (mvNR (unpackQ X) c) c) x)) := by
  rw [forceM_apply]
  refine congrArg B.all (funext fun x => congrArg (List.range 4096).any (funext fun c => ?_))
  rw [← mvN_toR]
  change (mvN (evalW 12 gG w) c ^^^ c == x) = Nat.beq (mvN (unpackQ (evalQ w)) c ^^^ c) x
  rw [tW_eq]
  exact Bool.eq_iff_iff.2 (by simp [Nat.beq_eq])

end CFSG.Quasithin.AppendixH.H12.ModelV2T0K
