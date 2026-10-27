module

public import Certificates.Data.CFSGNative.MonsterB.Co2Irred
public import CFSG.Monster.B.Co2.PermArr

public section

open CFSG.Monster.B.Co2

namespace CertificateChecks.Batch3027

open CFSG.Monster.B.Co2

@[expose] def colFold (i s : Nat) (l : List Nat) (c : Nat) : Nat :=
  l.foldl (fun c t => if (Native.rowMinusI i t).testBit s then c ||| 1 <<< t else c) c

theorem forIn_eq_colFold (i s : Nat) : ∀ (l : List Nat) (c : Nat),
    (forIn (m := Id) l c fun t c => if (Native.rowMinusI i t).testBit s = true then
      pure (ForInStep.yield (c ||| 1 <<< t)) else pure (ForInStep.yield c)) = colFold i s l c := by
  intro l
  induction l with
  | nil => intro c; rfl
  | cons a l ih =>
    intro c
    rw [List.forIn_cons, colFold, List.foldl_cons, ← colFold]
    split <;> exact ih _

theorem colOf_eq (i s : Nat) : Native.colOf i s = colFold i s (List.range' 0 22) 0 := by
  simp only [Native.colOf, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  exact forIn_eq_colFold i s _ 0

theorem irredCheck_eq_true : Native.irredCheck = true := by
  unfold Native.irredCheck Native.colArr
  simp only [colOf_eq, Bool.and_eq_true, allLt_iff]
  decide +kernel

end CertificateChecks.Batch3027

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Co2 in
theorem certificate3027 : Native.irredCheck = true := CertificateChecks.Batch3027.irredCheck_eq_true

end Certificates
