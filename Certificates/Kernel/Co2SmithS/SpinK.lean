module

public import Certificates.Data.Kernel.Co2SmithS.Spin
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCo2SmithS

open CFSG.KC.Co2SmithS CFSG.Sporadic.Co2Smith.Native

theorem all_take_drop {α : Type} {f : α → Bool} {l : List α} (n : Nat)
    (h1 : (l.take n).all f = true) (h2 : (l.drop n).all f = true) : l.all f = true := by
  rw [← List.take_append_drop n l, List.all_append, h1, h2] <;> rfl

theorem spA : (List.range 8).all (fun i => wordC [2 * i, 2 * i + 1] == idC) = true := by
  quickRfl

theorem spB0 : ((sp6CoverR ()).take 30).all (fun r => wordC (r.map sCode) == idC) = true := by
  quickRfl

theorem spB1 : (((sp6CoverR ()).drop 30).take 30).all (fun r => wordC (r.map sCode) == idC) = true := by
  quickRfl

theorem spB2 : ((((sp6CoverR ()).drop 30).drop 30).take 30).all (fun r => wordC (r.map sCode) == idC) = true := by
  quickRfl

theorem spB3 : (((((sp6CoverR ()).drop 30).drop 30).drop 30).take 30).all (fun r => wordC (r.map sCode) == idC) = true := by
  quickRfl

theorem spB4 : ((((((sp6CoverR ()).drop 30).drop 30).drop 30).drop 30).take 30).all (fun r => wordC (r.map sCode) == idC) = true := by
  quickRfl

theorem spB5 : (((((((sp6CoverR ()).drop 30).drop 30).drop 30).drop 30).drop 30).take 30).all (fun r => wordC (r.map sCode) == idC) = true := by
  quickRfl

theorem spB6 : ((((((((sp6CoverR ()).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).take 30).all (fun r => wordC (r.map sCode) == idC) = true := by
  quickRfl

theorem spB7 : ((((((((sp6CoverR ()).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).all (fun r => wordC (r.map sCode) == idC) = true := by
  quickRfl

theorem spB : (sp6CoverR ()).all (fun r => wordC (r.map sCode) == idC) = true :=
  all_take_drop 30 spB0 <|
  all_take_drop 30 spB1 <|
  all_take_drop 30 spB2 <|
  all_take_drop 30 spB3 <|
  all_take_drop 30 spB4 <|
  all_take_drop 30 spB5 <|
  all_take_drop 30 spB6 <|
  spB7

theorem spC : (wordC [0, 0] == negC) = true := by
  quickRfl

theorem spinK_ok : spinCheckK = true := by
  unfold spinCheckK
  rw [spA, spB, spC] <;> rfl

end CertificateChecks.KernelCo2SmithS

end
