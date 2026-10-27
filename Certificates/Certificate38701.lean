module

public import Certificates.Kernel.SmithD6T2.Facts
public import Certificates.Kernel.SmithD6Pinned.Model

public section

namespace Certificates

open CertificateChecks

open CFSG.SmithD6 CFSG.KC.SmithD6T2 CFSG.KD.SmithD6 in
theorem certificate38701 : (∀ g < 13, gensArr[g]! = lineOf (gensV.getD g (0, 0)).1 (gensV.getD g (0, 0)).2) ∧
    ∀ a b : Nat, a < 4096 → b < 4096 → a ≠ 0 → b ≠ 0 → a ≠ b → qf a = false → qf b = false →
      bf a b = false →
        Relation.ReflTransGen (fun x y : Nat × Nat => ∃ g < 13, d6Step g x.1 = y.1 ∧ d6Step g x.2 = y.2)
          (a, b) (1, 2) :=
  ⟨SmithD6Pinned.gensArr_get, fun _ _ ha hb ha0 hb0 hab haq hbq habf =>
    SmithD6T2.pair_reach_codes ha hb ha0 hb0 hab haq hbq habf⟩

end Certificates
