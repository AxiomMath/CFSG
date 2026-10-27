module

public import CFSG.Literature.ParrottTitsCheckInputs
import Certificates.Kernel.PresLetters.F2004A
import Certificates.Kernel.Parrott.Perms
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

open CFSG.Literature.ParrottTits CFSG.CosetTable CFSG.KC.MiscCoset

namespace Certificates

open CertificateChecks

open CFSG CFSG.Literature CFSG.Literature.ParrottTits CFSG.CosetTable CFSG.Sporadic.Schreier.Tits in
open CFSG.Monster.B.Co2 in
theorem certificate2004 : (Finite (PG 10 parrottWords) ∧ Nat.card (PG 10 parrottWords) ≤ 17971200)
    ∧ ∃ x : ℕ → Equiv.Perm (Fin 1755),
      (∀ w ∈ parrottWords, FreeGroup.lift (fun i : Fin 10 => x i) (FreeGroup.mk w) = 1) ∧
      ∀ j < 2, permOfArr 1755 titsDerivedArrs[j]! =
        wordIn 10 x ([parrottD0Word, parrottD1Word].getD j []) := by
  refine ⟨?_, KernelParrott.perms⟩
  have h := TableFact.card_restrict parrottWords (by norm_num) (subsetOf 10 [0, 2, 3, 4, 5, 6, 7, 8, 9])
    (by decide) CFSG.KBFact.PL2004a CFSG.KBFact.PL2004b
  exact ⟨h.1, h.2.trans (by norm_num)⟩

end Certificates
