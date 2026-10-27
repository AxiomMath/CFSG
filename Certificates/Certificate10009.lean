module

public import CFSG.LieType.Multipliers.TitsCheckInputs
import Certificates.Kernel.Misc.Coset.C10009

public section

namespace Certificates

open CertificateChecks

open CFSG.LieType CFSG.LieType.Multipliers CFSG.LieType.Multipliers.Tits CFSG.CosetTable
  CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2 in
theorem certificate10009 :
    (Finite (PG 3 titsRels) ∧ Nat.card (PG 3 titsRels) ≤ 17971200)
    ∧ (Finite (PG 3 titsCoverWords) ∧ Nat.card (PG 3 titsCoverWords) ≤ 17971200)
    ∧ ((∀ w ∈ titsOneWords, FreeGroup.lift (fun i : Fin 3 => wordIn 2
        (fun j => permOfArr 1755 titsDerivedArrs[j]!) (abcWords.getD i.val [])) (FreeGroup.mk w) = 1)
      ∧ ∀ j < 2, permOfArr 1755 titsDerivedArrs[j]! = wordIn 3
        (fun i => wordIn 2 (fun j => permOfArr 1755 titsDerivedArrs[j]!) (abcWords.getD i []))
        (titsDWords.getD j [])) :=
  ⟨KernelMiscCoset.C10009.card_rels, KernelMiscCoset.C10009.card_cover,
    KernelMiscCoset.C10009.perms⟩

end Certificates
