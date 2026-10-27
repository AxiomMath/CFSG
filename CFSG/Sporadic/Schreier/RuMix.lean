module

public import Certificates.Certificate15501
public import CFSG.Sporadic.Schreier.RuWitReps

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

noncomputable abbrev ruMix (p : ℕ) : Equiv.Perm (Fin 4060) :=
  ruYp p * (ruLGen 1 * ruYp p * (ruLGen 1)⁻¹)

theorem rep_ruMix
    {p : ℕ} (hp : p ∈ [5, 7, 13]) : Rep 4060 (ruMixA p) (ruMix p) :=
  rep_compA (rep_ruYp hp) (rep_compA (rep_compA (rep_ruLGen (i := 0) (by decide))
    (rep_ruYp hp)) (rep_ruInv (rep_ruLGen (i := 0) (by decide))
      (ruWit_check.2.2.2.2.2.1 0 (by decide))))

theorem orderOf_ruMix_thirteen :
    orderOf (ruMix 13) = 7 := by
  have h := Certificates.certificate15501
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  refine orderOf_eq_prime (eq_of_eqA (rep_powA (rep_ruMix (by decide)) 7) rep_idA h.1)
    fun h1 => ?_
  have h2 := (eqA_iff (rep_ruMix (by decide)) rep_idA).2 h1
  rw [h.2.1] at h2
  exact Bool.false_ne_true h2

theorem orderOf_ruMix_five :
    orderOf (ruMix 5) = 13 := by
  have h := Certificates.certificate15501
  have : Fact (Nat.Prime 13) := ⟨by decide⟩
  refine orderOf_eq_prime (eq_of_eqA (rep_powA (rep_ruMix (by decide)) 13) rep_idA h.2.2.1)
    fun h1 => ?_
  have h2 := (eqA_iff (rep_ruMix (by decide)) rep_idA).2 h1
  rw [h.2.2.2] at h2
  exact Bool.false_ne_true h2

end CFSG.Sporadic.RuSchreier
