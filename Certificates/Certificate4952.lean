module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15422CoreCertificate4952Inputs

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple.L15422

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F6
open scoped commutatorElement

private theorem cert4952_cycThree_sign : Equiv.Perm.sign cycThree = 1 := by
  decide +kernel

private theorem cert4952_cycFive_sign : Equiv.Perm.sign cycFive = 1 := by
  decide +kernel

private theorem cert4952_eq_one_of_commute_cyc : ∀ σ : Equiv.Perm (Fin 6), σ * cycThree = cycThree * σ →
    σ * cycFive = cycFive * σ → σ = 1 := by
  decide +kernel

end CFSG.Quasithin.EmptyFaithfulMultiple.L15422

namespace Certificates

open CFSG.Quasithin.EmptyFaithfulMultiple.L15422 in
theorem certificate4952 : (
    Equiv.Perm.sign cycThree = 1
  ) ∧ (
    Equiv.Perm.sign cycFive = 1
  ) ∧ (
    ∀ σ : Equiv.Perm (Fin 6), σ * cycThree = cycThree * σ →
      σ * cycFive = cycFive * σ → σ = 1
  ) :=
  ⟨CFSG.Quasithin.EmptyFaithfulMultiple.L15422.cert4952_cycThree_sign,
    CFSG.Quasithin.EmptyFaithfulMultiple.L15422.cert4952_cycFive_sign,
    CFSG.Quasithin.EmptyFaithfulMultiple.L15422.cert4952_eq_one_of_commute_cyc⟩

end Certificates
