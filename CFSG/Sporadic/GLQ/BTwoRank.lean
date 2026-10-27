module

public import CFSG.Sporadic.GLQ.RegisterProgram
public import Certificates.Certificate2080

public section

namespace CFSG.Sporadic.GLQ

theorem b_two_rank_at_least_five :
    ∀ (K : Type*) [Group K] [Finite K], Nonempty (K ≃* CFSG.Blueprint.NativeSporadic.B) →
      (∃ A : Subgroup K, CFSG.IsElementaryAbelian 2 A ∧ Nat.card A = 32) ∧
        5 ≤ CFSG.pRank 2 K := by
  intro K _ _ hK
  obtain ⟨f⟩ := hK
  obtain ⟨x, hsq, hcomm, hker⟩ := Certificates.certificate2080
  obtain ⟨-, -, -, -, hE, hcard⟩ := exists_elemAbelian_two x hsq hcomm hker
  obtain ⟨⟨A, hA, hAc⟩, hr⟩ := transport_elemAbelian_two _ hE hcard f
  exact ⟨⟨A, hA, hAc.trans rfl⟩, hr⟩

end CFSG.Sporadic.GLQ
