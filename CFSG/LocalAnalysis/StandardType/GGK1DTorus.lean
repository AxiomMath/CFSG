module

public import CFSG.LocalAnalysis.StandardType.GGK1DDefs
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

namespace CFSG.StandardType

open CFSG
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup relIndex_omegaGroup omegaGroup_le)
open CFSG.GroupTheory.WeirSylow

private theorem ggK1Dt2_card_omegaGroup {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K V = 2) {ε : ℤ}
    (hε : (ε = 1 ∧ IsPlusType Q) ∨ (ε = -1 ∧ ¬ IsPlusType Q)) :
    (Nat.card (omegaGroup Q hQ) : ℤ) = (Nat.card K : ℤ) - ε := by
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hidx := relIndex_omegaGroup Q hQ
  have hle := omegaGroup_le Q hQ
  have h1 := Subgroup.card_mul_index
    ((omegaGroup Q hQ).subgroupOf (TauCeti.QuadraticMap.orthogonalGroup Q))
  rw [show ((omegaGroup Q hQ).subgroupOf (TauCeti.QuadraticMap.orthogonalGroup Q)).index = 2
        from hidx,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h1
  have h2 := natCard_orthogonalGroup_of_type (K := K) hQ (m := 0) (by simpa using hdim) hε
  have h2' : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) =
      2 * ((Nat.card K : ℤ) - ε) := by
    rw [h2]
    simp
  have hcast : ((Nat.card (omegaGroup Q hQ) * 2 : ℕ) : ℤ) =
      2 * ((Nat.card K : ℤ) - ε) := by
    rw [h1]
    exact h2'
  push_cast at hcast
  linarith

theorem ggK1D_torus_exists {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K V = 2) {p : ℕ} (hp : p.Prime)
    (h : (IsPlusType Q ∧ p ∣ Nat.card K - 1) ∨ (¬ IsPlusType Q ∧ p ∣ Nat.card K + 1)) :
    ∃ e ∈ omegaGroup Q hQ, orderOf e = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun _ _ h => LinearEquiv.ext (congrFun h)
  have hcard : p ∣ Nat.card (omegaGroup Q hQ) := by
    rcases h with ⟨hplus, hdvd⟩ | ⟨hminus, hdvd⟩
    · have hc := ggK1Dt2_card_omegaGroup hQ hdim (ε := 1) (Or.inl ⟨rfl, hplus⟩)
      have hcard : Nat.card (omegaGroup Q hQ) = Nat.card K - 1 := by omega
      rwa [hcard]
    · have hc := ggK1Dt2_card_omegaGroup hQ hdim (ε := -1) (Or.inr ⟨rfl, hminus⟩)
      have hcard : Nat.card (omegaGroup Q hQ) = Nat.card K + 1 := by omega
      rwa [hcard]
  obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' (G := omegaGroup Q hQ) p hcard
  exact ⟨e.1, e.2, by simpa using he⟩

end CFSG.StandardType

end
