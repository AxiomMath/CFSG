module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFL34Four
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.ComponentClassification CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

theorem exists_conj_eq_of_commutator {K : Type} [Group K] [Group.IsPerfect K]
    (hodd : Odd (Nat.card (commutator (Outer (K ⧸ Subgroup.center K)))))
    {U : Subgroup (MulAut K)} (hU4 : Nat.card U = 4) (hsq : ∀ x ∈ U, x * x = 1)
    {y : MulAut K} (hyN : ∀ x ∈ U, y * x * y⁻¹ ∈ U) (hy3 : y ^ 3 = 1)
    {a : MulAut K} (haU : a ∈ U) (hay : y * a * y⁻¹ ≠ a) :
    ∀ u ∈ U, ∃ g : K, u = MulAut.conj g := by
  intro u hu
  obtain ⟨w, hwU, huw⟩ := exists_commutator_eq hU4 hsq hyN hy3 haU hay u hu
  let Φ := PerfectAutomorphisms.centerQuotientHom K
  let q : MulAut (K ⧸ Subgroup.center K) →* Outer (K ⧸ Subgroup.center K) :=
    QuotientGroup.mk' (OuterAutomorphisms.inner (K ⧸ Subgroup.center K))
  have hmem : q (Φ u) ∈ commutator (Outer (K ⧸ Subgroup.center K)) := by
    have h := Subgroup.commutator_mem_commutator (Subgroup.mem_top (q (Φ y)))
      (Subgroup.mem_top (q (Φ w)))
    rw [← commutator_def] at h
    have e : q (Φ u) = ⁅q (Φ y), q (Φ w)⁆ := by
      rw [huw, commutatorElement_def]
      simp only [map_mul, map_inv]
    rw [e]
    exact h
  have hsq1 : q (Φ u) * q (Φ u) = 1 := by
    rw [← map_mul, ← map_mul, hsq u hu, map_one, map_one]
  have hdvd2 : orderOf (q (Φ u)) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hsq1)
  have hdvdn := Subgroup.orderOf_dvd_natCard _ hmem
  have hone : orderOf (q (Φ u)) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
    · exact h
    · rw [h] at hdvdn
      obtain ⟨m, hm⟩ := hdvdn
      obtain ⟨j, hj⟩ := hodd
      omega
  have hq1 : q (Φ u) = 1 := orderOf_eq_one_iff.mp hone
  obtain ⟨p, hp⟩ : Φ u ∈ OuterAutomorphisms.inner (K ⧸ Subgroup.center K) :=
    (QuotientGroup.eq_one_iff _).mp hq1
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) p
  refine ⟨g, ?_⟩
  apply PerfectAutomorphisms.centerQuotientHom_injective K
  rw [centerQuotient_conj]
  exact hp.symm

end CFSG.Quasithin.SBd19F
