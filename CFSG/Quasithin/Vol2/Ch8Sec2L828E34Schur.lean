module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828TN5

public section

namespace CFSG.Quasithin.H13

open scoped IsMulCommutative

theorem e4_828_holds : E4_828 := by
  intro Q X _ _ _ hQ h3 ⟨e⟩ _ S hcyc
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite X := Finite.of_equiv _ e.toEquiv
  let π : Q →* X := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ∀ q : Q, π q = 1 ↔ q ∈ Subgroup.center Q := by
    intro q
    show e (QuotientGroup.mk q) = 1 ↔ _
    rw [e.map_eq_one_iff, QuotientGroup.eq_one_iff]
  let R : Subgroup Q := (S : Subgroup X).comap π
  have hRidx : R.index = (S : Subgroup X).index :=
    (S : Subgroup X).index_comap_of_surjective hπs
  let f : R →* (S : Subgroup X) :=
    (π.comp R.subtype).codRestrict (S : Subgroup X) (fun r => r.2)
  haveI : IsCyclic (S : Subgroup X) := hcyc
  have hRab : IsMulCommutative R := by
    refine f.isMulCommutative_of_isCyclic_of_ker_le_center ?_
    intro r hr
    have h1 : π (r : Q) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hr)
    have hz : (r : Q) ∈ Subgroup.center Q := (hker (r : Q)).1 h1
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 hz (g : Q))
  have hperf : commutator Q = ⊤ := hQ.1.commutator_eq_top
  have hV : ∀ q : Q, MonoidHom.transfer (MonoidHom.id R) q = 1 := by
    intro q
    have hle : commutator Q ≤ (MonoidHom.transfer (MonoidHom.id R)).ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hRab.is_comm.comm _ _
    have hq : q ∈ commutator Q := by rw [hperf]; exact Subgroup.mem_top q
    exact MonoidHom.mem_ker.1 (hle hq)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center Q)) 3 h3
  have hzQ : orderOf (z : Q) = 3 := by rw [Subgroup.orderOf_coe, hz]
  have hzR : (z : Q) ∈ R := by
    show π (z : Q) ∈ (S : Subgroup X)
    rw [(hker _).2 z.2]
    exact (S : Subgroup X).one_mem
  have key : ∀ (k : ℕ) (g₀ : Q), g₀⁻¹ * (z : Q) ^ k * g₀ ∈ R →
      g₀⁻¹ * (z : Q) ^ k * g₀ = (z : Q) ^ k := by
    intro k g₀ _
    have hc := Subgroup.mem_center_iff.1 (Subgroup.pow_mem _ z.2 k) g₀
    calc g₀⁻¹ * (z : Q) ^ k * g₀ = g₀⁻¹ * ((z : Q) ^ k * g₀) := mul_assoc _ _ _
      _ = g₀⁻¹ * (g₀ * (z : Q) ^ k) := by rw [hc]
      _ = (z : Q) ^ k := by group
  have hpow := MonoidHom.transfer_eq_pow (MonoidHom.id R) (z : Q) key
  have hz1 : (z : Q) ^ R.index = 1 := by
    have h := hV (z : Q)
    rw [hpow] at h
    exact congrArg Subtype.val h
  have h3R : 3 ∣ R.index := by
    have h := orderOf_dvd_of_pow_eq_one hz1
    rwa [hzQ] at h
  rw [hRidx] at h3R
  exact Sylow.not_dvd_index S h3R

end CFSG.Quasithin.H13
