module

public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionAction
public import CFSG.LocalAnalysis.SectionRank.Ccomm.CriticalDefinition
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators

public section

namespace CFSG.RankThree.PartOne.OddCore37

open CFSG CFSG.SectionRank.Ccomm
open scoped commutatorElement

variable {G : Type*} [Group G]

variable [Finite G]

theorem exists_critical_commutator {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A R : Subgroup G}
    (hA : Nat.card A = p) (hR2 : IsPGroup 2 R) (hRA : A ≤ Subgroup.normalizer (R : Set G))
    (hcomm : ⁅R, A⁆ = R) (hRne : R ≠ ⊥) :
    ∃ T : Subgroup G, T ≤ R ∧ ThompsonCritical (T.subgroupOf R) ∧
      A ≤ Subgroup.normalizer (T : Set G) ∧ ⁅T, A⁆ ≠ ⊥ ∧ ⁅⁅T, A⁆, A⁆ = ⁅T, A⁆ ∧
      A ≤ Subgroup.normalizer ((⁅T, A⁆ : Subgroup G) : Set G) ∧ ⁅T, A⁆ ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨T₀, hT₀⟩, hne⟩ := thompson_critical_subgroup (p := 2) (P := ↥R) hR2
  set T : Subgroup G := T₀.map R.subtype with hT
  have hTR : T ≤ R := Subgroup.map_subtype_le _
  have hTsub : T.subgroupOf R = T₀ :=
    Subgroup.comap_map_eq_self_of_injective R.subtype_injective T₀
  have hTcrit : ThompsonCritical (T.subgroupOf R) := hTsub ▸ hT₀
  have hAT : A ≤ Subgroup.normalizer (T : Set G) :=
    le_normalizer_of_characteristic hRA hTR (hTsub ▸ hT₀.1)
  have hApg : IsPGroup p A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hcop : Nat.Coprime p (Nat.card R) := by
    obtain ⟨k, hk⟩ := hR2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hcopT : Nat.Coprime p (Nat.card T) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hTR) hcop
  have hTA : ⁅T, A⁆ ≠ ⊥ := by
    intro hbot
    have hAcT : A ≤ Subgroup.centralizer (T : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 (by rw [Subgroup.commutator_comm]; exact hbot)
    have hself : Subgroup.centralizer (T₀ : Set ↥R) ≤ T₀ := fun x hx => (hT₀.2.2.2 ▸ hx).1
    have hall : A ≤ Subgroup.centralizer (R : Set G) := by
      intro a ha
      have hcon : conjHom A R hRA ⟨a, ha⟩ = 1 := by
        refine CFSG.ComponentClassification.CoprimeAutomorphisms.eq_one_of_self_centralizing
          2 hR2 T₀ hself _ p ?_ hcop ?_
        · rw [← map_pow]
          have : (⟨a, ha⟩ : ↥A) ^ p = 1 := by
            have h := pow_card_eq_one' (x := (⟨a, ha⟩ : ↥A))
            rwa [hA] at h
          rw [this, map_one]
        · intro x hx
          apply Subtype.ext
          have hxT : (x : G) ∈ T := ⟨x, hx, rfl⟩
          have h1 : (x : G) * a = a * x := Subgroup.mem_centralizer_iff.1 (hAcT ha) _ hxT
          change a * x * a⁻¹ = x
          rw [← h1]
          group
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have h := congrArg (fun f : MulAut ↥R => ((f ⟨r, hr⟩ : ↥R) : G)) hcon
      change a * r * a⁻¹ = r at h
      calc r * a = a * r * a⁻¹ * a := by rw [h]
        _ = a * r := by group
    have hbot : ⁅R, A⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hall
    exact hRne (by rw [← hcomm, hbot])
  exact ⟨T, hTR, hTcrit, hAT, hTA,
    CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent p hp A T hApg hAT
      hcopT,
    CFSG.SignalizerFunctor.Helpers.normalized_commutator_normalized A T hAT,
    CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing T A hAT⟩

end CFSG.RankThree.PartOne.OddCore37
