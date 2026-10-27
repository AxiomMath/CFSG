module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7AmbientModel
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseCentralizerSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27QuotientIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvariantOddPSubgroupCertificateDefs
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- In the A₇ component branch, the selected Sylow `2`-subgroup of `M` has
order `8`.  The ambient quotient by the odd core is `A₇`, and the odd kernel
has trivial intersection with the Sylow subgroup. -/
public theorem secondCase_a7_sylow_card
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    ∃ SM : Sylow 2 (↥w.M), Nat.card (SM : Subgroup w.M) = 8 := by
  classical
  let M : Subgroup G := w.M
  have hAmbient := secondCase_a7_ambient_quotient_model hmin c w d hA7 hmodel
  obtain ⟨SM, _hSMcent, _SE, _hSEamb⟩ := secondCase_centralizer_contains_sylow c w d
  let O : Subgroup M := pPrimeCore 2 M
  let q : M →* M ⧸ O := QuotientGroup.mk' O
  have hSMker : (SM : Subgroup M) ⊓ O = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    rw [Subgroup.mem_bot]
    have hxS : x ∈ (SM : Subgroup M) := (Subgroup.mem_inf.mp hx).1
    have hxO : x ∈ O := (Subgroup.mem_inf.mp hx).2
    rcases SM.isPGroup'.exists_card_eq with ⟨n, hn⟩
    have hdvd : orderOf x ∣ 2 ^ n := by
      have hd : orderOf x ∣ Nat.card (SM : Subgroup M) :=
        Subgroup.orderOf_dvd_natCard (SM : Subgroup M) hxS
      rwa [hn] at hd
    have hodd : Odd (orderOf x) :=
      Odd.of_dvd_nat
        (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := M)))
        (Subgroup.orderOf_dvd_natCard O hxO)
    rcases (Nat.dvd_prime_pow Nat.prime_two).mp hdvd with ⟨k, hk, hxeq⟩
    have hk0 : k = 0 := by
      by_contra hkne
      have h2dvd : 2 ∣ orderOf x := by
        rw [hxeq]
        exact ⟨2 ^ (k - 1), by
          rw [show k = (k - 1) + 1 by omega, pow_succ']
          rfl⟩
      exact hodd.not_two_dvd_nat h2dvd
    exact orderOf_eq_one_iff.mp (by simpa [hk0] using hxeq)
  let Q := M ⧸ O
  let SQ : Sylow 2 Q := SM.mapSurjective (QuotientGroup.mk'_surjective O)
  let SA : Sylow 2 (alternatingGroup (Fin 7)) := a7SylowD8
  have hcardSA : Nat.card (SA : Subgroup (alternatingGroup (Fin 7))) = 8 := by
    rw [Sylow.card_eq_multiplicity]
    have hcardA : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card]
      decide
    rw [hcardA]
    rw [show (2520 : ℕ).factorization 2 = 3 by
      rw [show (2520 : ℕ) = 2 ^ 3 * 315 by norm_num]
      rw [Nat.factorization_mul (by norm_num) (by norm_num)]
      rw [Nat.factorization_pow]
      simp [Nat.prime_two.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ (315 : ℕ))]]
    norm_num
  let eQ : Q ≃* alternatingGroup (Fin 7) := by
    simpa [Q, O] using hAmbient.some
  let SAQ : Sylow 2 Q :=
    SA.mapSurjective (f := eQ.symm.toMonoidHom) eQ.symm.surjective
  have hmapSAQ : (SAQ : Subgroup Q) =
    SA.map eQ.symm.toMonoidHom :=
    (Sylow.coe_mapSurjective (f := eQ.symm.toMonoidHom)
      eQ.symm.surjective SA).symm
  have hcardSAQ : Nat.card (SAQ : Subgroup Q) = 8 := by
    rw [hmapSAQ]
    have h := Subgroup.card_map_of_injective
      (K := (SA : Subgroup (alternatingGroup (Fin 7))))
      (f := eQ.symm.toMonoidHom) eQ.symm.injective
    rw [hcardSA] at h
    exact h
  have hcardSQ : Nat.card (SQ : Subgroup Q) = 8 := by
    have h := Nat.card_congr (Sylow.equiv SAQ SQ).toEquiv
    exact hcardSAQ ▸ h.symm
  have hmap : (SQ : Subgroup Q) = (SM : Subgroup M).map q :=
    (Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective O) SM).symm
  have hformula := card_map_eq_card_mul_card_ker q (SM : Subgroup M)
  have hcardSM : Nat.card (SM : Subgroup M) = 8 := by
    rw [hformula, ← hmap, hcardSQ]
    have hqker : q.ker = O := by
      simpa [q] using QuotientGroup.ker_mk' O
    rw [hqker, hSMker]
    simp
  exact ⟨SM, hcardSM⟩

end CFSG.GorensteinWalter
