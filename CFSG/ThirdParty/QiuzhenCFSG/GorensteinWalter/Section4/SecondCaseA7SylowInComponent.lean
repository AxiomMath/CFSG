module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7SylowCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseCentralizerSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27QuotientIndex
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- In the A₇ component branch, the selected Sylow `2`-subgroup of `M` is
contained in the selected component.  Both the ambient Sylow and the
component Sylow have order `8`, so the intersection equality from the
centralizer transfer is an equality with the whole ambient Sylow. -/
public theorem secondCase_a7_sylow_le_component
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    ∃ SM : Sylow 2 (↥w.M),
      Nat.card (SM : Subgroup w.M) = 8 ∧
        (SM : Subgroup w.M).map w.M.subtype ≤ d.E := by
  classical
  obtain ⟨SM, hSMcard⟩ := secondCase_a7_sylow_card hmin c w d hA7 hmodel
  obtain ⟨SM0, _hSMcent, SE, hSEamb⟩ := secondCase_centralizer_contains_sylow c w d
  have hSM0card : Nat.card (SM0 : Subgroup w.M) = 8 := by
    have h := Nat.card_congr (Sylow.equiv SM SM0).toEquiv
    calc
      Nat.card (SM0 : Subgroup w.M) = Nat.card (SM : Subgroup w.M) := h.symm
      _ = 8 := hSMcard
  have hSEcard : Nat.card (SE : Subgroup d.E) = 8 := by
    let Z : Subgroup d.E := Subgroup.center d.E
    let qE : d.E →* d.E ⧸ Z := QuotientGroup.mk' Z
    have hSEker : (SE : Subgroup d.E) ⊓ Z = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      rw [Subgroup.mem_bot]
      have hxS : x ∈ (SE : Subgroup d.E) := (Subgroup.mem_inf.mp hx).1
      have hxZ : x ∈ Z := (Subgroup.mem_inf.mp hx).2
      rcases SE.isPGroup'.exists_card_eq with ⟨n, hn⟩
      have hdvd : orderOf x ∣ 2 ^ n := by
        have hd : orderOf x ∣ Nat.card (SE : Subgroup d.E) :=
          Subgroup.orderOf_dvd_natCard (SE : Subgroup d.E) hxS
        rwa [hn] at hd
      have hodd : Odd (orderOf x) :=
        Odd.of_dvd_nat d.center_odd
          (Subgroup.orderOf_dvd_natCard Z hxZ)
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
    let SQ : Sylow 2 (d.E ⧸ Z) :=
      SE.mapSurjective (QuotientGroup.mk'_surjective Z)
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
    let SAQ : Sylow 2 (d.E ⧸ Z) :=
      SA.mapSurjective (f := hA7.some.symm.toMonoidHom) hA7.some.symm.surjective
    have hmapSAQ : (SAQ : Subgroup (d.E ⧸ Z)) =
        SA.map hA7.some.symm.toMonoidHom :=
      (Sylow.coe_mapSurjective (f := hA7.some.symm.toMonoidHom)
        hA7.some.symm.surjective SA).symm
    have hcardSAQ : Nat.card (SAQ : Subgroup (d.E ⧸ Z)) = 8 := by
      rw [hmapSAQ]
      have h := Subgroup.card_map_of_injective
        (K := (SA : Subgroup (alternatingGroup (Fin 7))))
        (f := hA7.some.symm.toMonoidHom) hA7.some.symm.injective
      rw [hcardSA] at h
      exact h
    have hcardSQ : Nat.card (SQ : Subgroup (d.E ⧸ Z)) = 8 := by
      have h := Nat.card_congr (Sylow.equiv SAQ SQ).toEquiv
      exact hcardSAQ ▸ h.symm
    have hformula := card_map_eq_card_mul_card_ker qE (SE : Subgroup d.E)
    have hmapSQ : (SQ : Subgroup (d.E ⧸ Z)) =
        (SE : Subgroup d.E).map qE :=
      (Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective Z) SE).symm
    rw [hformula, ← hmapSQ, show qE.ker = Z by simpa [qE] using QuotientGroup.ker_mk' Z,
      hSEker, hcardSQ]
    simp
  let Aamb : Subgroup G := (SM0 : Subgroup w.M).map w.M.subtype
  have hSMmapcard : Nat.card Aamb = 8 := by
    rw [Subgroup.card_map_of_injective w.M.subtype_injective, hSM0card]
  have hSEambcard : Nat.card (((SE : Subgroup d.E).map d.E.subtype)) = 8 := by
    rw [Subgroup.card_map_of_injective d.E.subtype_injective, hSEcard]
  have hIntercard : Nat.card (↥(Aamb ⊓ d.E)) = 8 := by
    change Nat.card (↥(((SM0 : Subgroup w.M).map w.M.subtype) ⊓ d.E)) = 8
    rw [← hSEamb]
    exact hSEambcard
  have hEq : Aamb ⊓ d.E = Aamb := by
    apply Subgroup.eq_of_le_of_card_ge (H :=
      Aamb ⊓ d.E) (K := Aamb)
    · exact inf_le_left
    · rw [hIntercard, hSMmapcard]
  refine ⟨SM0, hSM0card, ?_⟩
  change Aamb ≤ d.E
  rw [← hEq]
  exact inf_le_right

end CFSG.GorensteinWalter
