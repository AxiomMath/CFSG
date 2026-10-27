module

public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGC
public import CFSG.Quasithin.Vol2.Ch10SecKGA7b
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem factA7SectionCent_holds : FactA7SectionCent := by
  intro X _ _ hX B ⟨F, _, _, hF, ⟨e⟩⟩ x hx3 hxB
  obtain ⟨ψ, hψ, hN⟩ : ∃ ψ : X →* Equiv.Perm (Fin 7),
      (∀ g, ψ g = 1 → g ∈ Subgroup.center X ∧ g ^ 3 = 1) ∧
        (Nat.card X = 2520 ∨ Nat.card X = 7560) := by
    rcases hX with hA | ⟨-, hZ, ⟨φ⟩⟩
    · obtain ⟨φ⟩ := (hA : Nonempty (X ≃* alternatingGroup (Fin 7)))
      refine ⟨(alternatingGroup (Fin 7)).subtype.comp φ.toMonoidHom, fun g hg => ?_, Or.inl ?_⟩
      · have hg1 : g = 1 := φ.injective (Subtype.ext (by simpa using hg))
        rw [hg1]
        exact ⟨Subgroup.one_mem _, one_pow _⟩
      · rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
          Fintype.card_fin]
        rfl
    · refine ⟨(alternatingGroup (Fin 7)).subtype.comp
        (φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))), fun g hg => ?_, Or.inr ?_⟩
      · have hg' : QuotientGroup.mk' (Subgroup.center X) g = 1 :=
          φ.injective (Subtype.ext (by simpa using hg))
        have hgZ : g ∈ Subgroup.center X := (QuotientGroup.eq_one_iff g).mp hg'
        refine ⟨hgZ, orderOf_dvd_iff_pow_eq_one.mp ?_⟩
        rw [← hZ]
        exact Subgroup.orderOf_dvd_natCard _ hgZ
      · rw [(Subgroup.center X).card_eq_card_quotient_mul_card_subgroup,
          Nat.card_congr φ.toEquiv, hZ, Nat.card_eq_fintype_card, card_alternatingGroup,
          Fintype.card_fin]
        rfl
  by_contra hxZ
  have h5 : 5 ∣ Nat.card B := by
    have h60 : Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = 60 := by
      rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]
      norm_num
    rw [(CFSG.pCore 2 ↥B).card_eq_card_quotient_mul_card_subgroup, h60]
    exact Dvd.dvd.mul_right (by norm_num) _
  obtain ⟨-, hxO, hxC⟩ := hxB
  have h25 : ¬ 25 ∣ Nat.card X := by
    rcases hN with h | h <;> rw [h] <;> norm_num
  obtain ⟨c, hc5, hxc⟩ := C10KG.exists_commute_five h25 h5
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 B) (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 B)
    hxO hxC hx3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hψx : orderOf (ψ x) = 3 := by
    refine orderOf_eq_prime (by rw [← map_pow, ← hx3, pow_orderOf_eq_one, map_one]) fun h => ?_
    exact hxZ (hψ x h).1
  have hψc : orderOf (ψ c) = 5 := by
    refine orderOf_eq_prime (by rw [← map_pow, ← hc5, pow_orderOf_eq_one, map_one]) fun h => ?_
    have h1 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one (hψ c h).2
    rw [hc5] at h1
    norm_num at h1
  refine C10KG.perm_seven_orderOf_ne_fifteen (ψ x * ψ c) ?_
  rw [(hxc.map ψ).orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hψx, hψc]; norm_num), hψx, hψc]

theorem factA7Cent_holds : FactA7Cent := factA7Cent_of factA7SectionCent_holds

end CFSG.Quasithin.Vol2.Ch11.SecA
