module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestDefs
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestUnitaryCenter
public import CFSG.LocalAnalysis.StandardType.MarkingClassical
public import CFSG.LieType.Steinberg.CentralExt.OrthogonalTwoMultiplier

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted

namespace OrthRest

section Center

variable {H R : Type} [Group H] [Group R]

theorem center_data [Finite H] (e : H ≃* R) (hZH : Subgroup.center H = ⊥)
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* H), Function.Surjective π →
      π.ker ≤ Subgroup.center E → Nat.Coprime 2 (Nat.card π.ker) →
        ∃ s : H →* E, ∀ h, π (s h) = h)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Subgroup.center R = ⊥ ∧ GGCenterPrime p R := by
  have : Finite R := Finite.of_surjective e e.surjective
  have hZR : Subgroup.center R = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨h, rfl⟩ := e.surjective z
    have hh : h ∈ Subgroup.center H := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply e.injective
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.mp hz (e g)
    rw [hZH, Subgroup.mem_bot] at hh
    rw [hh, map_one]
    exact Subgroup.one_mem _
  refine ⟨hZR, ?_⟩
  intro L' _ _ ψ hψ hker hperf hdvd
  have hnp := StdSubRestU.noTorsion_ker_of_section (q := e.toMonoidHom) e.surjective hsplit hp hp2
    (fun z hz _ => e.injective (by rw [map_one]; exact hz)) hψ hker hperf
  have := Fact.mk hp
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hzk : (z : L') ∈ ψ.ker := by
    have h1 : ψ z ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨l, rfl⟩ := hψ r
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp z.2 l]
    rw [hZR, Subgroup.mem_bot] at h1
    exact h1
  have hzp : (z : L') ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    exact congrArg Subtype.val this
  have h1 : z = 1 := Subtype.ext (hnp _ hzk hzp)
  rw [h1, orderOf_one] at hz
  exact hp.one_lt.ne hz

end Center

section Spin

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem spinMinus_bij {b c : K} (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Function.Bijective (spinToStatedProj (quadMinus n K b c) (range_spinMatrix_quadMinus hn hirr)) ∧
      Subgroup.center (spinGroup (quadMinus n K b c)) = ⊥ := by
  obtain ⟨hq, hkerZ, hker⟩ := spinToStatedProj_quadMinus (K := K) hn hirr
  have hbot : (spinToStatedProj (quadMinus n K b c) (range_spinMatrix_quadMinus hn hirr)).ker =
      ⊥ := by
    rw [hkerZ]
    exact CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.scalarSpinM_eq_bot_of_two_eq_zero hirr
      CharTwo.two_eq_zero
  exact ⟨⟨(MonoidHom.ker_eq_bot_iff _).mp hbot, hq⟩, by rw [← hker, hbot]⟩

omit [Finite K] in
theorem spinPlus_bij (hn : 3 ≤ n) :
    Function.Bijective (spinToStatedProj (quadPlus n K) (range_spinMatrix_quadPlus hn)) ∧
      Subgroup.center (spinGroup (quadPlus n K)) = ⊥ := by
  obtain ⟨hq, hkerZ, hker⟩ := spinToStatedProj_quadPlus (K := K) hn
  have hbot : (spinToStatedProj (quadPlus n K) (range_spinMatrix_quadPlus hn)).ker = ⊥ := by
    rw [hkerZ]
    exact CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed.comap_statedScalars_quadPlus_eq_bot hn
      CharTwo.two_eq_zero
  exact ⟨⟨(MonoidHom.ker_eq_bot_iff _).mp hbot, hq⟩, by rw [← hker, hbot]⟩

end Spin

end OrthRest

section Holds


theorem ggOrthRestCenterInput_holds : GGOrthRestCenterInput := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun K _ _ n m p b c hK hm hp hpn hbc => ?_, fun K _ _ m hK hm => ?_⟩
  · have hn : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · have h1 : 1 < Nat.card K := Finite.one_lt_card
        rw [hK, h0, pow_zero] at h1
        omega
      · exact h0
    have : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn
        hK
    have hp2 : p ≠ 2 := by
      rintro rfl
      have h1 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
      omega
    obtain ⟨hbij, hZ⟩ := OrthRest.spinMinus_bij (K := K) (n := m + 1) (by omega) hbc
    have : Finite (spinGroup (quadMinus (m + 1) K b c)) :=
      CFSG.LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hbc)
    exact OrthRest.center_data
      ((MulEquiv.ofBijective _ hbij).trans (omegaMinusProjEquiv (m + 1) b c).symm) hZ
      (fun E _ _ π hπ hcen hC =>
        CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.spinMinus_exists_section_of_coprime hbc
          (by omega) hπ hcen hC) hp hp2
  · have : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        le_rfl (hK.trans (pow_one 2).symm)
    have hm3 : 3 ≤ m := by omega
    have : NeZero m := ⟨by omega⟩
    obtain ⟨hbij, hZ⟩ := OrthRest.spinPlus_bij (K := K) hm3
    have : Finite (spinGroup (quadPlus m K)) :=
      CFSG.LieType.Steinberg.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
    obtain ⟨O⟩ := CFSG.LieType.Steinberg.nonempty_commOrder_ofCartan
      (plusDatum m K hm3).isFiniteType (Dv := (plusDatum m K hm3).divisible) rfl
    exact OrthRest.center_data (MulEquiv.ofBijective _ hbij) hZ
      (fun E _ _ π hπ hcen hc =>
        CFSG.LieType.Steinberg.CentralExt.FieldFour.exists_section_of_coprime
          (CFSG.LieType.Steinberg.SpinPlus.isCTGroupDatum hm3) (plusDatum_steinbergExtras hm3)
          (CFSG.LieType.Steinberg.SpinPlus.chevalleyExtras hm3 O
            CFSG.LieType.Steinberg.SpinPlus.commC
            (CFSG.LieType.Steinberg.SpinPlus.commutatorFormula hm3 O)) E π hπ hcen hc)
      Nat.prime_three (by norm_num)

end Holds

end CFSG.StandardType
