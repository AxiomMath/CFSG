module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4Defs
public import CFSG.LieType.BorelExponent.Linear
public import CFSG.LieType.BorelExponent.Unitary
public import CFSG.LieType.BorelExponent.Symplectic
public import CFSG.LieType.BorelExponent.OrthogonalPlus
public import CFSG.LieType.BorelExponent.OrthogonalMinus
public import CFSG.LieType.BorelExponent.Chevalley
public import CFSG.LieType.BorelExponent.TwistedE6
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSL
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSp
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPOmegaEven
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderE6
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedE7
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedE8
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedF4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LieType.BorelExponent
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.ComponentClassification.CatLeaf (lieOrderDivisor)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.HardMathSupport.Lang.Coordinator (OuterFixedOrderBoundAt)

private theorem two_pow_sub_one_dvd_two_pow_two_mul_sub_one (f : ℕ) :
    2 ^ f - 1 ∣ 2 ^ (2 * f) - 1 := by
  have h := Nat.pow_sub_pow_dvd_pow_sub_pow (x := 2) (y := 1) (Dvd.intro_left 2 rfl :
    f ∣ 2 * f)
  rwa [one_pow, one_pow] at h

private theorem two_pow_add_one_dvd_two_pow_two_mul_sub_one (f : ℕ) :
    2 ^ f + 1 ∣ 2 ^ (2 * f) - 1 := by
  refine ⟨2 ^ f - 1, ?_⟩
  have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  rw [mul_comm 2 f, pow_mul]
  zify [h1, Nat.one_le_pow 2 (2 ^ f) (by omega)]
  ring

private theorem not_dvd_gcd_of_le_four {r k c : ℕ} (hr5 : 5 ≤ r) (hk0 : 0 < k) (hk : k ≤ 4) :
    ¬ r ∣ Nat.gcd k c := by
  intro h
  have hle : r ≤ Nat.gcd k c := Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ hk0) h
  have : Nat.gcd k c ≤ k := Nat.le_of_dvd hk0 (Nat.gcd_dvd_left k c)
  omega

theorem dvd_lieBorelExponent_of_borelAut {X : Type} [Group X] [Finite X] {t : StatedLieTag}
    {m f : ℕ} (hadm : StatedLieAdmissible t m 2 f) (hLie : CFSG.Blueprint.LieModel X t m 2 f)
    (hOut : OuterFixedOrderBoundAt t) (hB : BorelExponentAt t) (hTits : t ≠ .Tits)
    (hD4 : t ≠ .trialityD4) {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) {r : ℕ} (hr : r.Prime)
    (hr5 : 5 ≤ r) (hrf : ¬ r ∣ f) (hdiv : ¬ r ∣ lieOrderDivisor t m (2 ^ f)) {α : MulAut X}
    (hα1 : α ≠ 1) (hαr : α ^ r = 1) (hαU : U.map α.toMonoidHom = U) :
    r ∣ lieBorelExponent t f := by
  have hin : α ∈ inner X := by
    by_contra hin
    rcases hOut X m 2 f hadm hLie hTits r hr (by omega) hdiv (fun h => by omega) α hαr hin with
      ⟨f₀, hf, -⟩ | ⟨h, -⟩
    · exact hrf ⟨f₀, hf⟩
    · exact hD4 h
  obtain ⟨x, rfl⟩ := hin
  have : Fact r.Prime := ⟨hr⟩
  have hxU : x ∈ Subgroup.normalizer (U : Set X) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 hαU
  exact (hB X m f hadm hLie).dvd_of_orderOf_conj hU hr (by omega)
    (orderOf_eq_prime hαr hα1) hxU


theorem kLieBorelAutPrime_of_borelExponent
    (hL : BorelExponentAt .PSL) (hU : BorelExponentAt .PSU) (hSp : BorelExponentAt .PSp)
    (hOp : BorelExponentAt .POmegaPlus) (hOm : BorelExponentAt .POmegaMinus)
    (hF4 : BorelExponentAt .F4) (hE6 : BorelExponentAt .E6) (hE7 : BorelExponentAt .E7)
    (hE8 : BorelExponentAt .E8) (h2E6 : BorelExponentAt .twistedE6) : KLieBorelAutPrime := by
  intro X _ _ t m f hadm hLie hrank U hUs r hr hr5 hrf α hα1 hαr hαU
  have hdvd2 := two_pow_sub_one_dvd_two_pow_two_mul_sub_one f
  have hfin : r ∣ 2 ^ f - 1 →
      r ∣ 2 ^ (2 * f) - 1 ∧ (t ≠ .PSU → t ≠ .POmegaMinus → t ≠ .twistedE6 → r ∣ 2 ^ f - 1) :=
    fun h => ⟨h.trans hdvd2, fun _ _ _ => h⟩
  have key := fun (hO : OuterFixedOrderBoundAt t) (hB : BorelExponentAt t) (hT : t ≠ .Tits)
      (hD : t ≠ .trialityD4) (hd : ¬ r ∣ lieOrderDivisor t m (2 ^ f)) =>
    dvd_lieBorelExponent_of_borelAut hadm hLie hO hB hT hD hUs hr hr5 hrf hd hα1 hαr hαU
  cases t with
  | PSL =>
    by_cases hd : r ∣ lieOrderDivisor .PSL m (2 ^ f)
    · exact hfin (hd.trans (Nat.gcd_dvd_right _ _))
    · exact hfin (key CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.outerFixedOrderBoundAt_PSL
        hL (by decide) (by decide) hd)
  | PSU =>
    by_cases hd : r ∣ lieOrderDivisor .PSU m (2 ^ f)
    · exact ⟨(hd.trans (Nat.gcd_dvd_right _ _)).trans
        (two_pow_add_one_dvd_two_pow_two_mul_sub_one f), fun h => absurd rfl h⟩
    · exact ⟨key CFSG.HardMathSupport.Lang.Coordinator.outerFixedOrderBoundAt_PSU hU
        (by decide) (by decide) hd, fun h => absurd rfl h⟩
  | PSp =>
    have hd : ¬ r ∣ lieOrderDivisor .PSp m (2 ^ f) := by
      simp only [lieOrderDivisor]
      exact not_dvd_gcd_of_le_four hr5 (by norm_num) (by norm_num)
    exact hfin (key CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.outerFixedOrderBoundAt_PSp
      hSp (by decide) (by decide) hd)
  | POmegaOdd => exact absurd rfl hadm.2.2.2
  | POmegaPlus =>
    have hd : ¬ r ∣ lieOrderDivisor .POmegaPlus m (2 ^ f) := by
      simp only [lieOrderDivisor]
      exact not_dvd_gcd_of_le_four hr5 (by norm_num) (by norm_num)
    exact hfin (key CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.outerFixedOrderBoundAt_POmegaPlus
      hOp (by decide) (by decide) hd)
  | POmegaMinus =>
    have hd : ¬ r ∣ lieOrderDivisor .POmegaMinus m (2 ^ f) := by
      simp only [lieOrderDivisor]
      exact not_dvd_gcd_of_le_four hr5 (by norm_num) (by norm_num)
    exact ⟨key CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.outerFixedOrderBoundAt_POmegaMinus
      hOm (by decide) (by decide) hd, fun _ h => absurd rfl h⟩
  | G2 => simp [PartTwo.S17.CS17LieRank] at hrank
  | F4 =>
    have hd : ¬ r ∣ lieOrderDivisor .F4 m (2 ^ f) := by
      simp only [lieOrderDivisor, Nat.dvd_one]
      omega
    exact hfin (key CFSG.HardMathSupport.Lang.E6Descent.outerFixedOrderBoundAt_F4 hF4
      (by decide) (by decide) hd)
  | E6 =>
    have hd : ¬ r ∣ lieOrderDivisor .E6 m (2 ^ f) := by
      simp only [lieOrderDivisor]
      exact not_dvd_gcd_of_le_four hr5 (by norm_num) (by norm_num)
    exact hfin (key CFSG.HardMathSupport.Lang.Coordinator.outerFixedOrderBoundAt_E6 hE6
      (by decide) (by decide) hd)
  | E7 =>
    have hd : ¬ r ∣ lieOrderDivisor .E7 m (2 ^ f) := by
      simp only [lieOrderDivisor]
      exact not_dvd_gcd_of_le_four hr5 (by norm_num) (by norm_num)
    exact hfin (key CFSG.HardMathSupport.Lang.E6Descent.outerFixedOrderBoundAt_E7 hE7
      (by decide) (by decide) hd)
  | E8 =>
    have hd : ¬ r ∣ lieOrderDivisor .E8 m (2 ^ f) := by
      simp only [lieOrderDivisor, Nat.dvd_one]
      omega
    exact hfin (key CFSG.HardMathSupport.Lang.E6Descent.outerFixedOrderBoundAt_E8 hE8
      (by decide) (by decide) hd)
  | twistedE6 =>
    have hd : ¬ r ∣ lieOrderDivisor .twistedE6 m (2 ^ f) := by
      simp only [lieOrderDivisor]
      exact not_dvd_gcd_of_le_four hr5 (by norm_num) (by norm_num)
    exact ⟨key CFSG.HardMathSupport.Lang.Coordinator.outerFixedOrderBoundAt_twistedE6 h2E6
      (by decide) (by decide) hd, fun _ _ h => absurd rfl h⟩
  | trialityD4 => simp [PartTwo.S17.CS17LieRank] at hrank
  | twistedB2 => simp [PartTwo.S17.CS17LieRank] at hrank
  | twistedG2 => simp [PartTwo.S17.CS17LieRank] at hrank
  | twistedF4 => simp [PartTwo.S17.CS17LieRank] at hrank
  | Tits => simp [PartTwo.S17.CS17LieRank] at hrank

theorem kLieBorelAutPrime_holds : KLieBorelAutPrime :=
  kLieBorelAutPrime_of_borelExponent borelExponentAt_PSL borelExponentAt_PSU borelExponentAt_PSp
    borelExponentAt_POmegaPlus borelExponentAt_POmegaMinus borelExponentAt_F4 borelExponentAt_E6
    borelExponentAt_E7 borelExponentAt_E8 borelExponentAt_twistedE6

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
