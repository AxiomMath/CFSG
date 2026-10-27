module

public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofSeitzRest
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofSeitzOther
public import CFSG.RankThree.PartTwo.Sec4.E27.Transport
public import CFSG.RankThree.PartTwo.Sec4.E27.Vac
public import CFSG.RankThree.PartTwo.Sec4.E27.Inner
public import CFSG.RankThree.PartTwo.Sec4.E27.FixReeF4
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434OtherVacuityU

public section

open CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.CTP
open CFSG.Assembly.RankThreeEven (projSL projSU)

open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartOne

namespace CFSG.RankThree.PartTwo.Sec4.E27

@[expose] def Seitz27L3F : Prop :=
  ∀ n : ℕ, 4 ≤ n → n ≠ 6 → 3 ∣ n → ∀ (X : Type) [Group X] [Finite X], IsoLThreePi X 2 n →
    Seitz27 X

@[expose] def Seitz27D4 : Prop :=
  ∀ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 → 2 ≤ q.exponent →
    ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* Cat ⟨TauCeti.LieTypeIndex.trialityD4 q, hq⟩) →
      Seitz27 X

@[expose] def ReeF4EightFixPlaneGen : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K CFSG.LieType.Ree.ReeTag.F4.prime],
    Nat.card K = 2 ^ (2 * 1 + 1) → FixPlaneGen (CFSG.LieType.Ree.ReeTag.F4.reeGamma K 1) 3

section Plain

theorem seitz27_isoLThreePi_two (hL3F : Seitz27L3F) {n : ℕ} (hn4 : 4 ≤ n) (hn6 : n ≠ 6)
    {Y : Type} [Group Y] [Finite Y] (h : IsoLThreePi Y 2 n) : Seitz27 Y := by
  by_cases h3 : 3 ∣ n
  · exact hL3F n hn4 hn6 h3 Y h
  · have h2n : 2 < 2 ^ n := by
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hn4
      norm_num at this
      omega
    rcases h with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
    · exact seitz27_projSL_vac (by norm_num) (by omega) h3 φ
    · exact seitz27_projSU_vac (by norm_num) (by omega) h2n h3 φ

theorem seitz27_l3_threeDvd (hL3F : Seitz27L3F) {n : ℕ} (hn4 : 4 ≤ n) (hn6 : n ≠ 6) (h3 : 3 ∣ n)
    {Y : Type} [Group Y] [Finite Y]
    (h : Nonempty (Y ≃* projSL 3 (GaloisField 2 n)) ∨ Nonempty (Y ≃* projSU 3 2 n)) :
    Seitz27 Y := by
  rcases pow_mod_three_cases (p := 2) (e := n) Nat.prime_two (by norm_num) with h1 | h2
  · rcases h with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · exact hL3F n hn4 hn6 h3 Y (Or.inl ⟨h1, ⟨φ⟩⟩)
    · exact seitz27_projSU_wrongpi (by omega) h1 φ
  · rcases h with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · exact seitz27_projSL_wrongpi (by omega) h2 φ
    · exact hL3F n hn4 hn6 h3 Y (Or.inr ⟨h2, ⟨φ⟩⟩)

theorem seitz27_projSL_eight : Seitz27 (projSL 3 (GaloisField 2 3)) := by
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) (GaloisField 2 3)) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk :
      Matrix.GeneralLinearGroup (Fin 3) (GaloisField 2 3) →* _) Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (projSL 3 (GaloisField 2 3)) := Subtype.finite
  exact seitz27_of_card_le_nine fun B hB =>
    Sec4.Res4Three.card_le_nine_of_pRank_le_two
      pRank_three_mulAut_projSL_three_eight_le_two B hB

theorem seitz27_projSU_sixtyFour : Seitz27 (projSU 3 2 6) := by
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * 6))) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk :
      Matrix.GeneralLinearGroup (Fin 3) (GaloisField 2 (2 * 6)) →* _)
        Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (projSU 3 2 6) := Subtype.finite
  exact seitz27_of_card_le_nine fun B hB =>
    Sec4.Res4Three.card_le_nine_of_pRank_le_two
      pRank_three_mulAut_projSU_three_sixtyFour_le_two B hB

end Plain

section Rows

theorem seitz27_of_isSmallTwoOtherField (hD4 : Seitz27D4)
    (hF5c : ReeF4EightFixPlaneGen) {Y : Type}
    [Group Y] [Finite Y] (hY : IsSmallTwoOtherField Y) : Seitz27 Y := by
  rcases hY with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨q, hqp, hqe, hG⟩ | ⟨q, hq, hqp, hqe, ⟨φ⟩⟩ |
    ⟨m, hm, hm1, ⟨φ⟩⟩
  · exact seitz27_of_mulEquiv φ seitz27_projSL_eight
  · exact seitz27_of_mulEquiv φ seitz27_projSU_sixtyFour
  · exact seitz27_of_mulEquiv φ (seitz27_projSp (n := 6) (by norm_num))
  · exact seitz27_of_mulEquiv φ (seitz27_projSU4 (n := 6) (by norm_num))
  · exact seitz27_isoGTwo q hqp (by omega) hG
  · exact hD4 q hq hqp (by omega) Y ⟨φ⟩
  · obtain ⟨K, _, _, _, hm0, hK, -, ⟨e⟩⟩ := exists_reeGamma_equiv_cat hm
    have hm1' : m = 1 := by omega
    subst hm1'
    exact seitz27_of_mulEquiv (φ.trans e)
      (seitz27_reeF4_of_plane le_rfl hK (hF5c K hK))

theorem seitz434OtherTwentySeven_of_rows (hD4 : Seitz27D4)
    (hF5c : ReeF4EightFixPlaneGen) :
    Seitz434OtherTwentySeven := by
  intro X _ _ hq hZ hL E hE h27
  have eZ : (X ⧸ Subgroup.center X) ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact (seitz27_of_mulEquiv eZ.symm (seitz27_of_isSmallTwoOtherField hD4 hF5c hL)) E hE h27

section S7

theorem seitz27_reeF4_rows {m : ℕ} (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid) (hm2 : 2 ≤ m)
    {Y : Type} [Group Y] (φ : Y ≃* Cat ⟨TauCeti.LieTypeIndex.reeF4 m, hv⟩) : Seitz27 Y := by
  obtain ⟨K, _, _, _, -, hK, -, ⟨e⟩⟩ := exists_reeGamma_equiv_cat hv
  exact seitz27_of_mulEquiv (φ.trans e) (seitz27_reeF4 hm2 hK)

theorem seitz27_of_isLie42GenericRest (hL3F : Seitz27L3F) (hD4 : Seitz27D4) {Y : Type} [Group Y]
    [Finite Y] (hY : IsLie42GenericRest Y) : Seitz27 Y := by
  rcases hY with ⟨p, e, hpF, hp3, he1, he2, hiso⟩ | ⟨p, hpF, hp3, hrow⟩ |
    ⟨n, hn4, hn6, hrow⟩ | ⟨q, hqp, hq4, hq6, hG⟩ | ⟨q, hq, hqp, hq4, hq6, ⟨φ⟩⟩ |
    ⟨m, hm, hm2, ⟨φ⟩⟩
  ·
    haveI := hpF
    rcases hiso with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
    · exact seitz27_projSL_vac (by omega) he1 (by omega) φ
    · have hq : 2 < p ^ e := lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) p)
      exact seitz27_projSU_vac (by omega) he1 hq (by omega) φ
  ·
    haveI := hpF
    rcases hrow with ⟨q, hqp, hqe, hG⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · exact seitz27_isoGTwo_prime q hqe (hqp ▸ hp3) hG
    · exact seitz27_projSp_prime hp3 φ
    · exact seitz27_projSL4_prime hp3 φ
    · exact seitz27_projSU4_prime hp3 φ
  ·
    rcases hrow with hL | ⟨h3, hSLU⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · exact seitz27_isoLThreePi_two hL3F hn4 hn6 hL
    · exact seitz27_l3_threeDvd hL3F hn4 hn6 h3 hSLU
    · exact seitz27_of_mulEquiv φ (seitz27_projSp hn4)
    · exact seitz27_of_mulEquiv φ (seitz27_projSU4 hn4)
  · exact seitz27_isoGTwo q hqp hq4 hG
  · exact hD4 q hq hqp (by omega) Y ⟨φ⟩
  · exact seitz27_reeF4_rows hm hm2 φ

theorem seitz434RestTwentySeven_of_rows (hL3F : Seitz27L3F) (hD4 : Seitz27D4) :
    Seitz434RestTwentySeven := by
  intro X _ _ hq hZ hL E hE h27
  have eZ : (X ⧸ Subgroup.center X) ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact (seitz27_of_mulEquiv eZ.symm (seitz27_of_isLie42GenericRest hL3F hD4 hL)) E hE h27

end S7

end Rows

end CFSG.RankThree.PartTwo.Sec4.E27
