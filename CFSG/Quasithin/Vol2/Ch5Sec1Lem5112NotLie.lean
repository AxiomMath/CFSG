module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112A5
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112NotLieOrd
public import CFSG.Timmesfeld.Final.Simple
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.H13

open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

namespace NotLie

theorem card_quot_center_of_simple {X : Type} [Group X] [IsSimpleGroup X] :
    Nat.card (X ⧸ Subgroup.center X) = Nat.card X ∨ Nat.card (X ⧸ Subgroup.center X) = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · left
    exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq h).trans
      QuotientGroup.quotientBot).toEquiv
  · right
    have : Subsingleton (X ⧸ Subgroup.center X) := by
      rw [h]
      exact QuotientGroup.subsingleton_quotient_top
    exact Nat.card_unique

theorem not_of_card {X : Type} [Group X] {m : ℕ} (hm : EvenOrd.Excl m)
    (hX : Nat.card (X ⧸ Subgroup.center X) = m) : ¬ IsLieTypeChar2 X :=
  fun h => EvenOrd.card_ne_of_evenLieType hm h hX

theorem not_of_simple {X : Type} [Group X] [IsSimpleGroup X] {m : ℕ} (hm : EvenOrd.Excl m)
    (hX : Nat.card X = m) : ¬ IsLieTypeChar2 X := by
  rcases card_quot_center_of_simple (X := X) with h | h
  · exact not_of_card hm (h.trans hX)
  · exact not_of_card EvenOrd.excl_one h

theorem not_of_equiv {X S : Type} [Group X] [Group S] [IsSimpleGroup S] (e : X ≃* S) {m : ℕ}
    (hm : EvenOrd.Excl m) (hS : Nat.card S = m) : ¬ IsLieTypeChar2 X := by
  have : IsSimpleGroup X := e.isSimpleGroup
  exact not_of_simple hm ((Nat.card_congr e.toEquiv).trans hS)

theorem card_alt7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem isSimpleGroup_alt7 : IsSimpleGroup (alternatingGroup (Fin 7)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem card_psl2 {X : Type} [Group X] {p e : ℕ} (h : IsPSL 2 p e X) :
    Nat.card X = p ^ e * ((p ^ e) ^ 2 - 1) / Nat.gcd 2 (p ^ e - 1) := by
  obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := h
  rw [Nat.card_congr eK.toEquiv, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL
    (by norm_num), hK]
  norm_num

theorem card_psl35 {X : Type} [Group X] (h : IsPSL 3 5 1 X) : Nat.card X = 372000 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_five h

theorem card_psu35 {K : Type} [Field K] (hK : Nat.card K = 5 ^ 2) :
    Nat.card (StatedProj (StatedSU 3 5 K)) = 126000 := by
  have hK' : Nat.card K = (5 ^ 1) ^ 2 := by rw [hK]; norm_num
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_five le_rfl hK'
    (n := 3) (by norm_num)
  have e : Nat.card (StatedProj (StatedSU 3 5 K)) = Nat.card (StatedProj (StatedSU 3 (5 ^ 1) K)) :=
    rfl
  rw [e, h]
  decide

theorem card_sl35_quot {X : Type} [Group X] (h : IsSL3 5 X) :
    Nat.card (X ⧸ Subgroup.center X) = 372000 := by
  obtain ⟨K, _, _, hK, ⟨eK⟩⟩ := h
  let e₁ : X ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
    eK.trans (specialLinearGroupEquivStatedSL 3 K).symm
  let e₂ : X ⧸ Subgroup.center X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) K :=
    QuotientGroup.congr _ _ e₁ (Subgroup.map_center_eq e₁)
  rw [Nat.card_congr (e₂.trans (projectiveSpecialLinearGroupEquivStatedProj 3 K)).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hK]
  decide

theorem card_su35_quot {X : Type} [Group X] (h : IsSU3 5 X) :
    Nat.card (X ⧸ Subgroup.center X) = 126000 := by
  obtain ⟨K, _, _, hK, ⟨eK⟩⟩ := h
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hK' : Nat.card K = (5 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hZ : Subgroup.center ↥(StatedSU 3 5 K) =
      (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 5 K) :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 5) (f := 1)
      hK' le_rfl (by norm_num)).2
  let e₂ : X ⧸ Subgroup.center X ≃* StatedProj (StatedSU 3 5 K) :=
    QuotientGroup.congr _ _ eK (by rw [Subgroup.map_center_eq eK, hZ])
  rw [Nat.card_congr e₂.toEquiv, card_psu35 hK]

end NotLie

open NotLie in
theorem a314NotLie2_holds :
    A314NotLie2 := by
  refine ⟨fun X _ _ hX => ?_, fun X _ ⟨t, n, f, _, hm⟩ =>
    CFSG.Timmesfeld.isSimpleGroup_of_lieModel hm⟩
  have hA7 := isSimpleGroup_alt7
  have hM22 := CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  have hM23 := CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2
  have hJ1 := CFSG.Sporadic.J1.isSimpleGroup_J1
  have hJ2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  have hJ4 := CFSG.Sporadic.J4.isSimpleGroup_J4
  have hHS := CFSG.Sporadic.HS.isSimpleGroup_HS
  have hRu := CFSG.Sporadic.Ru.isSimpleGroup_Ru
  rcases hX with (hA | ⟨-, -, ⟨e⟩⟩) | (h25 | ⟨p, hp, hp5, hp8, hpsl⟩) | ⟨s, hs⟩ | (h35 | h35) |
      (hM | ⟨-, -, ⟨e⟩⟩) | hM | hJ | hJ | hJ | hJ | hJ
  · exact not_of_equiv (Classical.choice (hA : Nonempty (X ≃* alternatingGroup (Fin 7))))
      EvenOrd.excl_2520 card_alt7
  · exact not_of_card EvenOrd.excl_2520 ((Nat.card_congr e.toEquiv).trans card_alt7)
  · have : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 5 2 h25).2
    exact not_of_simple EvenOrd.excl_7800 (by rw [card_psl2 h25]; decide)
  · have : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 p 1 hpsl).2
    have hp11 := EvenOrd.eleven_le_of_cong hp hp5 hp8
    have hg : Nat.gcd 2 (p - 1) = 2 :=
      Nat.gcd_eq_left ((hp.even_sub_one (by omega)).two_dvd)
    refine not_of_simple (EvenOrd.excl_psl2 hp11 hp8) ?_
    rw [card_psl2 hpsl, pow_one, hg]
  · rcases s
    · rcases hs with h | h
      · have : IsSimpleGroup X :=
          (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity X 3 5 1 h).2
        obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := h
        exact not_of_simple EvenOrd.excl_126000
          ((Nat.card_congr eK.toEquiv).trans (card_psu35 (by rw [hK]; norm_num)))
      · exact not_of_card EvenOrd.excl_126000 (card_su35_quot h)
    · rcases hs with h | h
      · have : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 5 1 h).2
        exact not_of_simple EvenOrd.excl_372000 (card_psl35 h)
      · exact not_of_card EvenOrd.excl_372000 (card_sl35_quot h)
  · have : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 5 1 h35).2
    exact not_of_simple EvenOrd.excl_372000 (card_psl35 h35)
  · exact not_of_card EvenOrd.excl_372000 (card_sl35_quot h35)
  · exact not_of_equiv (S := ↥NativeSporadic.M22) (Classical.choice hM)
      EvenOrd.excl_443520 CFSG.Sporadic.Mathieu.card_M22
  · exact not_of_card EvenOrd.excl_443520
      ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Mathieu.card_M22)
  · exact not_of_equiv (S := ↥NativeSporadic.M23) (Classical.choice hM)
      EvenOrd.excl_10200960 card_native_M23_eq
  · exact not_of_equiv (S := NativeSporadic.J1) (Classical.choice hJ)
      EvenOrd.excl_175560 CFSG.Sporadic.J1.card_J1
  · exact not_of_equiv (S := NativeSporadic.J2) (Classical.choice hJ)
      EvenOrd.excl_604800 CFSG.Sporadic.J2.card_J2
  · exact not_of_equiv (S := NativeSporadic.J4) (Classical.choice hJ)
      EvenOrd.excl_J4 CFSG.Sporadic.J4.card_J4
  · exact not_of_equiv (S := NativeSporadic.HS) (Classical.choice hJ)
      EvenOrd.excl_44352000 CFSG.Sporadic.HS.card_HS
  · exact not_of_equiv (S := NativeSporadic.Ru) (Classical.choice hJ)
      EvenOrd.excl_Ru CFSG.Sporadic.Ru.card_Ru

end CFSG.Quasithin.H13
