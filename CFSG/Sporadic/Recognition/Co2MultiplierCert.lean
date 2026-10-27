module

public import CFSG.Sporadic.Recognition.Co2Multiplier
public import CFSG.Sporadic.Recognition.McLMultiplierCert
public import Certificates.Certificate24011

public section

namespace CFSG.Sporadic.Recognition.Co2Multiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Open

theorem co2TabCheck_eq_true : co2TabCheck = true :=
  Certificates.certificate24011.1

theorem coverIndex_le :
    (genSub (wordSet co2Cover) (subsetOf 7 [0, 1, 2, 3, 4, 5])).FiniteIndex ∧
      (genSub (wordSet co2Cover) (subsetOf 7 [0, 1, 2, 3, 4, 5])).index ≤ 47104 :=
  Certificates.certificate24011.2

theorem card_PG_mclRels_le :
    Finite (PG 6 McLMultiplier.mclRels) ∧ Nat.card (PG 6 McLMultiplier.mclRels) ≤ 898128000 :=
  McLMultiplier.card_presentedGroup_le_of_certificate

theorem card_PG_mclCover_of_certificate :
    Finite (PG 6 McLMultiplier.mclCover) ∧ Nat.card (PG 6 McLMultiplier.mclCover) = 2694384000 :=
  card_PG_mclCover McLMultiplier.isPresentation_mclGen_of_certificate
    McLMultiplier.lift_mclCommW_of_certificate McLMultiplier.card_presentedCover_le_of_certificate
    McLMultiplier.three_dvd_orderOf_mclR0_of_certificate

theorem card_center_dvd_three_of_certificate
    {Q : Type} [Group Q] (hQ : Group.IsPerfect Q)
    (e : Q ⧸ Subgroup.center Q ≃* CFSG.Blueprint.NativeSporadic.Co2) :
    Nat.card (Subgroup.center Q) ∣ 3 :=
  card_center_dvd_three co2TabCheck_eq_true card_PG_mclRels_le card_PG_mclCover_of_certificate
    coverIndex_le hQ e

end CFSG.Sporadic.Recognition.Co2Multiplier
