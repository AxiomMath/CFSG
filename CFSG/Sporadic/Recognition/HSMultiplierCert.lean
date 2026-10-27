module

public import CFSG.Sporadic.Recognition.HSMultiplier
public import Certificates.Certificate24010

public section

namespace CFSG.Sporadic.Recognition.HSMultiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Open CFSG.Sporadic.Recognition.CoverRecipe
  CFSG.Sporadic.SmallF2

theorem hsTabCheck_eq_true : hsTabCheck = true :=
  Certificates.certificate24010.1

theorem presented_card_le :
    Finite (PG 6 hsRels) ∧ Nat.card (PG 6 hsRels) ≤ 44352000 :=
  Certificates.certificate24010.2.1

theorem cover_card_le :
    Finite HSCover ∧ Nat.card HSCover ≤ 88704000 :=
  Certificates.certificate24010.2.2

theorem isPresentation_hsGen_of_certificate :
    IsPresentation hsGen (wordSet hsRels) := by
  obtain ⟨hfin, hle⟩ := presented_card_le
  have : Finite (PresentedGroup (wordSet hsRels)) := hfin
  exact IsPresentation.of_card_le (lift_hsGen_rels hsTabCheck_eq_true)
    (closure_hsGen hsTabCheck_eq_true) (by rw [card_J]; exact hle)

theorem card_griessHopfMultiplier_J_le_of_certificate :
    0 < Nat.card (griessHopfMultiplier (CFSG.Sporadic.SmallF2.J CFSG.Sporadic.HS.Native.hsData)) ∧
      Nat.card
        (griessHopfMultiplier (CFSG.Sporadic.SmallF2.J CFSG.Sporadic.HS.Native.hsData)) ≤ 2 :=
  card_griessHopfMultiplier_le_of_cover (p := 2) (cw := hsCommWord)
    isPresentation_hsGen_of_certificate (fun i => hsCommW_mem_commutator i)
    (fun i => lift_hsCommW hsTabCheck_eq_true i) (by
      rw [card_J]
      exact cover_card_le)

theorem card_center_le_two_of_certificate
    {Q : Type} [Group Q] (hQ : Group.IsPerfect Q)
    (e : Q ⧸ Subgroup.center Q ≃* CFSG.Blueprint.NativeSporadic.HS) :
    Nat.card (Subgroup.center Q) ≤ 2 := by
  obtain ⟨hpos, hle⟩ := card_griessHopfMultiplier_J_le_of_certificate
  have hd := card_center_dvd_of_cover
    (p := Nat.card (griessHopfMultiplier (J CFSG.Sporadic.HS.Native.hsData)))
    (cw := hsCommWord) isPresentation_hsGen_of_certificate (fun i => hsCommW_mem_commutator i)
    (fun i => lift_hsCommW hsTabCheck_eq_true i) rfl hQ (e.trans CFSG.Sporadic.Bridge.HS.nativeEquiv)
  exact (Nat.le_of_dvd hpos hd).trans hle

end CFSG.Sporadic.Recognition.HSMultiplier
