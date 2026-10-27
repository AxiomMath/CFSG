module

public import CFSG.Sporadic.Recognition.M23Multiplier
public import Certificates.Certificate24000

public section

namespace CFSG.Sporadic.Recognition.M23Multiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Open CFSG.Sporadic.Recognition.CoverRecipe

theorem m23TabCheck_eq_true : m23TabCheck = true :=
  Certificates.certificate24000.1

theorem presented_card_le :
    Finite (PG 6 m23Rels) ∧ Nat.card (PG 6 m23Rels) ≤ 10200960 :=
  Certificates.certificate24000.2.1

theorem cover_card_le :
    Finite M23Cover ∧ Nat.card M23Cover ≤ 10200960 :=
  Certificates.certificate24000.2.2

theorem isPresentation_m23Gen_of_certificate :
    IsPresentation m23Gen (wordSet m23Rels) := by
  obtain ⟨hfin, hcard⟩ := presented_card_le
  have : Finite (PresentedGroup (wordSet m23Rels)) := hfin
  exact IsPresentation.of_card_le (lift_m23Gen_rels m23TabCheck_eq_true)
    (closure_m23Gen m23TabCheck_eq_true) (hcard.trans card_m23.ge)

theorem card_griessHopfMultiplier_M23_of_certificate :
    Nat.card (griessHopfMultiplier CFSG.Blueprint.NativeSporadic.M23) = 1 := by
  obtain ⟨hfin, hcard⟩ := cover_card_le
  obtain ⟨hpos, hle⟩ := card_griessHopfMultiplier_le_of_cover (cw := m23CommWord) (p := 1)
    isPresentation_m23Gen_of_certificate (fun i => m23CommW_mem_commutator i)
    (fun i => lift_m23CommW m23TabCheck_eq_true i)
    ⟨hfin, hcard.trans (by rw [one_mul, card_m23])⟩
  omega

theorem card_ker_eq_one_of_certificate
    {E : Type} [Group E] [Group.IsPerfect E]
    (q : E →* CFSG.Blueprint.NativeSporadic.M23) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center E) : Nat.card q.ker = 1 :=
  Nat.dvd_one.1 (card_ker_dvd_of_cover (p := 1) (cw := m23CommWord)
    isPresentation_m23Gen_of_certificate (fun i => m23CommW_mem_commutator i)
    (fun i => lift_m23CommW m23TabCheck_eq_true i)
    card_griessHopfMultiplier_M23_of_certificate q hq hker)

theorem card_center_eq_one_of_certificate
    {Q : Type} [Group Q] (hQ : Group.IsPerfect Q)
    (e : Q ⧸ Subgroup.center Q ≃* CFSG.Blueprint.NativeSporadic.M23) :
    Nat.card (Subgroup.center Q) = 1 :=
  Nat.dvd_one.1 (card_center_dvd_of_cover (p := 1) (cw := m23CommWord)
    isPresentation_m23Gen_of_certificate (fun i => m23CommW_mem_commutator i)
    (fun i => lift_m23CommW m23TabCheck_eq_true i)
    card_griessHopfMultiplier_M23_of_certificate hQ e)

end CFSG.Sporadic.Recognition.M23Multiplier
