module

public import CFSG.Sporadic.Recognition.M22Multiplier
public import Certificates.Certificate24093
public import Certificates.Certificate24094

public section

namespace CFSG.Sporadic.Recognition.M22Multiplier

open CFSG.CosetTable

theorem m22TabCheck_eq_true : m22TabCheck = true :=
  Certificates.certificate24093.1

theorem card_PG_m22Rels_le :
    Finite (PG 2 m22Rels) ∧ Nat.card (PG 2 m22Rels) ≤ 443520 :=
  Certificates.certificate24093.2

theorem cover_bounds :
    Finite (PG 2 m22Cover) ∧ Nat.card (PG 2 m22Cover) ≤ 5322240 ∧
      12 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin 2) | r ∈ m22Cover.map FreeGroup.mk}
        (FreeGroup.mk m22B11)) :=
  Certificates.certificate24094

theorem center_cyclic_dvd_twelve_of_certificate
    {Q : Type} [Group Q]
    (hQ : Group.IsPerfect Q)
    (e : Q ⧸ Subgroup.center Q ≃* CFSG.Blueprint.NativeSporadic.M22) :
    IsCyclic (Subgroup.center Q) ∧ Nat.card (Subgroup.center Q) ∣ 12 :=
  center_cyclic_dvd_twelve m22TabCheck_eq_true card_PG_m22Rels_le cover_bounds hQ e

end CFSG.Sporadic.Recognition.M22Multiplier
