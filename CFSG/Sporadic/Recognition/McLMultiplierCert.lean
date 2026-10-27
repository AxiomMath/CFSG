module

public import CFSG.Sporadic.Recognition.McLMultiplier
public import CFSG.Sporadic.Recognition.McLMultiplierGlue
public import Certificates.Certificate6107

public section

namespace CFSG.Sporadic.Recognition.McLMultiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Open CFSG.Sporadic.McL

theorem mclMatFacts_of_certificate :
    (∀ r ∈ mclRels, mclEvalY r = 1) ∧ (∀ i : Fin 6, mclEvalY (mclCommWord i) = mclY i) ∧
      mclEvalY mclSurjA = mA ∧ mclEvalY mclSurjB = mB :=
  Certificates.certificate6107.1

theorem mk_mclCommW_of_certificate (i : Fin 6) :
    PresentedGroup.mk (wordSet mclRels) (mclCommW i) = PresentedGroup.of i :=
  Certificates.certificate6107.2.1 i

theorem card_presentedCover_le_of_certificate :
    Finite MclCover ∧ Nat.card MclCover ≤ 2694384000 :=
  Certificates.certificate6107.2.2.1

theorem three_dvd_orderOf_mclR0_of_certificate :
    3 ∣ orderOf (PresentedGroup.mk _ (FreeGroup.mk mclR0) : MclCover) :=
  Certificates.certificate6107.2.2.2

theorem card_presentedGroup_le_of_certificate :
    Finite (PG 6 mclRels) ∧ Nat.card (PG 6 mclRels) ≤ 898128000 :=
  card_presentedGroup_le_of_cover card_presentedCover_le_of_certificate
    three_dvd_orderOf_mclR0_of_certificate mk_mclCommW_of_certificate

section Multiplier


theorem isPresentation_mclGen_of_certificate : IsPresentation mclGen (wordSet mclRels) :=
  isPresentation_mclGen_of mclMatFacts_of_certificate.1 mclMatFacts_of_certificate.2.2.1
    mclMatFacts_of_certificate.2.2.2 card_presentedCover_le_of_certificate
    three_dvd_orderOf_mclR0_of_certificate mk_mclCommW_of_certificate

theorem lift_mclCommW_of_certificate (i : Fin 6) :
    FreeGroup.lift mclGen (mclCommW i) = mclGen i :=
  lift_mclCommW_of mclMatFacts_of_certificate.1 mclMatFacts_of_certificate.2.1 i

theorem card_griessHopfMultiplier_J_of_certificate : Nat.card (griessHopfMultiplier J) = 3 :=
  card_griessHopfMultiplier_J isPresentation_mclGen_of_certificate lift_mclCommW_of_certificate
    card_presentedCover_le_of_certificate three_dvd_orderOf_mclR0_of_certificate

theorem card_griessHopfMultiplier_McL_of_certificate :
    Nat.card (griessHopfMultiplier CFSG.Blueprint.NativeSporadic.McL) = 3 :=
  card_griessHopfMultiplier_McL isPresentation_mclGen_of_certificate lift_mclCommW_of_certificate
    card_presentedCover_le_of_certificate three_dvd_orderOf_mclR0_of_certificate

theorem isCyclic_griessHopfMultiplier_McL_of_certificate :
    IsCyclic (griessHopfMultiplier CFSG.Blueprint.NativeSporadic.McL) :=
  isCyclic_griessHopfMultiplier_McL isPresentation_mclGen_of_certificate
    lift_mclCommW_of_certificate card_presentedCover_le_of_certificate
    three_dvd_orderOf_mclR0_of_certificate

theorem card_center_dvd_three_of_certificate {Q : Type} [Group Q] (hQ : Group.IsPerfect Q)
    (e : Q ⧸ Subgroup.center Q ≃* CFSG.Blueprint.NativeSporadic.McL) :
    Nat.card (Subgroup.center Q) ∣ 3 :=
  card_center_dvd_three isPresentation_mclGen_of_certificate lift_mclCommW_of_certificate
    card_presentedCover_le_of_certificate three_dvd_orderOf_mclR0_of_certificate hQ e

theorem card_ker_dvd_three_of_certificate {E : Type} [Group E] [Group.IsPerfect E]
    (q : E →* CFSG.Sporadic.McL.J) (hq : Function.Surjective q) (hker : q.ker ≤ Subgroup.center E) :
    Nat.card q.ker ∣ 3 :=
  card_ker_dvd_three isPresentation_mclGen_of_certificate lift_mclCommW_of_certificate
    card_presentedCover_le_of_certificate three_dvd_orderOf_mclR0_of_certificate q hq hker

theorem exists_triple_cover_of_certificate :
    ∃ (L : Type) (_ : Group L) (_ : Finite L) (_ : Group.IsPerfect L)
      (q : L →* CFSG.Sporadic.McL.J),
      Function.Surjective q ∧ q.ker ≤ Subgroup.center L ∧ Nat.card q.ker = 3 :=
  exists_triple_cover isPresentation_mclGen_of_certificate lift_mclCommW_of_certificate
    card_presentedCover_le_of_certificate three_dvd_orderOf_mclR0_of_certificate

theorem exists_mulEquiv_of_triple_cover_of_certificate {L : Type} [Group L] [Finite L]
    [Group.IsPerfect L] (q : L →* CFSG.Sporadic.McL.J) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center L) (hcard : Nat.card q.ker = 3) :
    ∃ φ : MclCover ≃* L, q.comp φ.toMonoidHom =
      coverMap isPresentation_mclGen_of_certificate lift_mclCommW_of_certificate :=
  exists_mulEquiv_of_triple_cover isPresentation_mclGen_of_certificate
    lift_mclCommW_of_certificate card_presentedCover_le_of_certificate q hq hker hcard

theorem nonempty_mulEquiv_of_center_card_three_of_certificate {C₁ C₂ : Type} [Group C₁]
    [Group C₂] [Finite C₁] [Finite C₂] [Group.IsPerfect C₁] [Group.IsPerfect C₂]
    (e₁ : C₁ ⧸ Subgroup.center C₁ ≃* CFSG.Blueprint.NativeSporadic.McL)
    (e₂ : C₂ ⧸ Subgroup.center C₂ ≃* CFSG.Blueprint.NativeSporadic.McL)
    (hc₁ : Nat.card (Subgroup.center C₁) = 3) (hc₂ : Nat.card (Subgroup.center C₂) = 3) :
    Nonempty (C₁ ≃* C₂) :=
  nonempty_mulEquiv_of_center_card_three isPresentation_mclGen_of_certificate
    lift_mclCommW_of_certificate card_presentedCover_le_of_certificate e₁ e₂ hc₁ hc₂

theorem exists_mulEquiv_of_triple_covers_of_certificate {L₁ L₂ : Type} [Group L₁] [Group L₂]
    [Finite L₁] [Finite L₂] [Group.IsPerfect L₁] [Group.IsPerfect L₂]
    (q₁ : L₁ →* CFSG.Sporadic.McL.J) (q₂ : L₂ →* CFSG.Sporadic.McL.J)
    (hq₁ : Function.Surjective q₁) (hq₂ : Function.Surjective q₂)
    (hker₁ : q₁.ker ≤ Subgroup.center L₁) (hker₂ : q₂.ker ≤ Subgroup.center L₂)
    (hcard₁ : Nat.card q₁.ker = 3) (hcard₂ : Nat.card q₂.ker = 3) :
    ∃ ψ : L₁ ≃* L₂, q₂.comp ψ.toMonoidHom = q₁ :=
  exists_mulEquiv_of_triple_covers isPresentation_mclGen_of_certificate
    lift_mclCommW_of_certificate card_presentedCover_le_of_certificate q₁ q₂ hq₁ hq₂ hker₁ hker₂
    hcard₁ hcard₂

end Multiplier

end CFSG.Sporadic.Recognition.McLMultiplier
