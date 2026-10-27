module

public import CFSG.Sporadic.Recognition.HeMultiplier
public import Certificates.Certificate6103

public section

namespace CFSG.Sporadic.Recognition.HeMultiplier

open CFSG.Open

theorem card_griessHopfMultiplier_He_of_certificate :
    Nat.card (griessHopfMultiplier CFSG.Blueprint.NativeSporadic.He) = 1 :=
  Certificates.certificate6103

theorem heldTrivialMultiplier_of_certificate :
    CFSG.ComponentClassification.TBLit.HeldTrivialMultiplier := by
  intro Q _ _ hq he
  obtain ⟨e⟩ := he
  have hdvd : Nat.card (Subgroup.center Q) ∣
      Nat.card (griessHopfMultiplier CFSG.Blueprint.NativeSporadic.He) :=
    card_center_dvd_griess hq.1 e
  rw [card_griessHopfMultiplier_He_of_certificate, Nat.dvd_one] at hdvd
  exact Subgroup.eq_bot_of_card_eq _ hdvd

end CFSG.Sporadic.Recognition.HeMultiplier
