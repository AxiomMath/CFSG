module

public import CFSG.Sporadic.Recognition.J3MultiplierCover
import Certificates.Kernel.MatCC.J3.UHatA
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

open CFSG.CosetTable CFSG.Monster.Schur CFSG.Sporadic.Recognition.J3Multiplier CFSG.KC.MiscCoset

namespace Certificates

theorem card_uhat_le : Finite (PG 3 uhatWords) ∧ Nat.card (PG 3 uhatWords) ≤ 50232960 :=
  TableFact.card_restrict uhatWords (by norm_num) (subsetOf 3 [1]) (by decide)
    CFSG.KBFact.F24091w CFSG.KBFact.F24091v

open CFSG.CosetTable CFSG.Monster.Schur CFSG.Sporadic.Recognition.J3Multiplier in
theorem certificate24091 : (Finite (PG 2 plainWords) ∧ Nat.card (PG 2 plainWords) ≤ 50232960) ∧
    ∀ e : Fin 2 → Bool, (∃ i, e i = true) →
      Finite (PG (2 + 1) (epsRels U T e)) ∧ Nat.card (PG (2 + 1) (epsRels U T e)) ≤ 50232960 := by
  obtain ⟨hfin, hle⟩ := card_uhat_le
  refine ⟨⟨(card_plain_le_uhat).1, (card_plain_le_uhat).2.trans hle⟩, fun e he => ?_⟩
  exact ⟨(card_eps_le_uhat e he).1, (card_eps_le_uhat e he).2.trans hle⟩

end Certificates
