module

public import Certificates.Certificate24320

public section

namespace CFSG.Sporadic.Recognition.ONMultiplier

open CFSG.CosetTable

theorem center_eq_bot_of_certificate
    {Q : Type} [Group Q] [Finite Q] (hQ : Group.IsPerfect Q) (hZ : IsPGroup 2 (Subgroup.center Q))
    (e : Q ⧸ Subgroup.center Q ≃* CFSG.Blueprint.NativeSporadic.ON) :
    Subgroup.center Q = ⊥ := by
  obtain ⟨hT, -, hfin, hcard⟩ := Certificates.certificate24320
  obtain ⟨hgen, hrels, hcw⟩ := @hT
  exact CFSG.Sporadic.Recognition.CoverRecipe.center_eq_bot_of_cover₂ (g := onGF) (R := onRels)
    (cw := onCommWord) hgen hrels (fun i => CFSG.LieType.Multipliers.mk_commWords_mem_commutator _)
    hcw hfin (hcard.trans CFSG.Sporadic.ON.card_J.ge) hQ hZ (e.trans CFSG.Sporadic.ON.onEquivJ)

end CFSG.Sporadic.Recognition.ONMultiplier
