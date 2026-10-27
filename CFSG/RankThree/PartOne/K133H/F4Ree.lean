module

public import CFSG.RankThree.PartOne.K133H.F4Core
public import CFSG.RankThree.PartOne.K133B.Defs
public import CFSG.RankThree.PartOne.K133.MaxItems
public import CFSG.RankThree.PartOne.SEITZX.ReeSplit

public section

namespace CFSG.RankThree.PartOne.K133H

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K133 CFSG.RankThree.PartOne.K133B

set_option linter.unusedSectionVars false

theorem reeGamma_le_adjointGroup {X : Type} [Field X] [Finite X] [CharP X ReeTag.F4.prime]
    {m : ℕ} {y : ModGL ReeTag.F4.tag X}
    (hy : y ∈ ReeTag.F4.reeGamma X m) : y ∈ adjointGroup .F4 X := by
  obtain ⟨z, -, rfl⟩ := Subgroup.mem_map.1 hy
  exact z.2

theorem row8OddAt_leaf7_nine : Row8OddAt (K133.leaf7 9) := by
  intro Q _ _ p g Ē hp11 hZ hX h
  obtain ⟨m, hiso⟩ := hX
  have hp := h.prime
  have hp5 := h.five_le
  have : Fact p.Prime := ⟨hp⟩
  have := h.elem
  obtain ⟨X, _, _, hch, hm1, hXc, ⟨eK⟩⟩ := SEITZX.exists_reeGamma_model hiso
  have hch2 : CharP X 2 := hch
  let ce : Q ≃* Q ⧸ Subgroup.center Q :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  let eQ : Q ≃* ↥(ReeTag.F4.reeGamma X m) := ce.trans eK
  have hpX : ¬ p ∣ Nat.card X := by
    rw [hXc]
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd)
    omega
  intro _
  exact oddOrderOneOrThree_torusImage_F4 (ℓ := 2) hp hp5 hpX
    ((ReeTag.F4.reeGamma X m).subtype.comp eQ.toMonoidHom)
    (Subtype.val_injective.comp eQ.injective) (fun x => reeGamma_le_adjointGroup (eQ x).2)
    (fun x hx => elemPow_eq_one_of_isElementaryAbelian (A := Ē) x hx)

end CFSG.RankThree.PartOne.K133H
