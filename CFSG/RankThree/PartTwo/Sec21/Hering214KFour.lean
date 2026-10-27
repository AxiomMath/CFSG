module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KSyl27
public import CFSG.RankThree.PartTwo.Sec21.Hering214KGen
public import CFSG.Sporadic.SmallOddCore.J2
public import CFSG.Sporadic.HeldB.AutModel
public import CFSG.Sporadic.Schreier.RuAutInner

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Blueprint
open scoped commutatorElement

section Generic

@[expose] def FourData27 (Y : Type) [Group Y] : Prop :=
  ∃ x y : Y, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧ ⁅x, y⁆ ≠ 1 ∧
    FourDatum ⁅x, y⁆ x ∧ FourDatum ⁅x, y⁆ y ∧ FourDatum ⁅x, y⁆ (x * y) ∧
    FourDatum ⁅x, y⁆ (x * y ^ 2)

theorem eInvNine_of_fourData27 {Y : Type} [Group Y] [Finite Y] (hZ : Subgroup.center Y = ⊥)
    (hout : ∀ α : MulAut Y, α ^ 3 = 1 → ∃ y : Y, α = MulAut.conj y)
    (hL : (Nat.card Y).factorization 3 = 3) (h : FourData27 Y) : EInvNine Y := by
  obtain ⟨x, y, hx, hy, hzx, hzy, hz1, h₁, h₂, h₃, h₄⟩ := h
  exact eInvNine_of_extraspecial27_four hZ hout hx hy hzx hzy hz1 hL h₁ h₂ h₃ h₄

end Generic

section J2

theorem eInvNine_j2_of_data
    (h : FourData27 NativeSporadic.J2) : EInvNine NativeSporadic.J2 := by
  obtain ⟨hfin, -, hsimple⟩ := CFSG.Sporadic.J2.fam_j2_simplicity
  haveI := hfin
  have hZ : Subgroup.center NativeSporadic.J2 = ⊥ :=
    center_eq_bot_of_simple_of_not_prime hsimple (by rw [CFSG.Sporadic.J2.card_J2]; norm_num)
  have hcard : Nat.card (MulAut NativeSporadic.J2) ≤ 2 * Nat.card NativeSporadic.J2 := by
    obtain ⟨-, -, -, -, hAut⟩ :=
      CFSG.Sporadic.SmallOddCore.ctuc_j2_full_automorphism_permutation_model
    have e : MulAut NativeSporadic.J2 ≃* MulAut CFSG.Sporadic.Schreier.j2P :=
      @MulAut.congr NativeSporadic.J2 Units.instGroup _ _ CFSG.Sporadic.Schreier.j2PermEquiv
    rw [Nat.card_congr e.toEquiv, hAut, CFSG.Sporadic.J2.card_J2]
  refine eInvNine_of_fourData27 hZ
    (fun α hα => exists_conj_of_pow_three_of_card_le hZ hcard hα) ?_ h
  rw [CFSG.Sporadic.J2.card_J2, Nat.factorization_def _ Nat.prime_three]
  decide +kernel

end J2

section He

theorem eInvNine_he_of_data
    (h : FourData27 NativeSporadic.He) : EInvNine NativeSporadic.He := by
  obtain ⟨hfin, -, hsimple⟩ := CFSG.Sporadic.He.fam_he_simplicity
  haveI := hfin
  have hcard4 : Nat.card NativeSporadic.He = 4030387200 := CFSG.Sporadic.He.card_He
  have hZ : Subgroup.center NativeSporadic.He = ⊥ :=
    center_eq_bot_of_simple_of_not_prime hsimple (by rw [hcard4]; norm_num)
  have hcard : Nat.card (MulAut NativeSporadic.He) ≤ 2 * Nat.card NativeSporadic.He := by
    obtain ⟨hbij, -, hcardR, -⟩ :=
      CFSG.Sporadic.HeldB.ctbh_full_automorphism_permutation_model
    have e : MulAut NativeSporadic.He ≃* MulAut CFSG.Sporadic.HeldB.heP :=
      @MulAut.congr NativeSporadic.He Units.instGroup _ _ CFSG.Sporadic.HeldB.heEquivP
    rw [Nat.card_congr e.toEquiv, ← Nat.card_congr (Equiv.ofBijective _ hbij), hcardR, hcard4]
  refine eInvNine_of_fourData27 hZ
    (fun α hα => exists_conj_of_pow_three_of_card_le hZ hcard hα) ?_ h
  rw [hcard4, Nat.factorization_def _ Nat.prime_three]
  decide +kernel

end He

section Ru

theorem eInvNine_ru_of_data
    (h : FourData27 NativeSporadic.Ru) : EInvNine NativeSporadic.Ru := by
  obtain ⟨hfin, -, hsimple⟩ := CFSG.Sporadic.Ru.fam_ru_simplicity
  haveI := hfin
  have hcard4 : Nat.card NativeSporadic.Ru = 145926144000 := CFSG.Sporadic.Ru.card_Ru
  have hZ : Subgroup.center NativeSporadic.Ru = ⊥ :=
    center_eq_bot_of_simple_of_not_prime hsimple (by rw [hcard4]; norm_num)
  have hcard : Nat.card (MulAut NativeSporadic.Ru) ≤ 2 * Nat.card NativeSporadic.Ru := by
    obtain ⟨-, hbij, -, -⟩ :=
      CFSG.Sporadic.RuSchreier.CTUC_Ru_full_inner_automorphisms_and_second_centralizer
    have e : MulAut NativeSporadic.Ru ≃* MulAut CFSG.Sporadic.RuSchreier.ruP :=
      @MulAut.congr NativeSporadic.Ru Units.instGroup _ _ CFSG.Sporadic.RuSchreier.ruEquivP
    have h1 : Nat.card (MulAut CFSG.Sporadic.RuSchreier.ruP) =
        Nat.card CFSG.Sporadic.RuSchreier.ruP :=
      (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
    have h2 : Nat.card CFSG.Sporadic.RuSchreier.ruP = Nat.card NativeSporadic.Ru :=
      (Nat.card_congr CFSG.Sporadic.RuSchreier.ruEquivP.toEquiv).symm
    rw [Nat.card_congr e.toEquiv, h1, h2]
    omega
  refine eInvNine_of_fourData27 hZ
    (fun α hα => exists_conj_of_pow_three_of_card_le hZ hcard hα) ?_ h
  rw [hcard4, Nat.factorization_def _ Nat.prime_three]
  decide +kernel

end Ru

end CFSG.RankThree.PartTwo.Sec21.Hering214
