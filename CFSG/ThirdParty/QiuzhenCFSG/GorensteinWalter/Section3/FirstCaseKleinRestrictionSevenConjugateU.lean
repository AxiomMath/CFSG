module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSevenCardThree
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSevenTransfer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-! The transfer in restriction (7) lands on the whole odd core once the
card-three conclusion is known. -/

public theorem firstCase_klein_restrictionSeven_conjugate_X_eq_U
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {n : ℕ} {y : G} {X : Subgroup G}
    (hyJ : y ∈ firstCaseJ c n)
    (hn : 4 ≤ n)
    (hXne : X ≠ ⊥) (hXle : X ≤ c.Hhat)
    (hXodd : Nat.Coprime 2 (Nat.card X))
    (hXinv : ∀ x : G, x ∈ X → x ∈ invertedElements c.Hhat y)
    (hC_even : Even (Nat.card (Subgroup.centralizer (X : Set G))))
    (hN_even : Even (Nat.card
      ((Subgroup.normalizer (X : Set G) ⊓ c.Hhat : Subgroup G)))) :
    ∃ g : G, g ∉ c.Hhat ∧ conjugateSubgroup X g = c.U := by
  have hUcard := (firstCase_klein_restrictionSeven_card_three
    hmin c hfirst hklein hyJ hn hXne hXle hXodd hXinv hC_even hN_even).1
  obtain ⟨g, L, hLHall, hLne, hXgL, hgnot, _hNXg, _hFUcentXg⟩ :=
    firstCase_klein_restrictionSeven_transfer hmin c hfirst hklein
      hyJ hXne hXle hXodd hXinv hC_even
  have hXcard : Nat.card X = 3 :=
    (firstCase_klein_restrictionSeven_core hmin c hfirst hklein
      hyJ hXne hXle hXodd hXinv hC_even hN_even).1
  have hXgcard : Nat.card (conjugateSubgroup X g) = 3 := by
    calc
      Nat.card (conjugateSubgroup X g) = Nat.card X := by
        exact Nat.card_congr
          (Subgroup.equivMapOfInjective X (MulAut.conj g).toMonoidHom
            (MulAut.conj g).injective).toEquiv.symm
      _ = 3 := hXcard
  have hXgleFU : conjugateSubgroup X g ≤ c.FU := hXgL.trans hLHall.1
  have hFUleU : c.FU ≤ c.U := fittingSubgroupOf_le c.U
  have hXgleU : conjugateSubgroup X g ≤ c.U := hXgleFU.trans hFUleU
  have hFUne : c.FU ≠ ⊥ := by
    intro hFUbot
    apply hLne
    apply le_antisymm
    · intro z hz
      exact hFUbot ▸ (hLHall.1 hz)
    · exact bot_le
  have hFUdvd : Nat.card c.FU ∣ Nat.card c.U :=
    Subgroup.card_dvd_of_le hFUleU
  have hFUle : Nat.card c.FU ≤ 3 := by
    rw [hUcard] at hFUdvd
    exact Nat.le_of_dvd (by norm_num) hFUdvd
  have hFUcard : Nat.card c.FU = 3 := by
    have hFUpos : 0 < Nat.card c.FU := Nat.card_pos
    have hFUne1 : Nat.card c.FU ≠ 1 := by
      intro hcard
      exact hFUne (Subgroup.eq_bot_of_card_eq c.FU hcard)
    interval_cases hcard : Nat.card c.FU <;> simp_all
  have hXgeq : conjugateSubgroup X g = c.U := by
    apply Subgroup.eq_of_le_of_card_ge hXgleU
    rw [hUcard]
    omega
  exact ⟨g, hgnot, hXgeq⟩

end CFSG.GorensteinWalter
