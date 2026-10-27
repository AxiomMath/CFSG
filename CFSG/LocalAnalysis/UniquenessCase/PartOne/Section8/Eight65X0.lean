module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R8107OutOmega
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerBar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem not_le_centralizerBar_of_center_bar_eq_bot
    {L Z P : Subgroup G}
    (hZbar : Subgroup.center (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L) = ⊥)
    (hZL : Z ≤ L) (hZ3 : Nat.card Z = 3) (hZP : Z ≤ P) :
    ¬ Z ≤ centralizerBar P L := by
  classical
  intro hle
  haveI : Finite ↥Z := Nat.finite_of_card_ne_zero (by rw [hZ3]; norm_num)
  haveI : Fintype ↥Z := Fintype.ofFinite _
  obtain ⟨z, hz1⟩ :=
    Fintype.exists_ne_of_one_lt_card (by rw [← Nat.card_eq_fintype_card, hZ3]; norm_num)
      (1 : ↥Z)
  have hzZ : (z : G) ∈ Z := z.2
  have hzL : (z : G) ∈ L := hZL hzZ
  have hz3 : (z : G) ^ 3 = 1 := by
    have hdvd : orderOf (z : G) ∣ Nat.card ↥Z := Subgroup.orderOf_dvd_natCard Z hzZ
    have hne : orderOf (z : G) ≠ 1 := by
      intro h
      exact hz1 (Subtype.ext (orderOf_eq_one_iff.mp h))
    rcases (Nat.dvd_prime Nat.prime_three).mp (hZ3 ▸ hdvd) with h | h
    · exact absurd h hne
    · rw [← h]; exact pow_orderOf_eq_one (z : G)
  have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hm : ∀ y ∈ L, ⁅(z : G), y⁆ ∈ CFSG.Open.pCoreOf 2 L := by
    intro y hy
    have hmem : (z : G) ∈ centralizerBar P L := hle hzZ
    exact hmem.2 y hy
  have hfix : CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L
      ⟨(z : G), le_normalizer hzL⟩ = 1 := by
    ext w
    induction w using QuotientGroup.induction_on with
    | H x =>
      rw [MulAut.one_apply]
      exact (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_fix_iff L
        ⟨(z : G), le_normalizer hzL⟩ x).2 (hm x x.2)
  exact CFSG.LocalAnalysis.UniquenessCase.UC22.R8107Out.rhoL_ne_one_of_mem hZbar hzL hz3 hz1' hfix

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
