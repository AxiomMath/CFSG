module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Defs
import CFSG.LocalAnalysis.UniquenessCase.UC6K332OuterBound
import CFSG.LocalAnalysis.UniquenessCase.UC6K332OuterArith
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
import CFSG.RankThree.PartOne.FOC.PSUModel
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm
import CFSG.RankThree.PartOne.FOC.Transfer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open CFSG.Open CFSG.Blueprint
open CFSG.RankThree.PartTwo.Sec4.RonanK432 (OuterRow)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)

theorem outerRow_of_lieModel_psu {n : ℕ} {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : LieModel S .PSU n p f) (hD : ¬ 3 ∣ Nat.gcd n (p ^ f + 1)) : OuterRow S := by
  have hcl := h.statedClassicalModel (by decide)
  obtain ⟨K, _, _, hU, hn, hnq, ⟨e⟩⟩ := CFSG.RankThree.PartOne.FOC.exists_psu_model hcl
  have hsimple := CFSG.RankThree.Classical.isSimpleGroup_primeFormP_one hU hn hnq
  have hnc := CFSG.RankThree.Classical.not_commute_primeFormP_one hU hn hnq
  have hZ : Subgroup.center S = ⊥ :=
    center_eq_bot_of_mulEquiv e
      (CFSG.RankThree.PartOne.FOC.center_eq_bot_of_nonab hsimple
        (by simpa [not_forall] using hnc))
  have hcard : Nat.card S * lieOrderDivisor .PSU n (p ^ f) = lieOrderNumerator .PSU n (p ^ f) := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.HardMathSupport.Lang.Coordinator.card_primeFormP_one_mul_gcd hU (by omega)
  exact outerRow_of_bound CFSG.HardMathSupport.Lang.Coordinator.outerFixedOrderBoundAt_PSU
    (by decide) (by decide) (by decide) hcl.1 h hZ hD hcard
    (fun x hx => lieOrderNumerator_psu_pos hx)
    (fun x => three_mul_lieOrderNumerator_psu_dvd (by omega) x)

theorem outerRow_psu4_of_two_le (S : Type) [Group S] [Finite S] (p f : ℕ)
    (h : LieModel S .PSU 4 p f) (_hp2 : p ≠ 2) (_hp3 : p ≠ 3) (_hf : 2 ≤ f) : OuterRow S :=
  outerRow_of_lieModel_psu h fun h3 => by
    have := h3.trans (Nat.gcd_dvd_left 4 _)
    omega

theorem outerRow_psu5 (S : Type) [Group S] [Finite S] (p f : ℕ) (h : LieModel S .PSU 5 p f)
    (hq : p ^ f % 3 = 1) : OuterRow S :=
  outerRow_of_lieModel_psu h fun h3 => by
    have := h3.trans (Nat.gcd_dvd_right 5 _)
    omega

theorem outerRow_psu6 (S : Type) [Group S] [Finite S] (p f : ℕ) (h : LieModel S .PSU 6 p f)
    (hq : p ^ f % 3 = 1) : OuterRow S :=
  outerRow_of_lieModel_psu h fun h3 => by
    have := h3.trans (Nat.gcd_dvd_right 6 _)
    omega

theorem outerRow_psu7 (S : Type) [Group S] [Finite S] (p f : ℕ) (h : LieModel S .PSU 7 p f)
    (hq : p ^ f % 3 = 1) : OuterRow S :=
  outerRow_of_lieModel_psu h fun h3 => by
    have := h3.trans (Nat.gcd_dvd_right 7 _)
    omega

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
