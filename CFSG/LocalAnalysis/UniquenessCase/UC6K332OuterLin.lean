module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Defs
import CFSG.LocalAnalysis.UniquenessCase.UC6K332OuterBound
import CFSG.LocalAnalysis.UniquenessCase.UC6K332OuterArith
import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSL
import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open CFSG.Open CFSG.Blueprint
open CFSG.RankThree.PartTwo.Sec4.RonanK432 (OuterRow)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)

theorem outerRow_of_lieModel_psl {n : ℕ} (hn : 3 ≤ n) {S : Type} [Group S] [Finite S]
    {p f : ℕ} (h : LieModel S .PSL n p f) (hD : ¬ 3 ∣ Nat.gcd n (p ^ f - 1)) : OuterRow S := by
  have hcl := h.statedClassicalModel (by decide)
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hcl.2
  have hZ : Subgroup.center S = ⊥ :=
    center_eq_bot_of_mulEquiv
      (e.trans (CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.statedProjSLEquiv n K))
      (CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot hn)
  have hcard := CFSG.GH74.Generic.S1.kl5_card_mul_gcd_psl (by omega : 2 ≤ n) hcl
  exact outerRow_of_bound CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.outerFixedOrderBoundAt_PSL
    (by decide) (by decide) (by decide) hcl.1 h hZ hD
    (by simpa [lieOrderNumerator, lieOrderDivisor] using hcard)
    (fun x hx => lieOrderNumerator_psl_pos hx)
    (fun x => three_mul_lieOrderNumerator_psl_dvd (by omega) x)

theorem outerRow_psl4_of_two_le (S : Type) [Group S] [Finite S] (p f : ℕ)
    (h : LieModel S .PSL 4 p f) (_hp3 : p ≠ 3) (_hf : 2 ≤ f) : OuterRow S :=
  outerRow_of_lieModel_psl (by norm_num) h fun h3 => by
    have := h3.trans (Nat.gcd_dvd_left 4 _)
    omega

theorem outerRow_psl6 (S : Type) [Group S] [Finite S] (p f : ℕ) (h : LieModel S .PSL 6 p f)
    (hq : p ^ f % 3 = 2) : OuterRow S :=
  outerRow_of_lieModel_psl (by norm_num) h fun h3 => by
    have := h3.trans (Nat.gcd_dvd_right 6 _)
    omega

theorem outerRow_psl7 (S : Type) [Group S] [Finite S] (p f : ℕ) (h : LieModel S .PSL 7 p f)
    (hq : p ^ f % 3 = 2) : OuterRow S :=
  outerRow_of_lieModel_psl (by norm_num) h fun h3 => by
    have := h3.trans (Nat.gcd_dvd_right 7 _)
    omega

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
