module

public import CFSG.LocalAnalysis.StandardType.GGTwAutDefs
public import CFSG.LocalAnalysis.StandardType.GGInnLocalDefs
import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenModel
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreCl
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerLinearNonsplit
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMonomialIrred

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

theorem ggTwSL_facts_rec {K : Type} [Field K] [Finite K] [CharP K 2] {d r : ℕ} (hr : 3 ≤ r)
    (hd : 2 * r ≤ d ∧ d ≤ 2 * r + 1) (h3 : 3 ∣ Nat.card K + 1) :
    Subgroup.center (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) = ⊥ ∧
      GGOutdiagPrime 3 (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ) ∧
      GGCenterPrime 3 (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) := by
  have hpK' : ¬ 3 ∣ Nat.card K - 1 := SpNS.not_dvd_card_sub_one Nat.prime_three (by norm_num) h3
  let e := TypeA.recipeEquiv d K
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) = ⊥ := by
    have h1 := Subgroup.map_center_eq e
    rw [SlNsRootGen.center_projectiveSL_eq_bot_charTwo] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _
      (f := (e : LargeEvenProj (LargeEvenSLGroup (Fin d) K) →*
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL d K))
      e.injective).mp h1
  exact ⟨hZ, NbrInnerMore.ggOutdiagPrime_linear Nat.prime_three hpK' (by omega),
    ggCenterPrime_of_mulEquiv e (ggCenterPrime_projectiveSL Nat.prime_three hpK' (by omega))⟩

end CFSG.StandardType

end
