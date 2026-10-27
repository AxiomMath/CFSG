module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRootRefl1
public import CFSG.LieType.Chevalley.KernelComponentRoots

public section

namespace CFSG.StandardType.ExcFrames.E6QPlusThree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem f4_involution_fixed_hyperplane_conj_simple
    {w : WeylGroup Tag.F4} (hw : w * w = 1)
    (hf : Nat.card {s : Fin Tag.F4.rank → ZMod 3 //
      TableBExc.torusAct Tag.F4 3 w s = s} = 3 ^ 3) :
    ∃ (v : WeylGroup Tag.F4) (i : Fin Tag.F4.rank),
      w = v * (coxeterSystem Tag.F4).simple i * v⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfix : Nat.card {s : Fin Tag.F4.rank → ZMod 3 //
      TableBExc.torusAct Tag.F4 3 w s = s} = 3 ^ (Tag.F4.rank - 1) := by
    have hr : Tag.F4.rank = 4 := by decide
    exact hf.trans (by rw [hr])
  obtain ⟨β, hβ, hwβ⟩ := exists_rootReflection_of_natCard_fix_torusAct
    (τ := Tag.F4) (p := 3) (by decide) (by decide) hw hfix
  obtain ⟨v, i, hv⟩ := isRoot_iff_exists_smul_single.mp hβ
  exact ⟨v, i, hwβ.trans (rootReflection_eq_conj hv)⟩

end CFSG.StandardType.ExcFrames.E6QPlusThree

end
