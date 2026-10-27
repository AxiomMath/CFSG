module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelSp4
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisStructure

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

namespace Sp4

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b CFSG.RankThree.PartOne.KCRootAxis

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem not_solvable_normalizer_rootA {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (i : Axis) :
    ¬ Group.IsSolvable ↥(Subgroup.normalizer (rootA K i : Set (antiSp K))) := by
  have hst := even_symplectic_four_root_axis_centralizer_structure hK hn i
  have hle : rootC K i ≤ Subgroup.normalizer (rootA K i : Set (antiSp K)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨fun ha => hst.A_normal_C g hg a ha, fun ha => ?_⟩
    have h := hst.A_normal_C g⁻¹ (inv_mem hg) _ ha
    convert h using 1
    group
  obtain ⟨z, hzA, hz⟩ := hst.vec_surj (![1, 0] : Fin 2 → K)
  have hz1 : z ≠ 1 := by
    rintro rfl
    have := (hst.vec_ker 1 (one_mem _)).2 (one_mem _)
    rw [hz] at this
    exact one_ne_zero (congrFun this 0)
  have : Group.IsPerfect ↥(rootC K i) := hst.C_perfect
  have : Nontrivial ↥(rootC K i) :=
    ⟨⟨⟨z, hst.A_le_C hzA⟩, 1, fun h => hz1 (congrArg Subtype.val h)⟩⟩
  intro hsolv
  exact Group.IsPerfect.not_isSolvable ↥(rootC K i)
    (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle))

theorem not_solvable_overgroup {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    {Y : Subgroup (antiSp K)}
    (hlt : Subgroup.normalizer (antiUnipotent K : Set (antiSp K)) < Y) (hY : Y ≠ ⊤) :
    ¬ Group.IsSolvable ↥Y := by
  have hd := CFSG.QuasithinUnique.Borel252.Sp4.borelData_Sp hn hK
  rcases hd.only Y hlt (lt_top_iff_ne_top.2 hY) with rfl | rfl
  · exact not_solvable_normalizer_rootA hK hn Axis.one
  · exact not_solvable_normalizer_rootA hK hn Axis.two

end Sp4

end E68Proof

end E6

end CFSG.Quasithin
