module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OBorelSolv
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aOvergroup
public import CFSG.LieType.SteinbergBRTriangularSolvable

public section

namespace CFSG.Quasithin.H13.NQCore.L3Odd

open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

theorem le_upperTriangular_of_isSolvable {K : Type} [Field K] [Finite K] (hK : 4 ≤ Nat.card K)
    {H : Subgroup (LinearFlag.projectiveSL 3 K)} (hU : LinearFlag.projUnitriangular 3 K ≤ H)
    (hH : Group.IsSolvable H) {g : SL(3, K)} (hg : LinearFlag.proj 3 K g ∈ H) :
    g ∈ LinearFlag.upperTriangular 3 K := by
  set M : Subgroup SL(3, K) := H.comap (LinearFlag.proj 3 K) with hM
  have hUM : LinearFlag.unitriangular 3 K ≤ M := fun u hu => hU (Subgroup.mem_map_of_mem _ hu)
  have hMs : Group.IsSolvable M := isSolvable_comap_proj hH
  have hgM : g ∈ LinearFlag.flagStabilizer 3 K (LinearFlag.borelOvergroupCuts M) :=
    CFSG.QuasithinUnique.Setup.X7a.le_flagStabilizer_borelOvergroupCuts M hUM hg
  have h1 : (1 : ℕ) ∈ LinearFlag.borelOvergroupCuts M :=
    ⟨le_rfl, by norm_num, reflection_one_notMem hK hUM hMs⟩
  have h2 : (2 : ℕ) ∈ LinearFlag.borelOvergroupCuts M :=
    ⟨by norm_num, by norm_num, reflection_two_notMem hK hUM hMs⟩
  exact CFSG.LieType.SteinbergBR.mem_upperTriangular_of_map_flagSpace
    (LinearFlag.mem_stabilizer.1 (LinearFlag.mem_flagStabilizer.1 hgM 1 h1))
    (LinearFlag.mem_stabilizer.1 (LinearFlag.mem_flagStabilizer.1 hgM 2 h2))

end CFSG.Quasithin.H13.NQCore.L3Odd
