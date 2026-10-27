module

public import CFSG.RankThree.GroupTheory.SubnormalCores
public import CFSG.RankThree.LocalRank.ThetaPlaneAlpha

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank

variable {X : Type*} [Group X] [Finite X]

theorem map_inSubgroup_theta_centralizer_le {N : Subgroup X} (hN : N.Normal) (b : N) :
    (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set N))).map N.subtype ≤
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({(b : X)} : Set X)) := by
  have hKC : (Subgroup.centralizer ({b} : Set N)).map N.subtype ≤
      Subgroup.centralizer ({(b : X)} : Set X) := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y * b = b * y := Subgroup.mem_centralizer_singleton_iff.mp hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hy')
  have hK₀ : ((Subgroup.centralizer ({b} : Set N)).map N.subtype).subgroupOf
      (Subgroup.centralizer ({(b : X)} : Set X)) =
      N.subgroupOf (Subgroup.centralizer ({(b : X)} : Set X)) := by
    ext z
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, -, hy⟩
      exact hy ▸ y.2
    · intro hz
      refine ⟨⟨z, hz⟩, ?_, rfl⟩
      have hzc : (z : X) * b = b * z := Subgroup.mem_centralizer_singleton_iff.mp z.2
      exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hzc)
  have hnormal : (((Subgroup.centralizer ({b} : Set N)).map N.subtype).subgroupOf
      (Subgroup.centralizer ({(b : X)} : Set X))).Normal := by
    rw [hK₀]
    exact Subgroup.Normal.subgroupOf hN _
  have hsub := solvable_prime_complement_core_subnormal_intersection Nat.prime_three
    (Subgroup.Normal.isSubnormal hnormal)
  let e : Subgroup.centralizer ({b} : Set N) ≃*
      ((Subgroup.centralizer ({b} : Set N)).map N.subtype).subgroupOf
        (Subgroup.centralizer ({(b : X)} : Set X)) :=
    ((Subgroup.centralizer ({b} : Set N)).equivMapOfInjective N.subtype
      N.subtype_injective).trans (Subgroup.subgroupOfEquivOfLe hKC).symm
  have hθ := aschbacherSolvableCore_map_mulEquiv Nat.prime_three e
  have hstep : (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set N))).map
      N.subtype = (inSubgroup (aschbacherSolvableCore 3)
        (((Subgroup.centralizer ({b} : Set N)).map N.subtype).subgroupOf
          (Subgroup.centralizer ({(b : X)} : Set X)))).map
            (Subgroup.centralizer ({(b : X)} : Set X)).subtype := by
    simp only [inSubgroup]
    rw [← hθ]
    simp only [Subgroup.map_map]
    congr 1
  rw [hstep, hsub]
  exact Subgroup.map_mono inf_le_right

theorem map_thetaAlpha_subgroupOf_le {N : Subgroup X} (hN : N.Normal) {B : Subgroup X}
    (hBN : B ≤ N) : (thetaAlpha 3 (B.subgroupOf N)).map N.subtype ≤ thetaAlpha 3 B := by
  have hBmap : (B.subgroupOf N).map N.subtype = B := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hBN]
  unfold thetaAlpha
  rw [Subgroup.map_sup]
  refine sup_le_sup ?_ ?_
  · unfold thetaJ
    simp only [Subgroup.map_iSup]
    refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
    rw [Subgroup.map_commutator, hBmap]
    refine (Subgroup.commutator_mono (map_inSubgroup_theta_centralizer_le hN b) le_rfl).trans ?_
    refine le_iSup_of_le (b : X) (le_iSup_of_le (Subgroup.mem_subgroupOf.mp hb)
      (le_iSup_of_le ?_ le_rfl))
    exact fun h => hb1 (Subtype.ext h)
  · unfold thetaT
    refine le_iInf fun b => le_iInf fun hb => le_iInf fun hb1 => ?_
    have hbN : b ∈ N := hBN hb
    refine (Subgroup.map_mono (iInf_le_of_le (⟨b, hbN⟩ : N)
      (iInf_le_of_le (Subgroup.mem_subgroupOf.mpr hb)
        (iInf_le_of_le (fun h => hb1 (congrArg Subtype.val h)) le_rfl)))).trans ?_
    exact map_inSubgroup_theta_centralizer_le hN ⟨b, hbN⟩

theorem thetaAlpha_ne_bot_of_subgroupOf {N : Subgroup X} (hN : N.Normal) {B : Subgroup X}
    (hBN : B ≤ N) (h : thetaAlpha 3 (B.subgroupOf N) ≠ ⊥) : thetaAlpha 3 B ≠ ⊥ := by
  intro hB
  apply h
  have := map_thetaAlpha_subgroupOf_le hN hBN
  rw [hB, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective] at this
  exact this

end CFSG.RankThree.PartTwo.Sec13
