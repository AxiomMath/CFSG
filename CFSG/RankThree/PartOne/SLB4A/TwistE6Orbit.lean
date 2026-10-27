module

public import CFSG.RankThree.PartOne.SLB4A.TwistE6Odd
public import CFSG.RankThree.PartOne.SLB4A.ExcEven
public import CFSG.LieType.Chevalley.E6GraphRadicalCocycle

public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Param

variable {K : Type} [Field K] (σ : K →+* K)

@[expose] def fa (a : Fin 4) : Fin TwistTag.E6.foldedTag.rank := Fin.cast (by decide) a

theorem orbL_eq (a : Fin 4) : orbL a = TwistTag.E6.orbitWord (fa a) := by
  revert a
  decide +kernel

theorem orbitUnitParam_neg_one (a : Fin TwistTag.E6.foldedTag.rank) {j : Fin TwistTag.E6.tag.rank}
    (hj : j ∈ TwistTag.E6.orbit a) :
    orbitUnitParam TwistTag.E6 σ a (orbitFieldUnit TwistTag.E6 σ
      (-1 : (orbitField TwistTag.E6 K σ a)ˣ)) j = -1 := by
  obtain ⟨k, hk, rfl⟩ := TwistTag.E6.exists_eq_perm_pow_orbitMin hj
  rw [orbitUnitParam_pow TwistTag.E6 σ _ hk]
  refine Units.ext ?_
  simp [orbitFieldUnit]

@[expose] def rootsT6 : Fin 5 → Fin TwistTag.E6.tag.rank → ℤ :=
  ![![0, 0, 0, 1, 0, 0], ![0, 1, 0, 1, 0, 0], ![0, 1, 1, 2, 1, 0], ![1, 1, 1, 2, 1, 1],
    ![1, 1, 2, 3, 2, 1]]

theorem posRootData_T6 : PosRootData TwistTag.E6.tag rootsT6 := by
  unfold PosRootData
  decide +kernel

theorem fixT6 : ∀ i, permLattice TwistTag.E6.perm (rootsT6 i) = rootsT6 i := by
  decide +kernel

end Param

section Orbit

variable
  {K : Type} [Field K] (σ : K →+* K)

theorem tprod_orbL_mem (a : Fin 4) :
    ((tprod (orbL a) : adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) ∈
      graphFixedRootGroup TwistTag.E6 K σ := by
  have h := orbitH_mem_graphFixedRootGroup TwistTag.E6 σ (fa a) (-1)
  have e : ((tprod (orbL a) : adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) =
      (orbitH TwistTag.E6 K σ (fa a) (-1) : ModGL TwistTag.E6.tag K) := by
    refine (coe_tprod (τ := TwistTag.E6.tag) (K := K) (orbL a)).trans ?_
    rw [coe_orbitH_eq, orbL_eq]
    refine congrArg List.prod (List.map_congr_left fun j hj => ?_)
    rw [orbitUnitParam_neg_one σ (fa a) ((TwistTag.E6.mem_orbitWord).1 hj)]
  rw [e]
  exact h

theorem wElt_orbL_mem (a : Fin 4) :
    ((wElt (orbL a) : adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) ∈
      graphFixedRootGroup TwistTag.E6 K σ := by
  have h := orbitN_mem_graphFixedRootGroup TwistTag.E6 σ (fa a) 1
  have e : ((wElt (orbL a) : adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) =
      (orbitN TwistTag.E6 K σ (fa a) 1 : ModGL TwistTag.E6.tag K) := by
    rw [coe_orbitN_one, coe_wElt, orbL_eq]
  rw [e]
  exact h

theorem wElt_flatMap_mem (l : List (Fin 4)) :
    ((wElt (l.flatMap orbL) : adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) ∈
      graphFixedRootGroup TwistTag.E6 K σ := by
  induction l with
  | nil =>
    have : ((wElt ([] : List (Fin TwistTag.E6.tag.rank)) : adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) = 1 :=
      rfl
    simp only [List.flatMap_nil]
    rw [this]
    exact one_mem _
  | cons a l ih =>
    rw [List.flatMap_cons, wElt_append, Subgroup.coe_mul]
    exact mul_mem (wElt_orbL_mem σ a) ih

theorem gT_mem (k : Fin 5) :
    ((gT k : adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  by_cases hk : k.1 < 4
  · rw [gT_lt hk]
    exact tprod_orbL_mem σ _
  · rw [show k = 4 from Fin.ext (by omega), gT_four]
    exact wElt_flatMap_mem σ wordF4

theorem exists_two_pow_five_twistedE6_odd (hneg : (-1 : K) ≠ 1) :
    ∃ U : Subgroup (graphFixedRootGroup TwistTag.E6 K σ), IsElementaryAbelian 2 U ∧
      Nat.card U = 2 ^ 5 := by
  refine exists_two_pow_five_of_commInvol
    (fun k => (⟨((gT k : adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K), gT_mem σ k⟩ :
      graphFixedRootGroup TwistTag.E6 K σ))
    (fun i j => Subtype.ext (by simpa using congrArg Subtype.val (gT_comm i j)))
    (fun i => Subtype.ext (by simpa using congrArg Subtype.val (gT_sq i))) ?_
  intro v hv
  refine gT_ind hneg v (Subtype.ext ?_)
  have h := congrArg Subtype.val hv
  simpa only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_one] using h

theorem pinnedX_mem_graphFixedRootGroup (h2 : (2 : K) = 0)
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hroot : IsRoot TwistTag.E6.tag α) (hpos : 0 < height α)
    (hfix : permLattice TwistTag.E6.perm α = α) :
    pinnedX TwistTag.E6.tag K α 1 ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  refine graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.E6 K σ ?_
  refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_inf.2 ⟨pinnedX_mem_adjointGroup α 1, ?_⟩⟩
  · have := pinnedX_list_prod_mem_posUnipotent (R := K) [α]
      (fun β hβ => by rw [List.mem_singleton.1 hβ]; exact ⟨hroot, hpos⟩) (fun _ => (1 : K))
    simpa using this
  · show twistHom TwistTag.E6 K σ (pinnedX TwistTag.E6.tag K α 1) =
      (MonoidHom.id _) (pinnedX TwistTag.E6.tag K α 1)
    rw [E6GraphRadical.twistHom_pinnedX_of_two h2 σ hroot 1, hfix, map_one]
    rfl

theorem exists_two_pow_five_twistedE6_even [CharP K 2] :
    ∃ U : Subgroup (graphFixedRootGroup TwistTag.E6 K σ), IsElementaryAbelian 2 U ∧
      Nat.card U = 2 ^ 5 := by
  obtain ⟨hinj, hroot, hpos, hnn, hcol, hnr⟩ := posRootData_T6
  exact exists_two_pow_five_posRoots (graphFixedRootGroup TwistTag.E6 K σ) rootsT6 hinj hroot hpos
    hnn hcol hnr fun i => pinnedX_mem_graphFixedRootGroup σ CharTwo.two_eq_zero
      (RootOps.isRootB_iff.1 (hroot i)) (hpos i) (fixT6 i)

end Orbit

end CFSG.RankThree.PartOne.SLB4A
