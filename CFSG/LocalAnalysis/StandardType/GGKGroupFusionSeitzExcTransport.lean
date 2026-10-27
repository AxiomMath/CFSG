module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcComp

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def ggFixedSubgroup {K : Type} [Group K] (E : Subgroup (MulAut K)) : Subgroup K where
  carrier := {k | ∀ ε ∈ E, ε k = k}
  one_mem' := fun ε _ => map_one ε
  mul_mem' := fun {a b} ha hb ε hε => by rw [map_mul, ha ε hε, hb ε hε]
  inv_mem' := fun {a} ha ε hε => by rw [map_inv, ha ε hε]

@[expose] def ggFixedClosure {K : Type} [Group K] (E : Subgroup (MulAut K)) : Subgroup K :=
  Subgroup.closure {k | ∃ ε ∈ E, ε ≠ 1 ∧ ε k = k}

section Transport

variable {W : Type} [Group W] [Finite W] {p : ℕ} {H E : Subgroup W}

theorem ggSeitzExc_transport (hyp : GGHypThreeSixteen p H E) :
    ∃ E' : Subgroup (MulAut ↥(CFSG.generalizedFitting W)), IsElemAbelian p E' ∧
      Nat.card E' = p ^ 2 ∧ ggFixedClosure E' ≤ H.subgroupOf (CFSG.generalizedFitting W) ∧
        (IsPGroup p ↥(ggFixedSubgroup E') →
          IsPGroup p ↥(CFSG.generalizedFitting W ⊓ Subgroup.centralizer (E : Set W))) := by
  obtain ⟨⟨hp, -, hE, hEcard, hfus⟩, ⟨hsimple, hnab, -⟩, -⟩ := hyp
  set K := CFSG.generalizedFitting W
  have : K.Normal := CFSG.LocalCores.generalized_fitting_characteristic.2
  have hψ : Function.Injective (MulAut.conjNormal (H := K)) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    refine ggEq_one_of_commute_generalizedFitting hsimple hnab fun k hk => ?_
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hx ⟨k, hk⟩)
    rw [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1
  have hfix : ∀ (a : W) (k : K), MulAut.conjNormal (H := K) a k = k ↔ a * (k : W) * a⁻¹ = k := by
    intro a k
    rw [← Subtype.coe_inj, MulAut.conjNormal_apply]
  refine ⟨E.map (MulAut.conjNormal (H := K)),
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p ⟨hE.1, hE.2⟩ _,
    by rw [Subgroup.card_map_of_injective hψ, hEcard], ?_, fun hP => ?_⟩
  ·
    rw [ggFixedClosure, Subgroup.closure_le]
    rintro k ⟨_, ⟨a, haE, rfl⟩, hε1, hεk⟩
    have ha1 : a ≠ 1 := by
      rintro rfl
      exact hε1 (map_one _)
    have hfixa : a * (k : W) * a⁻¹ = k := (hfix a k).mp hεk
    refine Subgroup.mem_subgroupOf.mpr (hfus.centralizer_le haE ha1 ?_)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.mp hfixa).symm
  ·
    refine (hP.map K.subtype).to_le ?_
    rintro w ⟨hwK, hwC⟩
    refine ⟨⟨w, hwK⟩, ?_, rfl⟩
    rintro _ ⟨a, haE, rfl⟩
    refine (hfix a ⟨w, hwK⟩).mpr ?_
    have h1 := Subgroup.mem_centralizer_iff.mp hwC a haE
    rw [h1, mul_inv_cancel_right]

end Transport

section Comp

variable {W : Type} [Group W]

theorem ggSeitzExc_component_quot_equiv {H K C : Subgroup W}
    (hs : IsSimpleGroup ↥(commutator ↥(H.subgroupOf K)))
    (hns : ¬ Group.IsSolvable ↥(commutator ↥(H.subgroupOf K))) (hC : IsComponentOf C (H ⊓ K)) :
    Nonempty (↥C ⧸ Subgroup.center ↥C ≃* ↥(commutator ↥(H.subgroupOf K))) := by
  have hCeq := ggSeitzExc_component_eq hs hC
  let eC : ↥C ≃* ↥(commutator ↥(H.subgroupOf K)) :=
    (MulEquiv.subgroupCongr hCeq).trans (ggInfCommutatorEquiv H K)
  have : IsSimpleGroup ↥C := eC.isSimpleGroup
  have hCns : ¬ Group.IsSolvable ↥C := fun h' =>
    hns (Group.isSolvable_of_isSolvable_injective (f := eC.symm.toMonoidHom) eC.symm.injective)
  have hZ : Subgroup.center ↥C = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥C) with hc | hc
    · exact hc
    · refine absurd (Group.isSolvable_of_comm fun a b => ?_) hCns
      have hb : b ∈ Subgroup.center ↥C := hc ▸ Subgroup.mem_top b
      exact Subgroup.mem_center_iff.mp hb a
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans eC⟩

end Comp

end CFSG.StandardType
