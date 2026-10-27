module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCentralizerT

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
  CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore)

section SL2

variable {K : Type} [Field K]

theorem HSL_eq_uSL_mul (t : Kˣ) :
    HSL t = uSL (t : K) * vSL (-((t⁻¹ : Kˣ) : K)) * uSL (t : K) *
      (uSL (-1) * vSL 1 * uSL (-1)) := by
  have ht : (t : K) ≠ 0 := t.ne_zero
  have hti : ((t⁻¹ : Kˣ) : K) = (t : K)⁻¹ := Units.val_inv_eq_inv_val t
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL, coe_HSL, hti]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end SL2

section Pair

variable {G M : Type*} [Group G] [Group M]

@[expose] noncomputable def diagPairHom (f g : M →* G) (comm : ∀ A B, Commute (f A) (g B)) :
    M →* G :=
  (f.noncommCoprod g comm).comp ((MonoidHom.id M).prod (MonoidHom.id M))

end Pair

section W1

variable {K : Type} [Field K]

theorem rootSubgroup_le_centralizer_rootSubgroup {α β : Fin TwistTag.E6.tag.rank → ℤ}
    (h : ∀ c d : K, Commute (pinnedX TwistTag.E6.tag K α c) (pinnedX TwistTag.E6.tag K β d)) :
    rootSubgroup TwistTag.E6.tag K α ≤ centralizer (rootSubgroup TwistTag.E6.tag K β : Set _) := by
  intro x hx
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  rw [mem_centralizer_iff]
  intro y hy
  obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hy
  exact (h c d).symm.eq

theorem commute_rootSL2_shortRootU (A B : SL2 K) :
    Commute (rootSL2 Tag.E6 K shortRootU A) (rootSL2 Tag.E6 K shortRootU' B) := by
  obtain ⟨hU, hU', -, -, -⟩ := shortRoots_check
  replace hU : IsRoot TwistTag.E6.tag twistedE6ClassRootU := mem_rootFinset.1 hU
  replace hU' : IsRoot TwistTag.E6.tag twistedE6ClassRootU' := mem_rootFinset.1 hU'
  have hρ := permLattice_twistedE6ClassRootU
  have hρn : permLattice TwistTag.E6.perm (-twistedE6ClassRootU) = -twistedE6ClassRootU' := by
    decide
  have c1 : ∀ c d : K, Commute (pinnedX TwistTag.E6.tag K twistedE6ClassRootU c)
      (pinnedX TwistTag.E6.tag K twistedE6ClassRootU' d) := fun c d => by
    have h := commute_pinnedX_permLattice_twistedE6 (K := K) hU c d
    rwa [hρ] at h
  have c2 : ∀ c d : K, Commute (pinnedX TwistTag.E6.tag K (-twistedE6ClassRootU) c)
      (pinnedX TwistTag.E6.tag K (-twistedE6ClassRootU') d) := fun c d => by
    have h := commute_pinnedX_permLattice_twistedE6 (K := K) (IsRoot.neg hU) c d
    rwa [hρn] at h
  have c3 : ∀ c d : K, Commute (pinnedX TwistTag.E6.tag K twistedE6ClassRootU c)
      (pinnedX TwistTag.E6.tag K (-twistedE6ClassRootU') d) := fun c d =>
    commute_pinnedX_of_not_isRoot_of_ne_zero_E6 hU (IsRoot.neg hU')
      (by rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel) (by decide) c d
  have c4 : ∀ c d : K, Commute (pinnedX TwistTag.E6.tag K (-twistedE6ClassRootU) c)
      (pinnedX TwistTag.E6.tag K twistedE6ClassRootU' d) := fun c d =>
    commute_pinnedX_of_not_isRoot_of_ne_zero_E6 (IsRoot.neg hU) hU'
      (by rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel) (by decide) c d
  have hle : rootSubgroup TwistTag.E6.tag K twistedE6ClassRootU ⊔
      rootSubgroup TwistTag.E6.tag K (-twistedE6ClassRootU) ≤
        centralizer ((rootSubgroup TwistTag.E6.tag K twistedE6ClassRootU' ⊔
          rootSubgroup TwistTag.E6.tag K (-twistedE6ClassRootU') : Subgroup _) : Set _) := by
    refine sup_le ?_ ?_ <;> rw [le_centralizer_iff] <;> refine sup_le ?_ ?_ <;>
      rw [le_centralizer_iff]
    · exact rootSubgroup_le_centralizer_rootSubgroup c1
    · exact rootSubgroup_le_centralizer_rootSubgroup c3
    · exact rootSubgroup_le_centralizer_rootSubgroup c4
    · exact rootSubgroup_le_centralizer_rootSubgroup c2
  have hA : rootSL2 Tag.E6 K shortRootU A ∈ rootSubgroup TwistTag.E6.tag K twistedE6ClassRootU ⊔
      rootSubgroup TwistTag.E6.tag K (-twistedE6ClassRootU) := by
    have h := CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot (K := K)
      (mem_rootFinset.1 shortRoots_check.1)
    have hm : rootSL2 Tag.E6 K shortRootU A ∈ (rootSL2 Tag.E6 K shortRootU).range := ⟨A, rfl⟩
    rw [h] at hm
    exact hm
  have hB : rootSL2 Tag.E6 K shortRootU' B ∈ rootSubgroup TwistTag.E6.tag K twistedE6ClassRootU' ⊔
      rootSubgroup TwistTag.E6.tag K (-twistedE6ClassRootU') := by
    have h := CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot (K := K)
      (mem_rootFinset.1 shortRoots_check.2.1)
    have hm : rootSL2 Tag.E6 K shortRootU' B ∈ (rootSL2 Tag.E6 K shortRootU').range := ⟨B, rfl⟩
    rw [h] at hm
    exact hm
  exact (mem_centralizer_iff.1 (hle hA) _ hB).symm

@[expose] noncomputable def pairRootSL2 (K : Type) [Field K] : SL2 K →* ModGL TwistTag.E6.tag K :=
  diagPairHom (rootSL2 Tag.E6 K shortRootU) (rootSL2 Tag.E6 K shortRootU')
    commute_rootSL2_shortRootU

theorem pairRootSL2_apply (A : SL2 K) :
    pairRootSL2 K A = rootSL2 Tag.E6 K shortRootU A * rootSL2 Tag.E6 K shortRootU' A :=
  rfl

theorem pairRootSL2_uSL_vSL [CharP K 2] (a : K) :
    pairRootSL2 K (uSL a) = pinnedX TwistTag.E6.tag K twistedE6ClassRootU a *
        pinnedX TwistTag.E6.tag K twistedE6ClassRootU' a ∧
      pairRootSL2 K (vSL a) = pinnedX TwistTag.E6.tag K (-twistedE6ClassRootU) a *
        pinnedX TwistTag.E6.tag K (-twistedE6ClassRootU') a := by
  obtain ⟨hU, hU', -, -, -⟩ := shortRoots_check
  replace hU := mem_rootFinset.1 hU
  replace hU' := mem_rootFinset.1 hU'
  refine ⟨?_, ?_⟩
  · rw [pairRootSL2_apply, CFSG.RankThree.Chevalley.rootSL2_uSL_of_charTwo hU,
      CFSG.RankThree.Chevalley.rootSL2_uSL_of_charTwo hU']
    rfl
  · rw [pairRootSL2_apply, CFSG.RankThree.Chevalley.rootSL2_vSL_of_charTwo hU,
      CFSG.RankThree.Chevalley.rootSL2_vSL_of_charTwo hU']
    rfl

theorem shortRootTorus_le_shortRankOneGroup [CharP K 2] {k : Type} [Field k] (ι : k →+* K) :
    shortRootTorus ι ≤ shortRankOneGroup ι := by
  rintro _ ⟨l, rfl⟩
  change rootDiagUnit Tag.E6 (d4CentralDiag (Units.map ι.toMonoidHom l)
    (Units.map ι.toMonoidHom l)) ∈ shortRankOneGroup ι
  rw [← rootTorusSL2_mul_rootTorusSL2_eq]
  set c : Kˣ := Units.map ι.toMonoidHom l with hc
  have e : rootTorusSL2 Tag.E6 K shortRootU c * rootTorusSL2 Tag.E6 K shortRootU' c =
      pairRootSL2 K (HSL c) :=
    rfl
  rw [e, HSL_eq_uSL_mul, map_mul, map_mul, map_mul, map_mul, map_mul]
  have hu : ∀ x : k, pairRootSL2 K (uSL (ι x)) ∈ shortRankOneGroup ι := fun x => by
    rw [(pairRootSL2_uSL_vSL _).1]
    exact subset_closure ⟨x, Or.inl rfl⟩
  have hv : ∀ x : k, pairRootSL2 K (vSL (ι x)) ∈ shortRankOneGroup ι := fun x => by
    rw [(pairRootSL2_uSL_vSL _).2]
    exact subset_closure ⟨x, Or.inr rfl⟩
  have hc1 : (c : K) = ι l := rfl
  have hc2 : -((c⁻¹ : Kˣ) : K) = ι (-((l⁻¹ : kˣ) : k)) := by
    rw [map_neg, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀]
    rfl
  have h1 : (-1 : K) = ι (-1) := by rw [map_neg, map_one]
  have h1' : (1 : K) = ι 1 := (map_one ι).symm
  rw [hc1, hc2, h1, h1']
  exact mul_mem (mul_mem (mul_mem (hu _) (hv _)) (hu _)) (mul_mem (mul_mem (hu _) (hv _)) (hu _))

end W1

end CFSG.SeitzReduction.TwistedE6Pilot
