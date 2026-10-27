module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KY5
public import CFSG.RankThree.PartTwo.Sec13.Item136PGL
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLiePGL

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage)

theorem ks129_commutator_congr {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    Nonempty (_root_.commutator A ≃* _root_.commutator B) := by
  refine ⟨(MulEquiv.subgroupMap e (_root_.commutator A)).trans (MulEquiv.subgroupCongr ?_)⟩
  rw [commutator_def A, commutator_def B, Subgroup.map_commutator, Subgroup.map_equiv_top]

theorem ks129PGL3Shape_holds : KS129PGL3Shape := by
  intro Y' X' _ _ _ hns hX hY
  obtain ⟨π, p, f, K, hFld, hF, hq, ⟨eX⟩⟩ := hX
  obtain ⟨eY⟩ := hY
  have hf : 1 ≤ f := hF.one_le
  have hpf : 2 ≤ p ^ f := le_trans hF.prime.two_le (Nat.le_self_pow (by omega) p)
  by_cases h2 : 2 < p ^ f
  · have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
      fun h => by subst h; exact hF.unitary
    have hSP : projImage (Sec4.slPi π 3 (p ^ f) K) ≤ projImage (Sec4.glPi π 3 (p ^ f) K) :=
      Subgroup.map_mono (Sec4.slPi_le_glPi hπ)
    have hS : IsSimpleGroup ↥(projImage (Sec4.slPi π 3 (p ^ f) K)) :=
      CFSG.RankThree.PartTwo.Sec4.RonanK429Lie.isSimpleGroup_projImage_slPi hF (Or.inr h2)
    obtain ⟨eC⟩ := ks129_commutator_congr eX
    have eYP : Y' ≃* ↥(projImage (Sec4.slPi π 3 (p ^ f) K)) :=
      eY.trans (eC.trans ((MulEquiv.subgroupCongr
        (Sec13.commutator_projImage_glPi hF h2)).trans (Subgroup.subgroupOfEquivOfLe hSP)))
    haveI : IsSimpleGroup Y' := eYP.isSimpleGroup
    have hnc : ∃ a b : Y', a * b ≠ b * a := by
      by_contra hcon
      push_neg at hcon
      exact hns (Group.isSolvable_of_comm hcon)
    refine ⟨?_, Hering129HLift.center_eq_bot_of_simple inferInstance hnc⟩
    obtain ⟨p', e', hfact, he', hiso⟩ := Sec13.isLThreePi_projImage_slPi hF hq
    refine ⟨p', e', hfact, he', ?_⟩
    unfold Sec4.IsoLThreePi at hiso ⊢
    rcases hiso with ⟨h1, ⟨φ⟩⟩ | ⟨h1, ⟨φ⟩⟩
    · exact Or.inl ⟨h1, ⟨eYP.trans φ⟩⟩
    · exact Or.inr ⟨h1, ⟨eYP.trans φ⟩⟩
  · have hpf2 : p ^ f = 2 := by omega
    have hπ : π = false := by
      cases π
      · rfl
      · exfalso
        simp [Sec4.ModThree, hpf2] at hq
    subst hπ
    have hsolvM : Group.IsSolvable ↥(projImage (Sec4.glPi false 3 (p ^ f) K)) :=
      Sec13.isSolvable_projImage_glPi_two hF hpf2
    haveI : Group.IsSolvable X' :=
      Group.isSolvable_of_isSolvable_injective (f := eX.toMonoidHom) eX.injective
    exact absurd (Group.isSolvable_of_isSolvable_injective (f := eY.toMonoidHom) eY.injective) hns

end CFSG.RankThree.PartTwo.Sec12
