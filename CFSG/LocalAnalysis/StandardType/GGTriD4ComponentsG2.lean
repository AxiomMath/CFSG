module

public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputs
public import CFSG.LocalAnalysis.StandardType.GGTriD4ComponentsG2Raw
public import CFSG.LocalAnalysis.StandardType.GGTriD4ComponentsMark
import CFSG.LocalAnalysis.StandardType.GGL45FixA2Comp

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp

theorem ggTriD4_g2_clause
    {X : Type} [Group X] {C : Subgroup X} {n : ℕ} (hn : 1 ≤ n)
    {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2 ^ n)
    (E : ↥C ≃* ↥(adjointGroup Tag.G2 k)) {Q : Subgroup X} (hQ : IsComponentOf Q C) :
    Subgroup.center Q = ⊥ ∧ LargeEvenMarking Q fun lab _ _ _ _ _ => GGLabelG2 lab := by
  by_cases hn2 : 2 ≤ n
  · have hk3 : 3 ≤ Nat.card k := by
      rw [hk]
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    have hperf := ExcCopy.isPerfect_adjointGroup Tag.G2 k (fun _ => hk3)
    obtain ⟨hs, -⟩ := ExcCopy.isSimpleGroup_adjointGroup_of_perfect Tag.G2 k hperf
    let T : ↥⁅C, C⁆ ≃* ↥(adjointGroup Tag.G2 k) :=
      (ggCommutatorEquiv C).trans
        ((ggCommutatorCongr E).trans
          ((MulEquiv.subgroupCongr hperf.commutator_eq_top).trans Subgroup.topEquiv))
    obtain ⟨Qe⟩ := gffa2_component_equiv T hs hQ
    exact ggMarking_of_rawDatum (lab := ⟨.G2, 0, n⟩) (P := GGLabelG2)
      ⟨hn, rfl, hn2⟩ (Or.inl rfl) (ggG2_rawDatum hn2 hk Qe)
  · have hn1 : n = 1 := by omega
    subst hn1
    have hk2 : Nat.card k = 2 := by simpa using hk
    obtain ⟨hDs, -⟩ := ExcCopy.g2Two_derived_exc hk2
    let T : ↥⁅C, C⁆ ≃* ↥(commutator ↥(adjointGroup Tag.G2 k)) :=
      (ggCommutatorEquiv C).trans (ggCommutatorCongr E)
    obtain ⟨Qe⟩ := gffa2_component_equiv T hDs hQ
    exact ggMarking_of_rawDatum (lab := ⟨.G2der, 0, 1⟩) (P := GGLabelG2)
      ⟨le_rfl, rfl, rfl⟩ (Or.inr rfl)
      (ggG2der_rawDatum hk2 (Qe.trans (ggCommutatorEquiv (adjointGroup Tag.G2 k)).symm))

end CFSG.StandardType
