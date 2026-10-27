module

public import CFSG.RankThree.PartTwo.Sec8.Hering88Link
public import CFSG.RankThree.PartTwo.Sec8.Hering88Swap
import CFSG.RankThree.PartOne.S10.AmbientTheta
public import CFSG.RankThree.PartTwo.Sec8.Item89Res2ProofStepOne

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def KF88LinkCoreD83 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G), Sec8Pair G A c L a b X 1 →
    ∀ Y ∈ thetaComponentsAt 3 a, sec8I L a ⊔ sec8J X a ≤ Y → ∀ x : G, (x = c ∨ x = b) →
      (KFacts.InducesStdKind Y x .field ∨ KFacts.InducesStdKind Y x .graphField) →
      (∃ (A₀ : Subgroup G) (d' : G) (n' : ℕ), Data83 G a Y x A₀ d' n') →
      ∀ d ∈ Subgroup.closure ({c, b} : Set G), d ∉ Subgroup.zpowers x →
        IsQuasisimple (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) ⧸
          aschbacherSolvableCore 3
            (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)))) →
        (∃ m : ℕ, 1 ≤ m ∧
          IsType418 (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) ⧸
            aschbacherSolvableCore 3
              (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)))) m) →
        KFacts.InducesStdKind
          (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G))) x .field →
        ¬ ⁅inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) ⊓
              inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)),
            inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G))⁆ ≤
          inSubgroup (aschbacherSolvableCore 3)
            (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)))

namespace Hering88D

theorem kF88LinkOne_of_coreD83 (h83 : Item83) (hC : KF88SwapCent) (hI : KF88SwapInv)
    (hL : KF88LinkCoreD83) : KF88LinkOne := by
  intro G _ _ A c L a b X h Y hY hIJ x hx hxY d hdS hdx hUq htypeU hUx hle
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    (PartOne.mem_thetaComponentsAt_iff.mp h.mem_thetaComponentsAt).1
  set K := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) with hK
  set U := inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) with hU
  have hKcb : K ≤ Subgroup.centralizer {c} ⊓ Subgroup.centralizer {b} :=
    le_inf ((Item87Proof.residual_le _).trans (inf_le_left.trans hLc))
      ((Item87Proof.residual_le _).trans inf_le_right)
  have hKd : K ≤ Subgroup.centralizer ({d} : Set G) := by
    intro k hk
    have hk' : k ∈ Subgroup.centralizer ((Subgroup.closure ({c, b} : Set G) : Subgroup G) :
        Set G) := by
      rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨hkc, hkb⟩ := Subgroup.mem_inf.mp (hKcb hk)
      rcases hw with rfl | rfl
      · exact (Subgroup.mem_centralizer_singleton_iff.mp hkc).symm
      · exact (Subgroup.mem_centralizer_singleton_iff.mp hkb).symm
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hk' d hdS).symm
  refine hL G A c L a b X h Y hY hIJ x hx hxY (kF88Data83Y_of h83 hC hI h hY hIJ hx hxY) d hdS hdx
    hUq htypeU hUx ?_
  have h1 : ⁅U ⊓ K, K⁆ ≤ inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({d} : Set G)) :=
    (Subgroup.commutator_mono inf_le_left le_rfl).trans hle
  exact (le_inf h1 (Hering88.commutator_inf_le U K)).trans (Hering88.theta_inf_le_theta hKd)

theorem kF88Step_of_partsD83 (h83 : Item83) (hC : KF88SwapCent) (hI : KF88SwapInv)
    (hS : KF88StepDData83) (hL : KF88LinkCoreD83) (hF : KF84Field) : KF88Step :=
  kF88Step_of_link (kF88StepD_of_data83 h83 hC hI hS) (kF88LinkOne_of_coreD83 h83 hC hI hL) hF

end Hering88D

end CFSG.RankThree.PartTwo.Sec8
