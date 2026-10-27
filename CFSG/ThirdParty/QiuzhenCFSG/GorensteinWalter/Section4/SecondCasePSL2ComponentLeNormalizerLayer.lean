module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2NormalizerSylowNoncyclic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PerfectSubgroupLeTwoResidual
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.QuasisimpleOddCenterNormalAbsorption
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FUFittingContainment
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The selected PSL₂ component lies in controlled normalizer layers
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- For every nontrivial subgroup of the equation-(4) fixed part, the
selected PSL₂ component lies in the component layer of its normalizer. -/
public theorem secondCase_psl2_component_le_normalizer_layer
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (F X : Subgroup G)
    (hFleFU : F ≤ c.FU) (hFleM : F ≤ w.M)
    (hFcentE : F ≤ Subgroup.centralizer (d.E : Set G))
    (hXne : X ≠ ⊥) (hXleF : X ≤ F) :
    d.E ≤ componentLayerOf (Subgroup.normalizer (X : Set G)) := by
  classical
  let N : Subgroup G := Subgroup.normalizer (X : Set G)
  have hXcentE : X ≤ Subgroup.centralizer (d.E : Set G) :=
    hXleF.trans hFcentE
  have hEcentX : d.E ≤ Subgroup.centralizer (X : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hXcentE hx) z hz).symm
  have hEleN : d.E ≤ N :=
    hEcentX.trans (Subgroup.centralizer_le_normalizer (X : Set G))
  have hNproper : N ≠ ⊤ := by
    intro hNtop
    have hXnormal : X.Normal :=
      (Subgroup.normalizer_eq_top_iff (H := X)).mp hNtop
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ (minimalCounterexample_isSimple hmin)
        X hXnormal with hXbot | hXtop
    · exact hXne hXbot
    · apply w.M_maximal.ne_top
      apply top_unique
      intro g _hg
      have hgX : g ∈ X := by rw [hXtop]; trivial
      exact hFleM (hXleF hgX)
  have h26 : CentralizerStructure c := theorem_2_6 hmin c
  have hXleFHhat : X ≤ fittingSubgroupOf c.Hhat :=
    hXleF.trans (hFleFU.trans
      (FU_le_fittingSubgroupOf_Hhat_of_centralizerStructure c h26))
  have hcontrol : NormalizerControlledBy c.Hhat N :=
    ⟨X, hXne, hXleFHhat, le_rfl⟩
  have hnotle : ¬ N ≤ c.Hhat := by
    intro hNle
    have hEleHhat : d.E ≤ c.Hhat := hEleN.trans hNle
    have hCleHhat :
        Subgroup.centralizer ({c.t} : Set G) ⊓ w.M ≤ c.Hhat := by
      intro x hx
      exact c.H_le_Hhat (by rw [c.H_eq_centralizer]; exact hx.1)
    apply w.M_not_le_Hhat
    rw [secondCase_M_eq_component_sup_centralizer w d]
    exact sup_le hEleHhat hCleHhat
  have hEperfect : Group.IsPerfect d.E :=
    (Group.isPerfect_def).2 d.E_component.2.2.2.1
  have htResidual : c.t ∈ twoResidualOf N :=
    perfect_subgroup_le_twoResidualOf N d.E hEleN hEperfect d.t_mem_E
  have hSylow : ∀ P : Sylow 2 N, ¬ IsCyclic P :=
    secondCase_psl2_sylow_not_cyclic_of_component_le
      c w d K hK e N hEleN
  have htLayer : c.t ∈ componentLayerOf N := by
    by_contra htnot
    have h27 : Lemma27Hypothesis c N :=
      ⟨hNproper, hcontrol, hnotle, htnot, hSylow,
        Or.inr (Or.inr htResidual)⟩
    have hNsolv : Group.IsSolvable N := (lemma_2_7 hmin c N h27).2.2
    let : Group.IsSolvable N := hNsolv
    have : Group.IsSolvable (d.E.subgroupOf N) := inferInstance
    have hEsolv : Group.IsSolvable d.E :=
      isSolvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hEleN)
    let : Nontrivial d.E := d.E_component.2.2.1
    let : Group.IsPerfect d.E := hEperfect
    exact Group.IsPerfect.not_isSolvable d.E hEsolv
  exact quasisimple_le_of_normal_intersection_involution
    d.E (componentLayerOf N) N d.E_component.2.2 d.center_odd hEleN
      (componentLayerOf_isNormalIn N)
      ⟨c.t, ⟨d.t_mem_E, htLayer⟩, c.t_involution⟩

end CFSG.GorensteinWalter
