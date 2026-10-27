module

public import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofDefs
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PGroup
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PBasic
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PGroupJ
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PImg
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofTools
import CFSG.RankThree.PartTwo.Sec4.Item426A6Setup
import CFSG.RankThree.PartTwo.Sec4.Steps434

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Proof155P

theorem theta_w155_eq_and_mem_comp3In {A M W : Subgroup G} {LB : Subgroup G → Subgroup G}
    [(ker148 A M).Normal] (hWM : W ≤ M) (hWsub : CFSG.Open.IsSubnormal W M)
    (hWΔ : W ≤ delta A LB M) (hWsubΔ : CFSG.Open.IsSubnormal W (delta A LB M))
    (hWp : Group.IsPerfect ↥W) (hsol : IsSolvable ↥(W ⊓ pPrimeCoreOf 3 M))
    (htype : Nonempty (↥(img148 A M W) ≃* alternatingGroup (Fin 5)) ∨
      (Sec4.IsTripleCover ↥(img148 A M W) (alternatingGroup (Fin 6)) ∧
        CFSG.IsQuasisimple ↥(img148 A M W))) :
    inSubgroup (aschbacherSolvableCore 3) W = W ⊓ pPrimeCoreOf 3 M ∧
      W ∈ comp3In (delta A LB M) := by
  have hle : inSubgroup (aschbacherSolvableCore 3) W ≤ W ⊓ pPrimeCoreOf 3 M :=
    le_inf (Subgroup.map_subtype_le _) (inSubgroup_theta_le_pPrimeCoreOf hWsub)
  obtain ⟨hNn, hN3, -⟩ := inf_pPrimeCoreOf_facts hWM
  set K : Subgroup ↥W := (W ⊓ pPrimeCoreOf 3 M).subgroupOf W with hKdef
  have hKsol : Group.IsSolvable ↥K := by
    haveI : Group.IsSolvable ↥(W ⊓ pPrimeCoreOf 3 M) := hsol
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : W ⊓ pPrimeCoreOf 3 M ≤ W)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : W ⊓ pPrimeCoreOf 3 M ≤ W)).injective
  have hK3 : ¬ 3 ∣ Nat.card ↥K := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : W ⊓ pPrimeCoreOf 3 M ≤ W)).toEquiv]
    exact hN3
  have hKle : K ≤ aschbacherSolvableCore 3 ↥W :=
    (solvable_prime_complement_core_characterization Nat.prime_three).2.2.2.1 K hNn hKsol hK3
  have hge : W ⊓ pPrimeCoreOf 3 M ≤ inSubgroup (aschbacherSolvableCore 3) W := by
    rw [← Subgroup.map_subgroupOf_eq_of_le (inf_le_left : W ⊓ pPrimeCoreOf 3 M ≤ W)]
    exact Subgroup.map_mono hKle
  have hθ : inSubgroup (aschbacherSolvableCore 3) W = W ⊓ pPrimeCoreOf 3 M :=
    le_antisymm hle hge
  refine ⟨hθ, ?_⟩
  have hqW : CFSG.IsQuasisimple (↥W ⧸ aschbacherSolvableCore 3 ↥W) := by
    obtain ⟨e⟩ := nonempty_theta_quot_equiv_img148 (A := A) (M := M) hWM hθ
    exact LocalCores.isQuasisimple_of_mulEquiv e.symm (type155_facts htype).1
  have hperfΔ : Group.IsPerfect ↥(W.subgroupOf (delta A LB M)) :=
    Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hWΔ).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hWΔ).symm.surjective
  have hsnΔ : (W.subgroupOf (delta A LB M)).IsSubnormal :=
    (CFSG.Open.IsSubnormal.iff_subgroupOf hWΔ).mp hWsubΔ
  have hqΔ : CFSG.IsQuasisimple
      (↥(W.subgroupOf (delta A LB M)) ⧸
        aschbacherSolvableCore 3 ↥(W.subgroupOf (delta A LB M))) := by
    let e : ↥W ≃* ↥(W.subgroupOf (delta A LB M)) :=
      (Subgroup.subgroupOfEquivOfLe hWΔ).symm
    have hmap : (aschbacherSolvableCore 3 ↥W).map e.toMonoidHom =
        aschbacherSolvableCore 3 ↥(W.subgroupOf (delta A LB M)) :=
      aschbacherSolvableCore_map_mulEquiv Nat.prime_three e
    exact LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.congr _ _ e hmap) hqW
  have hmemθ : W ∈ thetaComponentsIn (delta A LB M) := by
    rw [mem_thetaComponentsIn_iff]
    exact ⟨hWΔ, hperfΔ, hsnΔ, hqΔ⟩
  have hoResQ : oPrimeResidual 3 (↥W ⧸ aschbacherSolvableCore 3 ↥W) = ⊤ := by
    obtain ⟨e⟩ := nonempty_theta_quot_equiv_img148 (A := A) (M := M) hWM hθ
    refine CFSG.RankThree.PartTwo.Sec17.Proof171Steps.oPrimeResidual_eq_top_of_mulEquiv e ?_
    rcases htype with ⟨⟨φ⟩⟩ | ⟨hT, -⟩
    · refine CFSG.RankThree.PartTwo.Sec17.Proof171Steps.oPrimeResidual_eq_top_of_mulEquiv φ ?_
      haveI : IsSimpleGroup (alternatingGroup (Fin 5)) :=
        alternatingGroup.isSimpleGroup (by simp)
      refine CFSG.RankThree.PartTwo.Sec17.Proof171Steps.oPrimeResidual_eq_top_of_isSimpleGroup ?_
      rw [nat_card_alternatingGroup, Nat.card_fin]
      norm_num [Nat.factorial]
    · exact CFSG.RankThree.PartTwo.Sec17.Proof171Steps.oPrimeResidual_eq_top_of_isTripleCover hT
        CFSG.RankThree.PartTwo.Sec17.Proof171Steps.oPrimeResidual_alternatingGroup_six
  have hoRes : W = oPrimeResidualOf 3 W :=
    CFSG.RankThree.PartTwo.Sec17.Proof171Steps.eq_oPrimeResidualOf_of_quot hWp hoResQ
  exact ⟨hmemθ, hoRes⟩

theorem w155_quot_facts {A M W : Subgroup G} [(ker148 A M).Normal] (hWM : W ≤ M)
    (hWp : Group.IsPerfect ↥W)
    (hθ : inSubgroup (aschbacherSolvableCore 3) W = W ⊓ pPrimeCoreOf 3 M)
    (hq2 : CFSG.IsQuasisimple (↥W ⧸ CFSG.pCore 2 ↥W))
    (htype : Nonempty (↥(img148 A M W) ≃* alternatingGroup (Fin 5)) ∨
      (Sec4.IsTripleCover ↥(img148 A M W) (alternatingGroup (Fin 6)) ∧
        CFSG.IsQuasisimple ↥(img148 A M W))) :
    W ⊓ pPrimeCoreOf 3 M ≤ CFSG.Open.pCoreOf 2 W ∧
      (Nonempty (↥W ⧸ CFSG.pCore 2 ↥W ≃* alternatingGroup (Fin 5)) ∨
        (Sec4.IsTripleCover (↥W ⧸ CFSG.pCore 2 ↥W) (alternatingGroup (Fin 6)) ∧
          CFSG.IsQuasisimple (↥W ⧸ CFSG.pCore 2 ↥W))) := by
  have hcard : Nat.card (↥W ⧸ aschbacherSolvableCore 3 ↥W) =
      Nat.card ↥(img148 A M W) := by
    obtain ⟨e⟩ := nonempty_theta_quot_equiv_img148 (A := A) (M := M) hWM hθ
    exact Nat.card_congr e.toEquiv
  have hp : ∀ p : ℕ, p.Prime → 5 ≤ p →
      ¬ p ^ 2 ∣ Nat.card (↥W ⧸ aschbacherSolvableCore 3 ↥W) := by
    intro p hp hp5
    rw [hcard]
    exact (type155_facts htype).2.2.2 p hp hp5
  have hθO2 : aschbacherSolvableCore 3 ↥W ≤ CFSG.pCore 2 ↥W :=
    aschbacherSolvableCore_le_pCore_two hq2 hp
  have hO2θ : CFSG.pCore 2 ↥W ≤ aschbacherSolvableCore 3 ↥W :=
    CFSG.RankThree.PartTwo.Sec4.le_aschbacherSolvableCore_of_isPGroup Nat.prime_two (by norm_num)
      CFSG.pCore_normal CFSG.pCore_isPGroup
  have h1 : W ⊓ pPrimeCoreOf 3 M ≤ CFSG.Open.pCoreOf 2 W := by
    rw [← hθ]
    exact Subgroup.map_mono hθO2
  refine ⟨h1, ?_⟩
  have hθO2eq : aschbacherSolvableCore 3 ↥W = CFSG.pCore 2 ↥W := le_antisymm hθO2 hO2θ
  obtain ⟨e⟩ := nonempty_theta_quot_equiv_img148 (A := A) (M := M) hWM hθ
  have hqIso : ↥W ⧸ CFSG.pCore 2 ↥W ≃* ↥(img148 A M W) :=
    (QuotientGroup.quotientMulEquivOfEq hθO2eq).symm.trans e
  rcases htype with ⟨⟨φ⟩⟩ | ⟨hT, -⟩
  · exact Or.inl ⟨hqIso.trans φ⟩
  · exact Or.inr ⟨CFSG.RankThree.PartTwo.Sec4.Item426.isTripleCover_of_mulEquiv hqIso.symm hT,
      hq2⟩

end Proof155P

end CFSG.RankThree.PartTwo.Sec15
