module

public import CFSG.RankThree.PartTwo.Sec16.Item166KdAssembly
import CFSG.RankThree.PartTwo.Sec16.Item166KdComm
import CFSG.RankThree.PartTwo.Sec16.Item166CtrLB
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.GroupTheory.PerfectSectionStability
public import CFSG.RankThree.PartTwo.Sec16.Item166CtrS6Push
public import CFSG.RankThree.PartTwo.Sec17.RouteForms

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec11
open scoped Pointwise commutatorElement

@[expose] noncomputable def Step166ThetaDComm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ d ∈ A, d ≠ 1 → IsThreeCentralIn L d →
    ∀ 𝒳 : Set (Subgroup G), 𝒳 ⊆ thetaComponentsAt 3 d → 𝒳.Nonempty →
      delta A (lB A) (Subgroup.centralizer ({d} : Set G)) =
        pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ sSup 𝒳 →
      lB A (Subgroup.closure {c, d}) ≤ sSup 𝒳 →
      Sec14.Ronan148Q.Inv143Q A d d (sSup 𝒳) →
      (Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
          (alternatingGroup (Fin 6)) ∨
        IsCentralProductA6Covers (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))) →
      ⁅inSubgroup (aschbacherSolvableCore 3) (sSup 𝒳), lB A (Subgroup.closure {c, d})⁆ ≤
        CFSG.Open.pCoreOf 2 (inSubgroup (aschbacherSolvableCore 3) (sSup 𝒳))

end CFSG.RankThree.PartTwo.Sec16

namespace CFSG.RankThree.PartTwo.Sec16.Kd166

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec11
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_theta_le_pCoreOf_of_cases {O X : Subgroup G} {d : G}
    (hOX : O ≤ Subgroup.normalizer (X : Set G))
    (hOC : O ⊔ X ≤ Subgroup.centralizer ({d} : Set G))
    (hcase : Subgroup.centralizer ({d} : Set G) ≤
        Subgroup.normalizer ((O ⊔ X : Subgroup G) : Set G) ∨
      X ∈ thetaComponentsAt 3 d) :
    CFSG.Open.pCoreOf 2 (inSubgroup (aschbacherSolvableCore 3) X) ≤
      CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) := by
  classical
  rcases hcase with hCnorm | hXmem
  · have hθle : CFSG.Open.pCoreOf 2 (inSubgroup (aschbacherSolvableCore 3) X) ≤
        O ⊔ X :=
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans
        ((Sec6.theta_le X).trans le_sup_right)
    have hNθ : O ⊔ X ≤ Subgroup.normalizer
        (inSubgroup (aschbacherSolvableCore 3) X : Set G) :=
      sup_le (hOX.trans (Sec6.normalizer_le_normalizer_theta X))
        (Sec6.le_normalizer_theta X)
    have hNcore : O ⊔ X ≤ Subgroup.normalizer
        (CFSG.Open.pCoreOf 2 (inSubgroup (aschbacherSolvableCore 3) X) : Set G) :=
      hNθ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
    have h1 : CFSG.Open.pCoreOf 2 (inSubgroup (aschbacherSolvableCore 3) X) ≤
        CFSG.Open.pCoreOf 2 (O ⊔ X) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hθle hNcore
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    have h2 : CFSG.Open.pCoreOf 2 (O ⊔ X) ≤
        CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) :=
      CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hOC hCnorm
    exact h1.trans h2
  · have hXleC : X ≤ Subgroup.centralizer ({d} : Set G) :=
      le_centralizer_of_mem_thetaComponentsAt hXmem
    have hXsub : (X.subgroupOf (Subgroup.centralizer ({d} : Set G))).IsSubnormal :=
      CFSG.RankThree.PartOne.isSubnormal_of_mem_thetaComponentsAt hXmem
    have hsub : CFSG.Open.IsSubnormal X
        (Subgroup.centralizer ({d} : Set G)) :=
      (CFSG.Open.IsSubnormal.iff_subgroupOf hXleC).mpr hXsub
    have hcore : CFSG.Open.pCoreOf 2 X ≤
        CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) :=
      CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_subnormal 2 hsub
    have h1 : CFSG.Open.pCoreOf 2 (inSubgroup (aschbacherSolvableCore 3) X) ≤
        CFSG.Open.pCoreOf 2 X :=
      CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 (Sec6.theta_le X)
        (Sec6.le_normalizer_theta X)
    exact h1.trans hcore

private theorem isPerfect_lB_closure
    {A : Subgroup G} {c : G} {L Y₀ : Subgroup G} {d : G}
    (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d) :
    Group.IsPerfect ↥(lB A (Subgroup.closure {c, d})) := by
  rw [Ctr166.lB_closure_eq_residual h hJ hdA hd1 hdc]
  exact Item148HJ.residual_isPerfect L d

private theorem commutator_commutator_le_pCoreOf {U Z J Ob C X : Subgroup G}
    (hcomm : ⁅⁅U, Z⁆, J⁆ ≤ X ⊓ Ob)
    (hXOb : X ⊓ Ob ≤ inSubgroup (aschbacherSolvableCore 3) X)
    (hθJ : ⁅inSubgroup (aschbacherSolvableCore 3) X, J⁆ ≤
      CFSG.Open.pCoreOf 2 (inSubgroup (aschbacherSolvableCore 3) X))
    (hJperf : Group.IsPerfect J)
    (hcoreO2 : CFSG.Open.pCoreOf 2 (inSubgroup (aschbacherSolvableCore 3) X) ≤
      CFSG.Open.pCoreOf 2 C) :
    ⁅⁅U, Z⁆, J⁆ ≤ CFSG.Open.pCoreOf 2 C := by
  have hθsolv : Group.IsSolvable ↥(inSubgroup (aschbacherSolvableCore 3) X) :=
    (Sec6.theta_solvable_and_not_dvd X).1
  have hθcoreN : ((CFSG.Open.pCoreOf 2
      (inSubgroup (aschbacherSolvableCore 3) X)).subgroupOf
        (inSubgroup (aschbacherSolvableCore 3) X)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _)).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hVcore : ⁅⁅U, Z⁆, J⁆ ≤ CFSG.Open.pCoreOf 2
      (inSubgroup (aschbacherSolvableCore 3) X) :=
    CFSG.GroupTheory.commutator_le_of_isPerfect_of_le (V := ⁅U, Z⁆) (J := J)
      (T := inSubgroup (aschbacherSolvableCore 3) X)
      (N := CFSG.Open.pCoreOf 2 (inSubgroup (aschbacherSolvableCore 3) X))
      hJperf hθsolv (CFSG.LieType.BorelTits.pCoreOf_le 2 _) hθcoreN hθJ
      (hcomm.trans hXOb)
  exact hVcore.trans hcoreO2

theorem step166KCommD_of_thetaDComm
    (h143 : Sec14.Ronan148Q.Item143QS14) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h1514 : Item1514S17) (hMeets : Claim1715Meets) (hθd : Step166ThetaDComm) :
    Step166KCommD := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro G _ _ A c L Y₀ h hJ d hdA hd1 hdc U hUQ hUC
  have hΩ : omegaA A = {Subgroup.zpowers c} :=
    Proof17Res10.omegaA_eq_of_j2 h (h1514 G A c L Y₀ h) (hMeets G A c L Y₀ h)
      h.zpowers_mem_omegaA h.mem_lA hJ
  obtain ⟨𝒳, h𝒳, h𝒳ne, hΔ, hinv, htypes⟩ :=
    exists_case2ii_at_d h143 h hΩ hJ hdA hd1 hdc
  set C : Subgroup G := Subgroup.centralizer ({d} : Set G)
  set O : Subgroup G := pPrimeCoreOf 3 C
  set W : Subgroup G := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))
  set X : Subgroup G := sSup 𝒳
  set J : Subgroup G := lB A (Subgroup.closure {c, d})
  set Z : Subgroup G := Subgroup.zpowers c
  set Ob : Subgroup G := pPrimeCoreOf 3 (O ⊔ X)
  have hcA : c ∈ A := (Sec13.zpowers_mem_omegaA_iff.mp h.zpowers_mem_omegaA).1
  have hU : U ≤ O ⊔ W ⊔ X := hΔ ▸ Sec14.le_delta hUQ hUC
  have hJX : J ≤ X := lB_le_sSup_of_case2ii h hJ hdA hd1 hdc h𝒳 hΔ hinv htypes
  have hOX : O ≤ Subgroup.normalizer (X : Set G) :=
    pPrimeCoreOf_le_normalizer_sSup_of_types h𝒳 htypes
  obtain ⟨Kd, hKd, hKdeq, _hKd𝒳, htypes'⟩ :=
    exists_Kd_data h134 h48 h hJ hΩ hdA hd1 hdc h𝒳 hΔ hinv htypes
  have hθJ : ⁅inSubgroup (aschbacherSolvableCore 3) X, J⁆ ≤
      CFSG.Open.pCoreOf 2 (inSubgroup (aschbacherSolvableCore 3) X) :=
    hθd G A c L Y₀ h hJ d hdA hd1 hdc 𝒳 h𝒳 h𝒳ne hΔ hJX hinv htypes'
  have hOC : O ⊔ X ≤ C :=
    sup_le (Sec14.pPrimeCoreOf_le 3 C) (sSup_le_centralizer_of_subset h𝒳)
  obtain ⟨hOOb, hθOb, hNOb⟩ := le_pPrimeCoreOf_sup_of_case2ii hOX
    (hOC.trans (Sec14.le_normalizer_pPrimeCoreOf 3 C))
    (Sec14.coprime_card_pPrimeCoreOf 3 C)
  obtain ⟨hZN, hZOb, hWN, hWZ, hJZ⟩ :=
    normalizer_centralizer_facts_of_case2ii h.toSec14Std.isE27.1.1 hcA hdA le_rfl
      (Sec14.pPrimeCoreOf_le 3 _) hinv
  have hXN : X ≤ Subgroup.normalizer (Ob : Set G) := le_sup_right.trans hNOb
  have hXOb : X ⊓ Ob ≤ inSubgroup (aschbacherSolvableCore 3) X :=
    inf_le_theta_of_types (X := X) (N := Ob) htypes hXN
      (Sec14.coprime_card_pPrimeCoreOf 3 (O ⊔ X))
  have hcoreO2 : CFSG.Open.pCoreOf 2 (inSubgroup (aschbacherSolvableCore 3) X) ≤
      CFSG.Open.pCoreOf 2 C :=
    pCoreOf_theta_le_pCoreOf_of_cases hOX hOC
      (hinv.imp id fun h => h.2.1)
  have hsuppOb : ∀ x ∈ X, ∃ j ∈ J, ∃ s ∈ X, x = j * s ∧
      ∀ l ∈ J, ⁅s, l⁆ ∈ Ob :=
    exists_supplement_mod_pPrimeCoreOf h𝒳 htypes hKd hKdeq hθOb
  have hcomm := commutator_commutator_le_of_supplement (U := U) (W := W) (O := O)
    (X := X) (Ob := Ob) (J := J) (Z := Z) hU hWN hWZ hZN hZOb hNOb hOX hOOb hJX hJZ
    hsuppOb
  exact commutator_commutator_le_pCoreOf hcomm hXOb hθJ
    (isPerfect_lB_closure h hJ hdA hd1 hdc) hcoreO2

end CFSG.RankThree.PartTwo.Sec16.Kd166
