module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofSolv
import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofRead
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.GroupTheory.SteinbergCEThetaSubnormalDichotomy
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofYB
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofHJ
import CFSG.RankThree.PartTwo.Sec14.Item148ProofYB

public section

namespace CFSG.RankThree.PartTwo.Sec15.LiebeckY4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

@[expose] noncomputable def Y4CoreMemSolvHJQR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → AllPointsHJ A → ∀ M ∈ scriptY2 A, generalizedFitting ↥M = CFSG.pCore 2 ↥M →
      (∃ B : Subgroup G, IsHyperplane A B ∧ ¬ YBOne A (lB A) M B) →
      IsQuasisimple ↥(((deltaZero A (lB A) M).subgroupOf M).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M))) →
      ∀ J ∈ comp3In (delta A (lB A) M), A ≤ Subgroup.normalizer (J : Set G) →
        ¬ Group.IsSolvable ↥(oPrimeResidualOf 3 (delta A (lB A) J))

@[expose] noncomputable def Y4CoreMemSolvHJProdR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → AllPointsHJ A → ∀ M ∈ scriptY2 A, generalizedFitting ↥M = CFSG.pCore 2 ↥M →
      ¬ IsQuasisimple ↥(((deltaZero A (lB A) M).subgroupOf M).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M))) →
      ∀ J ∈ comp3In (delta A (lB A) M), A ≤ Subgroup.normalizer (J : Set G) →
        ¬ Group.IsSolvable ↥(oPrimeResidualOf 3 (delta A (lB A) J))

theorem y4CoreMemSolvHJR_of_split (hQ : Y4CoreMemSolvHJQR) (hP : Y4CoreMemSolvHJProdR) :
    Y4CoreMemSolvHJR := by
  intro G _ _ A c L h hall M hM hF hcase J hJ hAJ
  by_cases hq : IsQuasisimple ↥(((deltaZero A (lB A) M).subgroupOf M).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)))
  · rcases hcase with hB | hnq
    · exact hQ G A c L h hall M hM hF hB hq J hJ hAJ
    · exact absurd hq hnq
  · exact hP G A c L h hall M hM hF hq J hJ hAJ

@[expose] noncomputable def Step148HJYBGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ M ∈ scriptY A, ¬ Group.IsSolvable ↥M →
      ∀ B : Subgroup G, IsHyperplane A B → ¬ YBOne A (lB A) M B →
      ∀ (b d : G) (Lb : Subgroup G), IsLBConfig A B b d Lb →
      ∀ YB ∈ thetaComponentsIn (M ⊓ Subgroup.centralizer (B : Set G)),
        (Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
          Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5))) →
        deltaZero A (lB A) (M ⊓ Subgroup.centralizer (B : Set G)) ≤
          pPrimeCoreOf 3 (M ⊓ Subgroup.centralizer (B : Set G)) ⊔ YB →
        YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B →
          ¬ IsMulCommutative ↥(((deltaZero A (lB A) YB).subgroupOf M).map
              (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M))) ∧
            ¬ Group.IsSolvable ↥(oPrimeResidualOf 3 (deltaZero A (lB A) YB))

@[expose] noncomputable def Step148HJYBLift : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → AllPointsHJ A → ∀ M ∈ scriptY A, ¬ Group.IsSolvable ↥M →
      ∀ B : Subgroup G, IsHyperplane A B → ¬ YBOne A (lB A) M B →
        ∃ J' ∈ thetaComponentsIn M, A ≤ Subgroup.normalizer (J' : Set G) ∧
          ∃ K : Subgroup G, K ≤ J' ∧ K = deltaZero A (lB A) K ∧
            ¬ IsMulCommutative ↥((K.subgroupOf M).map
              (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M))) ∧
            ¬ Group.IsSolvable ↥(oPrimeResidualOf 3 K)

@[expose] noncomputable def Step148HJYBLiftB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → AllPointsHJ A → ∀ M ∈ scriptY A, ¬ Group.IsSolvable ↥M →
      ∀ B : Subgroup G, IsHyperplane A B → ¬ YBOne A (lB A) M B →
        ∃ J' ∈ thetaComponentsIn M, A ≤ Subgroup.normalizer (J' : Set G) ∧
          ∃ K : Subgroup G, K ≤ J' ∧ K ≤ M ⊓ Subgroup.centralizer (B : Set G) ∧
            K = deltaZero A (lB A) K ∧
            ¬ IsMulCommutative ↥((K.subgroupOf M).map
              (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M))) ∧
            ¬ Group.IsSolvable ↥(oPrimeResidualOf 3 K)

theorem step148HJYBLift_of_liftB (h : Step148HJYBLiftB) : Step148HJYBLift := by
  intro G _ _ A c L hR hall M hM hMs B hB hnot
  obtain ⟨J', hJ', hAJ', K, hKJ', -, hKΔ, hnc, hns⟩ := h G A c L hR hall M hM hMs B hB hnot
  exact ⟨J', hJ', hAJ', K, hKJ', hKΔ, hnc, hns⟩

theorem deltaZero_deltaZero {G : Type} [Group G] [Finite G] (A : Subgroup G)
    (LB : Subgroup G → Subgroup G) (Y : Subgroup G) :
    deltaZero A LB (deltaZero A LB Y) = deltaZero A LB Y :=
  le_antisymm (deltaZero_le _) (sSup_le fun Q hQ => le_deltaZero hQ.1 (le_deltaZero hQ.1 hQ.2))

section Lift

theorem step148HJYBLiftB_of_gen (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (hG : Step148HJYBGen) : Step148HJYBLiftB := by
  intro G _ _ A c L h _ M hM hMs B hB hnot
  have h14 := h.toSec14Std
  obtain ⟨b, d, Lb, hconf⟩ := exists_isLBConfig_of_not_yBOne h14.isElemAbelian.1 hB hnot
  obtain ⟨YB, hYB, htype, hle, hYBle⟩ :=
    step148YBShape_holds G A c L h14 M hM hMs B hB hnot b d Lb hconf
  obtain ⟨Yd, -, hYBYd, -, J, hJ, hYdJ, hAJ⟩ :=
    Main148.exists_yd_j148 h45 h48 h14 hM hB hYB hconf
  obtain ⟨hnc, hns⟩ := hG G A c L h14 M hM hMs B hB hnot b d Lb hconf YB hYB htype hle hYBle
  refine ⟨J, hJ, hAJ, deltaZero A (lB A) YB, ?_, ?_, (deltaZero_deltaZero A (lB A) YB).symm,
    hnc, hns⟩
  · exact (deltaZero_le YB).trans (hYBYd.trans hYdJ)
  · exact (deltaZero_le YB).trans (le_of_mem_thetaComponentsIn hYB)

theorem step148HJYBLift_of_gen (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (hG : Step148HJYBGen) : Step148HJYBLift :=
  step148HJYBLift_of_liftB (step148HJYBLiftB_of_gen h45 h48 hG)

end Lift

section Tools

variable {G : Type} [Group G] [Finite G]

private theorem not_isSolvable_oPrimeResidual_delta {A : Subgroup G}
    {LB : Subgroup G → Subgroup G} {J K : Subgroup G} (hKJ : K ≤ J) (hKΔ : K = deltaZero A LB K)
    (hKns : ¬ Group.IsSolvable ↥(oPrimeResidualOf 3 K)) :
    ¬ Group.IsSolvable ↥(oPrimeResidualOf 3 (delta A LB J)) := fun hsol =>
  hKns (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
    (oPrimeResidualOf_mono 3 (hKΔ.le.trans ((deltaZero_mono hKJ).trans
      (deltaZero_le_delta J))))))

private theorem le_of_map_le_of_not_isMulCommutative {M J J' K : Subgroup G}
    (hJ : J ∈ thetaComponentsIn M) (hJ' : J' ∈ thetaComponentsIn M) (hKJ' : K ≤ J')
    (hKJ : (K.subgroupOf M).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)) ≤
      (J.subgroupOf M).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)))
    (hKnc : ¬ IsMulCommutative ↥((K.subgroupOf M).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)))) : K ≤ J := by
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M) with hπ
  obtain ⟨hJMle, hJ1⟩ := mem_thetaComponentsIn_iff.mp hJ
  obtain ⟨hJ'Mle, hJ'1⟩ := mem_thetaComponentsIn_iff.mp hJ'
  rcases GroupTheory.theta_component_subnormal_subgroup_dichotomy Nat.prime_three hJ'1
      hJ1.2.1 with hle | ⟨-, hcomm⟩
  · refine hKJ'.trans ?_
    rw [← Subgroup.map_subgroupOf_eq_of_le hJ'Mle, ← Subgroup.map_subgroupOf_eq_of_le hJMle]
    exact Subgroup.map_mono hle
  · exfalso
    have hcomm' : ⁅(J'.subgroupOf M).map π, (J.subgroupOf M).map π⁆ = ⊥ := by
      rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk']
      exact hcomm.trans (Proof15Res8Solv.inSubgroup_theta_le_pPrimeCore hJ'1)
    apply hKnc
    refine ⟨⟨fun x y => ?_⟩⟩
    apply Subtype.ext
    have hmem : ⁅((x : ↥((K.subgroupOf M).map π)) : ↥M ⧸ CFSG.pPrimeCore 3 ↥M),
        ((y : ↥((K.subgroupOf M).map π)) : ↥M ⧸ CFSG.pPrimeCore 3 ↥M)⁆ ∈
        ⁅(J'.subgroupOf M).map π, (J.subgroupOf M).map π⁆ :=
      Subgroup.commutator_mem_commutator
        (Proof15Res8Solv.map_subgroupOf_mono hKJ' π x.2) (hKJ y.2)
    rw [hcomm', Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem

private theorem not_isSolvable_of_mem_thetaComponentsIn {M J : Subgroup G}
    (hJM : J ∈ thetaComponentsIn M) : ¬ Group.IsSolvable ↥M :=
  Proof15Res8Solv.not_isSolvable_of_le (mem_thetaComponentsIn_iff.mp hJM).1
    (isPerfect_of_mem_thetaComponentsIn hJM) (Y4Core.ne_bot_of_mem_thetaComponentsIn hJM)

end Tools

section Item148

theorem y4CoreMemSolvHJQR_of_lift (h148 : Item148R) (h149 : Sec16.Item149S14)
    (hbot : Item145BotS14) (hL : Step148HJYBLift) : Y4CoreMemSolvHJQR := by
  intro G _ _ A c L h hall M hM hF ⟨B, hB, hnot⟩ hq J hJ hAJ
  have h14 := h.toSec14Std
  have hJM : J ∈ thetaComponentsIn M :=
    Y4Core.mem_thetaComponentsIn_of_item149 (h149 G A c L h14) hM.1 hJ
  have hJD : J ≤ deltaZero A (lB A) M :=
    calc J = oPrimeResidualOf 3 J := hJ.2
      _ ≤ oPrimeResidualOf 3 (delta A (lB A) M) :=
        oPrimeResidualOf_mono 3 (Y4Core.le_of_mem_comp3In hJ)
      _ ≤ deltaZero A (lB A) (delta A (lB A) M) :=
        Y4Core.oPrimeResidualOf_le_deltaZero h14.isE27 (hbot G A c L h14)
          (le_normalizer_delta M) (delta_delta M).symm
      _ ≤ deltaZero A (lB A) M := deltaZero_mono (delta_le M)
  obtain ⟨J', hJ'M, -, K, hKJ', hKΔ, hKnc, hKns⟩ :=
    hL G A c L h hall M hM.1 (not_isSolvable_of_mem_thetaComponentsIn hJM) B hB hnot
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)
  have hDc : IsComponent (((deltaZero A (lB A) M).subgroupOf M).map π) :=
    ⟨hq, ((h148 G A c L h M hM.1).1 : Subgroup.Normal _).isSubnormal⟩
  have hJR : ¬ J.subgroupOf M ≤ CFSG.pPrimeCore 3 ↥M := fun hle =>
    Y4Core.not_le_pPrimeCoreOf (⟨hJM, hJ.2⟩ : J ∈ comp3In M) (by
      rw [← Subgroup.map_subgroupOf_eq_of_le (mem_thetaComponentsIn_iff.mp hJM).1]
      exact Subgroup.map_mono hle)
  have hJbc : IsComponent ((J.subgroupOf M).map π) :=
    Y4Core.isComponent_map_mk' (mem_thetaComponentsIn_iff.mp hJM).2 hJR
  have hJbeq : (J.subgroupOf M).map π = ((deltaZero A (lB A) M).subgroupOf M).map π :=
    (Y4Core.eq_or_eq_of_le_sup hJbc (Or.inr hDc) (Or.inr hDc)
      ((Proof15Res8Solv.map_subgroupOf_mono hJD π).trans le_sup_left)).elim id id
  have hKM : K ≤ M := hKJ'.trans (le_of_mem_thetaComponentsIn hJ'M)
  refine not_isSolvable_oPrimeResidual_delta
    (le_of_map_le_of_not_isMulCommutative hJM hJ'M hKJ' ?_ hKnc) hKΔ hKns
  rw [hJbeq]
  exact Proof15Res8Solv.map_subgroupOf_mono (hKΔ.le.trans (deltaZero_mono hKM)) π

end Item148

end CFSG.RankThree.PartTwo.Sec15.LiebeckY4
