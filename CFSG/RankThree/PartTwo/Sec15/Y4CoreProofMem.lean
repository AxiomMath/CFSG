module

public import CFSG.RankThree.PartTwo.Sec4.Item44Narrow41
import CFSG.RankThree.PartTwo.Sec15.Item1423ProofTools
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.GroupTheory.ConjugatePairSubnormality
import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofDefs
public import CFSG.RankThree.PartTwo.Sec16.Item167Proof

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Y4CoreMemSolvR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ M ∈ scriptY2 A, generalizedFitting ↥M = CFSG.pCore 2 ↥M →
      ∀ J ∈ comp3In (delta A (lB A) M), A ≤ Subgroup.normalizer (J : Set G) →
        ¬ Group.IsSolvable ↥(oPrimeResidualOf 3 (delta A (lB A) J))

@[expose] noncomputable def Y4CoreMemExclR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ M ∈ scriptY2 A, generalizedFitting ↥M = CFSG.pCore 2 ↥M →
      ∀ J ∈ comp3In (delta A (lB A) M), A ≤ Subgroup.normalizer (J : Set G) →
        J ∈ thetaComponentsIn M → J = delta A (lB A) J →
        (Nonempty (↥J ⧸ Sec4.oTwoFitting ↥J ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∨
          (∃ p : ℕ, p.Prime ∧ 3 < p ∧
            Nonempty (↥J ⧸ Sec4.oTwoP p ↥J ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) ∨
          (Nonempty (↥J ⧸ Sec4.oTwoP 3 ↥J ≃*
              CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 3 1)) ∨
            Sec4.IsExtOf (↥J ⧸ Sec4.oTwoP 3 ↥J) (alternatingGroup (Fin 5)) Sec4.Q8D8)) →
          IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)

namespace Y4Core

theorem mem_thetaComponentsIn_mid {N K J : Subgroup G} (hJ : J ∈ thetaComponentsIn N)
    (hJK : J ≤ K) (hKN : K ≤ N) : J ∈ thetaComponentsIn K :=
  Sec6.mem_thetaComponentsIn_of hJK (isPerfect_of_mem_thetaComponentsIn hJ)
    (CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hKN (mem_thetaComponentsIn_iff.mp hJ).2.2.1)
    (isQuasisimple_theta_of_mem_thetaComponentsIn hJ)

theorem mem_thetaComponentsIn_of_item149 {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (h149 : Item149 A LB) {M J : Subgroup G} (hM : M ∈ scriptY A)
    (hJ : J ∈ comp3In (delta A LB M)) : J ∈ thetaComponentsIn M := by
  obtain ⟨h1, h2, -⟩ := h149 M hM
  have hNΔ : oPrimeResidualOf 3 (delta A LB M) ≤ delta A LB M := oPrimeResidualOf_le_self 3 _
  have hJN : J ≤ oPrimeResidualOf 3 (delta A LB M) :=
    hJ.2.le.trans (oPrimeResidualOf_mono 3 (le_of_mem_comp3In hJ))
  have hNn : ((oPrimeResidualOf 3 (delta A LB M)).subgroupOf M).Normal := by
    rw [h1]
    exact h2
  exact Proof1423.mem_thetaComponentsIn_of_isSubnormal (mem_thetaComponentsIn_mid hJ.1 hJN hNΔ)
    (hNΔ.trans (delta_le M)) hNn.isSubnormal

theorem eq_delta_of_not_isSolvable {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (h149 : Item149 A LB) {M J : Subgroup G} (hJM : J ∈ thetaComponentsIn M)
    (hJY : J ∈ scriptY A) (hs : ¬ Group.IsSolvable ↥(oPrimeResidualOf 3 (delta A LB J))) :
    J = delta A LB J := by
  obtain ⟨h1, h2, -⟩ := h149 J hJY
  have hNn : ((oPrimeResidualOf 3 (delta A LB J)).subgroupOf J).Normal := by
    rw [h1]
    exact h2
  set N := oPrimeResidualOf 3 (delta A LB J) with hN
  have hNΔ : N ≤ delta A LB J := oPrimeResidualOf_le_self 3 _
  have hNJ : N ≤ J := hNΔ.trans (delta_le J)
  obtain ⟨⟨n, hn, -⟩, -, hperf, -, -, hbot⟩ := CFSG.perfect_residual_characterization (G := ↥N)
  have hPp : Group.IsPerfect ↥((derivedSeries ↥N n).map N.subtype) := by
    rw [hn] at hperf
    exact Group.IsPerfect.map N.subtype
  have hP1 : (derivedSeries ↥N n).map N.subtype ≠ ⊥ := by
    intro h0
    apply hs
    rw [← hbot, hn]
    exact (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).mp h0
  have hNeq := eq_of_le_of_subgroupOf_normal (isPerfect_of_mem_thetaComponentsIn hJM)
    (isQuasisimple_theta_of_mem_thetaComponentsIn hJM) hNJ hNn (Subgroup.map_subtype_le _) hPp hP1
  exact le_antisymm (hNeq ▸ hNΔ) (delta_le J)

end Y4Core

open Y4Core

theorem y4CoreMemR_of_parts
    (h149 : Sec16.Item149S14) (hS : Y4CoreMemSolvR) (hE : Y4CoreMemExclR) : Y4CoreMemR := by
  intro G _ _ A c L h M hM hF J hJ hAJ
  have h149' := h149 G A c L h.toSec14Std
  have hJM : J ∈ thetaComponentsIn M := mem_thetaComponentsIn_of_item149 h149' hM.1 hJ
  have hJtop : J ≠ ⊤ := fun h' =>
    hM.1.1 (top_le_iff.mp (h' ▸ le_of_mem_thetaComponentsIn hJM))
  have hJY : J ∈ scriptY A := ⟨hJtop, hAJ⟩
  have : Nontrivial ↥J := (Subgroup.nontrivial_iff_ne_bot J).mpr (ne_bot hJ)
  have hO2 : CFSG.pCore 2 ↥J ≠ ⊥ :=
    pCore_ne_bot_of_isCharacteristicP (isCharacteristicP_of_mem_thetaComponentsIn hF hJM)
  have hΔ : J = delta A (lB A) J :=
    eq_delta_of_not_isSolvable h149' hJM hJY (hS G A c L h M hM hF J hJ hAJ)
  have hq : IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) := by
    have hS4 : SectionFourHyp ↥J := h.toTheoremFourHyp.sectionFourHyp hJtop
    have hJp : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hJM
    have hJq := isQuasisimple_theta_of_mem_thetaComponentsIn hJM
    have hθ := solvable_prime_complement_core_characterization (H := ↥J) Nat.prime_three
    set θ := aschbacherSolvableCore 3 ↥J
    set K := (Subgroup.center (↥J ⧸ θ)).comap (QuotientGroup.mk' θ)
    have hKn : K.Normal := Subgroup.Normal.comap inferInstance _
    have hKs : Group.IsSolvable K := isSolvable_comap_center θ hθ.1
    have : IsSimpleGroup ((↥J ⧸ θ) ⧸ Subgroup.center (↥J ⧸ θ)) := hJq.2.1
    have hKsimp : IsSimpleGroup (↥J ⧸ K) :=
      (quotientComapEquiv θ (Subgroup.center (↥J ⧸ θ))).isSimpleGroup
    have hex := hE G A c L h M hM hF J hJ hAJ hJM hΔ
    rcases Sec4.item4_4OTwo_holds ↥J hS4 hJp K hKs hKsimp hO2 with h1 | h2 | h3 | h4
    · exact h1
    · exact hex (Or.inl h2)
    · exact hex (Or.inr (Or.inl h3))
    · exact hex (Or.inr (Or.inr h4))
  exact ⟨⟨hJY, hJ.2, hΔ, hq⟩, ⟨hJY, pCoreOf_ne_bot_of_pCore_ne_bot hO2⟩⟩

end CFSG.RankThree.PartTwo.Sec15
