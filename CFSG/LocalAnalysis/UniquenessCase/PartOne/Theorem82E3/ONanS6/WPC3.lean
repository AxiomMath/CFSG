module

import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofGenTools
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.Context
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec18.Transport
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}

@[expose] def PCoreInfCentralizerNormal (c : Ctx82E3 D) (x : G) : Prop :=
  ((CFSG.Open.pCoreOf 2 c.L ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf
    (Subgroup.centralizer ({x} : Set G))).Normal

theorem pCoreOf_inf_centralizer_le_solvableCore (c : Ctx82E3 D) {x : G}
    (hQN : PCoreInfCentralizerNormal c x) :
    CFSG.Open.pCoreOf 2 c.L ⊓ Subgroup.centralizer ({x} : Set G) ≤
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({x} : Set G)) := by
  classical
  set W : Subgroup G := Subgroup.centralizer ({x} : Set G) with hW
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 c.L ⊓ W with hQ
  have hQ2 : IsPGroup 2 Q :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L).to_le inf_le_left
  have hQW : Q ≤ W := inf_le_right
  have hQNW : (Q.subgroupOf W).Normal := hQN
  have hQ2' : IsPGroup 2 (Q.subgroupOf W) := by
    obtain ⟨n, hn⟩ := hQ2.exists_card_eq
    rw [IsPGroup.iff_card]
    exact ⟨n, (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQW).toEquiv).trans hn⟩
  have hQsolv : Group.IsSolvable ↥(Q.subgroupOf W) :=
    @IsNilpotent.to_isSolvable _ _ hQ2'.isNilpotent
  have hQ3 : ¬ 3 ∣ Nat.card (Q.subgroupOf W) := by
    obtain ⟨n, hn⟩ := hQ2'.exists_card_eq
    intro h
    rw [hn] at h
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  have hmax := (solvable_prime_complement_core_characterization (H := ↥W)
    (p := 3) Nat.prime_three).2.2.2.1
  intro y hy
  have hyW : y ∈ W := hy.2
  have hyQ : (⟨y, hyW⟩ : ↥W) ∈ Q.subgroupOf W := Subgroup.mem_subgroupOf.mpr hy
  exact Subgroup.mem_map.mpr ⟨⟨y, hyW⟩, hmax (Q.subgroupOf W) hQNW hQsolv hQ3 hyQ, rfl⟩

theorem le_normalizer_of_commutator_le_theta {c : G} {J A : Subgroup G}
    (hJ : J ∈ thetaComponentsAt 3 c) (hA : A ≤ Subgroup.centralizer ({c} : Set G))
    (hcomm : ⁅J, A⁆ ≤
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G))) :
    A ≤ Subgroup.normalizer (J : Set G) := by
  classical
  set H : Subgroup G := Subgroup.centralizer ({c} : Set G) with hHdef
  have hJ' : J ∈ CFSG.RankThree.PartTwo.thetaComponentsIn H := hJ
  obtain ⟨hJH, hKmem⟩ := CFSG.RankThree.PartTwo.mem_thetaComponentsIn_iff.mp hJ'
  set K : Subgroup ↥H := J.subgroupOf H with hKdef
  have hJK : K.map H.subtype = J := Subgroup.map_subgroupOf_eq_of_le hJH
  set π : ↥H →* (↥H ⧸ aschbacherSolvableCore 3 ↥H) :=
    QuotientGroup.mk' (aschbacherSolvableCore 3 ↥H) with hπdef
  set P : Subgroup ↥H := (K.map π).comap π with hPdef
  have hPres : inSubgroup perfectResidual P = K :=
    perfectResidual_comap_map_of_mem_thetaComponents (H := ↥H) Nat.prime_three hKmem
  have hcommπ : ∀ k ∈ K, ∀ (a : ↥H), (a : G) ∈ A → π a * π k = π k * π a := by
    intro k hk a ha
    have hmem : ⁅k, a⁆ ∈ aschbacherSolvableCore 3 ↥H := by
      have h1 : ⁅(k : G), (a : G)⁆ ∈ inSubgroup (aschbacherSolvableCore 3) H :=
        Subgroup.commutator_le.mp hcomm (k : G) (Subgroup.mem_subgroupOf.mp hk) (a : G) ha
      obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.mp h1
      have hzk : ⁅k, a⁆ = z := Subtype.ext hzeq.symm
      rw [hzk]
      exact hz
    have hπ1 : π ⁅k, a⁆ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hmem
    have hc : ⁅π k, π a⁆ = 1 := by
      rw [← map_commutatorElement, hπ1]
    rw [commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc.symm
  have hfwd : ∀ a ∈ A, ∀ x ∈ (P.map H.subtype : Subgroup G),
      a * x * a⁻¹ ∈ P.map H.subtype := by
    intro a ha x hx
    obtain ⟨p, hpP, rfl⟩ := Subgroup.mem_map.mp hx
    have haH : a ∈ H := hA ha
    have hπp : π p ∈ K.map π := Subgroup.mem_comap.mp hpP
    obtain ⟨k, hkK, hkπ⟩ := Subgroup.mem_map.mp hπp
    have hc := hcommπ k hkK ⟨a, haH⟩ ha
    have hπeq : π (⟨a, haH⟩ * p * ⟨a, haH⟩⁻¹) = π p := by
      rw [map_mul, map_mul, map_inv, ← hkπ, hc]
      group
    refine Subgroup.mem_map.mpr ⟨⟨a, haH⟩ * p * ⟨a, haH⟩⁻¹, ?_, rfl⟩
    rw [Subgroup.mem_comap, hπeq]
    exact hπp
  have key : ∀ a ∈ A, a ∈ Subgroup.normalizer ((P.map H.subtype : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hfwd a ha x
    · intro hx
      have h := hfwd a⁻¹ (A.inv_mem ha) (a * x * a⁻¹) hx
      have he : a⁻¹ * (a * x * a⁻¹) * (a⁻¹)⁻¹ = x := by group
      rwa [he] at h
  have hres : inSubgroup perfectResidual (P.map H.subtype : Subgroup G) = J := by
    rw [CFSG.RankThree.PartTwo.Sec18.inSubgroup_perfectResidual_map H.subtype
        H.subtype_injective P, hPres, hJK]
  intro a ha
  rw [← hres]
  exact CFSG.RankThree.PartTwo.Sec8.Item812Res2.mem_normalizer_inSubgroup_perfectResidual
    (key a ha)

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
