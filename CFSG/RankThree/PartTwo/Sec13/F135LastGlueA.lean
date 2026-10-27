module

public import CFSG.RankThree.PartTwo.Sec13.F135LastParts
public import CFSG.RankThree.PartOne.S10.AmbientTheta
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7_Embed

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13
open CritProof
open scoped commutatorElement

section GlueA

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {p : ℕ}
  {C : Subgroup (CFSG.pCore p L)}

theorem ga_mem_dOf {g : G} : g ∈ dOf L p C ↔ ∃ x : L, x ∈ omegaOneCore p C ∧ (x : G) = g := by
  unfold dOf
  exact Subgroup.mem_map

theorem ga_conj_mem_dOf (hcrit : Crit135 L p C) {g d : G} (hg : g ∈ L) (hd : d ∈ dOf L p C) :
    g * d * g⁻¹ ∈ dOf L p C := by
  obtain ⟨x, hx, rfl⟩ := ga_mem_dOf.mp hd
  exact ga_mem_dOf.mpr ⟨(⟨g, hg⟩ : L) * x * (⟨g, hg⟩ : L)⁻¹,
    hcrit.criticalAt.normal.conj_mem x hx ⟨g, hg⟩, rfl⟩

theorem dOf_le_L : dOf L p C ≤ L := by
  unfold dOf
  exact Subgroup.map_subtype_le _

theorem isPGroup_dOf : IsPGroup p (dOf L p C) := by
  intro g
  obtain ⟨x, hx, hxg⟩ := ga_mem_dOf.mp g.2
  have hle : omegaOneCore p C ≤ CFSG.pCore p L := by
    unfold omegaOneCore
    exact Subgroup.map_subtype_le _
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := p) (G := ↥L)) ⟨x, hle hx⟩
  have hx' : x ^ p ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  have hx'' : (x : G) ^ p ^ k = 1 := by
    rw [← Subgroup.coe_pow, hx', Subgroup.coe_one]
  refine ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hxg]
  exact hx''

theorem dPrime_le_dOf (hcrit : Crit135 L p C) {z : G} (hz : z ∈ L) :
    dPrime L p C z ≤ dOf L p C := by
  unfold dPrime
  rw [Subgroup.commutator_le]
  intro d hd k hk
  have hkL : k ∈ L := Subgroup.zpowers_le.mpr hz hk
  have key : ⁅d, k⁆ = d * (k * d⁻¹ * k⁻¹) := by
    rw [commutatorElement_def]
    simp only [mul_assoc]
  rw [key]
  exact mul_mem hd (ga_conj_mem_dOf hcrit hkL (inv_mem hd))

theorem isPGroup_dPrime (hcrit : Crit135 L p C) {z : G} (hz : z ∈ L) :
    IsPGroup p (dPrime L p C z) :=
  IsPGroup.to_le isPGroup_dOf (dPrime_le_dOf hcrit hz)

theorem L_le_centralizer (hD : Sec13Data G A c L) : L ≤ Subgroup.centralizer ({c} : Set G) :=
  (CFSG.RankThree.PartOne.mem_thetaComponentsAt_iff.mp
    (CFSG.RankThree.PartTwo.Sec13.lA_subset A c hD.mem_lA)).1

theorem orderOf_c (hD : Sec13Data G A c L) : orderOf c = 3 :=
  (Nat.card_zpowers c).symm.trans
    (CFSG.RankThree.PartTwo.Sec13.zpowers_mem_omegaA_iff.mp hD.zpowers_mem_omegaA).2.1

theorem ga_isPGroup_subgroupOf {H : Subgroup G} (hH : IsPGroup p H) (K : Subgroup G) :
    IsPGroup p (H.subgroupOf K) := by
  intro s
  have hsH : ((s : K) : G) ∈ H := Subgroup.mem_subgroupOf.mp s.2
  obtain ⟨k, hk⟩ := hH ⟨((s : K) : G), hsH⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  simpa using congrArg Subtype.val hk

theorem ga_isSubnormal_dOf_subgroupOf (hcrit : Crit135 L p C) {X : Subgroup G}
    (hLsub : (L.subgroupOf X).IsSubnormal) : ((dOf L p C).subgroupOf X).IsSubnormal := by
  have hle : (dOf L p C).subgroupOf X ≤ L.subgroupOf X := Subgroup.subgroupOf_mono X dOf_le_L
  refine Subgroup.IsSubnormal.step _ (L.subgroupOf X) hle hLsub ?_
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro h k hh hk
  rw [Subgroup.mem_subgroupOf] at hh hk ⊢
  simpa using ga_conj_mem_dOf hcrit hk hh

theorem ga_dOf_le_pCoreOf (hcrit : Crit135 L p C) {X : Subgroup G} (hdX : dOf L p C ≤ X)
    (hLsub : (L.subgroupOf X).IsSubnormal) :
    dOf L p C ≤ CFSG.Open.pCoreOf p X := by
  unfold CFSG.Open.pCoreOf
  have hS : ((dOf L p C).subgroupOf X).IsSubnormal :=
    ga_isSubnormal_dOf_subgroupOf hcrit hLsub
  have hp : IsPGroup p ((dOf L p C).subgroupOf X) := ga_isPGroup_subgroupOf isPGroup_dOf X
  haveI : Fact p.Prime := ⟨hcrit.prime⟩
  have hle := CFSG.LocalAnalysis.RankThreeTheoremC.le_pCore_of_isSubnormal_of_isPGroup hS hp
  calc dOf L p C = ((dOf L p C).subgroupOf X).map X.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hdX).symm
    _ ≤ (CFSG.pCore p X).map X.subtype := Subgroup.map_mono hle

theorem dOf_le_pCoreOf (hD : Sec13Data G A c L) (hcrit : Crit135 L p C) :
    dOf L p C ≤ CFSG.Open.pCoreOf p (Subgroup.centralizer ({c} : Set G)) :=
  ga_dOf_le_pCoreOf hcrit (le_trans dOf_le_L (L_le_centralizer hD))
    (CFSG.RankThree.PartOne.isSubnormal_of_mem_thetaComponentsAt
      (CFSG.RankThree.PartTwo.Sec13.lA_subset A c hD.mem_lA))

end GlueA

end CFSG.RankThree.PartTwo.Sec13.F135Last
