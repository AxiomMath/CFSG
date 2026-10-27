module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Stroth80.Sec7Stmt
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem eq_bot_of_normal_pgroup_of_pCore {X : Type*} [Group X] [Finite X] {H P : Subgroup X}
    (hpc : pCore 2 ↥H = ⊥) (hPH : P ≤ H) (hPn : ∀ h ∈ H, h ∈ Subgroup.normalizer (P : Set X))
    (hP2 : IsPGroup 2 P) : P = ⊥ := by
  haveI : (P.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPH).mpr fun h hh => hPn h hh
  have h1 : IsPGroup 2 ↥(P.subgroupOf H) := hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  have h2 : P.subgroupOf H ≤ pCore 2 ↥H := le_sSup ⟨inferInstance, h1⟩
  rw [hpc] at h2
  have h3 : P.subgroupOf H = ⊥ := le_bot_iff.mp h2
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hPH hx⟩ : H) ∈ P.subgroupOf H := Subgroup.mem_subgroupOf.mpr hx
  rw [h3, Subgroup.mem_bot] at this
  have h4 : x = 1 := congrArg Subtype.val this
  rw [h4]; exact Subgroup.one_mem _

theorem sq_eq_one_bar (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    (hZc : Sec7CentreMpStatement) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) : ∀ x ∈ bar M Q Z0, x ^ 2 = 1 := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have hyZ : (y : G) ∈ Z0 := Subgroup.mem_subgroupOf.mp hy
  have hyL : (y : G) ∈ LB M Q B := (hZc G M Q Z B hc n t hs Z0 hZ0 _ hyZ).1
  have hsq : (y : G) ^ 2 ∈ Q := hc.sq_mem_Q_of_mem_LB hyL
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (by simpa using hsq))

end CFSG.RankThree.GF2n.Stroth80
