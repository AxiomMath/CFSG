module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WU3Rank
public import CFSG.RankThree.PartTwo.Sec13.Ronan138P5Core
import CFSG.RankThree.PartTwo.Sec14.Ronan148WU3Aut
import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofTools
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec4.LThreePiKind
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.RankThree.PartTwo.KFacts.KS12MovesSL
import CFSG.RankThree.PartTwo.Sec14.Item1413Res2ProofSimple
import CFSG.RankThree.PartTwo.Sec14.Item1413Res2ProofTools
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.RankThree.PartTwo.Sec4.Census.Interface46
import CFSG.Sporadic.Schreier.J4SProfileNode
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank

@[expose] def Step148OmegaRankThreeNine : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ e ∈ A, Subgroup.zpowers e ∈ omegaA A → ∀ Le ∈ lA A e,
    ∀ (p f : ℕ) [Fact p.Prime], 1 ≤ f →
      Sec4.IsoLThreePi (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) p f →
      (p ^ f % 9 = 1 ∨ p ^ f % 9 = 8) →
      ∀ F : Subgroup G, e ∈ F → CFSG.Open.IsElemAbelian 3 F → Nat.card F = 81 →
        F ⊓ Sec4.thetaQuotCentralizer Le ≤ Subgroup.zpowers e → False

variable {G : Type} [Group G] [Finite G]

theorem isPerfect_quotient (L : Type*) [Group L] [Group.IsPerfect L] (N : Subgroup L) [N.Normal] :
    Group.IsPerfect (L ⧸ N) := by
  refine ⟨?_⟩
  have h := Subgroup.map_commutator (⊤ : Subgroup L) ⊤ (QuotientGroup.mk' N)
  rw [show ⁅(⊤ : Subgroup L), ⊤⁆ = ⊤ from Group.IsPerfect.commutator_eq_top,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h
  exact h.symm

theorem mem_thetaQuotCentralizer_of_le_centralizer {L : Subgroup G} {e : G}
    (hLe : L ≤ Subgroup.centralizer ({e} : Set G)) : e ∈ Sec4.thetaQuotCentralizer L := by
  have hc : ∀ l ∈ L, e * l * e⁻¹ = l := fun l hl => by
    rw [(Subgroup.mem_centralizer_singleton_iff.mp (hLe hl)).symm, mul_inv_cancel_right]
  have heN : e ∈ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro l
    constructor
    · intro hl
      rw [hc l hl]
      exact hl
    · intro hl
      have h1 := hc _ hl
      have h2 : e * l * e⁻¹ = l :=
        calc e * l * e⁻¹ = e⁻¹ * (e * (e * l * e⁻¹) * e⁻¹) * e := by group
          _ = e⁻¹ * (e * l * e⁻¹) * e := by rw [h1]
          _ = l := by group
      rw [← h2]
      exact hl
  refine ⟨⟨e, heN⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply]
  have h1 : L.normalizerMonoidHom ⟨e, heN⟩ = 1 := by
    refine MulEquiv.ext fun l => Subtype.ext ?_
    rw [Sec4.coe_normalizerMonoidHom, MulAut.one_apply]
    exact hc l l.2
  rw [h1, map_one]

theorem step148OmegaRankThree_of (hCore : Step13PZeroCore)
    (hNine : Step148OmegaRankThreeNine) : Step148OmegaRankThree := by
  intro G _ _ A c L h e he heΩ Le hLeA hLt F heF hF hF81
  obtain ⟨p, f, hp, hf, hiso⟩ := hLt
  haveI := hp
  have h13 : Sec13Data G A e Le :=
    { h.toSec13Data with zpowers_mem_omegaA := heΩ, mem_lA := hLeA }
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := h.mem_partTwoF.1.2
  have he3 : e ^ 3 = 1 := hA3 e he
  have he1 : e ≠ 1 := by
    intro h1
    obtain ⟨-, hcard, -⟩ := heΩ
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hcard
    norm_num at hcard
  have hLeC : Le ≤ Subgroup.centralizer ({e} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLeA.1
  haveI : Group.IsPerfect ↥Le := Sec6.isPerfect_of_mem_thetaComponentsAt hLeA.1
  haveI : Group.IsPerfect (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) := isPerfect_quotient _ _
  have h3 : 3 ∣ Nat.card Le :=
    (Sec19.Step1914TriProof.three_dvd_card_of_isoLThreePi hf hiso).trans
      (Subgroup.card_quotient_dvd_card _)
  have hFC : F ≤ Subgroup.centralizer ({e} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hF.1.is_comm.comm ⟨x, hx⟩ ⟨e, heF⟩))
  have hFN : F ≤ Subgroup.normalizer (Le : Set G) :=
    hFC.trans (Proof1413Res3.centralizer_le_normalizer_of_mem_lA h heΩ hLeA h3)
  have heC : e ∈ Sec4.thetaQuotCentralizer Le := mem_thetaQuotCentralizer_of_le_centralizer hLeC
  by_cases hP : F ⊓ Sec4.thetaQuotCentralizer Le ≤ Subgroup.zpowers e
  · by_cases h9 : p ^ f % 9 = 1 ∨ p ^ f % 9 = 8
    · exact hNine G A c L h e he heΩ Le hLeA p f hf hiso h9 F heF hF hF81 hP
    have hq2 : 2 < p ^ f := by
      have hne := (Sec19.Step1914TriProof.isSimpleGroup_of_isoLThreePi hf hiso).2
      have hp2 := hp.out.two_le
      have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
      omega
    set φ := (Sec4.thetaQuotMulAut ↥Le).comp Le.normalizerMonoidHom with hφ
    set F' := F.subgroupOf (Subgroup.normalizer (Le : Set G)) with hF'
    set ψ := φ.comp F'.subtype with hψ
    have hF'card : Nat.card F' = 81 := by
      rw [hF', ← hF81]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFN).toEquiv
    have hF'ab : CFSG.Open.IsElemAbelian 3 F' := by
      refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun y hy => Subtype.ext ?_⟩
      · exact (show ((a : Subgroup.normalizer (Le : Set G)) : G) * b = b * a from
          congrArg Subtype.val (hF.1.is_comm.comm ⟨_, Subgroup.mem_subgroupOf.mp a.2⟩
            ⟨_, Subgroup.mem_subgroupOf.mp b.2⟩))
      · exact hF.2 _ (Subgroup.mem_subgroupOf.mp hy)
    have hrange : CFSG.Open.IsElemAbelian 3 ψ.range := by
      rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype]
      exact isElemAbelian_map _ hF'ab
    have hle9 := card_le_nine_of_isElemAbelian_mulAut hf hiso hq2 h9 hrange
    have hmem : ∀ x : ψ.ker, (((x : F') : Subgroup.normalizer (Le : Set G)) : G) ∈
        Subgroup.zpowers e := by
      intro x
      apply hP
      refine ⟨Subgroup.mem_subgroupOf.mp (x : F').2, ⟨(x : F'), ?_, rfl⟩⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      exact MonoidHom.mem_ker.mp x.2
    have hker3 : Nat.card ψ.ker ≤ 3 := by
      calc Nat.card ψ.ker ≤ Nat.card (Subgroup.zpowers e) :=
            Nat.card_le_card_of_injective (fun x => ⟨_, hmem x⟩) (by
              intro x y hxy
              have h1 := congrArg (fun z : Subgroup.zpowers e => (z : G)) hxy
              simp only at h1
              exact Subtype.ext (Subtype.ext (Subtype.ext h1)))
        _ ≤ 3 := by
          rw [Nat.card_zpowers]
          exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one he3)
    have hcard : Nat.card F' = Nat.card ψ.ker * Nat.card ψ.range := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, mul_comm]
    nlinarith [hcard, hker3, hle9, hF'card]
  ·
    obtain ⟨x, hxP, hxe⟩ := Set.not_subset.mp hP
    have hxF : x ∈ F := hxP.1
    have hxC : x ∈ Sec4.thetaQuotCentralizer Le := hxP.2
    have hx3 : x ^ 3 = 1 := hF.2 x hxF
    have hxecomm : x * e = e * x := congrArg Subtype.val (hF.1.is_comm.comm ⟨x, hxF⟩ ⟨e, heF⟩)
    have hord : orderOf e = 3 := orderOf_eq_prime he3 he1
    have hP9 : Nat.card (Subgroup.zpowers e ⊔ Subgroup.zpowers x : Subgroup G) = 9 :=
      Sec4.card_zpowers_sup_zpowers hx3 hord hxe hxecomm
    have hPF : (Subgroup.zpowers e ⊔ Subgroup.zpowers x : Subgroup G) ≤ F :=
      sup_le (Subgroup.zpowers_le.mpr heF) (Subgroup.zpowers_le.mpr hxF)
    have hPC : (Subgroup.zpowers e ⊔ Subgroup.zpowers x : Subgroup G) ≤
        Sec4.thetaQuotCentralizer Le :=
      sup_le (Subgroup.zpowers_le.mpr heC) (Subgroup.zpowers_le.mpr hxC)
    have hPab : CFSG.Assembly.IsElemAbelian 3
        (Subgroup.zpowers e ⊔ Subgroup.zpowers x : Subgroup G) :=
      ⟨⟨⟨fun a b => Subtype.ext (show (a : G) * b = b * a from congrArg Subtype.val
        (hF.1.is_comm.comm ⟨a, hPF a.2⟩ ⟨b, hPF b.2⟩))⟩⟩, fun y hy => hF.2 y (hPF hy)⟩
    exact hCore G A e Le h13 ⟨p, f, hp, hf, hiso⟩ _
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers e)) hPC hPab hP9

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
