module

public import CFSG.Quasithin.Vol2.Ch3T326V
public import CFSG.Quasithin.Background.B1MoreSevenA
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.Fischer.Pairs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingSymmetric
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3Structure312Facts
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M22
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CPrime
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Transvection.Statement
public import CFSG.Walter.J1
public import Certificates.Certificate8026Base

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

theorem exists_pow_eq_mul {G : Type} [Group G] {L : Subgroup G} {l n : G} (hl : l ∈ L)
    (hn : n ∈ Subgroup.normalizer (L : Set G)) (m : ℕ) : ∃ l' ∈ L, (l * n) ^ m = l' * n ^ m := by
  induction m with
  | zero => exact ⟨1, L.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨l', hl', h⟩ := ih
    have hc : n ^ m * l * (n ^ m)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hn m) l).mp hl
    refine ⟨l' * (n ^ m * l * (n ^ m)⁻¹), L.mul_mem hl' hc, ?_⟩
    rw [pow_succ (l * n), h, pow_succ n]
    group

namespace Ctx

variable {G : Type} [Group G] [Finite G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem exists_pow_of_centralizer
    (hA37 : Vol2Native.A37ForSQTKCat) (hA38 : Vol2Native.A38ForSQTKCat)
    [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))]
    (hL32 : IsPSL 3 2 1 ↥(autOn L (conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))))
    {l : G} (hl : l ∈ L)
    (hlc : l ∈ Subgroup.centralizer (conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)) : Set G)) :
    ∃ b : ℕ, l ^ 2 ^ b = 1 := by
  have hLVM := c.L_le_NVM
  have hs := Vol2.Ch10.SecA.isSimpleGroup_of_not_normal hA37 hA38 c.fsu.simple
    c.fsu.nonabelian c.fsu.qtke c.fsu.faithful c.not_le_normalizer
  set VM := conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))
    with hVMdef
  set C := (Subgroup.centralizer (VM : Set G)).subgroupOf L with hCdef
  have hCn : C.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hx ⊢
    intro v hv
    have hv' : (g : G)⁻¹ * v * g ∈ VM :=
      (Subgroup.mem_normalizer_iff''.mp (hLVM g.2) v).mp hv
    have h1 := hx _ hv'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc v * ((g : G) * x * (g : G)⁻¹) = g * (((g : G)⁻¹ * v * g) * x) * (g : G)⁻¹ := by group
      _ = g * (x * ((g : G)⁻¹ * v * g)) * (g : G)⁻¹ := by rw [h1]
      _ = (g : G) * x * (g : G)⁻¹ * v := by group
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hCπ : (C.map π).Normal := hCn.map π (QuotientGroup.mk'_surjective _)
  rcases hs.eq_bot_or_eq_top_of_normal (C.map π) with h | h
  · have hmem : (⟨l, hl⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
      rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥L)]
      have h2 : π ⟨l, hl⟩ ∈ C.map π := ⟨⟨l, hl⟩, Subgroup.mem_subgroupOf.mpr hlc, rfl⟩
      rw [h, Subgroup.mem_bot] at h2
      exact MonoidHom.mem_ker.mpr h2
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 ↥(CFSG.pCore 2 ↥L)) ⟨_, hmem⟩
    exact ⟨b, congrArg (fun y : ↥(CFSG.pCore 2 ↥L) => ((y : ↥L) : G)) hb⟩
  · exfalso
    apply not_isPGroup_two_of_isPSL hL32
    have hP : IsPGroup 2 ↥((CFSG.pCore 2 ↥L).map L.subtype) :=
      (CFSG.pCore_isPGroup : IsPGroup 2 ↥(CFSG.pCore 2 ↥L)).map _
    have hPVM : (CFSG.pCore 2 ↥L).map L.subtype ≤ Subgroup.normalizer (VM : Set G) :=
      (Subgroup.map_subtype_le _).trans hLVM
    have hA : IsPGroup 2 ↥(autOn ((CFSG.pCore 2 ↥L).map L.subtype) VM) :=
      (hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPVM).symm).map (conjAct VM)
    refine hA.to_le fun b hb => ?_
    obtain ⟨m, hm, rfl⟩ := Setup.mem_autOn_iff.mp hb
    have h2 : π ⟨m, hm⟩ ∈ C.map π := by rw [h]; trivial
    obtain ⟨y, hyC, hy⟩ := h2
    have hyC' : (y : G) ∈ Subgroup.centralizer (VM : Set G) := hyC
    have hy' : ((y : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) = ((⟨m, hm⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) :=
      hy
    have hq : y⁻¹ * ⟨m, hm⟩ ∈ CFSG.pCore 2 ↥L := QuotientGroup.eq.mp hy'
    have hqVM : ((y⁻¹ * ⟨m, hm⟩ : ↥L) : G) ∈ Subgroup.normalizer (VM : Set G) :=
      hLVM (y⁻¹ * ⟨m, hm⟩).2
    refine Setup.mem_autOn_iff.mpr ⟨⟨_, hqVM⟩, ⟨_, hq, rfl⟩, ?_⟩
    ext v
    rw [Setup.coe_conjAct_apply, Setup.coe_conjAct_apply]
    have hw : (m : G) * v * (m : G)⁻¹ ∈ VM := (Subgroup.mem_normalizer_iff.mp m.2 v).mp v.2
    have hyw := Subgroup.mem_centralizer_iff.mp hyC' _ hw
    show (y : G)⁻¹ * m * v * ((y : G)⁻¹ * m)⁻¹ = m * v * (m : G)⁻¹
    calc (y : G)⁻¹ * m * v * ((y : G)⁻¹ * m)⁻¹ =
        (y : G)⁻¹ * ((m * v * (m : G)⁻¹) * y) := by group
      _ = (y : G)⁻¹ * (y * (m * v * (m : G)⁻¹)) := by rw [hyw]
      _ = m * v * (m : G)⁻¹ := by group

theorem mem_pCoreOf_of_commute (hA37 : Vol2Native.A37ForSQTKCat)
    (hA38 : Vol2Native.A38ForSQTKCat)
    [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))]
    (hL32 : IsPSL 3 2 1 ↥(autOn L (conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))))
    {k : G} (hk : k ∈ L ⊔ (T ⊓ Subgroup.normalizer (L : Set G)))
    (hc : ∀ b ∈ autOn L (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))),
      conjAct _ ⟨k, c.H_le_NVM hk⟩ * b = b * conjAct _ ⟨k, c.H_le_NVM hk⟩) :
    k ∈ pCoreOf 2 (L ⊔ (T ⊓ Subgroup.normalizer (L : Set G))) := by
  have hHVM := c.H_le_NVM
  have hHL := c.H_le_NL
  have hLVM := c.L_le_NVM
  have hT2 : IsPGroup 2 T := c.fsu.sylow.1
  have hcen := SBc11.center_eq_bot_of_list (Or.inl hL32)
  set VM := conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))
    with hVMdef
  set H := L ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) with hHdef
  set Lb := autOn L VM with hLbdef
  set K : Subgroup G := H ⊓ ((Subgroup.centralizer (Lb : Set (MulAut ↥VM))).comap
    (conjAct VM)).map (Subgroup.normalizer (VM : Set G)).subtype with hKdef
  have hmemK : ∀ g, ∀ hgH : g ∈ H, (∀ b ∈ Lb, conjAct VM ⟨g, hHVM hgH⟩ * b =
      b * conjAct VM ⟨g, hHVM hgH⟩) → g ∈ K := fun g hgH hgc =>
    ⟨hgH, ⟨g, hHVM hgH⟩, Subgroup.mem_centralizer_iff.mpr fun b hb => (hgc b hb).symm, rfl⟩
  have hKc : ∀ g ∈ K, ∃ hgH : g ∈ H, ∀ b ∈ Lb, conjAct VM ⟨g, hHVM hgH⟩ * b =
      b * conjAct VM ⟨g, hHVM hgH⟩ := by
    rintro g ⟨hgH, g', hg', rfl⟩
    exact ⟨hgH, fun b hb => (Subgroup.mem_centralizer_iff.mp hg' b hb).symm⟩
  have hnorm : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_of_conj fun h hh g hg => by
    obtain ⟨hgH, hgc⟩ := hKc g hg
    refine hmemK _ (H.mul_mem (H.mul_mem hh hgH) (H.inv_mem hh)) fun b hb => ?_
    set hb' := conjAct VM ⟨h, hHVM hh⟩ with hhb
    have e : conjAct VM ⟨h * g * h⁻¹, hHVM (H.mul_mem (H.mul_mem hh hgH) (H.inv_mem hh))⟩ =
        hb' * conjAct VM ⟨g, hHVM hgH⟩ * hb'⁻¹ := by
      rw [hhb, ← map_inv, ← map_mul, ← map_mul]
      rfl
    have hbn : hb'⁻¹ * b * hb' ∈ Lb :=
      (Subgroup.mem_normalizer_iff''.mp (H13.autOn_le_normalizer hLVM hHVM hHL
        (Setup.mem_autOn_iff.mpr ⟨⟨h, hHVM hh⟩, hh, rfl⟩)) b).mp hb
    have h1 := hgc _ hbn
    rw [e]
    calc hb' * conjAct VM ⟨g, hHVM hgH⟩ * hb'⁻¹ * b =
        hb' * (conjAct VM ⟨g, hHVM hgH⟩ * (hb'⁻¹ * b * hb')) * hb'⁻¹ := by group
      _ = hb' * ((hb'⁻¹ * b * hb') * conjAct VM ⟨g, hHVM hgH⟩) * hb'⁻¹ := by rw [h1]
      _ = b * (hb' * conjAct VM ⟨g, hHVM hgH⟩ * hb'⁻¹) := by group
  have hK2 : IsPGroup 2 ↥K := by
    rintro ⟨g, hg⟩
    obtain ⟨hgH, -⟩ := hKc g hg
    have hgH' : g ∈ ((L ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) : Subgroup G) : Set G) := hgH
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L _ inf_le_right] at hgH'
    obtain ⟨l, hl, n, hn, rfl⟩ := hgH'
    obtain ⟨a, ha⟩ := hT2 ⟨n, hn.1⟩
    have ha' : n ^ 2 ^ a = 1 := congrArg Subtype.val ha
    obtain ⟨l', hl', he⟩ := exists_pow_eq_mul hl hn.2 (2 ^ a)
    rw [ha', mul_one] at he
    have hl'K : l' ∈ K := he ▸ K.pow_mem hg (2 ^ a)
    obtain ⟨hl'H, hl'c⟩ := hKc l' hl'K
    have hmem : conjAct VM ⟨l', hHVM hl'H⟩ ∈ Lb :=
      Setup.mem_autOn_iff.mpr ⟨⟨l', hHVM hl'H⟩, hl', rfl⟩
    have hz : (⟨_, hmem⟩ : ↥Lb) ∈ Subgroup.center ↥Lb := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hl'c y y.2).symm
    rw [hcen, Subgroup.mem_bot] at hz
    have hl'1 : conjAct VM ⟨l', hHVM hl'H⟩ = 1 := congrArg Subtype.val hz
    have hl'C : l' ∈ Subgroup.centralizer (VM : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have h2 := congrArg (fun φ : MulAut ↥VM => ((φ ⟨v, hv⟩ : ↥VM) : G)) hl'1
      simp only [Setup.coe_conjAct_apply, MulAut.one_apply] at h2
      calc v * l' = l' * v * l'⁻¹ * l' := by rw [h2]
        _ = l' * v := by group
    obtain ⟨b, hb⟩ := c.exists_pow_of_centralizer hA37 hA38 hL32 hl' hl'C
    refine ⟨a + b, Subtype.ext ?_⟩
    show (l * n) ^ 2 ^ (a + b) = 1
    rw [pow_add, pow_mul, he, hb]
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hnorm hK2
    (hmemK k hk hc)

end Ctx

end CFSG.Quasithin.H13.T326
