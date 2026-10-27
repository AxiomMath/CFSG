module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
public import CFSG.Milestones.ASVolI.I2
import CFSG.LocalAnalysis.UniquenessCase.UC22P20c
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.GH74.KGroups.L3EpsOuterLin
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.OddKernel.CompleteRankComparison
public import CFSG.RankThree.PartOne.KF.ClsPSL
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.KF.SymCtxMatrix
public import CFSG.RankThree.PartOne.KF.ToralQuot
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.S11c.Sec66PSL
public import CFSG.RankThree.PartOne.S11c.Sec66Sp
public import CFSG.RankThree.PartOne.S11c.SuFiveD
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.ASVolI.ChIJK
open CFSG.Blueprint (LieModel)

theorem uc22p20l_prod_sup_prod {A C : Type} [Group A] [Group C] (H₁ H₂ : Subgroup A)
    (K₁ K₂ : Subgroup C) : H₁.prod K₁ ⊔ H₂.prod K₂ = (H₁ ⊔ H₂).prod (K₁ ⊔ K₂) := by
  refine le_antisymm (sup_le (prod_mono le_sup_left le_sup_left)
    (prod_mono le_sup_right le_sup_right)) (prod_le_iff.2 ⟨?_, ?_⟩)
  · rw [Subgroup.map_sup]
    exact sup_le (le_sup_of_le_left (by rintro _ ⟨a, ha, rfl⟩; exact ⟨ha, K₁.one_mem⟩))
      (le_sup_of_le_right (by rintro _ ⟨a, ha, rfl⟩; exact ⟨ha, K₂.one_mem⟩))
  · rw [Subgroup.map_sup]
    exact sup_le (le_sup_of_le_left (by rintro _ ⟨c, hc, rfl⟩; exact ⟨H₁.one_mem, hc⟩))
      (le_sup_of_le_right (by rintro _ ⟨c, hc, rfl⟩; exact ⟨H₂.one_mem, hc⟩))

theorem uc22p20l_prod_splitBN {A C : Type} [Group A] [Group C] {B₁ N₁ : Subgroup A} {B₂ N₂ : Subgroup C}
    (h₁ : IsSplitBNPair 2 B₁ N₁) (h₂ : IsSplitBNPair 2 B₂ N₂) :
    IsSplitBNPair 2 (B₁.prod B₂) (N₁.prod N₂) := by
  have hinf : B₁.prod B₂ ⊓ N₁.prod N₂ = (B₁ ⊓ N₁).prod (B₂ ⊓ N₂) := by
    ext ⟨a, c⟩
    simp only [mem_inf, mem_prod]
    tauto
  obtain ⟨S₁, hS₁1, hS₁2, hS₁3, hS₁4⟩ := h₁.coxeter
  obtain ⟨S₂, hS₂1, hS₂2, hS₂3, hS₂4⟩ := h₂.coxeter
  obtain ⟨U₁, hU₁B, hU₁n, hU₁p, hU₁i, hU₁N, hU₁H, hsat₁⟩ := h₁.split
  obtain ⟨U₂, hU₂B, hU₂n, hU₂p, hU₂i, hU₂N, hU₂H, hsat₂⟩ := h₂.split
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [uc22p20l_prod_sup_prod, h₁.gen, h₂.gen]
    ext x
    simp [mem_prod]
  · rw [hinf]
    refine (normal_subgroupOf_iff (prod_mono inf_le_right inf_le_right)).2 ?_
    rintro ⟨h₁', h₂'⟩ ⟨k₁, k₂⟩ hh hk
    obtain ⟨hh₁, hh₂⟩ := mem_prod.1 hh
    obtain ⟨hk₁, hk₂⟩ := mem_prod.1 hk
    exact mem_prod.2 ⟨(normal_subgroupOf_iff inf_le_right).1 h₁.normal_inter h₁' k₁ hh₁ hk₁,
      (normal_subgroupOf_iff inf_le_right).1 h₂.normal_inter h₂' k₂ hh₂ hk₂⟩
  · refine ⟨(MonoidHom.inl A C) '' S₁ ∪ (MonoidHom.inr A C) '' S₂, ?_, ?_, ?_, ?_⟩
    · rintro s (⟨s', hs', rfl⟩ | ⟨s', hs', rfl⟩)
      · obtain ⟨hN, hB, h2⟩ := hS₁1 s' hs'
        exact ⟨mem_prod.2 ⟨hN, N₂.one_mem⟩, fun h => hB (mem_prod.1 h).1,
          mem_prod.2 ⟨by simpa using h2, by simp⟩⟩
      · obtain ⟨hN, hB, h2⟩ := hS₂1 s' hs'
        exact ⟨mem_prod.2 ⟨N₁.one_mem, hN⟩, fun h => hB (mem_prod.1 h).2,
          mem_prod.2 ⟨by simp, by simpa using h2⟩⟩
    · have hgen : (closure S₁).map (MonoidHom.inl A C) ⊔ (closure S₂).map (MonoidHom.inr A C) =
          (closure S₁).prod (closure S₂) := by
        refine le_antisymm (sup_le ?_ ?_) (prod_le_iff.2 ⟨le_sup_left, le_sup_right⟩)
        · rintro _ ⟨a, ha, rfl⟩
          exact ⟨ha, (closure S₂).one_mem⟩
        · rintro _ ⟨c, hc, rfl⟩
          exact ⟨(closure S₁).one_mem, hc⟩
      rw [Subgroup.closure_union, ← MonoidHom.map_closure, ← MonoidHom.map_closure, hgen, hinf,
        uc22p20l_prod_sup_prod, hS₁2, hS₂2]
    · rintro s (⟨s', hs', rfl⟩ | ⟨s', hs', rfl⟩) ⟨w₁, w₂⟩ hw ⟨b₁, b₂⟩ hb
      · obtain ⟨hw₁, -⟩ := mem_prod.1 hw
        obtain ⟨hb₁, hb₂⟩ := mem_prod.1 hb
        obtain ⟨c₁, hc₁, c₂, hc₂, h | h⟩ := hS₁3 s' hs' w₁ hw₁ b₁ hb₁
        · refine ⟨(c₁, b₂), mem_prod.2 ⟨hc₁, hb₂⟩, (c₂, 1), mem_prod.2 ⟨hc₂, B₂.one_mem⟩,
            Or.inl ?_⟩
          simp [h]
        · refine ⟨(c₁, b₂), mem_prod.2 ⟨hc₁, hb₂⟩, (c₂, 1), mem_prod.2 ⟨hc₂, B₂.one_mem⟩,
            Or.inr ?_⟩
          simp [h]
      · obtain ⟨-, hw₂⟩ := mem_prod.1 hw
        obtain ⟨hb₁, hb₂⟩ := mem_prod.1 hb
        obtain ⟨c₁, hc₁, c₂, hc₂, h | h⟩ := hS₂3 s' hs' w₂ hw₂ b₂ hb₂
        · refine ⟨(b₁, c₁), mem_prod.2 ⟨hb₁, hc₁⟩, (1, c₂), mem_prod.2 ⟨B₁.one_mem, hc₂⟩,
            Or.inl ?_⟩
          simp [h]
        · refine ⟨(b₁, c₁), mem_prod.2 ⟨hb₁, hc₁⟩, (1, c₂), mem_prod.2 ⟨B₁.one_mem, hc₂⟩,
            Or.inr ?_⟩
          simp [h]
    · rintro s (⟨s', hs', rfl⟩ | ⟨s', hs', rfl⟩)
      · obtain ⟨b, hb, hsb⟩ := hS₁4 s' hs'
        exact ⟨(b, 1), mem_prod.2 ⟨hb, B₂.one_mem⟩, fun h => hsb (by simpa using (mem_prod.1 h).1)⟩
      · obtain ⟨b, hb, hsb⟩ := hS₂4 s' hs'
        exact ⟨(1, b), mem_prod.2 ⟨B₁.one_mem, hb⟩, fun h => hsb (by simpa using (mem_prod.1 h).2)⟩
  · refine ⟨U₁.prod U₂, prod_mono hU₁B hU₂B, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine (normal_subgroupOf_iff (prod_mono hU₁B hU₂B)).2 ?_
      rintro ⟨u₁, u₂⟩ ⟨b₁, b₂⟩ hu hb
      obtain ⟨hu₁, hu₂⟩ := mem_prod.1 hu
      obtain ⟨hb₁, hb₂⟩ := mem_prod.1 hb
      exact mem_prod.2 ⟨(normal_subgroupOf_iff hU₁B).1 hU₁n u₁ b₁ hu₁ hb₁,
        (normal_subgroupOf_iff hU₂B).1 hU₂n u₂ b₂ hu₂ hb₂⟩
    · rintro ⟨⟨a, c⟩, ha⟩
      obtain ⟨ha₁, ha₂⟩ := mem_prod.1 ha
      obtain ⟨n₁, hn₁⟩ := hU₁p ⟨a, ha₁⟩
      obtain ⟨n₂, hn₂⟩ := hU₂p ⟨c, ha₂⟩
      have h₁' : a ^ 2 ^ n₁ = 1 := by simpa using congrArg Subtype.val hn₁
      have h₂' : c ^ 2 ^ n₂ = 1 := by simpa using congrArg Subtype.val hn₂
      refine ⟨n₁ + n₂, Subtype.ext ?_⟩
      have hpow : ∀ n : ℕ, ((a, c) : A × C) ^ n = (a ^ n, c ^ n) := fun n => rfl
      change ((a, c) : A × C) ^ 2 ^ (n₁ + n₂) = 1
      rw [hpow, pow_add, pow_mul, pow_mul', h₁', h₂', one_pow, one_pow]
      rfl
    · rw [Subgroup.index_prod]
      exact fun h => ((Nat.Prime.dvd_mul Nat.prime_two).1 h).elim hU₁i hU₂i
    · rw [eq_bot_iff]
      rintro ⟨a, c⟩ hx
      obtain ⟨⟨haU, hcU⟩, haN, hcN⟩ :=
        And.intro (mem_prod.1 (mem_inf.1 hx).1) (mem_prod.1 (mem_inf.1 hx).2)
      have h1 : a ∈ U₁ ⊓ N₁ := mem_inf.2 ⟨haU, haN⟩
      have h2 : c ∈ U₂ ⊓ N₂ := mem_inf.2 ⟨hcU, hcN⟩
      rw [hU₁N, mem_bot] at h1
      rw [hU₂N, mem_bot] at h2
      rw [mem_bot]
      simp [h1, h2]
    · rw [hinf, uc22p20l_prod_sup_prod, hU₁H, hU₂H]
    · ext ⟨a, c⟩
      constructor
      · intro h
        have h' := burnsideI2BN_mem_iInf_conjugate.1 h
        have ha : a ∈ ⨅ n ∈ N₁, CFSG.conjugate B₁ n := by
          rw [burnsideI2BN_mem_iInf_conjugate]
          intro n hn
          exact (mem_prod.1 (h' (n, 1) (mem_prod.2 ⟨hn, N₂.one_mem⟩))).1
        have hc : c ∈ ⨅ n ∈ N₂, CFSG.conjugate B₂ n := by
          rw [burnsideI2BN_mem_iInf_conjugate]
          intro n hn
          exact (mem_prod.1 (h' (1, n) (mem_prod.2 ⟨N₁.one_mem, hn⟩))).2
        rw [hsat₁] at ha
        rw [hsat₂] at hc
        rw [hinf]
        exact mem_prod.2 ⟨ha, hc⟩
      · intro h
        rw [hinf] at h
        obtain ⟨ha, hc⟩ := mem_prod.1 h
        rw [← hsat₁, burnsideI2BN_mem_iInf_conjugate] at ha
        rw [← hsat₂, burnsideI2BN_mem_iInf_conjugate] at hc
        rw [burnsideI2BN_mem_iInf_conjugate]
        rintro ⟨n₁, n₂⟩ hn
        obtain ⟨hn₁, hn₂⟩ := mem_prod.1 hn
        exact mem_prod.2 ⟨ha n₁ hn₁, hc n₂ hn₂⟩

theorem uc22p20l_not_two_dvd_card_center {X Y : Type} [Group X] [Group Y] [Finite Y]
    (hX : CFSG.pCore 2 X = ⊥) (f : Y →* X) (hf : Function.Injective f)
    (hc : ∀ z ∈ Subgroup.center Y, f z ∈ Subgroup.center X) :
    ¬ 2 ∣ Nat.card (Subgroup.center Y) := by
  intro h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hz2 : (z : Y) ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    simpa using congrArg Subtype.val this
  have hfz : f z ^ 2 = 1 := by rw [← map_pow, hz2, map_one]
  have hnorm : (Subgroup.zpowers (f z)).Normal :=
    Subgroup.normal_of_le_center (by rw [Subgroup.zpowers_le]; exact hc _ z.2)
  have hp : IsPGroup 2 (Subgroup.zpowers (f z)) := by
    rintro ⟨_, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, pow_one, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp [hfz]
  have hle : Subgroup.zpowers (f z) ≤ CFSG.pCore 2 X := le_sSup ⟨hnorm, hp⟩
  rw [hX] at hle
  have h1 : f z = 1 := Subgroup.mem_bot.1 (hle (Subgroup.mem_zpowers _))
  have h3 : z = 1 := Subtype.ext (hf (by rw [h1]; simp))
  rw [h3, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem uc22p20l_exists_hom_central {X : Type} [Group X] {K₁ K₂ : Subgroup X} (hsup : K₁ ⊔ K₂ = ⊤)
    (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) :
    ∃ φ : ↥K₁ × ↥K₂ →* X, Function.Surjective φ ∧ φ.ker ≤ Subgroup.center (↥K₁ × ↥K₂) := by
  have hc : ∀ (a : ↥K₁) (b : ↥K₂), Commute (K₁.subtype a) (K₂.subtype b) :=
    fun a b => hcomm a a.2 b b.2
  refine ⟨MonoidHom.noncommCoprod K₁.subtype K₂.subtype hc, ?_, ?_⟩
  · rw [← MonoidHom.range_eq_top, MonoidHom.noncommCoprod_range, Subgroup.range_subtype,
      Subgroup.range_subtype, hsup]
  · rintro ⟨a, b⟩ hab
    rw [MonoidHom.mem_ker, MonoidHom.noncommCoprod_apply] at hab
    have hab' : (a : X) * (b : X) = 1 := hab
    rw [Subgroup.mem_center_iff]
    rintro ⟨a', b'⟩
    have haK : (a : X) ∈ K₂ := by
      rw [eq_inv_of_mul_eq_one_left hab']
      exact K₂.inv_mem b.2
    have hbK : (b : X) ∈ K₁ := by
      rw [eq_inv_of_mul_eq_one_right hab']
      exact K₁.inv_mem a.2
    exact Prod.ext (Subtype.ext (hcomm a' a'.2 a haK)) (Subtype.ext (hcomm b hbK b' b'.2).symm)

section Shapes


variable {G : Type} [Group G] [Finite G]

theorem uc22p20l_splitBN_of_cover {X : Type} [Group X] [Finite X]
    (hodd : ¬ 2 ∣ Nat.card (Subgroup.center X)) {n : ℕ} (h : IsSL3 X n ∨ IsSU3 X n) :
    ∃ B N : Subgroup X, IsSplitBNPair 2 B N := by
  have h' : ∃ B N : Subgroup (X ⧸ Subgroup.center X), IsSplitBNPair 2 B N := by
    rcases h with h | h <;> exact lieModel_has_splitBNPair Nat.prime_two (by decide) h.2
  refine (splitBNPair_iff_of_central_primeToP_surjection Nat.prime_two
    (QuotientGroup.mk' (Subgroup.center X)) (QuotientGroup.mk'_surjective _) ?_ ?_).2 h'
  · rw [QuotientGroup.ker_mk']
  · rwa [QuotientGroup.ker_mk']

theorem uc22p20l_splitBN_of_szL2Product {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : IsSzL2Product X n) : ∃ B N : Subgroup X, IsSplitBNPair 2 B N := by
  obtain ⟨A, C, _, _, ⟨e⟩, hA, hC⟩ := h
  haveI : Finite (A × C) := Finite.of_equiv X e.toEquiv
  haveI : Finite A := Finite.of_surjective (Prod.fst : A × C → A) Prod.fst_surjective
  haveI : Finite C := Finite.of_surjective (Prod.snd : A × C → C) Prod.snd_surjective
  have hsz : ∀ {Y : Type} [Group Y] [Finite Y], (IsSz Y n ∨ IsL2 Y n) →
      ∃ B N : Subgroup Y, IsSplitBNPair 2 B N := fun h =>
    h.elim (fun h => lieModel_has_splitBNPair Nat.prime_two (by decide) h)
      (fun h => lieModel_has_splitBNPair Nat.prime_two (by decide) h)
  obtain ⟨B₁, N₁, h₁⟩ := hsz hA
  obtain ⟨B₂, N₂, h₂⟩ := hsz hC
  exact burnsideI2BN_exists_of_mulEquiv e.symm ⟨_, _, uc22p20l_prod_splitBN h₁ h₂⟩

theorem uc22p20l_splitBN_of_centralSquare {X : Type} [Group X] [Finite X]
    (hX : CFSG.pCore 2 X = ⊥) (h : IsSU3CentralSquare X) :
    ∃ B N : Subgroup X, IsSplitBNPair 2 B N := by
  obtain ⟨K₁, K₂, hsup, hcomm, h₁, h₂, -⟩ := h
  have hcen : ∀ {K K' : Subgroup X}, K ⊔ K' = ⊤ → (∀ a ∈ K, ∀ b ∈ K', a * b = b * a) →
      ¬ 2 ∣ Nat.card (Subgroup.center K) := by
    intro K K' hsup hcomm
    refine uc22p20l_not_two_dvd_card_center hX K.subtype K.subtype_injective fun z hz => ?_
    rw [Subgroup.mem_center_iff]
    intro x
    have hle : K ⊔ K' ≤ Subgroup.centralizer {((z : K) : X)} := by
      refine sup_le (fun k hk => ?_) (fun b hb => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro m hm
        rw [Set.mem_singleton_iff] at hm
        rw [hm]
        exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨k, hk⟩)).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro m hm
        rw [Set.mem_singleton_iff] at hm
        rw [hm]
        exact hcomm _ z.2 b hb
    have hx : x ∈ Subgroup.centralizer {((z : K) : X)} :=
      hle (by rw [hsup]; exact Subgroup.mem_top x)
    exact (Subgroup.mem_centralizer_iff.1 hx _ (Set.mem_singleton _)).symm
  obtain ⟨B₁, N₁, hBN₁⟩ := uc22p20l_splitBN_of_cover (hcen hsup hcomm) (Or.inr h₁)
  obtain ⟨B₂, N₂, hBN₂⟩ := uc22p20l_splitBN_of_cover
    (hcen (by rwa [sup_comm]) fun a ha b hb => (hcomm b hb a ha).symm) (Or.inr h₂)
  obtain ⟨φ, hφ, hker⟩ := uc22p20l_exists_hom_central hsup hcomm
  exact ⟨_, _, burnsideI2BN_map (uc22p20l_prod_splitBN hBN₁ hBN₂) φ hφ hker⟩

theorem uc22p20l_splitBN_of_shape (D : Data G) (h20_7 : S20_7 D) (h1930 : H1930 D) {L : Subgroup G}
    (hL : L ∈ calL D.T D.M) : ∃ B N : Subgroup (Bar2 L), IsSplitBNPair 2 B N := by
  have hX : CFSG.pCore 2 (Bar2 L) = ⊥ := uc22p20c_pCore_quotient_pCore
  have hodd : ¬ 2 ∣ Nat.card (Subgroup.center (Bar2 L)) :=
    uc22p20l_not_two_dvd_card_center hX (MonoidHom.id _) Function.injective_id fun _ hz => hz
  have key : ∀ {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m n : ℕ}, t ≠ .Tits →
      LieModel (Bar2 L) t m 2 n → ∃ B N : Subgroup (Bar2 L), IsSplitBNPair 2 B N :=
    fun ht h => lieModel_has_splitBNPair Nat.prime_two ht h
  rcases h20_7 h1930 L hL with
    ⟨n, -, h | h | h | h | h | h | h | h | h | h | h | h | h | h⟩ | h | h | h | h | h | ⟨n, -, h⟩ | h
  · exact key (by decide) h
  · exact key (by decide) h
  · exact key (by decide) h
  · exact key (by decide) h
  · exact key (by decide) h
  · exact key (by decide) h
  · exact key (by decide) h
  · exact key (by decide) h
  · exact key (by decide) h
  · exact key (by decide) h
  · exact uc22p20l_splitBN_of_cover hodd (Or.inl h)
  · exact uc22p20l_splitBN_of_cover hodd (Or.inr h)
  · exact key (by decide) h
  · exact key (by decide) h
  · exact key (by decide) h
  · exact key (by decide) h
  · exact key (by decide) h
  · exact key (by decide) h
  · exact key (by decide) h
  · exact uc22p20l_splitBN_of_szL2Product h
  · exact uc22p20l_splitBN_of_centralSquare hX h

end Shapes

end CFSG.LocalAnalysis.UniquenessCase.UC22
