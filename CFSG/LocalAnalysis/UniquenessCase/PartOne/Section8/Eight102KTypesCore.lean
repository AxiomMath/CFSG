module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KTypesDefs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KTypesMap
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.GroupTheory.ABGLocalTools.Constraint
import CFSG.GroupTheory.BaerSuzuki
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LieType.Chevalley.LangRootArithmetic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.RankThree.Asc83Table.Automizer
import CFSG.RankThree.PartTwo.Late.GammaZero
import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.RankThree.PartTwo.Sec13.Statements
import CFSG.RankThree.PartTwo.Sec18.Notation
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.RankThree.PartTwo.Sec21.Item229Diagram
import CFSG.RankThree.PartTwo.Sec21.Item23Tools
import CFSG.RankThree.PartTwo.Sec21.Membership
import CFSG.RankThree.PartTwo.Sec21.SylowThree
import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
import CFSG.RankThree.PartTwo.Sec4.StatementsGraphField
import CFSG.StronglyEmbedded.ParityCriterion
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem notationA8103_map_conj_iff {L A : Subgroup G} {g : G} (hg : g ∈ L)
    (hA : A ≤ L) {p n : ℕ} :
    F08.NotationA8103 L L p n (A.map (MulAut.conj g).toMonoidHom) ↔
      F08.NotationA8103 L L p n A := by
  have hmap : CFSG.RankThree.PartTwo.Sec21.U4Lines.mapL
      (MulAut.conj (⟨g, hg⟩ : L)) A = A.map (MulAut.conj g).toMonoidHom :=
    CFSG.RankThree.PartTwo.Sec21.U4Lines.mapL_conj (⟨g, hg⟩ : L) hA
  have hL : CFSG.RankThree.PartTwo.Sec21.U4Lines.mapL
      (MulAut.conj (⟨g, hg⟩ : L)) L = L := by
    rw [CFSG.RankThree.PartTwo.Sec21.U4Lines.mapL_conj (⟨g, hg⟩ : L) (le_refl L)]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)
  have h := notationA8103_mapL_iff (E := MulAut.conj (⟨g, hg⟩ : L)) (P := L) (A := A)
    hA (p := p) (n := n)
  rwa [hL, hmap] at h

theorem notationB8103_map_conj_iff {L B : Subgroup G} {g : G} (hg : g ∈ L)
    (hB : B ≤ L) {n : ℕ} :
    F08.NotationB8103 L L n (B.map (MulAut.conj g).toMonoidHom) ↔
      F08.NotationB8103 L L n B := by
  have hmap : CFSG.RankThree.PartTwo.Sec21.U4Lines.mapL
      (MulAut.conj (⟨g, hg⟩ : L)) B = B.map (MulAut.conj g).toMonoidHom :=
    CFSG.RankThree.PartTwo.Sec21.U4Lines.mapL_conj (⟨g, hg⟩ : L) hB
  have hL : CFSG.RankThree.PartTwo.Sec21.U4Lines.mapL
      (MulAut.conj (⟨g, hg⟩ : L)) L = L := by
    rw [CFSG.RankThree.PartTwo.Sec21.U4Lines.mapL_conj (⟨g, hg⟩ : L) (le_refl L)]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)
  have h := notationB8103_mapL_iff (E := MulAut.conj (⟨g, hg⟩ : L)) (P := L) (B := B)
    hB (n := n)
  rwa [hL, hmap] at h

private theorem card_bar2_derInf8_map_conj {L A : Subgroup G} {g : G} (hg : g ∈ L)
    (hA : A ≤ L) :
    Nat.card (Bar2 (F08.DerInf8 (L ⊓ centralizer
      (A.map (MulAut.conj g).toMonoidHom : Set G)))) =
      Nat.card (Bar2 (F08.DerInf8 (L ⊓ centralizer (A : Set G)))) := by
  have hmap : CFSG.RankThree.PartTwo.Sec21.U4Lines.mapL
      (MulAut.conj (⟨g, hg⟩ : L)) A = A.map (MulAut.conj g).toMonoidHom :=
    CFSG.RankThree.PartTwo.Sec21.U4Lines.mapL_conj (⟨g, hg⟩ : L) hA
  obtain ⟨e⟩ := nonempty_bar2_derInf8_mapL (E := MulAut.conj (⟨g, hg⟩ : L)) hA
  rw [hmap] at e
  exact (Nat.card_congr e.toEquiv).symm

private theorem notationA8103_iff_le_and {L S A : Subgroup G} {p n : ℕ} (hS : S ≤ L) :
    F08.NotationA8103 L S p n A ↔ A ≤ S ∧ F08.NotationA8103 L L p n A := by
  unfold F08.NotationA8103
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h2, h1, h2.trans hS, h3, h4⟩
  · rintro ⟨h2, h1, -, h3, h4⟩
    exact ⟨h1, h2, h3, h4⟩

omit [Finite G] in
private theorem notationB8103_iff_le_and {L S B : Subgroup G} {n : ℕ} (hS : S ≤ L) :
    F08.NotationB8103 L S n B ↔ B ≤ S ∧ F08.NotationB8103 L L n B := by
  unfold F08.NotationB8103
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, h1, h2.trans hS, h3⟩
  · rintro ⟨h2, h1, -, h3⟩
    exact ⟨h1, h2, h3⟩

private theorem exists_conj_map_le_of_card_eq_three {L S A : Subgroup G} (hS : S ≤ L)
    (hSp : IsPGroup 3 S) (hSidx : ¬ 3 ∣ S.relIndex L) (hA : A ≤ L)
    (hcard : Nat.card A = 3) :
    ∃ g ∈ L, A.map (MulAut.conj g).toMonoidHom ≤ S := by
  have hS'p : IsPGroup 3 (S.subgroupOf L) :=
    hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hS).symm
  have hS'idx : ¬ 3 ∣ (S.subgroupOf L).index := hSidx
  let S' : Sylow 3 ↥L := hS'p.toSylow hS'idx
  have hS'coe : (S' : Subgroup ↥L) = S.subgroupOf L := IsPGroup.toSylow_coe hS'p hS'idx
  have hA'card : Nat.card (A.subgroupOf L) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv, hcard]
  have hA'p : IsPGroup 3 (A.subgroupOf L) :=
    IsPGroup.of_card (n := 1) (by rw [hA'card, pow_one])
  obtain ⟨Q, hAQ⟩ := hA'p.exists_le_sylow
  have hpre : MulAction.IsPretransitive ↥L (Sylow 3 ↥L) :=
    @Sylow.isPretransitive_of_finite 3 ↥L _ Nat.fact_prime_three
      (Sylow.finite_of_finiteIndex S')
  obtain ⟨x, hx⟩ := hpre.exists_smul_eq Q S'
  refine ⟨(x : G), x.2, ?_⟩
  intro y hy
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
  have haQ : (⟨a, hA ha⟩ : ↥L) ∈ Q := hAQ (Subgroup.mem_subgroupOf.mpr ha)
  have hxQ : (MulAut.conj x (⟨a, hA ha⟩ : ↥L) : ↥L) ∈
      ((x • Q : Sylow 3 ↥L) : Set ↥L) := by
    rw [Sylow.coe_smul]
    exact Set.mem_smul_set.mpr ⟨⟨a, hA ha⟩, haQ, rfl⟩
  have hS'coe' : (S' : Set ↥L) = (S.subgroupOf L : Set ↥L) := by
    rw [← Sylow.coe_coe, hS'coe]
  rw [hx, hS'coe'] at hxQ
  change ((MulAut.conj x (⟨a, hA ha⟩ : ↥L) : ↥L) : G) ∈ S
  exact Subgroup.mem_subgroupOf.mp hxQ

theorem kTypesAt_of_reps {L A₀ B₀ : Subgroup G} {p n : ℕ}
    (hcl : ∀ ℓ : Subgroup G, ℓ ≤ L → Nat.card ℓ = 3 → ∃ g ∈ L,
      ℓ = A₀.map (MulAut.conj g).toMonoidHom ∨ ℓ = B₀.map (MulAut.conj g).toMonoidHom)
    (hA : F08.NotationA8103 L L p n A₀) (hB : F08.NotationB8103 L L n B₀)
    (hAd : p ∣ Nat.card (Bar2 (F08.DerInf8 (L ⊓ centralizer (A₀ : Set G)))))
    (hAB : ¬ F08.NotationB8103 L L n A₀) (hBA : ¬ F08.NotationA8103 L L p n B₀) :
    KTypesAt G L p n := by
  intro S hS hSp hSidx
  have hA₀L : A₀ ≤ L := hA.2.1
  have hB₀L : B₀ ≤ L := hB.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨g, hg, hle⟩ := exists_conj_map_le_of_card_eq_three hS hSp hSidx hA₀L hA.1
    exact ⟨A₀.map (MulAut.conj g).toMonoidHom,
      (notationA8103_iff_le_and hS).mpr
        ⟨hle, (notationA8103_map_conj_iff hg hA₀L).mpr hA⟩⟩
  · obtain ⟨g, hg, hle⟩ := exists_conj_map_le_of_card_eq_three hS hSp hSidx hB₀L hB.1
    exact ⟨B₀.map (MulAut.conj g).toMonoidHom,
      (notationB8103_iff_le_and hS).mpr
        ⟨hle, (notationB8103_map_conj_iff hg hB₀L).mpr hB⟩⟩
  · intro Y hY hYcard
    obtain ⟨g, hg, hYeq | hYeq⟩ := hcl Y (hY.trans hS) hYcard
    · subst hYeq
      exact Or.inl ((notationA8103_iff_le_and hS).mpr
        ⟨hY, (notationA8103_map_conj_iff hg hA₀L).mpr hA⟩)
    · subst hYeq
      exact Or.inr ((notationB8103_iff_le_and hS).mpr
        ⟨hY, (notationB8103_map_conj_iff hg hB₀L).mpr hB⟩)
  · intro A hA'
    have hAL : F08.NotationA8103 L L p n A := (notationA8103_iff_le_and hS).mp hA' |>.2
    obtain ⟨g, hg, hAeq | hAeq⟩ := hcl A (hA'.2.1.trans hS) hA'.1
    · rw [hAeq, card_bar2_derInf8_map_conj hg hA₀L]
      exact hAd
    · exfalso
      have hnot : F08.NotationA8103 L L p n B₀ :=
        (notationA8103_map_conj_iff hg hB₀L).mp (hAeq ▸ hAL)
      exact hBA hnot
  · intro B₁ B₂ hB₁ hB₂
    have key : ∀ B : Subgroup G, F08.NotationB8103 L S n B →
        ∃ g ∈ L, B = B₀.map (MulAut.conj g).toMonoidHom := by
      intro B hB'
      have hBL : F08.NotationB8103 L L n B := (notationB8103_iff_le_and hS).mp hB' |>.2
      obtain ⟨g, hg, hBeq | hBeq⟩ := hcl B (hB'.2.1.trans hS) hB'.1
      · exfalso
        have hnot : F08.NotationB8103 L L n A₀ :=
          (notationB8103_map_conj_iff hg hA₀L).mp (hBeq ▸ hBL)
        exact hAB hnot
      · exact ⟨g, hg, hBeq⟩
    obtain ⟨g₁, hg₁, hB₁eq⟩ := key B₁ hB₁
    obtain ⟨g₂, hg₂, hB₂eq⟩ := key B₂ hB₂
    refine ⟨g₂ * g₁⁻¹, L.mul_mem hg₂ (L.inv_mem hg₁), ?_⟩
    rw [hB₂eq, hB₁eq, Subgroup.map_map]
    congr 1
    ext y
    simp [MulAut.conj_apply, mul_assoc]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes
