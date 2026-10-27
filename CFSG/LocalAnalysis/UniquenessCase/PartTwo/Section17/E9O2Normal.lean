module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Blueprint.Catalog
public import CFSG.Open.LocalVocabulary
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center
import CFSG.GroupTheory.ABGLocalTools.PStabilityQDickson
import CFSG.ClassicalInvolution.SubnormalClosure
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Sylow
import CFSG.GroupTheory.PRankQuotientLift
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
import CFSG.Monster.Code.Weights
import CFSG.Quasithin.Background.B1More13A
import CFSG.Quasithin.Background.B1More13Defs
import CFSG.Quasithin.Background.B1MoreEleven
import CFSG.Quasithin.Background.B5Basic
import CFSG.Quasithin.Background.B5CompA
import CFSG.Quasithin.Background.B5CompB
import CFSG.Quasithin.Background.B6
import CFSG.Quasithin.Background.B6Example
import CFSG.Quasithin.Background.B6Sections
import CFSG.Quasithin.Background.C2Basic
import CFSG.Quasithin.Background.InternalSecAutOn
import CFSG.Quasithin.Background.InternalSecB4
import CFSG.Quasithin.Background.SmithC27Star

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

@[expose] def E9O2Normal (M : Subgroup G) : Prop :=
  ∃ B : Subgroup G, B ≤ M ∧ IsElemAbelian 3 B ∧ Nat.card B = 3 ^ 2 ∧
    ((B ⊔ pCoreOf 2 M).subgroupOf M).Normal

private abbrev E9 : Type := Multiplicative (ZMod 3) × Multiplicative (ZMod 3)

private theorem E9_card : Nat.card E9 = 9 := by
  rw [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd), Nat.card_zmod]

private theorem e9_pow_three : ∀ x : E9, x ^ 3 = 1 := by decide

theorem center_eq_bot_of_lieModel_psl2 {A : Type} [Group A] [Finite A] {l f : ℕ}
    (h : CFSG.Blueprint.LieModel A .PSL 2 l f) : Subgroup.center A = ⊥ := by
  rcases h with ⟨-, hscm⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, h0', -⟩
  · rw [CFSG.Open.StatedClassicalModel] at hscm
    obtain ⟨-, K, hK, hKf, hcard, ⟨e⟩⟩ := hscm
    refine CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv
      (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm) ?_
    exact CFSG.GorensteinWalter.psl2_center_eq_bot K
  · simp at h0
  · simp at h0
  · simp at h0

private theorem center_prod_e9 {A : Type} [Group A] {F : Type} [Group F] [Finite F]
    (e : F ≃* (A × E9)) (hcentA : Subgroup.center A = ⊥) :
    Nat.card ↥(Subgroup.center F) = 9 ∧ (∀ x : ↥(Subgroup.center F), x ^ 3 = 1) := by
  have hmap : (Subgroup.center F).map e.toMonoidHom = Subgroup.center (A × E9) :=
    Subgroup.map_center_eq e
  have hcenter : Subgroup.center (A × E9) = (⊥ : Subgroup A).prod (⊤ : Subgroup E9) := by
    rw [Subgroup.center_prod, hcentA, Subgroup.center_eq_top]
  have hcard : Nat.card ↥(Subgroup.center F) = 9 := by
    rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hmap, hcenter,
      Nat.card_congr (Subgroup.prodEquiv (⊥ : Subgroup A) (⊤ : Subgroup E9)).toEquiv,
      Nat.card_prod, Subgroup.card_bot, Subgroup.card_top, E9_card]
  refine ⟨hcard, fun x => ?_⟩
  have hx : e x.1 ∈ Subgroup.center (A × E9) := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem e.toMonoidHom x.2
  rw [hcenter, Subgroup.mem_prod] at hx
  obtain ⟨hx1, -⟩ := hx
  rw [Subgroup.mem_bot] at hx1
  have hx3 : e x.1 ^ 3 = 1 := by
    refine Prod.ext ?_ ?_
    · rw [Prod.pow_fst, hx1, one_pow, Prod.fst_one]
    · rw [Prod.pow_snd, e9_pow_three, Prod.snd_one]
  have h1 : e (x.1 ^ 3) = 1 := by rw [map_pow, hx3]
  have h2 : x.1 ^ 3 = 1 := by
    have := congrArg e.symm h1
    simpa using this
  exact Subtype.ext h2

theorem e9O2Normal_of_mulEquiv {M : Subgroup G} {A : Type} [Group A] {l f : ℕ}
    (hLieA : LieModel A .PSL 2 l f)
    (eF : ↥(genFittingFStar (Bar2 M)) ≃*
      A × (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) : E9O2Normal M := by
  have hfinA : Finite A := by
    haveI : Finite (A × E9) :=
      Finite.of_injective (fun x : A × E9 => eF.symm x) eF.symm.injective
    exact Finite.of_injective (fun a : A => (a, (1 : E9))) (fun a b h => by simpa using h)
  haveI := hfinA
  set F : Subgroup (Bar2 M) := CFSG.Open.genFittingFStar (Bar2 M) with hFdef
  have hFnormal : F.Normal := CFSG.ClassicalInvolution.genFittingFStar_normal (Bar2 M)
  have hcentA : Subgroup.center A = ⊥ := center_eq_bot_of_lieModel_psl2 hLieA
  have hZF := center_prod_e9 eF hcentA
  set K : Subgroup (Bar2 M) := (Subgroup.center ↥F).map F.subtype with hKdef
  have hKcard : Nat.card ↥K = 9 := by
    rw [hKdef, Subgroup.card_map_of_injective F.subtype_injective, hZF.1]
  have hKexp : ∀ x : ↥K, x ^ 3 = 1 := by
    intro x
    refine Subtype.ext ?_
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp x.2
    have h1 : (y : ↥F) ^ 3 = 1 := by
      have := hZF.2 ⟨y, hy⟩
      simpa using this
    show ((x : ↥K) : Bar2 M) ^ 3 = 1
    rw [← hxy, ← map_pow, h1, map_one]
  have hKnormal : K.Normal := by
    have h := CFSG.BenderSuzuki.normal_subgroupOf_map_of_characteristic_of_normal F K ⊤ le_top
      (Subgroup.Normal.subgroupOf hFnormal ⊤) (Subgroup.center ↥F) Subgroup.centerCharacteristic
      hKdef.symm le_top
    exact Subgroup.Normal.mk fun n hn g =>
      (Subgroup.normal_subgroupOf_iff le_top).mp h n g hn trivial
  haveI : (CFSG.pCore 2 ↥M).Normal := CFSG.pCore_normal
  have hK3 : IsPGroup 3 ↥K := by
    refine IsPGroup.iff_card.mpr ⟨2, ?_⟩
    rw [hKcard]
    norm_num
  have hcop : Nat.Coprime 3 (Nat.card (CFSG.pCore 2 ↥M)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hk]
    exact ((Nat.coprime_primes Nat.prime_three Nat.prime_two).mpr (by norm_num)).pow_right k
  obtain ⟨Dsub, hDp, ⟨eD⟩, hDsup⟩ :=
    CFSG.GroupTheory.exists_isPGroup_of_coprime_kernel (CFSG.pCore 2 ↥M) Nat.prime_three
      hcop hK3
  have hDcard : Nat.card ↥Dsub = 9 := by
    rw [Nat.card_congr eD.toEquiv, hKcard]
  have hDexp : ∀ x ∈ Dsub, x ^ 3 = 1 := by
    intro x hx
    have h1 : (eD ⟨x, hx⟩) ^ 3 = 1 := hKexp (eD ⟨x, hx⟩)
    have h2 : eD ((⟨x, hx⟩ : ↥Dsub) ^ 3) = 1 := by rw [map_pow, h1]
    have h3 : (⟨x, hx⟩ : ↥Dsub) ^ 3 = 1 := by
      have := congrArg eD.symm h2
      simpa using this
    simpa using congrArg Subtype.val h3
  have hcardB : Nat.card ↥(Dsub.map M.subtype) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective M.subtype_injective, hDcard]
    norm_num
  refine ⟨Dsub.map M.subtype, Subgroup.map_subtype_le Dsub,
    ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hcardB, ?_⟩, hcardB, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    simpa using congrArg M.subtype (hDexp y hy)
  · have hsup : Dsub.map M.subtype ⊔ CFSG.Open.pCoreOf 2 M =
        (Dsub ⊔ CFSG.pCore 2 ↥M).map M.subtype := by
      rw [CFSG.Open.pCoreOf, Subgroup.map_sup]
    have h1 : (Dsub ⊔ CFSG.pCore 2 ↥M).Normal := by
      rw [hDsup]
      exact Subgroup.Normal.comap hKnormal (QuotientGroup.mk' (CFSG.pCore 2 ↥M))
    rw [hsup]
    have heq : ((Dsub ⊔ CFSG.pCore 2 ↥M).map M.subtype).subgroupOf M =
        (Dsub ⊔ CFSG.pCore 2 ↥M) := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hxy⟩
        have h2 : y = x := Subtype.ext hxy
        rwa [h2] at hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [heq]
    exact h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
