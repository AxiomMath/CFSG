module

import CFSG.RankThree.PartTwo.Sec15.Sylow1523KStruct
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.Models.PGLSimple
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Late.Transitivity
public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec15.Item1523Proof

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] noncomputable def Step1523KSolv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ Y ∈ scriptY0Star A (lB A), ¬ MeetsY4 A (lB A) L Y →
      ((∃ _ : Fact (Nat.Prime 7), Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃*
          CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))) ∨
        Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7))) →
      ∀ d : G, d ∈ A → d ≠ 1 → IsThreeCentralIn L d → Subgroup.zpowers d ∉ omegaA A →
        deltaZero A (lB A) Y = pPrimeCoreOf 3 (deltaZero A (lB A) Y) ⊔
          deltaZero A (lB A) (Y ⊓ Subgroup.centralizer ({d} : Set G)) →
        Y = (Y ⊓ k1523 A d) ⊔ CFSG.Open.pCoreOf 2 Y →
        Group.IsSolvable ↥(k1523 A d ⊓ pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)))

namespace Sylow1523K

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_k1523_inf (A : Subgroup G) (d : G) :
    k1523 A d ≤ Subgroup.normalizer
      ((k1523 A d ⊓ pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) : Subgroup G) : Set G) :=
  Late.le_normalizer_inf Subgroup.le_normalizer
    ((k1523_le_centralizer A d).trans (le_normalizer_pPrimeCoreOf 3 _))

theorem not_three_dvd_card_k1523_inf (A : Subgroup G) (d : G) :
    ¬ 3 ∣ Nat.card ↥(k1523 A d ⊓ pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h3
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
    (h3.trans (Subgroup.card_dvd_of_le inf_le_right))

theorem facts_of_l37_or_a7 {T : Type*} [Group T]
    (hT : (∃ _ : Fact (Nat.Prime 7), Nonempty (T ≃*
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))) ∨
      Nonempty (T ≃* alternatingGroup (Fin 7))) :
    IsSimpleGroup T ∧ 3 ∣ Nat.card T ∧ 7 ∣ Nat.card T := by
  rcases hT with ⟨h7, ⟨e⟩⟩ | he
  · have : IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) :=
      CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (GaloisField 7 1) (by norm_num)
        (Or.inl (by norm_num)) (Or.inl (by norm_num))
    have hcard := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 7 1)
    have hF : Nat.card (GaloisField 7 1) = 7 := by
      rw [GaloisField.card 7 1 one_ne_zero, pow_one]
    rw [hF] at hcard
    norm_num at hcard
    rw [Nat.card_congr e.toEquiv]
    exact ⟨e.isSimpleGroup, by omega, by omega⟩
  · obtain ⟨e⟩ := he
    have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    have hA7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    rw [Nat.card_congr e.toEquiv, hA7]
    exact ⟨e.isSimpleGroup, by norm_num, by norm_num⟩

theorem surjective_inf_quot {Y K : Subgroup G} (hYK : Y = (Y ⊓ K) ⊔ CFSG.Open.pCoreOf 2 Y) :
    Function.Surjective ((QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp
      (Subgroup.inclusion (inf_le_left : Y ⊓ K ≤ Y))) := by
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y) q
  have h2 : ((Y ⊓ K) ⊔ CFSG.Open.pCoreOf 2 Y).subgroupOf Y =
      (Y ⊓ K).subgroupOf Y ⊔ CFSG.pCore 2 ↥Y := by
    rw [CFSG.Open.pCoreOf, Subgroup.subgroupOf_sup inf_le_left (Subgroup.map_subtype_le _)]
    congr 1
    rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective Y.subtype_injective]
  have hy : y ∈ (Y ⊓ K).subgroupOf Y ⊔ CFSG.pCore 2 ↥Y := by
    rw [← h2, Subgroup.mem_subgroupOf, ← hYK]
    exact y.2
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
  refine ⟨⟨(a : G), ha⟩, ?_⟩
  have ha' : Subgroup.inclusion (inf_le_left : Y ⊓ K ≤ Y) ⟨(a : G), ha⟩ = a := Subtype.ext rfl
  rw [MonoidHom.comp_apply, ha', QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq, inv_mul_cancel_left]
  exact hb

theorem isQuasisimple_of_isTripleCover {Q : Type*} [Group Q] [Group.IsPerfect Q] {S : Type*}
    [Group S] [IsSimpleGroup S] (hT : Sec4.IsTripleCover Q S) : CFSG.IsQuasisimple Q := by
  obtain ⟨-, ⟨e⟩⟩ := hT
  have hs : IsSimpleGroup (Q ⧸ Subgroup.center Q) := e.isSimpleGroup
  refine ⟨inferInstance, hs, ?_⟩
  by_contra hcomm
  push Not at hcomm
  have : Group.IsPerfect (Q ⧸ Subgroup.center Q) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have : IsMulCommutative (Q ⧸ Subgroup.center Q) := ⟨⟨fun a b => hcomm a b⟩⟩
  have : Nontrivial (Q ⧸ Subgroup.center Q) := hs.toNontrivial
  exact Group.IsPerfect.not_isMulCommutative (Q ⧸ Subgroup.center Q) inferInstance

end Sylow1523K

open Sylow1523K

end CFSG.RankThree.PartTwo.Sec15
