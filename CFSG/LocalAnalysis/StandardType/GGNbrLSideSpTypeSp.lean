module

public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitComm
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GCenterQuot
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSp
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2
import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Open.StatedAPI
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlockEquivOne)

private theorem typeSp_four_le_card {K : Type} [Field K] [Finite K]
    (hq : CFSG.IsQuasisimple ↥(commutator (StatedSp 1 K))) : 4 ≤ Nat.card K := by
  by_contra hlt
  have h2 : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
  have hcard : Nat.card K = 2 ∨ Nat.card K = 3 := by omega
  haveI : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) K) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable K hcard
  haveI : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) K) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin 2) K →* Matrix.GeneralLinearGroup (Fin 2) K))
      Matrix.SpecialLinearGroup.toGL_injective
  haveI : Group.IsSolvable (StatedSp 1 K) :=
    Group.isSolvable_of_surjective (f := (longBlockEquivOne K).toMonoidHom)
      (longBlockEquivOne K).surjective
  haveI : Group.IsSolvable ↥(commutator (StatedSp 1 K)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (commutator (StatedSp 1 K)).subtype) Subtype.val_injective
  haveI : Group.IsPerfect ↥(commutator (StatedSp 1 K)) := hq.1
  haveI : Nontrivial ↥(commutator (StatedSp 1 K)) :=
    CFSG.LocalCores.isQuasisimple_nontrivial hq
  exact Group.IsPerfect.not_isSolvable ↥(commutator (StatedSp 1 K)) inferInstance

private theorem typeSp_group {n s : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n)
    (hq : CFSG.IsQuasisimple ↥(commutator (StatedSp s K))) :
    (∃ (t : StatedLieTag) (m f : ℕ), ((t = .PSp ∧ m = s) ∨ (t = .PSL ∧ m = 2)) ∧
        CFSG.Blueprint.LieModel
          (↥(commutator (StatedSp s K)) ⧸
            Subgroup.center ↥(commutator (StatedSp s K))) t m 2 f) ∨
      Nat.card (↥(commutator (StatedSp s K)) ⧸
        Subgroup.center ↥(commutator (StatedSp s K))) ≤ 720 := by
  classical
  haveI := Fintype.ofFinite K
  rcases Nat.eq_zero_or_pos s with rfl | hspos
  · exfalso
    have hcard : Nat.card (StatedSp 0 K) = 1 := by
      rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp]
      simp
    haveI : Subsingleton (StatedSp 0 K) := (Nat.card_eq_one_iff_unique.mp hcard).1
    haveI : Subsingleton ↥(commutator (StatedSp 0 K)) := inferInstance
    haveI : Nontrivial ↥(commutator (StatedSp 0 K)) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hq
    obtain ⟨a, b, hab⟩ := exists_pair_ne ↥(commutator (StatedSp 0 K))
    exact hab (Subsingleton.elim a b)
  · by_cases h1 : s = 1
    · subst h1
      have h4 : 4 ≤ Nat.card K := typeSp_four_le_card hq
      have h4' : 4 ≤ Fintype.card K := by rwa [Nat.card_eq_fintype_card] at h4
      obtain ⟨t4, -, ht4⟩ := Finset.exists_subset_card_eq h4'
      haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) :=
        (CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_SL (F := K) (m := 2) le_rfl
          (Or.inr ⟨t4, ht4⟩)).1
      have hperfSp : Group.IsPerfect (StatedSp 1 K) :=
        Group.IsPerfect.ofSurjective (f := (longBlockEquivOne K).toMonoidHom)
          (longBlockEquivOne K).surjective
      have htop : commutator (StatedSp 1 K) = ⊤ := hperfSp.commutator_eq_top
      have eTop : ↥(commutator (StatedSp 1 K)) ≃* StatedSp 1 K :=
        (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
      obtain ⟨eZc⟩ :=
        CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_of_mulEquiv eTop
      obtain ⟨eZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sl 2
        (X := StatedSp 1 K) (longBlockEquivOne K).symm
      have eComb : ↥(commutator (StatedSp 1 K)) ⧸
          Subgroup.center ↥(commutator (StatedSp 1 K)) ≃* StatedProj (StatedSL 2 K) :=
        eZc.trans eZ
      have hadm : StatedLieAdmissible .PSL 2 2 n := by
        refine ⟨Nat.prime_two, hn, le_rfl, ?_, ?_⟩
        · intro h
          obtain ⟨-, h2⟩ := Prod.mk.inj h
          omega
        · intro h
          obtain ⟨-, h3⟩ := Prod.mk.inj h
          omega
      refine Or.inl ⟨.PSL, 2, n, Or.inr ⟨rfl, rfl⟩, ?_⟩
      exact Or.inl ⟨by decide, ⟨hadm, K, inferInstance, inferInstance, hK, ⟨eComb⟩⟩⟩
    · have hs2 : 2 ≤ s := by omega
      by_cases hspecial : s = 2 ∧ Nat.card K = 2
      · obtain ⟨rfl, hK2⟩ := hspecial
        right
        have h1 : Nat.card (↥(commutator (StatedSp 2 K)) ⧸
            Subgroup.center ↥(commutator (StatedSp 2 K))) ≤
            Nat.card ↥(commutator (StatedSp 2 K)) :=
          Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
        have h2 : Nat.card ↥(commutator (StatedSp 2 K)) ≤ Nat.card (StatedSp 2 K) :=
          Nat.card_le_card_of_injective (Subgroup.subtype _) Subtype.val_injective
        have h3 : Nat.card (StatedSp 2 K) = 720 := by
          rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two, hK2]
          norm_num
        omega
      · have hne : ¬ (s = 2 ∧ Nat.card K = 2) := hspecial
        have hne' : (s, Fintype.card K) ≠ (2, 2) := by
          intro h
          obtain ⟨h1, h2⟩ := Prod.mk.inj h
          exact hne ⟨h1, by rw [Nat.card_eq_fintype_card]; exact h2⟩
        have htop : commutator (StatedSp s K) = ⊤ :=
          (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFactorFacts_holds
            K s hs2 hne').perfect
        have eTop : ↥(commutator (StatedSp s K)) ≃* StatedSp s K :=
          (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
        obtain ⟨eZc⟩ :=
          CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_of_mulEquiv eTop
        have hchar : CharP K 2 := by
          haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          exact charP_of_card_eq_prime_pow (f := n) (by
            rw [← Nat.card_eq_fintype_card]; exact hK)
        obtain ⟨eZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sp
          (K := K) (X := StatedSp s K) hs2 hne hchar (MulEquiv.refl _)
        have eComb : ↥(commutator (StatedSp s K)) ⧸
            Subgroup.center ↥(commutator (StatedSp s K)) ≃* StatedProj (StatedSp s K) :=
          eZc.trans eZ
        have hadm : StatedLieAdmissible .PSp s 2 n := by
          refine ⟨Nat.prime_two, hn, hs2, ?_⟩
          intro h
          obtain ⟨h1, h2⟩ := Prod.mk.inj h
          exact hne ⟨h1, hK.trans h2⟩
        refine Or.inl ⟨.PSp, s, n, Or.inl ⟨rfl, rfl⟩, ?_⟩
        exact Or.inl ⟨by decide, ⟨hadm, K, inferInstance, inferInstance, hK, ⟨eComb⟩⟩⟩

theorem ggNbrLSideSp_typeSp {n : ℕ} {K : Type} [Field K] [Finite K]
    {G : Type} [Group G] {A : Subgroup G} {s : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) (φ : ↥A ≃* ↥(StatedSp s K))
    (hq : CFSG.IsQuasisimple ↥⁅A, A⁆) :
    (∃ (t : StatedLieTag) (m f : ℕ), ((t = .PSp ∧ m = s) ∨ (t = .PSL ∧ m = 2)) ∧
        CFSG.Blueprint.LieModel (↥⁅A, A⁆ ⧸ Subgroup.center ↥⁅A, A⁆) t m 2 f) ∨
      Nat.card (↥⁅A, A⁆ ⧸ Subgroup.center ↥⁅A, A⁆) ≤ 720 := by
  have hqB : CFSG.IsQuasisimple ↥(commutator (StatedSp s K)) :=
    (GGNbrLSideKit.quasisimple_commutator_iff φ).1 hq
  rcases typeSp_group hK hn hqB with ⟨t, m, f, htm, hmodel⟩ | hcard
  · exact Or.inl ⟨t, m, f, htm, GGNbrLSideKit.lieModel_quot_commutator_of_mulEquiv φ hmodel⟩
  · exact Or.inr (by
      rw [GGNbrLSideKit.card_quot_commutator_of_mulEquiv φ]
      exact hcard)

end CFSG.StandardType
