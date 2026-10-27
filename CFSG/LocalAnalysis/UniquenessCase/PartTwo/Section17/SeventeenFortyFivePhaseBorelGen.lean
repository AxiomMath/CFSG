module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFivePhaseProps
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFivePhaseBorelInner
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFivePhaseBorelLin
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BorelTorusAbelianHolds
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerLie
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerD4
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Chev2GlueHolds
import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
import CFSG.LieType.Catalog.Realization
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup
open scoped commutatorElement

theorem not_dvd_thirty_one_two_pow_add_one (f : ℕ) : ¬ 31 ∣ 2 ^ f + 1 := by
  have h16 : 2 ^ (f % 5) ≤ 16 := by
    have h4 : f % 5 ≤ 4 := by
      have := Nat.mod_lt f (by norm_num : 0 < 5)
      omega
    calc 2 ^ (f % 5) ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) h4
      _ = 16 := by norm_num
  have hlt : 2 ^ (f % 5) < 31 := by omega
  have hlt' : 2 ^ (f % 5) + 1 < 31 := by omega
  have h1 : 2 ^ f = (2 ^ 5) ^ (f / 5) * 2 ^ (f % 5) := by
    have hf : f = 5 * (f / 5) + f % 5 := by
      have := Nat.div_add_mod f 5
      omega
    nth_rewrite 1 [hf]
    rw [pow_add, pow_mul]
  have hmod : 2 ^ f % 31 = 2 ^ (f % 5) := by
    have h2 : (2 ^ 5) ^ (f / 5) % 31 = 1 := by
      rw [Nat.pow_mod, show (2 : ℕ) ^ 5 % 31 = 1 by norm_num, one_pow,
        Nat.mod_eq_of_lt (by norm_num : 1 < 31)]
    rw [h1, Nat.mul_mod, h2, one_mul, Nat.mod_mod, Nat.mod_eq_of_lt hlt]
  intro h
  have h0 : (2 ^ f + 1) % 31 = 2 ^ (f % 5) + 1 := by
    rw [Nat.add_mod, hmod, Nat.mod_eq_of_lt (by norm_num : 1 < 31)]
    exact Nat.mod_eq_of_lt hlt'
  rw [Nat.mod_eq_zero_of_dvd h] at h0
  have hpos : 0 < 2 ^ (f % 5) := by positivity
  omega

theorem exists_abelian_of_pslModel {X : Type} [Group X] [Finite X] {L A₁ A₂ B S : Subgroup X}
    [L.Normal] (hcen : centralizer (L : Set X) = ⊥) {n f : ℕ}
    (hE : CFSG.Open.StatedClassicalModel ↥L .PSL n 2 f ∧ 31 ∣ Nat.gcd n (2 ^ f - 1))
    (hAodd : Odd (Nat.card ↥(A₁ ⊔ A₂))) (hAB : ⁅A₁ ⊔ A₂, B⁆ = A₁ ⊔ A₂)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S L) (hAS : A₁ ⊔ A₂ ≤ normalizer (S : Set X)) :
    ∃ C : Subgroup X, IsMulCommutative C ∧ A₁ ≤ C ∧ L ≤ S ⊔ (L ⊓ normalizer (C : Set X)) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.AGLEmbedding.ParabAutIrr.exists_equiv_projectiveSL hE.1
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by rwa [← Nat.card_eq_fintype_card])
  have hn2 : 2 ≤ n := by
    have hadm := hE.1.1
    simp only [CFSG.Open.StatedLieAdmissible] at hadm
    exact hadm.2.2.1
  have hn3 : 3 ≤ n := by
    have h31 : 31 ∣ n := hE.2.trans (Nat.gcd_dvd_left n (2 ^ f - 1))
    have := Nat.le_of_dvd (by omega : 0 < n) h31
    omega
  obtain ⟨C, hC, hAC, hLC⟩ := exists_abelian_of_projectiveSL hcen hn3 e hAodd hAB hS hAS
  exact ⟨C, hC, le_sup_left.trans hAC, hLC⟩

section PGoodOut


theorem pGoodOut_thirty_one_of_lieModel {L : Type} [Group L] [Finite L]
    {t : CFSG.Open.StatedLieTag} {n f : ℕ} (hadm : CFSG.Open.StatedLieAdmissible t n 2 f)
    (hmod : CFSG.Blueprint.LieModel L t n 2 f)
    (hE : ¬ (CFSG.Open.StatedClassicalModel L .PSL n 2 f ∧ 31 ∣ Nat.gcd n (2 ^ f - 1))) :
    CFSG.AGLEmbedding.TwoGenInner.PGoodOut 31 L := by
  refine CFSG.AGLEmbedding.TwoGenInner.pGoodOut_of_lieModel (p := 31) (by norm_num) (by norm_num)
    hadm hmod ?_ ?_ CFSG.AGLEmbedding.TwoGenInner.d4PGood
  · intro hcl hdvd
    exact hE ⟨hcl, hdvd⟩
  · intro _ hdvd
    exact not_dvd_thirty_one_two_pow_add_one f (hdvd.trans (Nat.gcd_dvd_right n (2 ^ f + 1)))

end PGoodOut


theorem exists_abelian_of_not_pslModel {X : Type} [Group X] [Finite X] {L : Subgroup X}
    {A₁ A₂ B S : Subgroup X} [L.Normal] {t : CFSG.Open.StatedLieTag} {n f : ℕ}
    (hcen : centralizer (L : Set X) = ⊥) (hmod : CFSG.Blueprint.LieModel ↥L t n 2 f)
    (hE : ¬ (CFSG.Open.StatedClassicalModel ↥L .PSL n 2 f ∧ 31 ∣ Nat.gcd n (2 ^ f - 1)))
    (hAsup : IsPGroup 31 ↥(A₁ ⊔ A₂)) (hAodd : Odd (Nat.card ↥(A₁ ⊔ A₂)))
    (hcomm : ⁅A₁ ⊔ A₂, B⁆ = A₁ ⊔ A₂) (hS : CFSG.ABGLocalTools.IsSylowOf 2 S L)
    (hAS : A₁ ⊔ A₂ ≤ normalizer (S : Set X)) (hnt : Nontrivial ↥L)
    (hsimple : IsSimpleGroup ↥L) (hA₁ : Nat.card A₁ = 31) :
    ∃ C : Subgroup X, IsMulCommutative C ∧ A₁ ≤ C ∧ L ≤ S ⊔ (L ⊓ normalizer (C : Set X)) := by
  have hAL : A₁ ⊔ A₂ ≤ L :=
    le_of_commutator_eq_of_pGoodOut hcen
      (pGoodOut_thirty_one_of_lieModel hmod.admissible hmod hE) hAsup hcomm
  have hA₁L : A₁ ≤ L := le_sup_left.trans hAL
  have : IsSimpleGroup ↥L := hsimple
  have hLnab : ∃ a b : ↥L, a * b ≠ b * a := by
    by_contra h
    have hnc : ∀ a b : ↥L, a * b = b * a := by
      intro a b
      by_contra hab
      exact h ⟨a, b, hab⟩
    have hle : L ≤ Subgroup.centralizer (L : Set X) := fun x hx =>
      Subgroup.mem_centralizer_iff.mpr fun y hy => congrArg Subtype.val (hnc ⟨y, hy⟩ ⟨x, hx⟩)
    rw [hcen] at hle
    have hbot : L = ⊥ := le_bot_iff.mp hle
    have : Subsingleton ↥L := by rw [hbot]; infer_instance
    exact (not_subsingleton_iff_nontrivial.mpr hnt) inferInstance
  obtain ⟨hq, hZ⟩ := CFSG.Walter.isQuasisimple_of_isSimpleGroup' (Q := ↥L) hLnab
  by_cases ht : t = .Tits
  · rw [ht] at hmod
    exact absurd (hA₁ ▸ Subgroup.card_dvd_of_le hA₁L)
      (CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.not_dvd_card_of_lieModel_tits
        hmod (r := 31) (by norm_num) (by norm_num) (by norm_num))
  · obtain ⟨B₀, N₀, hBN⟩ := CFSG.ASVolI.ChIJK.lieModel_has_splitBNPair Nat.prime_two ht hmod
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hsyl : CFSG.QuasithinUnique.IsSylowTwoOf (S.subgroupOf L) ⊤ := by
      obtain ⟨-, hS2, hSidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hS
      refine ⟨le_top, hS2.comap_subtype, ?_⟩
      rwa [show ((S.subgroupOf L).subgroupOf ⊤).index = (S.subgroupOf L).index from
        Subgroup.relIndex_top_right _]
    have hab : IsMulCommutative (TauCeti.Subgroup.normalizerQuotient (S.subgroupOf L)) :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.k_BorelTorusAbelian_holds
        ↥L t n f hmod.admissible (CFSG.Blueprint.LieModel.quotient_center hZ hmod)
        ⟨hq.2.1, hq.2.2⟩ (S.subgroupOf L) hsyl
    obtain ⟨C, hC, hAC, hLC⟩ :=
      exists_abelian_le_sup_normalizer_of_splitBN (A := A₁ ⊔ A₂) hBN hS hab hAL hAodd hAS
    exact ⟨C, hC, le_sup_left.trans hAC, hLC⟩

theorem k45CharTwoBorelGen_holds : K45CharTwoBorelGen := by
  intro X _ _ L A₁ A₂ B S d hLn hcent hLd hd hdt hA₁ hA₂ hA₁₂ hc hB hBA₁ hBA₂ hcomm hS hAS
  have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  have : L.Normal := hLn
  have hA₁p : IsPGroup 31 A₁ := IsPGroup.of_card (n := 1) (by rw [hA₁, pow_one])
  have hA₂p : IsPGroup 31 A₂ := IsPGroup.of_card (n := 1) (by rw [hA₂, pow_one])
  have hnorm : A₁ ≤ Subgroup.normalizer (A₂ : Set X) :=
    hc.trans (Subgroup.centralizer_le_normalizer _)
  have hAsup : IsPGroup 31 ↥(A₁ ⊔ A₂) := IsPGroup.to_sup_of_normal_right' hA₁p hA₂p hnorm
  have hAodd : Odd (Nat.card ↥(A₁ ⊔ A₂)) := by
    obtain ⟨m, hm⟩ := hAsup.exists_card_eq
    rw [hm]
    exact Odd.pow (by norm_num : Odd 31)
  obtain ⟨e⟩ := hLd
  obtain ⟨t, n, f, hmod⟩ := CFSG.StandardType.ChevTwo.exists_lieModel_two_of_valid d hd e
  obtain ⟨hLfin, hnt, hsimple⟩ :=
    CFSG.LieType.Catalog.lieModel_finite_simple ↥L t n 2 f hmod
  have : Finite ↥L := hLfin
  by_cases hE : CFSG.Open.StatedClassicalModel ↥L .PSL n 2 f ∧ 31 ∣ Nat.gcd n (2 ^ f - 1)
  · exact exists_abelian_of_pslModel hcent hE hAodd hcomm hS hAS
  · exact exists_abelian_of_not_pslModel hcent hmod hE hAsup hAodd hcomm hS hAS hnt hsimple hA₁

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
