module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KStrongEmbedded72Holds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyFive72
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclCard
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyFive

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

private theorem nlsz_exists_mul_ne {S : Type} [Group S] {n : ℕ} (hS : IsL2 S n ∨ IsSz S n) :
    ∃ a b : S, a * b ≠ b * a := by
  rcases hS with hS | hS
  · exact CFSG.ComponentClassification.HarrisLit.nonabelian_of_lieModel_psl2 hS
  · exact CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_twistedB2 hS

private theorem nlsz_card_ne_sixty {S : Type} [Group S] {n : ℕ} (hn : 3 ≤ n)
    (hS : IsL2 S n ∨ IsSz S n) : Nat.card S ≠ 60 := by
  intro h60
  rcases hS with hS | hS
  · have h8 : 2 ^ 3 ∣ Nat.card S := by
      rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two
        (CFSG.Blueprint.LieModel.statedClassicalModel hS (by decide))]
      exact (pow_dvd_pow 2 hn).mul_right _
    rw [h60] at h8
    norm_num at h8
  · exact CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hS
      (h60 ▸ by norm_num)

theorem not_hasL2SzSection_of_isSolvable {G : Type} [Group G] {N : Subgroup G}
    (hN : Group.IsSolvable ↥N) {n : ℕ} : ¬ HasL2SzSection n N := by
  rintro ⟨Y, hYN, Z, hZ, hS⟩
  have := hZ
  have : IsSimpleGroup (↥Y ⧸ Z) := isSimpleGroup_of_isL2_or_isSz hS
  have : Group.IsSolvable ↥Y :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hYN)
  obtain ⟨a, b, hab⟩ := nlsz_exists_mul_ne hS
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance a b)

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.PerfectCoreCover
  (exists_perfect_normal_map_eq_top) in
theorem not_hasL2SzSection_of_forall_isAlt_five {G : Type} [Group G] [Finite G] {N : Subgroup G}
    (hN : ∀ Y : Subgroup G, Y ≤ N → ⁅Y, Y⁆ = Y → ∀ (S : Type) [Group S],
      IsSimpleGroup S → ∀ f : ↥Y →* S, Function.Surjective f → IsAlt S 5) {n : ℕ} (hn : 3 ≤ n) :
    ¬ HasL2SzSection n N := by
  rintro ⟨Y, hYN, Z, hZ, hS⟩
  have := hZ
  have : IsSimpleGroup (↥Y ⧸ Z) := isSimpleGroup_of_isL2_or_isSz hS
  have : Group.IsPerfect (↥Y ⧸ Z) :=
    CFSG.RankThree.OddKernel.isPerfect_of_isSimpleGroup' (nlsz_exists_mul_ne hS)
  obtain ⟨D, -, hD, hDtop⟩ :=
    exists_perfect_normal_map_eq_top (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
  have hDY : D.map Y.subtype ≤ Y := Subgroup.map_subtype_le D
  have hperf : ⁅D.map Y.subtype, D.map Y.subtype⁆ = D.map Y.subtype := by
    rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hD]
  let f : ↥(D.map Y.subtype) →* ↥Y ⧸ Z := (QuotientGroup.mk' Z).comp (Subgroup.inclusion hDY)
  have hf : Function.Surjective f := by
    intro s
    have hs : s ∈ D.map (QuotientGroup.mk' Z) := by
      rw [hDtop]
      exact Subgroup.mem_top s
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hs
    exact ⟨⟨Y.subtype d, Subgroup.mem_map_of_mem _ hd⟩, rfl⟩
  have hA5 := hN _ (hDY.trans hYN) hperf (↥Y ⧸ Z) inferInstance f hf
  exact nlsz_card_ne_sixty hn hS (Om8Excl.card_isAlt_five hA5)

theorem k_19_25_noL2SzSection_of_normal :
    ∀ (Q : Type) [Group Q] [Finite Q] (p : ℕ) (Y : Subgroup Q), p.Prime → p ≠ 2 → Y.Normal →
      genFittingFStar Q ≤ Y → CFSG.pPrimeCore p Q = ⊥ →
      ((∃ m : ℕ, LieModel ↥Y .PSL 2 p m) ∨ (∃ m : ℕ, LieModel ↥Y .PSU 3 p m) ∨
        (p = 3 ∧ (F07.IsReeType ↥Y 1 ∨ IsSpor ↥Y .M11 ∨ IsL3 ↥Y 2)) ∨
        (p = 5 ∧ (F07.IsAutSz ↥Y 5 ∨ LieModel ↥Y .Tits 0 2 1 ∨ IsSpor ↥Y .McL ∨ IsAlt ↥Y 10)) ∨
        (p = 11 ∧ IsSpor ↥Y .J4)) →
      ∀ N : Subgroup Q, IsStronglyPEmbedded p N → ∀ n : ℕ, 3 ≤ n → ¬ HasL2SzSection n N := by
  intro Q _ _ p Y hp hp2 hYN hFY hO hY N hN n hn
  rcases kStrongEmbedded72_holds p hp hp2 Q hO Y hYN hFY hY N hN with hsolv | ⟨-, -, hA5⟩
  · exact not_hasL2SzSection_of_isSolvable hsolv
  · exact not_hasL2SzSection_of_forall_isAlt_five hA5 hn

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
