module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KFacts
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
import CFSG.Adapters.LieModelSimple
import CFSG.Quasithin.Background.A1bTransvection
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd rhoL)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem three_not_mem_sig_of_hyp8102 {D : Data G} (hSg : SigmaStd D) {L P : Subgroup G}
    {p n : ℕ} (hH : F08.Hyp8102 D L P p n) : 3 ∉ D.sig := by
  intro h3
  exact hH.2.2.1
    (CFSG.LocalAnalysis.UniquenessCase.UC6S846.sp_of_mem_sig hSg
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC hH.1) h3)

theorem prime_of_hyp8102 {D : Data G} (hSg : SigmaStd D) {L P : Subgroup G} {p n : ℕ}
    (hH : F08.Hyp8102 D L P p n) : p.Prime ∧ p ≠ 2 ∧ p ≠ 3 := by
  have hp := hH.2.2.2.1
  have hpp := D.sig_prime p hp
  refine ⟨hpp.1, hpp.2, ?_⟩
  intro h3
  exact three_not_mem_sig_of_hyp8102 hSg hH (by simpa [h3] using hp)

theorem isSimpleGroup_bar2_of_hyp8102 {D : Data G} {L P : Subgroup G} {p n : ℕ}
    (hH : F08.Hyp8102 D L P p n) : IsSimpleGroup (Bar2 L) := by
  rcases hH.2.1 with ⟨hU5, -⟩ | hU4
  · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU5
  · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU4

theorem center_bar2_eq_bot_of_hyp8102 {D : Data G} {L P : Subgroup G} {p n : ℕ}
    (hH : F08.Hyp8102 D L P p n) : center (Bar2 L) = ⊥ := by
  haveI hsimple := isSimpleGroup_bar2_of_hyp8102 hH
  haveI hperf : Group.IsPerfect (Bar2 L) := ⟨hH.1.2.2.1⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (Bar2 L)) with h | h
  · exact h
  · exact absurd (Subgroup.center_eq_top_iff.mp h)
      (Group.IsPerfect.not_isMulCommutative (Bar2 L))

theorem isU45_of_hyp8102 {D : Data G} {L P : Subgroup G} {p n : ℕ}
    (hH : F08.Hyp8102 D L P p n) (hn : Even n) : IsU45 (Bar2 L) n := by
  rcases hH.2.1 with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, hn⟩

theorem pRank_le_three_of_evenRank (D : Data G) (he : evenRank G = 3) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) : Open.pRank r D.M ≤ 3 := by
  have h := CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank r hr hr2 D.M
    D.maxLocal.1
  omega

theorem mem_centralizer_of_rhoL_fix {L S : Subgroup G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hS : IsPGroup r S) (hSN : S ≤ normalizer (L : Set G)) {x : G} (hxS : x ∈ S) (hxL : x ∈ L)
    (hfix : ∀ (s : G) (hs : s ∈ S),
      rhoL L ⟨s, hSN hs⟩ (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L) =
        (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L)) :
    x ∈ centralizer (S : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  haveI : Fact r.Prime := ⟨hr⟩
  have hmem : s * x * s⁻¹ * x⁻¹ ∈ pCoreOf 2 L :=
    (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_fix_iff L ⟨s, hSN hs⟩
      ⟨x, hxL⟩).mp (hfix s hs)
  have hmemS : s * x * s⁻¹ * x⁻¹ ∈ S :=
    S.mul_mem (S.mul_mem (S.mul_mem hs hxS) (S.inv_mem hs)) (S.inv_mem hxS)
  have hone : s * x * s⁻¹ * x⁻¹ = 1 :=
    CFSG.Quasithin.A1b.eq_one_of_mem_pGroups (p := r) (q := 2) hr2 hS
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.isPGroup_pCoreOf L) hmemS hmem
  exact commutatorElement_eq_one_iff_mul_comm.mp hone

theorem stronglyEmbedded_of_two_le_pRank_centralizer {D : Data G} (hSg : SigmaStd D)
    (hns : ¬ Group.IsSolvable ↥D.M) (h76 : F07.R76Sig D) (h614 : UC6.R6_14 D) {p : ℕ}
    (hp : p ∈ D.sig) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrs : r ∉ D.sig) {R E : Subgroup G}
    (hR : IsSylowOf r R D.M) (hER : E ≤ R ⊓ centralizer (R : Set G)) (hE : IsElemAbelian r E)
    (hEc : Nat.card E = r ^ 2) (hrank : 2 ≤ Open.pRank p (D.M ⊓ centralizer (E : Set G))) :
    IsStronglyPEmbedded r D.M := by
  have hp' := D.sig_prime p hp
  have hsp : IsStronglyPEmbedded p D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.sp_of_mem_sig hSg hns hp
  have hEM : E ≤ D.M := hER.trans (inf_le_left.trans hR.le)
  have h0 : 0 < Open.pRank p (D.M ⊓ centralizer (E : Set G)) := by omega
  have hX : ∀ X : Subgroup G, X ≤ E → Nat.card X = r →
      1 < Open.pRank p (D.M ⊓ normalizer (X : Set G)) := by
    intro X hXE _
    have hcX : centralizer (E : Set G) ≤ normalizer (X : Set G) :=
      (Subgroup.centralizer_le (show (X : Set G) ⊆ (E : Set G) from hXE)).trans
        (Subgroup.centralizer_le_normalizer (X : Set G))
    have hmono := CFSG.SectionRank.pRank_mono hp'.1.one_lt (inf_le_inf_left D.M hcX)
    omega
  exact h614 (CFSG.LocalAnalysis.UniquenessCase.UC6S846.sig_subset_sig1 hSg hns) r hr hr2 hrs R
    hR E hER hE hEc (h76 p hp hp'.2 hsp r hr E hEM hE hEc h0 hX)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
