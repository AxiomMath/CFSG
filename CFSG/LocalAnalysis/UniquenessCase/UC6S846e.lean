module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846a
public import CFSG.LocalAnalysis.UniquenessCase.UCKU3
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6S846

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

structure SigmaStd (D : Data G) : Prop where
  nonempty : D.sig.Nonempty
  three_le : ∀ p ∈ D.sig, 3 ≤ Open.pRank p D.M
  sig1_sp : ∀ p ∈ D.sig1, IsStronglyPEmbedded p D.M
  solvable_of : (D.sig2 ∪ D.sig3).Nonempty → Group.IsSolvable ↥D.M
  four_mem : ∀ r : ℕ, r.Prime → r ≠ 2 → 4 ≤ Open.pRank r D.M → r ∈ D.sig

theorem not_solvable_of_mem_calC {M L : Subgroup G} (hL : L ∈ calC M) : ¬ Group.IsSolvable ↥M := by
  intro hs
  have hLM : L ≤ M := hL.1.le
  haveI : Group.IsSolvable ↥L :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLM)
      (Subgroup.inclusion_injective hLM)
  haveI : Group.IsSolvable (Bar2 L) := inferInstance
  obtain ⟨hperf, hsimple⟩ := hL.2.2
  haveI : Nontrivial (Bar2 L ⧸ center (Bar2 L)) := hsimple.toNontrivial
  haveI : Nontrivial (Bar2 L) := (QuotientGroup.mk'_surjective (center (Bar2 L))).nontrivial
  exact (IsSolvable.commutator_lt_top_of_nontrivial (Bar2 L)).ne hperf

theorem sig_subset_sig1 {D : Data G} (hSg : SigmaStd D) (hns : ¬ Group.IsSolvable ↥D.M) :
    D.sig ⊆ D.sig1 := by
  intro p hp
  have hp' : p ∈ D.sig1 ∪ D.sig2 ∪ D.sig3 := by rw [← D.sig_sub]; exact hp
  rcases hp' with (h1 | h2) | h3
  · exact h1
  · exact absurd (hSg.solvable_of ⟨p, Or.inl h2⟩) hns
  · exact absurd (hSg.solvable_of ⟨p, Or.inr h3⟩) hns

theorem sp_of_mem_sig {D : Data G} (hSg : SigmaStd D) (hns : ¬ Group.IsSolvable ↥D.M) {p : ℕ}
    (hp : p ∈ D.sig) : IsStronglyPEmbedded p D.M :=
  hSg.sig1_sp p (sig_subset_sig1 hSg hns hp)

@[expose] def CalCRankTwice (M : Subgroup G) : Prop :=
  ∀ L ∈ calC M, ¬ M ≤ normalizer (L : Set G) → ∀ q : ℕ, q.Prime → q ≠ 2 →
    ¬ q ∣ Nat.card (center (Bar2 L)) → ∀ E : Subgroup G, E ≤ L → IsElemAbelian q E →
      ∀ a : ℕ, Nat.card E = q ^ a → 2 * a ≤ Open.pRank q M

theorem exists_elemAbelian_sq_of_isSU3 (hSyl : UCK.U3Syl) {L : Subgroup G} {n : ℕ}
    (hX : IsSU3 (Bar2 L) n) {q : ℕ} (hq : q.Prime) (hq3 : 3 < q) (hqn : q ∣ 2 ^ n + 1) :
    ∃ E : Subgroup G, E ≤ L ∧ IsElemAbelian q E ∧ Nat.card E = q ^ 2 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hq2 : q ≠ 2 := by rintro rfl; omega
  obtain ⟨S⟩ : Nonempty (Sylow q (Bar2 L)) := inferInstance
  obtain ⟨Eb, hEbS, hEbel, hEbcard⟩ :=
    (hSyl (Bar2 L) n hX q hq hq3 hqn (S : Subgroup (Bar2 L)) S.isPGroup' S.not_dvd_index).1
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hker : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup
  obtain ⟨Q, hQp, hQmap, hQdisj⟩ :=
    exists_lift_pGroup π (QuotientGroup.mk'_surjective _) hker hq hq2 Eb (hEbel.isPGroup)
  refine ⟨Q.map L.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · exact (isElemAbelian_of_disjoint_ker π Q hQdisj (by rw [hQmap]; exact hEbel)).map _
  · rw [Subgroup.card_map_of_injective L.subtype_injective,
      ← card_map_of_disjoint_ker π Q hQdisj, hQmap, hEbcard]

theorem le_pRank' {p : ℕ} (hp : p.Prime) {H E : Subgroup G} (hEH : E ≤ H) (hel : IsElemAbelian p E)
    {k : ℕ} (hcard : Nat.card E = p ^ k) : k ≤ Open.pRank p H :=
  le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove p hp H) ⟨E, hEH, hel, hcard⟩

end CFSG.LocalAnalysis.UniquenessCase.UC6S846
