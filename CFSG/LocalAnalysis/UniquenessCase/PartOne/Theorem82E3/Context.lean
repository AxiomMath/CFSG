module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22R82Four

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.Yardstones.Mf4cdcdf2e013 (Hyp81 TheoremCAt Theorem82At)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G]

structure Std82E3 (D : Data G) : Prop where
  rank : CFSG.Open.evenRank G = 3
  kProper : CFSG.Open.IsKProper G
  sig_nonempty : D.sig.Nonempty
  three_le : ∀ p ∈ D.sig, 3 ≤ CFSG.Open.pRank p D.M
  sig1_sp : ∀ p ∈ D.sig1, IsStronglyPEmbedded p D.M
  solvable_of : (D.sig2 ∪ D.sig3).Nonempty → Group.IsSolvable ↥D.M
  three_mem_sig : 3 ∈ CFSG.Open.rankThreeSigmaA G → 3 ∈ D.sig
  u2 : ∀ p ∈ D.sig, ∀ H : Subgroup G, CFSG.Open.IsTwoLocal H →
    2 ≤ CFSG.Open.pRank p (H ⊓ D.M) → H ≤ D.M
  theoremC : TheoremCAt D.M
  r614 : D.sig ⊆ D.sig1 → ∀ r : ℕ, r.Prime → r ≠ 2 → r ∉ D.sig →
    ∀ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf r R D.M →
      ∀ E : Subgroup G, E ≤ R ⊓ Subgroup.centralizer (R : Set G) → CFSG.Open.IsElemAbelian r E →
        Nat.card E = r ^ 2 → CFSG.Open.rankThreeGamma 1 r E ≤ D.M → IsStronglyPEmbedded r D.M
  r76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M →
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 D.M p

structure Ctx82E3 (D : Data G) extends Std82E3 D where
  L : Subgroup G
  hyp81 : Hyp81 D.M L
  not_strong : ¬ IsStronglyPEmbedded 3 D.M

namespace Ctx82E3

variable {D : Data G}

theorem L_ne_bot (c : Ctx82E3 D) : c.L ≠ ⊥ := by
  intro hbot
  have h3 : 3 ≤ CFSG.Open.pRank 3 c.L := c.hyp81.2.2.2.1
  have h0 : CFSG.Open.pRank 3 c.L = 0 := by
    apply le_antisymm ?_ (Nat.zero_le _)
    apply CFSG.SectionRank.pRank_le (p := 3) (H := c.L) (k := 0) (by norm_num)
    intro E hE _
    have hEbot : E = ⊥ := by simpa [hbot] using hE
    rw [hEbot]
    simp
  omega

theorem not_isSolvable (c : Ctx82E3 D) : ¬ Group.IsSolvable D.M := by
  intro hM
  haveI : Group.IsSolvable ↥D.M := hM
  haveI : Nontrivial ↥c.L := (Subgroup.nontrivial_iff_ne_bot c.L).mpr (L_ne_bot c)
  haveI : Group.IsSolvable ↥c.L :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion c.hyp81.1)
      (Subgroup.inclusion_injective c.hyp81.1)
  have hcomm : commutator ↥c.L = ⊤ := by
    apply Subgroup.map_injective c.L.subtype_injective
    rw [Subgroup.map_subtype_commutator, c.hyp81.2.2.1, Subgroup.map_top, c.L.range_subtype]
  have hlt : commutator ↥c.L < ⊤ :=
    Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥c.L)
  rw [hcomm] at hlt
  exact (lt_irrefl (⊤ : Subgroup ↥c.L)) hlt

theorem sigma_subset_sigmaOne (c : Ctx82E3 D) : D.sig ⊆ D.sig1 := by
  intro p hp
  have hp' : p ∈ D.sig1 ∪ D.sig2 ∪ D.sig3 := by rw [← D.sig_sub]; exact hp
  rcases hp' with (h1 | h2) | h3
  · exact h1
  · exact absurd (c.solvable_of ⟨p, Or.inl h2⟩) (not_isSolvable c)
  · exact absurd (c.solvable_of ⟨p, Or.inr h3⟩) (not_isSolvable c)

theorem isStronglyPEmbedded_of_mem_sigma (c : Ctx82E3 D) {p : ℕ} (hp : p ∈ D.sig) :
    IsStronglyPEmbedded p D.M :=
  c.sig1_sp p (sigma_subset_sigmaOne c hp)

theorem three_not_mem_sigma (c : Ctx82E3 D) : 3 ∉ D.sig :=
  fun h3 => c.not_strong (isStronglyPEmbedded_of_mem_sigma c h3)

theorem pRank_le_three (c : Ctx82E3 D) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p D.M ≤ 3 :=
  (CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank p hp hp2 D.M D.maxLocal.1).trans
    c.rank.le

theorem pRank_three_M (c : Ctx82E3 D) : CFSG.Open.pRank 3 D.M = 3 := by
  have hge3 : 3 ≤ CFSG.Open.pRank 3 D.M :=
    c.hyp81.2.2.2.1.trans
      (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 (by norm_num) c.hyp81.1)
  have hle3 : CFSG.Open.pRank 3 D.M ≤ 3 := pRank_le_three c (by norm_num) (by norm_num)
  omega

theorem pRank_three_L (c : Ctx82E3 D) : CFSG.Open.pRank 3 c.L = 3 := by
  apply le_antisymm
  · exact (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 (by norm_num) c.hyp81.1).trans
      (pRank_three_M c).le
  · exact c.hyp81.2.2.2.1

theorem five_le_of_mem_sigma (c : Ctx82E3 D) {p : ℕ} (hp : p ∈ D.sig) : 5 ≤ p := by
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact three_not_mem_sigma c hp
  exact Nat.Prime.five_le_of_ne_two_of_ne_three (D.sig_prime p hp).1 (D.sig_prime p hp).2 hp3

theorem pRank_eq_three_of_mem_sigma (c : Ctx82E3 D) {p : ℕ} (hp : p ∈ D.sig) :
    CFSG.Open.pRank p D.M = 3 :=
  le_antisymm (pRank_le_three c (D.sig_prime p hp).1 (D.sig_prime p hp).2) (c.three_le p hp)

theorem M_ne_top (_ : Ctx82E3 D) : D.M ≠ ⊤ := by
  haveI := D.standing.simple
  exact CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab D.maxLocal.1

theorem conclusion76 (c : Ctx82E3 D) {p : ℕ} (hp : p ∈ D.sig) :
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 D.M p :=
  c.r76 p hp (isStronglyPEmbedded_of_mem_sigma c hp)

theorem not_rankThreeGamma_le_of_le_center (c : Ctx82E3 D) {P E : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hE : E ≤ P ⊓ Subgroup.centralizer (P : Set G)) (hEab : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) :
    ¬ CFSG.Open.rankThreeGamma 1 3 E ≤ D.M := by
  intro hΓ
  exact c.not_strong
    (c.r614 (sigma_subset_sigmaOne c) 3 (by norm_num) (by norm_num)
      (three_not_mem_sigma c) P hP E hE hEab hcard hΓ)

end Ctx82E3

theorem theorem82At_of_isEmpty {D : Data G} (hstd : Std82E3 D) (h : Ctx82E3 D → False) :
    Theorem82At D.M := by
  intro L hL
  by_contra hnotstrong
  exact h ⟨hstd, L, hL, hnotstrong⟩

theorem r82_of_isEmpty {D : Data G} (hstd : Std82E3 D) (h : Ctx82E3 D → False) :
    UC22.F08.R82 D :=
  UC22.r82_of_theorem82At (theorem82At_of_isEmpty hstd h)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
