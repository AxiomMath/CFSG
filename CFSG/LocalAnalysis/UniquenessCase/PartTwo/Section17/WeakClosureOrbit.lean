module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiveA6Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.VZeroSmall17
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20o
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ConjSetCard
public import CFSG.Quasithin.Background.F6SQTK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNine
public import CFSG.LocalAnalysis.StronglyEmbedded.PSubgroups
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.NineThreeSylData
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSixBorel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSixE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSixteen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap17_5_A6Pair (D : Data G) (V₀ V : Subgroup G) : Prop :=
  Hyp125 D V₀ V → ∀ L : Subgroup G, L ∈ calC D.M →
    Nonempty (BarO2Z17 L ≃* alternatingGroup (Fin 6)) → ¬ ExpFourAut17 D L →
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M → UniqueMax D.M (L ⊔ D.T) →
    ¬ D.T ≤ normalizer (L : Set G) → L ≤ centralizer (V₀ : Set G) → Nat.card V₀ ≤ 4

@[expose] def Gap17_15_TOrbitFour (D : Data G) (V₀ V : Subgroup G) : Prop :=
  Hyp125 D V₀ V → ∀ L : Subgroup G, L ∈ calC D.M → IsL2Over17 (Bar2 L) 7 →
    CFSG.Quasithin.F6.IsPGL2 7 (Bar2 (L ⊔ NTL17 D L)) →
    (∃ (A : Type) (_ : Group A) (φ : ↥((L ⊔ D.T) ⊓ normalizer (L : Set G)) →* A),
      Function.Surjective φ ∧
      (∀ x : ↥((L ⊔ D.T) ⊓ normalizer (L : Set G)),
        φ x = 1 ↔ (x : G) ∈ centSection (L ⊔ D.T) L (CFSG.Quasithin.oTwoThreeIn L)) ∧
      (CFSG.Quasithin.F6.IsPGL2 7 A ∨
        Inputs1719.IsAutOf A (alternatingGroup (Fin 6)) ∨ Inputs1719.IsM10 A ∨
        CFSG.Quasithin.F6.IsPGL2 9 A)) →
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M → UniqueMax D.M (L ⊔ D.T) →
    2 < (conjSetOf D.T L).ncard → L ≤ centralizer (V₀ : Set G) → Nat.card V₀ ≤ 4

theorem pRank_three_M_le_three_of_evenRank (D : Data G) (he3 : CFSG.Open.evenRank G = 3) :
    CFSG.Open.pRank 3 D.M ≤ 3 := by
  have h := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3 Nat.prime_three
    (by norm_num) D.M D.maxLocal.1
  rwa [he3] at h

theorem exists_ncard_conjSetOf_eq_two_pow (D : Data G) (L : Subgroup G) :
    ∃ n : ℕ, (conjSetOf D.T L).ncard = 2 ^ n := by
  obtain ⟨k, hk⟩ := uc22p20o_orbit_card D L
  have hset : (Set.range fun t : D.T => uc22p20bCj (t : G) L) = conjSetOf D.T L := by
    ext K
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  refine ⟨k, ?_⟩
  rw [← hset, ← Nat.card_coe_set_eq]
  exact hk

theorem exists_conj_pair_of_ncard_conjSetOf_eq_two {T L : Subgroup G}
    (h : (conjSetOf T L).ncard = 2) :
    ∃ L₂ : Subgroup G, (∃ t ∈ T, L₂ = CFSG.Quasithin.conjSubgroup L t) ∧ L ≠ L₂ ∧
      ∀ t ∈ T, CFSG.Quasithin.conjSubgroup L t = L ∨
        CFSG.Quasithin.conjSubgroup L t = L₂ := by
  obtain ⟨L', hne, hset⟩ := exists_pair_eq_conjSetOf_of_ncard_eq_two (mem_conjSetOf_self T L) h
  have hL' : L' ∈ conjSetOf T L := by
    rw [hset]
    exact Or.inr rfl
  obtain ⟨s, hs, hsL⟩ := hL'
  refine ⟨L', ⟨s⁻¹, T.inv_mem hs, ?_⟩, hne.symm, fun t ht => ?_⟩
  · rw [hsL, CFSG.Quasithin.conjSubgroup, inv_inv]
  · have hmem : CFSG.Quasithin.conjSubgroup L t ∈ conjSetOf T L :=
      ⟨t⁻¹, T.inv_mem ht, rfl⟩
    rw [hset] at hmem
    simpa using hmem

theorem mem_calP_of_isStronglyPEmbedded {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hne : V₀ ≠ ⊥) (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M) {P : Subgroup G}
    (hPM : P ≤ D.M) (hP : IsPGroup 3 P) : P ∈ CFSG.LocalAnalysis.WeakClosure81.calP V₀ := by
  refine TwelveSixteen.mem_calP D (hyp125_inCalV h hne) (hyp125_isTI h hne) Nat.prime_three
    (by norm_num) hP ?_ ?_
  · intro g hg _
    have hg' : g⁻¹ ∉ D.M := fun h => hg (by simpa using D.M.inv_mem h)
    simpa [CFSG.Quasithin.conjSubgroup] using
      hsp.inf_map_conj_eq_bot Nat.prime_three hPM hP g⁻¹ hg'
  · exact hsp.rankThreeGamma_one_le_of_le Nat.prime_three hP hPM

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
