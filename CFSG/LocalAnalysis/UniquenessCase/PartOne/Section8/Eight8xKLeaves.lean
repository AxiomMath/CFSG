module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Spine
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08 (List880)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (IsAutSz)

@[expose] def List880NotSL3PiType : Prop :=
  ∀ (X : Type) [Group X], List880 X → ¬ IsSL3PiType X

theorem j2NotSL3PiType_of_list880 (h : List880NotSL3PiType) : J2NotSL3PiType :=
  fun X _ hJ2 => h X (Or.inr (Or.inl hJ2))

@[expose] def List880SylowThreeTwoGenerated : Prop :=
  ∀ (X : Type) [Group X] [Finite X], List880 X → CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 →
    ∀ Q : Subgroup X, IsSylowOf 3 Q ⊤ → Group.rank ↥Q ≤ 2

private theorem prod_three_dvd_48 {d : ℕ} (hd : d ≤ 2) :
    (∏ i : Fin d, (3 ^ d - 3 ^ (i : ℕ))) ∣ 48 := by
  interval_cases d <;> norm_num [Fin.prod_univ_succ]

private theorem card_mulAut_frattini_quotient_three_dvd_48 {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup 3 Q) (hrank : Group.rank Q ≤ 2) :
    Nat.card (MulAut (Q ⧸ frattini Q)) ∣ 48 := by
  obtain ⟨-, hcomm, hpow, helem, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hQ
  have hcard := @CFSG.elementaryAbelian_card_eq_pow_generatorRank 3 _
    (Q ⧸ frattini Q) _ _ helem
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 3)
    (fun a b => hcomm.is_comm.comm a b) hpow hcard
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e,
    CFSG.SectionRank.Ccomm.card_GL_zmod (p := 3)]
  apply prod_three_dvd_48
  rw [CFSG.generatorRank_eq_group_rank]
  exact (Group.rank_le_of_surjective (QuotientGroup.mk' (frattini Q))
    (QuotientGroup.mk'_surjective _)).trans hrank

theorem not_dvd_card_mulAut_of_pGroup_three_of_rank_le_two {Q : Type} [Group Q] [Finite Q]
    (hQ : IsPGroup 3 Q) (hrank : Group.rank Q ≤ 2) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ¬ p ∣ Nat.card (MulAut Q) := by
  intro hdiv
  let φ : MulAut Q →* MulAut (Q ⧸ frattini Q) :=
    CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini Q)
  have hker : IsPGroup 3 φ.ker :=
    CFSG.OrderReductions.FrattiniAutomorphisms.frattini_automorphism_kernel_isPGroup 3 hQ
  obtain ⟨k, hk⟩ := hker.exists_card_eq
  have hrange : Nat.card φ.range ∣ 48 :=
    (Subgroup.card_subgroup_dvd_card φ.range).trans
      (card_mulAut_frattini_quotient_three_dvd_48 hQ hrank)
  have hcard : Nat.card (MulAut Q) ∣ 3 ^ k * 48 := by
    rw [← Subgroup.card_ker_mul_card_range φ, hk]
    exact mul_dvd_mul_left (3 ^ k) hrange
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hnot48 : ¬ p ∣ 48 := by
    intro h
    have h' : p ∣ 2 ^ 4 * 3 := by simpa using h
    rcases hp.dvd_mul.mp h' with h2 | h3
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2))
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3)
  have hnot : ¬ p ∣ 3 ^ k * 48 := by
    intro h
    rcases hp.dvd_mul.mp h with h3 | h48
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3))
    · exact hnot48 h48
  exact hnot (hdiv.trans hcard)

@[expose] def FiveEmbeddedNoAlt6 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (N S : Subgroup Y), N.Normal → genFittingFStar Y ≤ N →
    ((∃ n : ℕ, LieModel ↥N .PSL 2 5 n) ∨ (∃ n : ℕ, LieModel ↥N .PSU 3 5 n) ∨ IsAutSz ↥N 5 ∨
      LieModel ↥N .Tits 0 2 1 ∨ IsSpor ↥N .McL ∨ IsAlt ↥N 10) →
    IsStronglyPEmbedded 5 S → 1 < CFSG.Open.pRank 5 S →
    ¬ ∃ (A : Subgroup ↥S) (V : Subgroup ↥A) (_ : V.Normal), IsAlt (↥A ⧸ V) 6

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
