module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K331Basic
public import CFSG.LieType.SeitzGeneration.ExcTorusThreeTwCat
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CharPGenThreeExc
import CFSG.LocalAnalysis.UniquenessCase.UC22K331RankCl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open TauCeti
open CFSG.Open (GLBCore)
open CFSG.LieType.SeitzGeneration (Cat exists_isElemAbelian_card_of_not_rankLE2)

theorem three_le_pRank_of_glbCore_eq_top {L : Type} [Group L] [Finite L] [Nontrivial L] {p : ℕ}
    (hp : p.Prime) {P : Subgroup L} (h : GLBCore p 3 P = ⊤) :
    3 ≤ CFSG.Open.pRank p (⊤ : Subgroup L) := by
  by_contra hlt
  have hbot : GLBCore p 3 P = ⊥ := by
    refine sSup_eq_bot.2 ?_
    rintro N ⟨Q, -, hQ, -⟩
    exact absurd (hQ.trans (CFSG.SectionRank.pRank_mono hp.one_lt le_top)) hlt
  rw [h] at hbot
  obtain ⟨g, hg⟩ := exists_ne (1 : L)
  exact hg (Subgroup.mem_bot.1 (hbot ▸ Subgroup.mem_top g))

theorem exists_noncomm_of_pRank_three_eq_two {L : Type} [Group L] [Finite L] (hs : IsSimpleGroup L)
    (h2 : CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2) : ∃ a b : L, a * b ≠ b * a := by
  by_contra h
  have hc : ∀ a b : L, a * b = b * a := fun a b => not_not.mp fun hab => h ⟨a, b, hab⟩
  have : IsMulCommutative L := ⟨⟨hc⟩⟩
  have hp : (Nat.card L).Prime := (Group.is_simple_iff_prime_card (α := L)).1 hs
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) (⊤ : Subgroup L)
  rw [h2] at hE
  have h9 : 9 ∣ Nat.card L := by
    have := Subgroup.card_subgroup_dvd_card E
    rwa [hE] at this
  rcases hp.eq_one_or_self_of_dvd 9 h9 with h1 | h1
  · norm_num at h1
  · rw [← h1] at hp
    norm_num at hp

section Certified


theorem k331Idx_twistedE6 (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid) :
    K331Idx (.lie ⟨.twistedE6 q, hv⟩) := by
  intro L _ _ hs h2 ⟨e⟩
  exfalso
  by_cases hp3 : q.p = 3
  · have hd : CFSG.AGLEmbedding.IsExceptionalIndex ⟨.twistedE6 q, hv⟩ :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩)))))
    haveI := hs.toNontrivial
    obtain ⟨T⟩ : Nonempty (Sylow 3 L) := inferInstance
    have hcore := CFSG.AGLEmbedding.charPGen3At_exceptional L hs
      (exists_noncomm_of_pRank_three_eq_two hs h2) ⟨.twistedE6 q, hv⟩ hd ⟨e⟩ 3 Nat.prime_three
      (by norm_num) (by simp [hp3]) (by rintro (⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩) <;> cases h) T
    have := three_le_pRank_of_glbCore_eq_top (L := L) Nat.prime_three hcore
    omega
  · haveI : Finite (Cat ⟨.twistedE6 q, hv⟩) := Finite.of_equiv L e.toEquiv
    obtain ⟨-, E, hE, hc⟩ := exists_isElemAbelian_card_of_not_rankLE2 Nat.prime_three
      (CFSG.LieType.SeitzGeneration.not_rankLE2_cat_twistedE6_three q hv (Ne.symm hp3))
    have := three_le_pRank_of_equiv e (CFSG.SectionRank.le_pRank (by norm_num) le_top hE hc)
    omega

end Certified

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3
