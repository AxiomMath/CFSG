module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer
import CFSG.LocalAnalysis.StronglyEmbedded.PSubgroups
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Opp
import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.DerivedQuotient
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

@[expose] def R9_21Opp (D : Data G) : Prop :=
  IsStronglyPEmbedded 3 D.M →
    ∀ Y : Subgroup G, Opp 3 Y ≠ ⊥ → Y ≤ D.M → pCoreOf 2 Y ≠ ⊥ →
      (∀ A ∈ F09.Inv9' D.M (Opp 3 Y) 3, ⁅A, Opp 3 Y⁆ ≤ pCoreOf 2 A) →
      (∃ k : ℕ, ((Opp 3 Y).subgroupOf Y).index = 2 ^ k) →
        UniqueMax D.M Y ∨ Y ∈ F09.calY2_9 D

private theorem c16n9o_not_le {N M : Subgroup G} (hN : rankThreeIsMaxTwoLocal N)
    (hM : rankThreeIsMaxTwoLocal M) (hNM : N ≠ M) : ¬ N ≤ M :=
  fun h => hNM (hN.2 M hM.1 h).symm

private theorem c16n9o_exists_order_three {Y : Subgroup G} (h : Opp 3 Y ≠ ⊥) :
    ∃ u ∈ Opp 3 Y, orderOf u = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hxY, ⟨k, hk⟩, hx1⟩ :
      ∃ x : G, x ∈ Y ∧ (∃ k : ℕ, orderOf x = 3 ^ k) ∧ x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    refine h (eq_bot_iff.2 ((Subgroup.closure_le _).2 ?_))
    rintro x ⟨hxY, hk⟩
    exact Subgroup.mem_bot.2 (hcon x hxY hk)
  have hxX : x ∈ Opp 3 Y := Subgroup.subset_closure ⟨hxY, k, hk⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hx1 (orderOf_eq_one_iff.1 (by simpa using hk))
  have h3 : 3 ∣ Nat.card (Opp 3 Y) := by
    have h1 : orderOf (⟨x, hxX⟩ : ↥(Opp 3 Y)) ∣ Nat.card (Opp 3 Y) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hk] at h1
    exact (dvd_pow_self 3 hk0).trans h1
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Opp 3 Y)) 3 h3
  exact ⟨u, u.2, (Subgroup.orderOf_coe u).trans hu⟩

private theorem c16n9o_mem_uniqueSet {M A : Subgroup G} (hSP : IsStronglyPEmbedded 3 M)
    (hAM : A ≤ M) (hA3 : IsPGroup 3 A) (hA1 : A ≠ ⊥) : A ∈ uniqueSet M := by
  refine ⟨hAM, fun g hAg => ?_⟩
  by_cases hg : g ∈ M
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hg)
  · exfalso
    have h := hSP.inf_map_conj_eq_bot Nat.prime_three hAM hA3 g hg
    exact hA1 (eq_bot_iff.2 (by rw [← h]; exact le_inf le_rfl hAg))

private theorem c16n9o_pRank_le_one {D : Data G} (h63 : UC6.R6_3 D)
    (hSP : IsStronglyPEmbedded 3 D.M) {N U : Subgroup G} (hN : rankThreeIsMaxTwoLocal N)
    (hNM : N ≠ D.M) (hUN : U ≤ N) (hUM : U ≤ D.M) (hU3 : IsPGroup 3 U) (hU1 : U ≠ ⊥) :
    CFSG.Open.pRank 3 N ≤ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hgt
  have h2 : 2 ≤ CFSG.Open.pRank 3 N := by omega
  obtain ⟨E, hEN, hE, hEcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank h2
  obtain ⟨P, hP, hUP⟩ := UC6.exists_isSylowOf_ge hUN hU3
  have hPM : P ≤ D.M := hSP.le_of_isPGroup_inf hP.isPGroup
    (fun h => hU1 (eq_bot_iff.2 (by rw [← h]; exact le_inf hUP hUM)))
  obtain ⟨k, hkN, hk⟩ := UC6.exists_conj_le_of_isSylowOf hP hEN hE.isPGroup
  obtain ⟨E', hE'P, hE'N, hE'el, hE'card⟩ : ∃ E' : Subgroup G, E' ≤ P ∧ E' ≤ N ∧
      IsElemAbelian 3 E' ∧ Nat.card E' = 3 ^ 2 := by
    refine ⟨E.map (MulAut.conj k⁻¹).toMonoidHom, ?_, ?_, hE.map _, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      simpa [MulAut.conj_apply] using hk x hx
    · rintro _ ⟨x, hx, rfl⟩
      simpa [MulAut.conj_apply] using N.mul_mem (N.mul_mem (N.inv_mem hkN) (hEN hx)) hkN
    · rw [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, hEcard]
  have hE'M : E' ≤ D.M := hE'P.trans hPM
  have hΓ : rankThreeGamma 1 3 E' ≤ D.M :=
    hSP.rankThreeGamma_one_le_of_le Nat.prime_three hE'el.isPGroup hE'M
  have hUniq := h63 3 Nat.prime_three (by norm_num) E' hE'M hE'el hE'card hΓ
  have hNmem : N ∈ calMOf E' := ⟨hN, hE'N⟩
  rw [hUniq] at hNmem
  exact hNM (Set.mem_singleton_iff.1 hNmem)

private theorem c16n9o_mem_calH9 {D : Data G} (h63 : UC6.R6_3 D)
    (hSP : IsStronglyPEmbedded 3 D.M) {Y : Subgroup G} (hX : Opp 3 Y ≠ ⊥) (hYM : Y ≤ D.M)
    {N : Subgroup G} (hN : N ∈ calMOf Y) (hNM : N ≠ D.M) : N ∈ F09.calH9 D Y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, huX, hu3⟩ := c16n9o_exists_order_three hX
  have hu : u ^ 3 = 1 := by rw [← hu3]; exact pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu3; norm_num at hu3
  have hUcard : Nat.card (Subgroup.zpowers u) = 3 := by rw [Nat.card_zpowers, hu3]
  have hU3 : IsPGroup 3 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [hUcard]; norm_num)
  have hUX : Subgroup.zpowers u ≤ Opp 3 Y := Subgroup.zpowers_le.2 huX
  have hUY : Subgroup.zpowers u ≤ Y := hUX.trans (close16_opp_le 3 Y)
  have hUne : Subgroup.zpowers u ≠ ⊥ := fun h => hu1 (Subgroup.zpowers_eq_bot.1 h)
  have hrk : CFSG.Open.pRank 3 N ≤ 1 :=
    c16n9o_pRank_le_one h63 hSP hN.1 hNM (hUY.trans hN.2) (hUY.trans hYM) hU3 hUne
  refine ⟨hN.2, c16n9o_not_le hN.1 D.maxLocal hNM, le_antisymm ?_ ?_⟩
  · refine (CFSG.SectionRank.pRank_mono (by norm_num) ?_).trans hrk
    refine iSup_le fun h => ?_
    rintro _ ⟨x, hx, rfl⟩
    have hxN : x ∈ N := hN.2 ((close16_opp_le 3 Y) hx)
    simpa [MulAut.conj_apply] using N.mul_mem (N.mul_mem h.2 hxN) (N.inv_mem h.2)
  · refine CFSG.SectionRank.le_pRank (by norm_num) ?_ (isElemAbelian_zpowers hu)
      (by rw [hUcard, pow_one])
    intro x hx
    refine le_iSup (fun h : ↥N => (Opp 3 Y).map (MulAut.conj (h : G)).toMonoidHom) 1 ?_
    exact ⟨x, hUX hx, by simp [MulAut.conj_apply]⟩

theorem r9_21Opp_of_r6_3 (D : Data G) (h63 : UC6.R6_3 D) : R9_21Opp D := by
  intro hSP Y hX hYM _ hA hidx
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hU : UniqueMax D.M Y
  · exact Or.inl hU
  refine Or.inr ?_
  obtain ⟨N, hNmem, hNM⟩ : ∃ N ∈ calMOf Y, N ≠ D.M := by
    by_contra hcon
    push Not at hcon
    refine hU (Set.eq_singleton_iff_unique_mem.2 ⟨⟨D.maxLocal, hYM⟩, fun N hN => hcon N hN⟩)
  have hNtop : N ≠ ⊤ := by
    haveI := D.standing.simple
    exact CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab hNmem.1.1
  obtain ⟨C, hC, hNC⟩ : ∃ C : Subgroup G, IsCoatom C ∧ N ≤ C := by
    rcases IsCoatomic.eq_top_or_exists_le_coatom N with h | h
    · exact absurd h hNtop
    · exact h
  have hCM : C ≠ D.M := fun h =>
    c16n9o_not_le hNmem.1 D.maxLocal hNM (h ▸ hNC)
  have hY9 : Y ∈ F09.calY9 D := by
    refine ⟨hYM, fun h => hCM ?_, fun A hAY hAcard => ?_⟩
    · exact Set.mem_singleton_iff.1 (h ▸ (⟨hC, hNmem.2.trans hNC⟩ : C ∈ calNOf Y))
    · have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by rw [hAcard]; norm_num)
      exact c16n9o_mem_uniqueSet hSP (hAY.trans hYM) hA3
        (fun h => by rw [h, Subgroup.card_bot] at hAcard; norm_num at hAcard)
  refine ⟨hY9, hU, fun H hH => ?_, fun A hAmem => ?_, hidx⟩
  · by_cases hHM : H = D.M
    · exact Or.inr hHM
    · exact Or.inl (c16n9o_mem_calH9 h63 hSP hX hYM hH hHM)
  · exact hA A ⟨hAmem.1, hAmem.2.1, (close16_opp_le 3 Y).trans hAmem.2.2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
