module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsSetting
public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEight
import CFSG.LocalAnalysis.WeakClosure81.Eleven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

namespace TwelveSix

theorem hasCompFactor_calL1_iff (H : Subgroup G) :
    F12.HasCompFactor H IsCalL1 ↔ CFSG.LocalAnalysis.RankThreeUC.Asc1930HasA H := by
  constructor
  · rintro ⟨L, _, hL, n, hn, h1, hP⟩
    refine ⟨L, inferInstance, hL, n, hn, h1, ?_⟩
    rcases hP with hP | hP | hP
    · exact Or.inl hP
    · exact Or.inr (Or.inr hP)
    · exact Or.inr (Or.inl hP)
  · rintro ⟨L, _, hL, n, hn, h1, hP⟩
    refine ⟨L, inferInstance, hL, n, hn, h1, ?_⟩
    rcases hP with hP | hP | hP
    · exact Or.inl hP
    · exact Or.inr (Or.inr hP)
    · exact Or.inr (Or.inl hP)

theorem hasCompFactor_calL0_iff (H : Subgroup G) :
    F12.HasCompFactor H IsCalL0 ↔ CFSG.LocalAnalysis.RankThreeUC.Asc1930HasB H := by
  constructor
  · rintro ⟨L, _, hL, hP⟩
    refine ⟨L, inferInstance, hL, ?_⟩
    rcases hP with ⟨n, hn, t, m, hP⟩ | hP | hP | hP | hP | hP | hP
    · exact Or.inl ⟨t, m, n, hn, hP⟩
    · exact Or.inr (Or.inl hP)
    · exact Or.inr (Or.inr (Or.inl hP))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hP)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hP))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hP)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hP)))))
  · rintro ⟨L, _, hL, hP⟩
    refine ⟨L, inferInstance, hL, ?_⟩
    rcases hP with ⟨t, m, n, hn, hP⟩ | hP | hP | hP | hP | hP | hP
    · exact Or.inl ⟨n, hn, t, m, hP⟩
    · exact Or.inr (Or.inl hP)
    · exact Or.inr (Or.inr (Or.inl hP))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hP)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hP))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hP)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hP)))))

theorem pCoreOf_ne_bot_of_mem_hSet (D : Data G) {H : Subgroup G}
    (hH : H ∈ CFSG.LocalAnalysis.RankThreeUC.hSet D.T D.M) : pCoreOf 2 H ≠ ⊥ := by
  intro h
  apply hH.2.1
  intro x hx
  have hx' : x ∈ H ⊓ centralizer (pCoreOf 2 H : Set G) := by
    refine Subgroup.mem_inf.2 ⟨hx, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy1 : y = 1 := by
      rw [h] at hy
      exact Subgroup.mem_bot.1 hy
    simp [hy1]
  have h1 := hH.2.2 hx'
  rw [h, Subgroup.mem_bot] at h1
  rw [h1]
  exact D.M.one_mem

theorem exists_mem_calMOf_le (D : Data G) {H : Subgroup G}
    (hH : H ∈ CFSG.LocalAnalysis.RankThreeUC.hSet D.T D.M) : ∃ N ∈ calMOf D.T, H ≤ N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hloc : IsTwoLocal (normalizer (pCoreOf 2 H : Set G)) :=
    ⟨pCoreOf 2 H, pCoreOf_ne_bot_of_mem_hSet D hH,
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H, rfl⟩
  obtain ⟨N, hN, hle⟩ := exists_isMaxTwoLocalSubgroup_le hloc
  have hHN : H ≤ N := (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H).trans hle
  exact ⟨N, ⟨hN, hH.1.trans hHN⟩, hHN⟩

theorem ne_top_of_mem_hSet (D : Data G) {H : Subgroup G}
    (hH : H ∈ CFSG.LocalAnalysis.RankThreeUC.hSet D.T D.M) : H ≠ ⊤ := by
  haveI := D.standing.simple
  obtain ⟨N, hN, hHN⟩ := exists_mem_calMOf_le D hH
  intro htop
  apply CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab hN.1.1
  rw [← top_le_iff, ← htop]
  exact hHN

theorem isKGroup_of_mem_hSet (D : Data G) {H : Subgroup G}
    (hH : H ∈ CFSG.LocalAnalysis.RankThreeUC.hSet D.T D.M) : CFSG.Open.IsKGroup ↥H :=
  D.standing.kProper.isKGroup H (ne_top_of_mem_hSet D hH)

theorem pRank_three_le_one (D : Data G) (h66 : UC6.R6_6 D) {H : Subgroup G}
    (hH : H ∈ CFSG.LocalAnalysis.RankThreeUC.hSet D.T D.M) (hsp : IsStronglyPEmbedded 3 D.M) :
    CFSG.Open.pRank 3 H ≤ 1 := by
  obtain ⟨N, hN, hHN⟩ := exists_mem_calMOf_le D hH
  by_contra h
  have h2 : 2 ≤ CFSG.Open.pRank 3 N := by
    have := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hHN
    omega
  have hNM := (h66 3 Nat.prime_three (by norm_num)).1 (Or.inl hsp) N hN h2
  exact hH.2.1 (hNM ▸ hHN)

theorem pRank_three_le_three (D : Data G) (h66 : UC6.R6_6 D) {H : Subgroup G}
    (hH : H ∈ CFSG.LocalAnalysis.RankThreeUC.hSet D.T D.M) : CFSG.Open.pRank 3 H ≤ 3 := by
  obtain ⟨N, hN, hHN⟩ := exists_mem_calMOf_le D hH
  by_contra h
  have h4 : 4 ≤ CFSG.Open.pRank 3 N := by
    have := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hHN
    omega
  have hNM := (h66 3 Nat.prime_three (by norm_num)).2.2 rfl N hN h4
  exact hH.2.1 (hNM ▸ hHN)

theorem pRank_inf_le_one (D : Data G) (h66 : UC6.R6_6 D) {H : Subgroup G}
    (hH : H ∈ CFSG.LocalAnalysis.RankThreeUC.hSet D.T D.M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h3 : 3 < CFSG.Open.pRank p H) : CFSG.Open.pRank p (H ⊓ D.M) ≤ 1 := by
  obtain ⟨N, hN, hHN⟩ := exists_mem_calMOf_le D hH
  by_contra h
  have h4 : 4 ≤ CFSG.Open.pRank p N := by
    have := CFSG.SectionRank.pRank_mono hp.one_lt hHN
    omega
  have h2 : 2 ≤ CFSG.Open.pRank p (D.M ⊓ N) := by
    have := CFSG.SectionRank.pRank_mono hp.one_lt
      (show H ⊓ D.M ≤ D.M ⊓ N from fun x hx => ⟨hx.2, hHN hx.1⟩)
    omega
  have hNM := (h66 p hp hp2).2.1 N hN.1 h4 h2
  exact hH.2.1 (hNM ▸ hHN)

theorem pRank_inf_conjSubgroup_le_one (D : Data G) (h66 : UC6.R6_6 D) {H : Subgroup G}
    (hH : H ∈ CFSG.LocalAnalysis.RankThreeUC.hSet D.T D.M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h3 : 3 < CFSG.Open.pRank p H) (g : G) :
    CFSG.Open.pRank p (H ⊓ conjSubgroup D.M g) ≤ 1 := by
  obtain ⟨N, hN, hHN⟩ := exists_mem_calMOf_le D hH
  by_contra h
  set f : G →* G := (MulAut.conj g).toMonoidHom with hf
  have hfi : Function.Injective f := (MulAut.conj g).injective
  have hN'max : rankThreeIsMaxTwoLocal (N.map f) := by
    have := UC6.isMaxTwoLocal_conj hN.1 g⁻¹
    simpa [uniqueFourConj, hf, rankThreeIsMaxTwoLocal] using this
  have h4 : 4 ≤ CFSG.Open.pRank p (N.map f) := by
    have h1 := CFSG.SectionRank.pRank_mono hp.one_lt hHN
    have h2 := CFSG.SectionRank.pRank_le_map hp.one_lt f hfi N
    omega
  have h2 : 2 ≤ CFSG.Open.pRank p (D.M ⊓ N.map f) := by
    have h1 := CFSG.SectionRank.pRank_le_map hp.one_lt f hfi (H ⊓ conjSubgroup D.M g)
    have hle : (H ⊓ conjSubgroup D.M g).map f ≤ D.M ⊓ N.map f := by
      rintro _ ⟨x, ⟨hxH, hxM⟩, rfl⟩
      exact ⟨mem_conjSubgroup_iff.1 hxM, ⟨x, hHN hxH, rfl⟩⟩
    have h5 := CFSG.SectionRank.pRank_mono hp.one_lt hle
    omega
  have hNM : N.map f = D.M := (h66 p hp hp2).2.1 _ hN'max h4 h2
  have hfM : ∀ x ∈ H, g * x * g⁻¹ ∈ D.M := fun x hx => by
    rw [← hNM]
    exact ⟨x, hHN hx, rfl⟩
  have hgM : g⁻¹ ∈ D.M := by
    refine TwelveEight.mem_of_le_map_conj D (fun t ht => ?_)
    refine ⟨g * t * g⁻¹, hfM t (hH.1 ht), ?_⟩
    simp [mul_assoc]
  apply hH.2.1
  intro x hx
  have hx' : x = g⁻¹ * (g * x * g⁻¹) * g := by group
  rw [hx']
  exact D.M.mul_mem (D.M.mul_mem hgM (hfM x hx)) (by simpa using D.M.inv_mem hgM)

theorem w3Hyp171 (D : Data G) (h66 : UC6.R6_6 D) {H : Subgroup G}
    (hH : H ∈ CFSG.LocalAnalysis.RankThreeUC.hSet D.T D.M) : W3Hyp171 D H := by
  refine ⟨TwelveEight.fstar_eq_pCoreOf_of_mem_hSet hH, hH.1, fun p hp hp2 h3 g => ?_⟩
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at h3 ⊢
  exact pRank_inf_conjSubgroup_le_one D h66 hH hp hp2 h3 g

theorem w3Hyp181 (D : Data G) (h66 : UC6.R6_6 D) {H : Subgroup G}
    (hH : H ∈ CFSG.LocalAnalysis.RankThreeUC.hSet D.T D.M) (hsp : IsStronglyPEmbedded 3 D.M) :
    W3Hyp181 D H :=
  ⟨by rw [CFSG.SectionRank.pRank_coe_eq_openPRank]; exact pRank_three_le_one D h66 hH hsp, hsp⟩

theorem w3Hyp182 (D : Data G) (h66 : UC6.R6_6 D) {H : Subgroup G}
    (hH : H ∈ CFSG.LocalAnalysis.RankThreeUC.hSet D.T D.M) : W3Hyp182 D H := by
  refine ⟨by rw [CFSG.SectionRank.pRank_coe_eq_openPRank]; exact pRank_three_le_three D h66 hH,
    fun p hp hp2 h3 => ?_⟩
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at h3 ⊢
  exact pRank_inf_le_one D h66 hH hp hp2 h3

end TwelveSix

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
