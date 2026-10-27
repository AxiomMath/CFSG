module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846j
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
import CFSG.LocalAnalysis.UniquenessCase.UC6R77E2
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CentralizingRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6S846

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem mem_centralizer_of_rhoL_eq_one {L S : Subgroup G} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hSL : S ≤ L) (hSq : IsPGroup q S) {b : G} (hb : b ∈ normalizer (L : Set G))
    (hbS : b ∈ normalizer (S : Set G)) (h1 : rhoL L ⟨b, hb⟩ = 1) :
    b ∈ centralizer (S : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hsL : s ∈ L := hSL hs
  have hfix : rhoL L ⟨b, hb⟩ (QuotientGroup.mk (⟨s, hsL⟩ : ↥L)) =
      QuotientGroup.mk (⟨s, hsL⟩ : ↥L) := by
    rw [h1]
    rfl
  have h2 := (rhoL_fix_iff L ⟨b, hb⟩ ⟨s, hsL⟩).1 hfix
  have h3 : b * s * b⁻¹ * s⁻¹ ∈ S :=
    S.mul_mem ((Subgroup.mem_normalizer_iff.1 hbS s).1 hs) (S.inv_mem hs)
  have h4 : b * s * b⁻¹ * s⁻¹ = 1 :=
    eq_one_of_mem_isPGroup_of_mem_isPGroup hq hq2 hSq (isPGroup_pCoreOf L) h3 h2
  have h5 : b * s * b⁻¹ = s := mul_inv_eq_one.1 h4
  calc s * b = b * s * b⁻¹ * b := by rw [h5]
    _ = b * s := by group

theorem keyLemma3 (hgr : CFSG.Open.GriessAllModelsStatement) {M L : Subgroup G} (hLM : L ≤ M)
    (hN : M ≤ normalizer (L : Set G)) {n : ℕ} (hX : IsSU3 (Bar2 L) n) {q p : ℕ} (hq : q.Prime)
    (hq3 : 3 < q) (hqn : q ∣ 2 ^ n + 1) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q)
    (hOp : UC22.F10.OpRes p M = M) (hrank : 3 ≤ Open.pRank p M) :
    ∃ S E : Subgroup G, S ≤ L ∧ IsPGroup q S ∧
      (∀ T : Subgroup G, T ≤ L → IsPGroup q T → S ≤ T → T = S) ∧
      E ≤ S ∧ IsElemAbelian q E ∧ Nat.card E = q ^ 2 ∧
      (3 ≤ Open.pRank p (M ⊓ normalizer (E : Set G)) ∨
        2 ≤ Open.pRank p (M ⊓ centralizer (E : Set G))) ∧
      ∃ Sb : Subgroup (Bar2 L), IsPGroup q Sb ∧ ¬ q ∣ Sb.index ∧
        (S.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = Sb := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hq2 : q ≠ 2 := by rintro rfl; omega
  obtain ⟨B, hBM, hBel, hBcard⟩ := exists_elemAbelian_card_of_le_pRank hp hrank
  obtain ⟨B₁, hB₁B, hB₁card, hbr, Sb, hSb⟩ :=
    exists_sub_fixing_sylow hgr hN hX hq hq3 hqn hp hp2 hOp hBM hBel (k := 2) hBcard
  obtain ⟨S, hSL, hSq, hSmax, hSmap, hB₁S⟩ := exists_lift_normalized (hB₁B.trans (hBM.trans hN))
    hp hq hq2 hpq hp2 (hBel.isPGroup.to_le hB₁B) Sb hSb
  obtain ⟨E, hES, hEel, hEcard, hNE⟩ := exists_omega_normalized hgr hX hq hq3 hqn hSL hSq Sb hSmap
  refine ⟨S, E, hSL, hSq, hSmax, hES, hEel, hEcard, ?_, Sb, Sb.isPGroup', Sb.not_dvd_index, hSmap⟩
  rcases hbr with rfl | htriv
  ·
    exact Or.inl (le_pRank' hp (le_inf hBM (hB₁S.trans hNE)) hBel hBcard)
  ·
    have hB₁C : B₁ ≤ centralizer (E : Set G) := fun b hb =>
      Subgroup.centralizer_le hES (mem_centralizer_of_rhoL_eq_one hq hq2 hSL hSq
        (hB₁B.trans (hBM.trans hN) hb) (hB₁S hb) (htriv b _ hb))
    obtain ⟨j, hj⟩ := (hBel.isPGroup.to_le hB₁B).exists_card_eq
    have hj2 : 2 ≤ j := by
      rw [hj] at hB₁card
      exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hB₁card
    exact Or.inr (hj2.trans (le_pRank' hp (le_inf (hB₁B.trans hBM) hB₁C) (hBel.mono hB₁B) hj))

theorem r846_of_rank_three (hgr : CFSG.Open.GriessAllModelsStatement) (D : Data G)
    (hSg : SigmaStd D) (h76 : UC22.F07.R76Sig D) (h614 : UC6.R6_14 D) : UC22.F08.R846 D := by
  refine r846_of_key hgr D hSg h614 fun L hL n hX q hq hq3 hqn hqs hN p hpσ hpq hsp hOp => ?_
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpσ
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨S, E, hSL, hSp, hSmax, hES, hEel, hEcard, hrk, Sb, hSbp, hSbidx, hSbmap⟩ :=
    keyLemma3 hgr hL.1.le hN hX hq hq3 hqn hp hp2 hpq hOp (hSg.three_le p hpσ)
  have hEM : E ≤ D.M := hES.trans (hSL.trans hL.1.le)
  have h76p : PartOne.Section7.Conclusion76 D.M p := h76 p hpσ hp2 hsp
  have hG : rankThreeGamma 1 q E ≤ D.M := by
    rcases hrk with h3 | h2
    · exact UC6R77.rankThreeGamma_le_of_two_lt_pRank hpq h76p hEM hEel hEcard (by omega)
    · exact PartOne.Section7.rankThreeGamma_le_of_two_le_pRank_inf_centralizer hsp h76p hEM
        hEel.isPGroup (le_pRank' hq le_rfl hEel hEcard) h2
  exact ⟨S, E, hSL, hSp, hSmax, hES, hEel, hEcard, hG, Sb, hSbp, hSbidx, hSbmap⟩

end CFSG.LocalAnalysis.UniquenessCase.UC6S846
