module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Shape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritO2Hyp
public import CFSG.RankThree.PartOne.S11d.OutCentral
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Good
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Seventeen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16h_two_le_pRank_of_isPOnePlusTwo {X : Type} [Group X] [Finite X]
    (h : IsPOnePlusTwo 3 X) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨hext, hcard, -⟩ := h
  haveI : IsExtraspecial 3 X := hext
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  by_contra hle
  have hle1 : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 1 := by omega
  have hXp : IsPGroup 3 (⊤ : Subgroup X) :=
    IsPGroup.of_card (n := 3) (by rw [Subgroup.card_top, hcard])
  have hcyc : IsCyclic ↥(⊤ : Subgroup X) :=
    CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one (p := 3) (by norm_num) (by norm_num)
      (L := ⊤) (S := ⊤) le_rfl hXp (by
        rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.Quasithin.pRank_top_subtype]
        exact hle1)
  have hcycX : IsCyclic X := (Subgroup.topEquiv.isCyclic).mp hcyc
  have hnc : ¬ IsMulCommutative X := by
    intro hcomm
    letI : IsMulCommutative X := hcomm
    have htop : Subgroup.center X = ⊤ := Subgroup.center_eq_top
    have hsub : Subsingleton (X ⧸ Subgroup.center X) :=
      (QuotientGroup.subsingleton_iff (N := Subgroup.center X)).2 htop
    exact not_nontrivial_iff_subsingleton.mpr hsub hext.quotient_nontrivial
  exact hnc (by haveI := hcycX; infer_instance)

private theorem s16h_v1Sub_eq_v0_of_odd_card (D : Data G) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hodd : Odd (Nat.card ↥(lBar V₀ V hV L))) :
    v1Sub D.M V₀ V hV L = V₀ := by
  by_cases h0 : V₀ = ⊥
  · subst h0
    exact s16c167_v1Sub_eq_bot_of_inf_fixV D hV rfl
      (s16c167_wTil_inf_fixV_eq_bot_of_odd hV L hodd)
  · exact v1Sub_of_ne_bot D.M V₀ V hV L h0

theorem s16h_hyp154_of_central (D : Data G) (S : s16h_Std D)
    (h4 : 3 < CFSG.Open.evenRank G) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hδ : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2 →
      delta15 D.M V₀ V h.hyp151.isElemAbelian L <
        gamma15 D.M V₀ V h.hyp151.isElemAbelian L - 1)
    (hs : 1 < s15 D.M V₀ V h.hyp151.isElemAbelian L)
    (hU₂ : s16h_CondU2 D V₀ V L h.hyp151.isElemAbelian)
    (h3 : 3 ∉ D.sig)
    (hshape : (IsPOnePlusTwo 3 ↥(lBar V₀ V h.hyp151.isElemAbelian L) ∧
        rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V h.hyp151.isElemAbelian))
          (lBar V₀ V h.hyp151.isElemAbelian L)) = 6) ∨
      (IsElemAbelianOfRank 3 2 ↥(lBar V₀ V h.hyp151.isElemAbelian L) ∧
        rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V h.hyp151.isElemAbelian))
          (lBar V₀ V h.hyp151.isElemAbelian L)) = 6) ∨
      (IsElemAbelianOfRank 3 2 ↥(lBar V₀ V h.hyp151.isElemAbelian L) ∧
        rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V h.hyp151.isElemAbelian))
          (lBar V₀ V h.hyp151.isElemAbelian L)) = 8 ∧
        ∀ x ∈ lBar V₀ V h.hyp151.isElemAbelian L, x ≠ 1 →
          rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V h.hyp151.isElemAbelian))
            (Subgroup.zpowers x)) = 6))
    (hodd : Odd (Nat.card ↥(lBar V₀ V h.hyp151.isElemAbelian L))) : Hyp154 D V₀ V L := by
  have hV := h.hyp151.isElemAbelian
  obtain ⟨q, hq⟩ := S.hx.sig_nonempty
  have hqprime := (D.sig_prime q hq).1
  have hq2 : q ≠ 2 := (D.sig_prime q hq).2
  have hq3 : q ≠ 3 := fun heq => h3 (heq ▸ hq)
  have hσ3 : ∃ p ∈ D.sig, 3 ≤ CFSG.Open.pRank p D.M := ⟨q, hq, S.hx.three_le q hq⟩
  have hfix : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓ fixV
      (lBar V₀ V hV L) = ⊥ := s16c167_wTil_inf_fixV_eq_bot_of_odd hV L hodd
  have hBB : s16h_BlockBound (Mbar D.M V₀ V hV) (lBar V₀ V hV L) q 1 := by
    intro E hE hEab
    have hle := s16h_card_le_mul_cent_of_shape (s15_Infra_vtil_sq_eq_one V₀ V hV)
      hqprime hq2 hq3 hfix hshape (hE.trans inf_le_right) hEab
    simpa using hle
  have hv1 : v1Sub D.M V₀ V hV L ≤ V₀ := (s16h_v1Sub_eq_v0_of_odd_card D hV hodd).le
  by_cases hs2 : s15 D.M V₀ V hV L = 2
  · obtain ⟨E, hEM, hEab, hEcard⟩ :=
      c23_exists_elemAbelian_card_pow (p := q) (M := D.M) (k := 3) hqprime
        (by rw [UC6.groupPRank_eq_pRank]; exact S.hx.three_le q hq)
    have hEn := s16h_barSub_le_normalizer_of_s15_le_two D h.hyp151 (by omega)
      (hqprime.odd_of_ne_two hq2) hEM hEab
    have hcard := s16h_card_le_pow_mul_card_inf_preBarSub D h.hyp151 hBB hEM hEab hEn
    have hPcard : q ^ 2 ≤ Nat.card ↥(E ⊓ preBarSub D.M V₀ V hV
        (centSub (wTil V₀ V hV L))) := by
      rw [hEcard, pow_one] at hcard
      have h : q * q ^ 2 ≤ q * Nat.card ↥(E ⊓ preBarSub D.M V₀ V hV
          (centSub (wTil V₀ V hV L))) := by
        calc q * q ^ 2 = q ^ 3 := by ring
          _ ≤ q * Nat.card ↥(E ⊓ preBarSub D.M V₀ V hV
              (centSub (wTil V₀ V hV L))) := hcard
      exact Nat.le_of_mul_le_mul_left h hqprime.pos
    have hW1 := s16h_uniqueMax_of_card_le D S.h61 S.h127 h hq (S.hx.three_le q hq) hEab hPcard
    exact s16h_hyp154_of_unique₁_two D h.hyp151 hs2
      (s16h_unique₁_of_wSub D h.hyp151 hv1 hW1) (hδ hs2)
  · have hs3le : 3 ≤ s15 D.M V₀ V hV L := by omega
    by_cases hs4 : 3 < s15 D.M V₀ V hV L
    · exact s16h_hyp154_of_condU2 D S.h61 h hσ3 hU₂ hs4
    · have hs_eq3 : s15 D.M V₀ V hV L = 3 := by omega
      exact s16h_hyp154_of_blockBound_one D S.h61 S.h127 h hs_eq3 hq
        (S.hSig.sig1_sp q (hσ ▸ hq)) (S.hx.four_le h4 q hq) hv1 hBB

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
