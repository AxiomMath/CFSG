module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupAlmostSimple
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Shape
public import CFSG.Quasithin.Background.F617Bridge
public import CFSG.Quasithin.EmptyFaithful.Insp9Psl
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5L34
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L2b
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Tools
public import CFSG.Quasithin.Vol2.E2Eleven
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35Red2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.WeakClosure81 CFSG.Quasithin
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

theorem inFGroup_mono {Q : Type} [Group Q] [Finite Q] {j j' : ℕ} (hjj : j ≤ j')
    (h : InFGroup j Q) : InFGroup j' Q := by
  intro T hT Ω hΩ
  have hprod := h T hT Ω hΩ
  have hle : genEi j T Ω ≤ genEi j' T Ω := by
    refine iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => ?_
    have hK' : InCalEi j' T A K :=
      ⟨hK.1, hK.2.trans hjj⟩
    exact le_iSup₂_of_le A hA (le_iSup_of_le hAT (le_iSup₂_of_le K hK' le_rfl))
  refine Set.eq_univ_of_univ_subset ?_
  rw [← hprod]
  exact Set.mul_subset_mul hle subset_rfl

theorem pRank_two_top_le_of_autRank {A : Type} [Group A] [Finite A] {L : Subgroup A} [L.Normal]
    (hC : Subgroup.centralizer (L : Set A) = ⊥) {B : ℕ}
    (hbound : ∀ E : Subgroup (MulAut ↥L), (∀ e ∈ E, e * e = 1) → Nat.card E ≤ B)
    {k : ℕ} (hk : B ≤ 2 ^ k) :
    CFSG.Open.pRank 2 (⊤ : Subgroup A) ≤ k :=
  (CFSG.LocalAnalysis.UniquenessCase.UCK.pRank_le_pRank_mulAut (p := 2) L hC).trans
    (CFSG.SectionRank.pRank_le one_lt_two fun E _ hE =>
      (hbound E fun e he => by rw [← pow_two]; exact hE.2 e he).trans hk)

theorem inFGroup_of_almostSimple_l2Odd (h410 : W4Lem4_10)
    (hrank57 : CFSG.ComponentClassification.GSThmB.CFAutL2Rank)
    (hrankAll : CFSG.ComponentClassification.GSThmB.CFL2Rank)
    {A : Type} [Group A] [Finite A] {L : Subgroup A} [L.Normal] {q : ℕ}
    (hF : Fstar (⊤ : Subgroup A) = L)
    (hC : Subgroup.centralizer (L : Set A) = ⊥)
    (hL2 : IsL2Over17 ↥L q) (hq3 : 3 < q) (hodd : Odd q)
    (hquot : IsPGroup 2 (A ⧸ L)) :
    (9 < q → InFGroup 1 A) ∧ (q ≤ 9 → q ≠ 9 → InFGroup 2 A) ∧
      (q = 9 → InFGroup 3 A) := by
  classical
  obtain ⟨p, e, hp, hp2, hq, hfe, hm⟩ := hL2
  have hF6 : CFSG.Quasithin.F6.IsL2 p e ↥L :=
    CFSG.Quasithin.F617.isL2_of_lieModel_PSL_two hm
  obtain ⟨hsimpleL, hnabL⟩ :=
    CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8.simple_of_lieModel_psl_two hm
  have hLne : L ≠ ⊥ := by
    rintro rfl
    obtain ⟨a, b, hab⟩ := hnabL
    exact hab (Subsingleton.elim (a * b) (b * a))
  have hL2' : IsL2Over17 ↥L q := ⟨p, e, hp, hp2, hq, hfe, hm⟩
  have hLorder : 2 * Nat.card ↥L = q * (q ^ 2 - 1) := by
    rw [hq]
    exact CFSG.LocalAnalysis.WeakClosure81.two_mul_card_isL2_odd hp hp2 hF6
  obtain ⟨T⟩ := Sylow.nonempty (p := 2) (G := A)
  have hsup : L ⊔ (T : Subgroup A) = ⊤ :=
    CFSG.OrderReductions.PrimeQuotientFrattini.kernel_sup_sylow_eq_top 2 L hquot T
  have hT : IsSylowIn 2 (T : Subgroup A) ⊤ := isSylowIn_top T
  refine ⟨?_, ?_, ?_⟩
  · intro hq9
    have hq5 : p ^ e ≠ 5 := by rw [← hq]; omega
    rcases h410 A L (T : Subgroup A) q (inferInstance : L.Normal) hF
      ⟨p, e, hp, hp2, hq, hF6⟩ hq3 hodd hT hsup with
      hF1 | hAlt | ⟨hsmall, -⟩
    · exact hF1
    · exact absurd hAlt
        (CFSG.LocalAnalysis.WeakClosure81.not_isAlt_five_of_isL2_odd hp hp2 hq5 hF6)
    · exfalso
      have hq11 : 11 ≤ q := by
        obtain ⟨k, hk⟩ := hodd
        omega
      have hmono : 11 * (11 ^ 2 - 1) ≤ q * (q ^ 2 - 1) := by gcongr <;> omega
      rcases hsmall with h7 | h9 | hsym
      ·
        have hAsimple : IsSimpleGroup A := CFSG.Quasithin.Insp9.isSimpleGroup_psl_two h7
        have hLtop : L = ⊤ := (hAsimple.eq_bot_or_eq_top_of_normal L).resolve_left hLne
        have hAorder : 2 * Nat.card A = 7 * (7 ^ 2 - 1) :=
          CFSG.LocalAnalysis.WeakClosure81.two_mul_card_isL2_odd (by norm_num) (by norm_num) h7
        rw [hLtop, Subgroup.card_top] at hLorder
        norm_num at hAorder
        omega
      ·
        have hAsimple : IsSimpleGroup A := CFSG.Quasithin.Insp9.isSimpleGroup_psl_two h9
        have hLtop : L = ⊤ := (hAsimple.eq_bot_or_eq_top_of_normal L).resolve_left hLne
        have hAorder : 2 * Nat.card A = 9 * (9 ^ 2 - 1) :=
          CFSG.LocalAnalysis.WeakClosure81.two_mul_card_isL2_odd (by norm_num) (by norm_num) h9
        rw [hLtop, Subgroup.card_top] at hLorder
        norm_num at hAorder
        omega
      ·
        obtain ⟨esym⟩ := hsym
        have hA720 : Nat.card A = 720 := by
          rw [Nat.card_congr esym.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
            Fintype.card_fin]
          norm_num
        have hdvd : Nat.card ↥L ∣ Nat.card A := Subgroup.card_subgroup_dvd_card L
        have hle : Nat.card ↥L ≤ Nat.card A := Subgroup.card_le_card_group L
        rw [hA720] at hdvd hle
        have hge : 660 ≤ Nat.card ↥L := by omega
        have hne720 : Nat.card ↥L ≠ 720 := by
          intro heq
          have hLtop : L = ⊤ := Subgroup.eq_top_of_card_eq L (by rw [heq, hA720])
          have htop : IsSimpleGroup ↥(⊤ : Subgroup A) := hLtop ▸ hsimpleL
          have hAsimple : IsSimpleGroup A :=
            (Subgroup.topEquiv (G := A)).isSimpleGroup_congr.mp htop
          exact CFSG.Quasithin.E2.not_isSimpleGroup_perm_six
            (esym.isSimpleGroup_congr.mp hAsimple)
        have hlt : Nat.card ↥L < 720 := lt_of_le_of_ne hle hne720
        have hquot1 : 720 / Nat.card ↥L ≠ 1 := by
          intro hq1
          apply hne720
          have h := Nat.mul_div_cancel' hdvd
          rw [hq1, mul_one] at h
          omega
        have hquot0 : 0 < 720 / Nat.card ↥L := by
          exact Nat.div_pos (by omega) (by omega)
        have hquot2 : 2 ≤ 720 / Nat.card ↥L := by omega
        have h2 : 2 * Nat.card ↥L ≤ 720 := by
          calc 2 * Nat.card ↥L ≤ (720 / Nat.card ↥L) * Nat.card ↥L :=
                Nat.mul_le_mul_right _ hquot2
            _ = 720 := by rw [mul_comm, Nat.mul_div_cancel' hdvd]
        omega
  · intro hqle hqne9
    interval_cases q
    · exact absurd hodd (by norm_num)
    ·
      have hLodd : IsL2Odd ↥L 5 := by
        obtain ⟨r, f, hr, hr2, hq5, hf, hm5⟩ := hL2'
        have hr5 : r = 5 := by
          have hdvd : r ∣ 5 := by rw [hq5]; exact dvd_pow_self r (by omega)
          rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h | h
          · exact absurd h hr.one_lt.ne'
          · exact h
        subst hr5
        have hf1 : f = 1 := by
          have hpow : 5 ^ 1 = 5 ^ f := by rw [pow_one, ← hq5]
          exact (Nat.pow_right_injective (by norm_num : 2 ≤ 5) hpow).symm
        subst hf1
        simpa [IsL2Odd] using hm5
      have hbound : ∀ E : Subgroup (MulAut ↥L), (∀ x ∈ E, x * x = 1) →
          Nat.card E ≤ 4 := fun E hE => hrank57 ↥L (Or.inl hLodd) E hE
      have hm2 := pRank_two_top_le_of_autRank hC hbound (k := 2) (by norm_num)
      exact inFGroup_of_twoRank_le (inferInstance : L.Normal) hsimpleL hnabL hC
        ⟨(T : Subgroup A), hT, hsup⟩ hm2
    · exact absurd hodd (by norm_num)
    ·
      have hLodd : IsL2Odd ↥L 7 := by
        obtain ⟨r, f, hr, hr2, hq7, hf, hm7⟩ := hL2'
        have hr7 : r = 7 := by
          have hdvd : r ∣ 7 := by rw [hq7]; exact dvd_pow_self r (by omega)
          rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hdvd with h | h
          · exact absurd h hr.one_lt.ne'
          · exact h
        subst hr7
        have hf1 : f = 1 := by
          have hpow : 7 ^ 1 = 7 ^ f := by rw [pow_one, ← hq7]
          exact (Nat.pow_right_injective (by norm_num : 2 ≤ 7) hpow).symm
        subst hf1
        simpa [IsL2Odd] using hm7
      have hbound : ∀ E : Subgroup (MulAut ↥L), (∀ x ∈ E, x * x = 1) →
          Nat.card E ≤ 4 := fun E hE => hrank57 ↥L (Or.inr hLodd) E hE
      have hm2 := pRank_two_top_le_of_autRank hC hbound (k := 2) (by norm_num)
      exact inFGroup_of_twoRank_le (inferInstance : L.Normal) hsimpleL hnabL hC
        ⟨(T : Subgroup A), hT, hsup⟩ hm2
    · exact absurd hodd (by norm_num)
    · exact False.elim (hqne9 rfl)
  · intro hq9
    subst hq9
    have hbound : ∀ E : Subgroup (MulAut ↥L), (∀ x ∈ E, x * x = 1) →
        Nat.card E ≤ 8 := fun E hE => hrankAll ↥L p e hp hp2 hfe hm E hE
    have hm3 := pRank_two_top_le_of_autRank hC hbound (k := 3) (by norm_num)
    exact inFGroup_of_twoRank_le (inferInstance : L.Normal) hsimpleL hnabL hC
      ⟨(T : Subgroup A), hT, hsup⟩ hm3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
