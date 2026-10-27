module

public import CFSG.RankThree.PartOne.CTP.StrongPQuotient
public import CFSG.LocalAnalysis.SignalizerFunctor.MinimalNormal
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public section

namespace CFSG.RankThree.PartOne

open StrongP

universe u

theorem StrongP.false_of_solvable (p : ℕ) [Fact p.Prime] :
    ∀ (n : ℕ) (H : Type u) [Group H] [Finite H], Nat.card H = n → Group.IsSolvable H →
      ∀ (Y E : Subgroup H), IsStronglyPEmbedded p Y → E ≤ Y → CFSG.IsElementaryAbelian p E →
        Nat.card E = p ^ 2 → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H _ _ hn hsol Y E hY hEY hEab hEc
  have hnt : Nontrivial H := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hY.1 (Subsingleton.elim _ _)
  obtain ⟨M, hMn, hM1, -, q, r, hq, hr, -, hMc⟩ :=
    CFSG.SignalizerFunctor.Helpers.solvable_minimal_normal_exists (GroupType := H)
  have hp := (Fact.out : p.Prime)
  by_cases hqp : q = p
  ·
    subst hqp
    obtain ⟨P, hP, hPY⟩ := hY.exists_isSylowOf_le
    have hPsyl : ¬ q ∣ P.index := by
      simpa [Subgroup.relIndex_top_right] using hP.2.2
    have hMle : M ≤ (hP.2.1.toSylow hPsyl : Subgroup H) :=
      (IsPGroup.of_card hMc).le_sylow_of_normal (hP.2.1.toSylow hPsyl)
    have hMY : M ≤ Y := hMle.trans hPY
    refine hY.not_dvd_card_of_normal_le hMY ?_
    rw [hMc]
    exact dvd_pow_self q (by omega)
  · have hpM : ¬ p ∣ Nat.card M := by
      rw [hMc]
      intro hd
      exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hd)).symm
    have hpow : ∀ x : E, (x : H) ^ p = 1 := fun x =>
      elemPow_eq_one_of_isElementaryAbelian (A := E) (x : H) x.2
    have hpowE : ∀ x : E, x ^ p = 1 := fun x => Subtype.ext (hpow x)
    have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
      p hp E M hpowE hEc hpM
      (fun e _ => by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top e)
    have hMY : M ≤ Y := by
      rw [hgen]
      refine iSup₂_le fun x hx1 => inf_le_right.trans (hY.centralizer_le ?_ (hpow x) (hEY x.2))
      exact fun h => hx1 (Subtype.ext h)
    have hlt : Nat.card (H ⧸ M) < n := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup M
      have h2 : 1 < Nat.card M := (Subgroup.one_lt_card_iff_ne_bot M).mpr hM1
      have h3 : 0 < Nat.card (H ⧸ M) := Nat.card_pos
      rw [← hn, h1]
      nlinarith
    have := hEab
    exact ih (Nat.card (H ⧸ M)) hlt (H ⧸ M) rfl inferInstance (Y.map (QuotientGroup.mk' M))
      (E.map (QuotientGroup.mk' M)) (hY.map_quotient hMY hpM) (Subgroup.map_mono hEY)
      (CFSG.IsElementaryAbelian.map (QuotientGroup.mk' M))
      (by rw [card_map_quotient_of_coprime (CFSG.IsElementaryAbelian.isPGroup p E) hpM, hEc])

theorem IsStronglyPEmbedded.false_of_generation {p : ℕ} [Fact p.Prime] {H : Type u} [Group H]
    [Finite H] {Y : Subgroup H} (hY : IsStronglyPEmbedded p Y) {E : Subgroup H} (hEY : E ≤ Y)
    [CFSG.IsElementaryAbelian p E] (hE : Nat.card E = p ^ 2) {S : Subgroup H} [S.Normal]
    (hgen : S ≤ Subgroup.closure {k : H | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k})
    (hsol : Group.IsSolvable (H ⧸ S)) : False := by
  have hSY : S ≤ Y := by
    refine hgen.trans ((Subgroup.closure_le Y).mpr ?_)
    rintro k ⟨x, hxE, hx1, hk⟩
    exact hY.centralizer_le hx1 (elemPow_eq_one_of_isElementaryAbelian (A := E) x hxE) (hEY hxE)
      (Subgroup.mem_centralizer_singleton_iff.mpr hk)
  have hpS := hY.not_dvd_card_of_normal_le hSY
  exact StrongP.false_of_solvable p _ (H ⧸ S) rfl hsol (Y.map (QuotientGroup.mk' S))
    (E.map (QuotientGroup.mk' S)) (hY.map_quotient hSY hpS) (Subgroup.map_mono hEY)
    (CFSG.IsElementaryAbelian.map (QuotientGroup.mk' S))
    (by rw [card_map_quotient_of_coprime (CFSG.IsElementaryAbelian.isPGroup p E) hpS, hE])

end CFSG.RankThree.PartOne
