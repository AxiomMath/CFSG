module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Blocks
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Rank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16h_not_quasisimple_of_card_dvd_prime {X : Type*} [Group X] {p : ℕ}
    (hp : p.Prime) (h : Nat.card X ∣ p) : ¬ CFSG.Open.IsQuasisimple X := by
  intro hq
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic X := isCyclic_of_card_dvd_prime h
  have hsub : Subsingleton (X ⧸ Subgroup.center X) :=
    QuotientGroup.subsingleton_iff.mpr Subgroup.center_eq_top
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hq.2
  exact not_nontrivial_iff_subsingleton.mpr hsub inferInstance

private theorem s16h_prime_card_not_quasisimple {X : Type*} [Group X] {p : ℕ} (hp : p.Prime)
    (h : Nat.card X = p) : ¬ CFSG.Open.IsQuasisimple X :=
  s16h_not_quasisimple_of_card_dvd_prime hp (by rw [h])

theorem s16h_conc4_133_of_prime_card {W : Type} [CommGroup W] {A L : Subgroup (MulAut W)}
    {t : MulAut W} {p : ℕ} (hp : p.Prime) (hL : Nat.card ↥L = p) (h : Conc4_136W A t L) :
    Conc4_133 A t L := by
  obtain ⟨-, -, hcases⟩ := h
  rcases hcases with h133 | ⟨K, hK, g, -, -, hKL, -⟩ | ⟨hcomp, -⟩ | ⟨-, -, hcomp, -⟩
  · exact h133
  · have hKle : K ≤ L := by rw [hKL]; exact le_sup_left
    have hdK : Nat.card ↥K ∣ p := by
      rw [← hL]
      exact Subgroup.card_dvd_of_le hKle
    exact absurd hK.2.2 (s16h_not_quasisimple_of_card_dvd_prime hp hdK)
  · exact absurd hcomp.2.2 (s16h_prime_card_not_quasisimple hp hL)
  · exact absurd hcomp.2.2 (s16h_prime_card_not_quasisimple hp hL)

theorem s16h_rk_wTil_le_three_of_chi (D : Data G) {V₀ V L : Subgroup G}
    (h : Setting16 D V₀ V L) (hc : Conc4_136 D V₀ V h.hyp151.isElemAbelian L) {p : ℕ}
    (hp : p.Prime) (hLp : IsCyclicOrd ↥(lBar V₀ V h.hyp151.isElemAbelian L) p)
    (hχ : ∀ n ∈ Mbar D.M V₀ V h.hyp151.isElemAbelian,
      n ∈ normalizer ((lBar V₀ V h.hyp151.isElemAbelian L : Subgroup _) : Set _) →
        ∀ l ∈ lBar V₀ V h.hyp151.isElemAbelian L, n * l = l * n) :
    rk ↥(wTil V₀ V h.hyp151.isElemAbelian L) ≤ 3 := by
  haveI : Finite (Vtil V₀ V h.hyp151.isElemAbelian) := inferInstance
  change rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V h.hyp151.isElemAbelian))
    (lBar V₀ V h.hyp151.isElemAbelian L)) ≤ 3
  obtain ⟨t, htM, -, -, htr, hW⟩ := hc
  have h133 := s16h_conc4_133_of_prime_card hp hLp.2 hW
  obtain ⟨q, hq, -, hLt, hind, -⟩ := h133
  rcases s16h_bl_mem_normalizer_or_rk hW hind htM htr with hnorm | hrk
  · exfalso
    have hcomm := hχ t htM hnorm
    have hbot : ⁅lBar V₀ V h.hyp151.isElemAbelian L, Subgroup.zpowers t⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro l hl
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      exact (show Commute t l from hcomm l hl).zpow_left k |>.eq
    exact hLt hbot
  · exact hrk

theorem s16h_card_wTil_of_chi_eq_one (D : Data G) {V₀ V L : Subgroup G}
    (h : Setting16 D V₀ V L) (hc : Conc4_136 D V₀ V h.hyp151.isElemAbelian L) {p : ℕ}
    (hp : p.Prime) (hLp : IsCyclicOrd ↥(lBar V₀ V h.hyp151.isElemAbelian L) p)
    (hχ : ∀ n ∈ Mbar D.M V₀ V h.hyp151.isElemAbelian,
      n ∈ normalizer ((lBar V₀ V h.hyp151.isElemAbelian L : Subgroup _) : Set _) →
        ∀ l ∈ lBar V₀ V h.hyp151.isElemAbelian L, n * l = l * n) :
    (p = 3 ∨ p = 7) ∧ Nat.card ↥(wTil V₀ V h.hyp151.isElemAbelian L) = p + 1 := by
  haveI : Finite (Vtil V₀ V h.hyp151.isElemAbelian) := inferInstance
  have hw : rk ↥(wTil V₀ V h.hyp151.isElemAbelian L) =
      rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V h.hyp151.isElemAbelian))
        (lBar V₀ V h.hyp151.isElemAbelian L)) := rfl
  have hm : rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V h.hyp151.isElemAbelian))
      (lBar V₀ V h.hyp151.isElemAbelian L)) ≤ 3 := by
    rw [← hw]
    exact s16h_rk_wTil_le_three_of_chi D h hc hp hLp hχ
  obtain ⟨t, htM, -, -, htr, hW⟩ := hc
  have h133 := s16h_conc4_133_of_prime_card hp hLp.2 hW
  obtain ⟨q, hq, -, hLt, hind, hrows⟩ := h133
  suffices hmain : (p = 3 ∧ rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V h.hyp151.isElemAbelian))
        (lBar V₀ V h.hyp151.isElemAbelian L)) = 2) ∨
      (p = 7 ∧ rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V h.hyp151.isElemAbelian))
        (lBar V₀ V h.hyp151.isElemAbelian L)) = 3) by
    rcases hmain with ⟨hp3, hr2⟩ | ⟨hp7, hr3⟩
    · have hcard : Nat.card ↥(wTil V₀ V h.hyp151.isElemAbelian L) =
          2 ^ rk ↥(wTil V₀ V h.hyp151.isElemAbelian L) :=
        card_eq_two_pow (s15_Infra_vtil_sq_eq_one V₀ V h.hyp151.isElemAbelian)
          (wTil V₀ V h.hyp151.isElemAbelian L)
      refine ⟨Or.inl hp3, ?_⟩
      rw [hp3, hcard, hw, hr2]
      norm_num
    · have hcard : Nat.card ↥(wTil V₀ V h.hyp151.isElemAbelian L) =
          2 ^ rk ↥(wTil V₀ V h.hyp151.isElemAbelian L) :=
        card_eq_two_pow (s15_Infra_vtil_sq_eq_one V₀ V h.hyp151.isElemAbelian)
          (wTil V₀ V h.hyp151.isElemAbelian L)
      refine ⟨Or.inr hp7, ?_⟩
      rw [hp7, hcard, hw, hr3]
      norm_num
  rcases hrows with ⟨hc3, hr⟩ | ⟨hc5, hr⟩ | ⟨hP, hr⟩ | ⟨hE, hr, -, -⟩ | ⟨hc7, hr⟩ |
    ⟨r, m', hpm, hr2, hE, hreq, -⟩ | ⟨hE, hr, -⟩
  · have hp3 : p = 3 := hLp.2.symm.trans hc3.2
    refine Or.inl ⟨hp3, ?_⟩
    rcases hr with hr | hr | hr <;> omega
  · exfalso
    omega
  · exfalso
    have h3p : 3 ^ 3 = p := hP.2.1.symm.trans hLp.2
    exact absurd (hp.pow_eq_iff.mp h3p).2 (by norm_num)
  · exfalso
    have h32p : 3 ^ 2 = p := (s16h_dc_card_of_elem hE).symm.trans hLp.2
    exact absurd (hp.pow_eq_iff.mp h32p).2 (by norm_num)
  · have hp7 : p = 7 := hLp.2.symm.trans hc7.2
    refine Or.inr ⟨hp7, ?_⟩
    rcases hr with hr | hr <;> omega
  · exfalso
    have hqp : q ^ r = p := (s16h_dc_card_of_elem hE).symm.trans hLp.2
    have hr1 : r = 1 := (hp.pow_eq_iff.mp hqp).2
    omega
  · exfalso
    have h32p : 3 ^ 2 = p := (s16h_dc_card_of_elem hE).symm.trans hLp.2
    exact absurd (hp.pow_eq_iff.mp h32p).2 (by norm_num)

theorem s16h_gamma_le_three_of_chi_eq_one (D : Data G) {V₀ V L : Subgroup G}
    (h : Setting16 D V₀ V L) (hc : Conc4_136 D V₀ V h.hyp151.isElemAbelian L) {p : ℕ}
    (hp : p.Prime) (hLp : IsCyclicOrd ↥(lBar V₀ V h.hyp151.isElemAbelian L) p)
    (hχ : ∀ n ∈ Mbar D.M V₀ V h.hyp151.isElemAbelian,
      n ∈ normalizer ((lBar V₀ V h.hyp151.isElemAbelian L : Subgroup _) : Set _) →
        ∀ l ∈ lBar V₀ V h.hyp151.isElemAbelian L, n * l = l * n) :
    gamma15 D.M V₀ V h.hyp151.isElemAbelian L ≤ 3 :=
  (c8_gamma15_le_rk_wTil D h.hyp151.hyp125 h.hyp151.isElemAbelian L).trans
    (s16h_rk_wTil_le_three_of_chi D h hc hp hLp hχ)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
