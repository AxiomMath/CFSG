module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Rank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritS2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3Lift
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private lemma s16h_e3_CycTwoRank_le_stabSub_wTil {V₀ V L E : Subgroup G}
    (hV : IsElemAbelian 2 V)
    (hEn : barSub V₀ V hV E ≤
      Subgroup.normalizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV)))) :
    barSub V₀ V hV E ≤ stabSub (wTil V₀ V hV L) := by
  intro g hg
  have hgN : g ∈ Subgroup.normalizer
      (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := hEn hg
  have hgiN : g⁻¹ ∈ Subgroup.normalizer
      (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
    (Subgroup.normalizer _).inv_mem hgN
  rw [mem_stabSub]
  intro u
  constructor
  · intro hu
    have h2 : g⁻¹ (g u) ∈ wTil V₀ V hV L :=
      commSub_top_stable151b (X := barSub V₀ V hV L) (g := g⁻¹)
        (fun x hx => (Subgroup.mem_normalizer_iff.1 hgiN x).1 hx) (g u) hu
    simpa using h2
  · intro hu
    exact commSub_top_stable151b (X := barSub V₀ V hV L) (g := g)
      (fun x hx => (Subgroup.mem_normalizer_iff.1 hgN x).1 hx) u hu

theorem s16h_e3_CycTwoRank_two_le
    (D : Data G) (S : s16h_Std D) (hr3 : CFSG.Open.evenRank G = 3)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L)
    (h3 : 3 ∈ D.sig) (hs2 : s15 D.M V₀ V hV L ≤ 2)
    (hW : ¬ ∀ w ∈ wSub V₀ V hV L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))) :
    2 ≤ CFSG.Open.pRank 3 (autSub (Mbar D.M V₀ V hV ⊓
      Subgroup.normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))))
      (wTil V₀ V hV L)) := by
  have hE : IsElemAbelian 2 V := h.hyp151.isElemAbelian
  have hVeq : hV = hE := Subsingleton.elim hV hE
  have hs2' : s15 D.M V₀ V hE L ≤ 2 := hVeq ▸ hs2
  have hW' : ¬ ∀ w ∈ wSub V₀ V hE L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := hVeq ▸ hW
  have hmain : 2 ≤ CFSG.Open.pRank 3 (autSub (Mbar D.M V₀ V hE ⊓
      Subgroup.normalizer (lBar V₀ V hE L : Set (MulAut (Vtil V₀ V hE))))
      (wTil V₀ V hE L)) := by
    have hMs : D.M ≤ stabTil V₀ V :=
      le_stabTil h.hyp16.hyp125.pairFacts.le_normalizer
        h.hyp16.hyp125.pairFacts.le_normalizer₀
    have hM : D.M ≤ normalizer (V : Set G) := h.hyp151.hyp125.pairFacts.le_normalizer
    have hp3 : (3 : ℕ).Prime := Nat.prime_three
    have h3rank : 3 ≤ CFSG.Open.pRank 3 D.M := by
      rw [s16h_pRank_eq_three D S hr3 h3]
    have h3rank' : 3 ≤ CFSG.pRank 3 D.M := by
      rw [UC6.groupPRank_eq_pRank]
      exact h3rank
    obtain ⟨E, hEM, hEea, hEcard⟩ :=
      c23_exists_elemAbelian_card_pow (p := 3) (M := D.M) (k := 3) hp3 h3rank'
    have hEn : barSub V₀ V hE E ≤
        Subgroup.normalizer (barSub V₀ V hE L : Set (MulAut (Vtil V₀ V hE))) :=
      s16h_barSub_le_normalizer_of_s15_le_two D h.hyp151 hs2'
        (by norm_num : Odd 3) hEM hEea
    have hQea : IsElemAbelian 3 (barSub V₀ V hE E) :=
      s16h_barSub_isElemAbelian hE hEea
    have hQstab : barSub V₀ V hE E ≤ stabSub (wTil V₀ V hE L) :=
      s16h_e3_CycTwoRank_le_stabSub_wTil hE hEn
    have hQN : barSub V₀ V hE E ≤ Mbar D.M V₀ V hE ⊓
        Subgroup.normalizer (lBar V₀ V hE L : Set (MulAut (Vtil V₀ V hE))) :=
      le_inf (barSub_mono V₀ V hE hEM) (by simpa [lBar] using hEn)
    have hAE : autSub (barSub V₀ V hE E) (wTil V₀ V hE L) ≤
        autSub (Mbar D.M V₀ V hE ⊓
          Subgroup.normalizer (lBar V₀ V hE L : Set (MulAut (Vtil V₀ V hE))))
          (wTil V₀ V hE L) :=
      autSub_mono hQN (wTil V₀ V hE L)
    have hAab : IsElemAbelian 3 (autSub (barSub V₀ V hE E) (wTil V₀ V hE L)) := by
      have h := (hQea.subgroupOf (stabSub (wTil V₀ V hE L))).map
        (resHom (wTil V₀ V hE L))
      simpa [autSub] using h
    have hcard1 : Nat.card (autSub (barSub V₀ V hE E) (wTil V₀ V hE L)) *
        Nat.card ↥(barSub V₀ V hE E ⊓ centSub (wTil V₀ V hE L)) =
        Nat.card ↥(barSub V₀ V hE E) :=
      card_autSub_mul hQstab
    have hcard2 := s16h_card_mul_card_barSub_inf (V₀ := V₀) (V := V) (M := D.M) (E := E)
      hE hEM hM hMs (centSub (wTil V₀ V hE L))
    have hnot9 : ¬ 9 ≤ Nat.card ↥(E ⊓ preBarSub D.M V₀ V hE
        (centSub (wTil V₀ V hE L))) := by
      intro h9
      have hPcard : 3 ^ 2 ≤ Nat.card ↥(E ⊓ preBarSub D.M V₀ V h.hyp151.isElemAbelian
          (centSub (wTil V₀ V h.hyp151.isElemAbelian L))) := by
        rw [show (3 : ℕ) ^ 2 = 9 by norm_num]
        exact h9
      exact hW' (s16h_uniqueMax_of_card_le D S.h61 S.h127 h h3 h3rank hEea hPcard)
    have hlt9 : Nat.card ↥(E ⊓ preBarSub D.M V₀ V hE
        (centSub (wTil V₀ V hE L))) < 9 := not_le.1 hnot9
    have hdvd : Nat.card ↥(E ⊓ preBarSub D.M V₀ V hE
        (centSub (wTil V₀ V hE L))) ∣ 3 ^ 3 := by
      rw [← hEcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hdle : Nat.card ↥(E ⊓ preBarSub D.M V₀ V hE
        (centSub (wTil V₀ V hE L))) ≤ 3 := by
      obtain ⟨k, _hk3, hk⟩ := (Nat.dvd_prime_pow (p := 3) (m := 3) hp3).1 hdvd
      have hk1 : k ≤ 1 := by
        by_contra hcon
        have h2 : 2 ≤ k := by omega
        have h9 : 9 ≤ 3 ^ k := by
          calc 9 = 3 ^ 2 := by norm_num
            _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h2
        rw [← hk] at h9
        omega
      calc Nat.card ↥(E ⊓ preBarSub D.M V₀ V hE (centSub (wTil V₀ V hE L)))
          = 3 ^ k := hk
        _ ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
        _ = 3 := by norm_num
    have hcount : Nat.card ↥E =
        Nat.card (autSub (barSub V₀ V hE E) (wTil V₀ V hE L)) *
          Nat.card ↥(E ⊓ preBarSub D.M V₀ V hE (centSub (wTil V₀ V hE L))) := by
      have hEq : Nat.card ↥E *
            Nat.card ↥(barSub V₀ V hE E ⊓ centSub (wTil V₀ V hE L)) =
          (Nat.card (autSub (barSub V₀ V hE E) (wTil V₀ V hE L)) *
              Nat.card ↥(E ⊓ preBarSub D.M V₀ V hE (centSub (wTil V₀ V hE L)))) *
            Nat.card ↥(barSub V₀ V hE E ⊓ centSub (wTil V₀ V hE L)) := by
        calc Nat.card ↥E *
              Nat.card ↥(barSub V₀ V hE E ⊓ centSub (wTil V₀ V hE L))
            = Nat.card ↥(barSub V₀ V hE E) *
              Nat.card ↥(E ⊓ preBarSub D.M V₀ V hE (centSub (wTil V₀ V hE L))) := hcard2
          _ = (Nat.card (autSub (barSub V₀ V hE E) (wTil V₀ V hE L)) *
                Nat.card ↥(barSub V₀ V hE E ⊓ centSub (wTil V₀ V hE L))) *
              Nat.card ↥(E ⊓ preBarSub D.M V₀ V hE (centSub (wTil V₀ V hE L))) := by
                rw [← hcard1]
          _ = (Nat.card (autSub (barSub V₀ V hE E) (wTil V₀ V hE L)) *
                Nat.card ↥(E ⊓ preBarSub D.M V₀ V hE (centSub (wTil V₀ V hE L)))) *
              Nat.card ↥(barSub V₀ V hE E ⊓ centSub (wTil V₀ V hE L)) := by ring
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hEq
    have h9aut : 9 ≤ Nat.card (autSub (barSub V₀ V hE E) (wTil V₀ V hE L)) := by
      have hle : Nat.card (autSub (barSub V₀ V hE E) (wTil V₀ V hE L)) *
          Nat.card ↥(E ⊓ preBarSub D.M V₀ V hE (centSub (wTil V₀ V hE L))) ≤
          Nat.card (autSub (barSub V₀ V hE E) (wTil V₀ V hE L)) * 3 :=
        Nat.mul_le_mul_left _ hdle
      have hle' : 27 ≤ Nat.card (autSub (barSub V₀ V hE E) (wTil V₀ V hE L)) * 3 := by
        rw [← hcount, hEcard] at hle
        norm_num at hle
        exact hle
      have hle'' : 9 * 3 ≤ Nat.card (autSub (barSub V₀ V hE E) (wTil V₀ V hE L)) * 3 := by
        simpa using hle'
      exact Nat.le_of_mul_le_mul_right hle'' (by norm_num)
    have hApg : IsPGroup 3 (autSub (barSub V₀ V hE E) (wTil V₀ V hE L)) := hAab.isPGroup
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 3)).1 hApg
    have hk2 : 2 ≤ k := by
      have h1 : 3 ^ 2 ≤ 3 ^ k := by
        rw [← hk]
        norm_num
        exact h9aut
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h1
    have hle := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hAE hAab hk
    omega
  rw [hVeq]
  exact hmain

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
