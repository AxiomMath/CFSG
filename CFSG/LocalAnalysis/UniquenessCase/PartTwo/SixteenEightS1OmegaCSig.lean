module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeS
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Four
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NatRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16e_om_card_GL_eight :
    Nat.card (GL (Fin 8) (ZMod 2)) = 5348063769211699200 := by
  rw [Matrix.card_GL_field, ZMod.card]
  decide

private theorem s16e_om_not_cube_dvd_gl8 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ¬ p ^ 3 ∣ 5348063769211699200 := by
  intro h
  have hdvd : p ∣ 5348063769211699200 := (dvd_pow_self p (by norm_num)).trans h
  have hfac : (5348063769211699200 : ℕ) = 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 := by
    norm_num
  rw [hfac] at hdvd
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · rcases (Nat.Prime.dvd_mul hp).1 h3 with h4 | h4
        · rcases (Nat.Prime.dvd_mul hp).1 h4 with h5 | h5
          · rcases (Nat.Prime.dvd_mul hp).1 h5 with h6 | h6
            · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
                (hp.dvd_of_dvd_pow h6))
            · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
                (hp.dvd_of_dvd_pow h6))
          · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).1
              (hp.dvd_of_dvd_pow h5)
            subst this
            norm_num at h
        · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).1
            (hp.dvd_of_dvd_pow h4)
          subst this
          norm_num at h
      · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 17)).1 h3
        subst this
        norm_num at h
    · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 31)).1 h2
      subst this
      norm_num at h
  · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 127)).1 h1
    subst this
    norm_num at h

theorem s16e_om_mem_sig_eq_three (D : Data G) (hx : DataExt D)
    (h4 : 3 < CFSG.Open.evenRank G) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (h : Case162_7 D V₀ V hV L) {p : ℕ} (hp : p ∈ D.sig) : p = 3 := by
  obtain ⟨hprime, hp2⟩ := D.sig_prime p hp
  by_contra hp3
  have h3 := s16c1610_three_le_pRank_mBar_of_four D hx h61 h127 hset.hyp16 hV h4 hp
  obtain ⟨E, hE, -, hEcard⟩ := CFSG.SectionRank.exists_pRank hprime.one_lt (Mbar D.M V₀ V hV)
  have hdvdE : p ^ 3 ∣ Nat.card E := by
    rw [hEcard]
    exact pow_dvd_pow p h3
  have hdvdM : p ^ 3 ∣ Nat.card (Mbar D.M V₀ V hV) :=
    hdvdE.trans (Subgroup.card_dvd_of_le hE)
  have hcard := c23_card_mbar_v1Sub_eq D h1217 hset.hyp151 hV
  have hdvdM' : p ^ 3 ∣ Nat.card (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) := by
    rwa [hcard]
  have hdvdAut : Nat.card (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) ∣
      Nat.card (MulAut (vStar D.M V₀ V hV L)) := Subgroup.card_subgroup_dvd_card _
  have hsq : ∀ v : vStar D.M V₀ V hV L, v ^ 2 = 1 := s15_Infra_vtil_sq_eq_one _ V hV
  have hWcard : Nat.card (vStar D.M V₀ V hV L) = 2 ^ 8 := by
    rw [s16e_card_eq_two_pow_rk_top hsq]
    have h1 := s16c1610_rk_natOmegaPlus (H := lStar D.M V₀ V hV L)
      (U := wStar D.M V₀ V hV L) (n := 4) (a := 2) h.2.1
    rw [s15_Three_wStar_eq_top D h1217 hset.hyp151 hV hL h.2.2] at h1
    rw [h1]
  have hdvdGL : Nat.card (MulAut (vStar D.M V₀ V hV L)) ∣
      Nat.card (GL (Fin 8) (ZMod 2)) :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.N588.card_mulAut_dvd_card_GL
      (fun a b => mul_comm a b) hsq hWcard
  rw [s16e_om_card_GL_eight] at hdvdGL
  exact s16e_om_not_cube_dvd_gl8 hprime hp2 hp3 (hdvdM'.trans (hdvdAut.trans hdvdGL))

theorem s16e_om_sig_eq_three (D : Data G) (hx : DataExt D)
    (h4 : 3 < CFSG.Open.evenRank G) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (h : Case162_7 D V₀ V hV L) : D.sig = {3} := by
  obtain ⟨p, hp⟩ := hx.sig_nonempty
  have hp3 : p = 3 := s16e_om_mem_sig_eq_three D hx h4 h61 h127 h1217 hV hset hL hconc h hp
  ext q
  constructor
  · intro hq
    rw [Set.mem_singleton_iff]
    exact s16e_om_mem_sig_eq_three D hx h4 h61 h127 h1217 hV hset hL hconc h hq
  · intro hq
    have hq3 : q = 3 := Set.mem_singleton_iff.1 hq
    rw [hq3, ← hp3]
    exact hp

theorem s16e_omc_three_le_pRank (D : Data G) (hx : DataExt D)
    (h4 : 3 < CFSG.Open.evenRank G) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (h : Case162_7 D V₀ V hV L) : 3 ≤ CFSG.Open.pRank 3 (Mbar D.M V₀ V hV) := by
  have h3 : 3 ∈ D.sig := by
    rw [s16e_om_sig_eq_three D hx h4 h61 h127 h1217 hV hset hL hconc h]
    exact Set.mem_singleton 3
  exact s16c1610_three_le_pRank_mBar_of_four D hx h61 h127 hset.hyp16 hV h4 h3

theorem s16e_omc_dvd_card_mBar (D : Data G) (hx : DataExt D)
    (h4 : 3 < CFSG.Open.evenRank G) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (h : Case162_7 D V₀ V hV L) : 27 ∣ Nat.card ↥(Mbar D.M V₀ V hV) := by
  have h3 := s16e_omc_three_le_pRank D hx h4 h61 h127 h1217 hV hset hL hconc h
  obtain ⟨E, hE, -, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) (Mbar D.M V₀ V hV)
  have hdvdE : 3 ^ 3 ∣ Nat.card E := by
    rw [hEcard]
    exact pow_dvd_pow 3 h3
  exact hdvdE.trans (Subgroup.card_dvd_of_le hE)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
