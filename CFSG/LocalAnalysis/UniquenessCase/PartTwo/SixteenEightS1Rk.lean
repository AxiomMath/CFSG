module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Four

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Arith

private theorem s16e_card_GL_two_dvd_eight {d : ℕ} (hd : d ≤ 8) :
    Nat.card (GL (Fin d) (ZMod 2)) ∣ 5348063769211699200 := by
  rw [Matrix.card_GL_field, ZMod.card]
  interval_cases d <;> simp [Fin.prod_univ_succ]

private theorem s16e_not_cube_dvd_gl8 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
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

end Arith

section Generic

variable {T : Type*} [CommGroup T]

theorem s16e_pRank_lt_three_of_rk_le_eight [Finite T] (hT : ∀ v : T, v ^ 2 = 1) {d : ℕ}
    (hd : d ≤ 8) (hcard : Nat.card T = 2 ^ d) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (A : Subgroup (MulAut T)) : CFSG.Open.pRank p A < 3 := by
  by_contra hge
  push Not at hge
  obtain ⟨E, hEA, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt A
  have h1 : p ^ 3 ∣ Nat.card E := by
    rw [hEcard]
    exact pow_dvd_pow p hge
  have h2 : Nat.card E ∣ Nat.card A := Subgroup.card_dvd_of_le hEA
  have h3 : Nat.card A ∣ Nat.card (MulAut T) := Subgroup.card_subgroup_dvd_card A
  have h4 : Nat.card (MulAut T) ∣ Nat.card (GL (Fin d) (ZMod 2)) :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.N588.card_mulAut_dvd_card_GL
      (fun a b => mul_comm a b) hT hcard
  exact s16e_not_cube_dvd_gl8 hp hp2 hp3
    (h1.trans (h2.trans (h3.trans (h4.trans (s16e_card_GL_two_dvd_eight hd)))))

end Generic

section Sigma

variable {G : Type} [Group G] [Finite G]

theorem s16e_eq_three_of_mem_sig_of_rk_le_eight (D : Data G) (hx : DataExt D)
    (h4 : 3 < CFSG.Open.evenRank G) (h61 : UC6.R6_1 D) (h127 : R127 D) {V₀ V : Subgroup G}
    (h16 : Hyp16 D V₀ V) (hV : IsElemAbelian 2 V)
    (hrk : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) ≤ 8) {p : ℕ} (hp : p ∈ D.sig) : p = 3 := by
  by_contra hne
  obtain ⟨hprime, hp2⟩ := D.sig_prime p hp
  have h3 := s16c1610_three_le_pRank_mBar_of_four D hx h61 h127 h16 hV h4 hp
  have hT := s15_Infra_vtil_sq_eq_one V₀ V hV
  have := s16e_pRank_lt_three_of_rk_le_eight hT hrk (s16e_card_eq_two_pow_rk_top hT) hprime hp2
    hne (Mbar D.M V₀ V hV)
  omega

theorem s16e_sig_eq_three_of_rk_le_eight (D : Data G) (hx : DataExt D)
    (h4 : 3 < CFSG.Open.evenRank G) (h61 : UC6.R6_1 D) (h127 : R127 D) {V₀ V : Subgroup G}
    (h16 : Hyp16 D V₀ V) (hV : IsElemAbelian 2 V)
    (hrk : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) ≤ 8) : D.sig = {3} := by
  obtain ⟨p, hp⟩ := hx.sig_nonempty
  have hp3 := s16e_eq_three_of_mem_sig_of_rk_le_eight D hx h4 h61 h127 h16 hV hrk hp
  ext q
  constructor
  · intro hq
    exact (s16e_eq_three_of_mem_sig_of_rk_le_eight D hx h4 h61 h127 h16 hV hrk hq)
  · intro hq
    rw [Set.mem_singleton_iff.1 hq]
    rw [← hp3]
    exact hp

end Sigma

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
