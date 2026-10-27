module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalFixedSubgroups
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8TwoSp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

private theorem s168e3_sp_six_four_arithmetic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ 4 ^ 2 - 1)
    (h : p ^ 2 ∣ 2 ^ 18 * 3 ^ 4 * 5 ^ 3 * 7 * 13 * 17) : False := by
  have hpN : p ∣ 2 ^ 18 * 3 ^ 4 * 5 ^ 3 * 7 * 13 * 17 :=
    (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans h
  have hvals : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 17 := by
    rcases hp.dvd_mul.mp hpN with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · rcases hp.dvd_mul.mp h with h | h
          · rcases hp.dvd_mul.mp h with h | h
            · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
                (hp.dvd_of_dvd_pow h))
            · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
                (hp.dvd_of_dvd_pow h)))
          · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp
              (hp.dvd_of_dvd_pow h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl
            ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).mp h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13)).mp h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 17)).mp h)))))
  rcases hvals with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hp2 rfl
  · exact hpq (by norm_num)
  · exact hpq (by norm_num)
  · norm_num at h
  · norm_num at h
  · norm_num at h

private theorem s168e3_sp_six_eight_arithmetic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ 8 ^ 2 - 1)
    (h : p ^ 2 ∣ 2 ^ 27 * 3 ^ 7 * 5 * 7 ^ 3 * 13 * 19 * 73) : False := by
  have hpN : p ∣ 2 ^ 27 * 3 ^ 7 * 5 * 7 ^ 3 * 13 * 19 * 73 :=
    (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans h
  have hvals : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 19 ∨ p = 73 := by
    rcases hp.dvd_mul.mp hpN with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · rcases hp.dvd_mul.mp h with h | h
          · rcases hp.dvd_mul.mp h with h | h
            · rcases hp.dvd_mul.mp h with h | h
              · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
                  (hp.dvd_of_dvd_pow h))
              · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
                  (hp.dvd_of_dvd_pow h)))
            · exact Or.inr (Or.inr (Or.inl
                ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h)))
          · exact Or.inr (Or.inr (Or.inr (Or.inl
              ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).mp
                (hp.dvd_of_dvd_pow h)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13)).mp h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 19)).mp h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 73)).mp h))))))
  rcases hvals with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hp2 rfl
  · exact hpq (by norm_num)
  · norm_num at h
  · exact hpq (by norm_num)
  · norm_num at h
  · norm_num at h
  · norm_num at h

private theorem s168e3_false_of_sp_six_natural_aux
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    {K : Type} [fieldK : Field K] [finiteK : Finite K]
    {a : ℕ} (ha : a = 2 ∨ a = 3) (hK : Nat.card K = 2 ^ a)
    (hR : (FFModel.nat (StatedSp 3 K)).Realizes (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L))) : False := by
  let Γ : Subgroup (GL (Fin 3 ⊕ Fin 3) K) := StatedSp 3 K
  have hRΓ : (FFModel.nat Γ).Realizes (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) := by
    simpa only [Γ] using hR
  have hKq : Nat.card K = 4 ∨ Nat.card K = 8 := by
    rcases ha with rfl | rfl
    · left
      rw [hK]
      norm_num
    · right
      rw [hK]
      norm_num
  obtain ⟨p, hpσ⟩ := c.std.hx.sig_nonempty
  have hp : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  have hpq : p ∣ Nat.card K ^ 2 - 1 := by
    by_contra hpq
    have hAut : ¬ p ∣ Nat.card (RingAut K) := by
      rw [s16k_card_ringAut_of_card hK]
      rcases ha with rfl | rfl
      · intro h2
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
      · intro h3
        have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
        exact hpq (by rw [hp3, hK]; norm_num)
    have hUnits : ¬ p ∣ Nat.card Kˣ := by
      rw [s16k_card_units_of_card hK]
      rcases ha with rfl | rfl
      · intro h3
        have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
        exact hpq (by rw [hp3, hK]; norm_num)
      · intro h7
        have hp7 : p = 7 :=
          (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).mp h7
        exact hpq (by rw [hp7, hK]; norm_num)
    obtain ⟨F, hFN, hFel, hFcard⟩ :=
      s168e3_exists_matrix_elem_of_natural_of_coprime c hs Γ hRΓ
        (addCommutantScalar_statedSp (m := 3) (K := K)) hpσ hAut
    obtain ⟨μ, -, hμ⟩ := s16g_exists_mult_statedSp (m := 3) (by norm_num) (K := K)
    have hμF : ∀ x : ↥(Subgroup.normalizer (Γ : Set (GL (Fin 3 ⊕ Fin 3) K))),
        (x : GL (Fin 3 ⊕ Fin 3) K) ∈ F → μ x = 1 :=
      s16g_mu_eq_one_of_coprime μ hFN hp hFel.isPGroup hUnits
    have hFΓ : F ≤ Γ := by
      intro x hx
      have hxN : x ∈ Subgroup.normalizer (Γ : Set (GL (Fin 3 ⊕ Fin 3) K)) := hFN hx
      exact (hμ ⟨x, hxN⟩).1 (hμF ⟨x, hxN⟩ hx)
    have hdvd : p ^ 2 ∣ Nat.card Γ := by
      rw [← hFcard]
      exact Subgroup.card_dvd_of_le hFΓ
    rcases hKq with hK4 | hK8
    · have hpq4 : ¬ p ∣ 4 ^ 2 - 1 := by simpa [hK4] using hpq
      have hSp4 : Nat.card Γ = 2 ^ 18 * 3 ^ 4 * 5 ^ 3 * 7 * 13 * 17 := by
        change Nat.card (StatedSp 3 K) = 2 ^ 18 * 3 ^ 4 * 5 ^ 3 * 7 * 13 * 17
        rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := K) 3,
          hK4]
        rw [show Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) by decide]
        norm_num
      exact s168e3_sp_six_four_arithmetic hp hp2 hpq4 (hSp4 ▸ hdvd)
    · have hpq8 : ¬ p ∣ 8 ^ 2 - 1 := by simpa [hK8] using hpq
      have hSp8 : Nat.card Γ = 2 ^ 27 * 3 ^ 7 * 5 * 7 ^ 3 * 13 * 19 * 73 := by
        change Nat.card (StatedSp 3 K) = 2 ^ 27 * 3 ^ 7 * 5 * 7 ^ 3 * 13 * 19 * 73
        rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := K) 3,
          hK8]
        rw [show Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) by decide]
        norm_num
      exact s168e3_sp_six_eight_arithmetic hp hp2 hpq8 (hSp8 ▸ hdvd)
  have hne : ∃ a : Multiplicative (Fin 3 ⊕ Fin 3 → K), a ≠ 1 := by
    refine ⟨Multiplicative.ofAdd (Pi.single (Sum.inl ⟨0, by norm_num⟩) (1 : K)), ?_⟩
    intro h
    have h0 : (1 : K) = 0 := by
      have h1 := congrArg (fun x : Multiplicative (Fin 3 ⊕ Fin 3 → K) =>
        (Multiplicative.toAdd x) (Sum.inl ⟨0, by norm_num⟩)) h
      simp at h1
    exact one_ne_zero h0
  exact s168e3_false_of_natural_fixNc c hs Γ hRΓ hne hpσ
    (s16g_fixNc_statedSp_blocks (m := 3) (by norm_num) hp hpq)


theorem s168e3_false_of_sp_six_natural_field_four_eight
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    {a : ℕ} (ha : a = 2 ∨ a = 3)
    (hN : NatSpn (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 6 a) : False := by
  obtain ⟨-, K, hF, hFin, hK, hR⟩ := hN
  exact s168e3_false_of_sp_six_natural_aux (fieldK := hF) (finiteK := hFin) c hs ha hK
    (by simpa only [show 6 / 2 = 3 by norm_num] using hR)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
