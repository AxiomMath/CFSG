module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalFixedSubgroups
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8TwoOmega
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKLift

open scoped Matrix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.GF2n.Stroth80 CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin (quadPlus quadMinus coe_quadPlus coe_quadMinus)

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

private theorem s168e3_omega_plus_six_four_arithmetic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ 4 ^ 2 - 1)
    (h : p ^ 2 ∣ 2 ^ 13 * 3 ^ 4 * 5 ^ 2 * 7 * 17) : False := by
  have hpN : p ∣ 2 ^ 13 * 3 ^ 4 * 5 ^ 2 * 7 * 17 :=
    (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans h
  have hvals : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 17 := by
    rcases hp.dvd_mul.mp hpN with h | h
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
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 17)).mp h))))
  rcases hvals with rfl | rfl | rfl | rfl | rfl
  · exact hp2 rfl
  · exact hpq (by norm_num)
  · exact hpq (by norm_num)
  · norm_num at h
  · norm_num at h

private theorem s168e3_omega_plus_six_eight_arithmetic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ 8 ^ 2 - 1)
    (h : p ^ 2 ∣ 2 ^ 19 * 3 ^ 4 * 5 * 7 ^ 3 * 13 * 73) : False := by
  have hpN : p ∣ 2 ^ 19 * 3 ^ 4 * 5 * 7 ^ 3 * 13 * 73 :=
    (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans h
  have hvals : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 73 := by
    rcases hp.dvd_mul.mp hpN with h | h
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
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 73)).mp h)))))
  rcases hvals with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hp2 rfl
  · exact hpq (by norm_num)
  · norm_num at h
  · exact hpq (by norm_num)
  · norm_num at h
  · norm_num at h

theorem s168e3_false_of_omega_plus_six_natural_field_four_eight
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    {a : ℕ} (ha : a = 2 ∨ a = 3)
    (hN : NatOmegaPlus (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 6 a) : False := by
  obtain ⟨-, K, hF, hFin, hK, hR⟩ := hN
  let := hF
  let := hFin
  have ha1 : 1 ≤ a := by rcases ha with rfl | rfl <;> norm_num
  have : CharP K 2 := s16k_charP_two_of_card (a := a) ha1 hK
  let Γ : Subgroup (GL (Fin 3 ⊕ Fin 3) K) := StatedOmega (StatedQuadPlus 3 K)
  have hRΓ : (FFModel.nat Γ).Realizes (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) := by
    simpa only [Γ, show 6 / 2 = 3 by norm_num] using hR
  have hKq : Nat.card K = 4 ∨ Nat.card K = 8 := by
    rcases ha with rfl | rfl
    · left; rw [hK]; norm_num
    · right; rw [hK]; norm_num
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
    have hΓ : AddCommutantScalar Γ :=
      addCommutantScalar_statedOmegaPlus (m := 3) (by norm_num) (K := K)
    obtain ⟨F, hFN, hFel, hFcard⟩ :=
      s168e3_exists_matrix_elem_of_natural_of_coprime c hs Γ hRΓ hΓ hpσ hAut
    obtain ⟨μ, hμ⟩ := s16g_exists_mult_omegaPlus (m := 3) (by norm_num) (K := K)
    have hμF : ∀ x : ↥(Subgroup.normalizer (Γ : Set (GL (Fin 3 ⊕ Fin 3) K))),
        (x : GL (Fin 3 ⊕ Fin 3) K) ∈ F → μ x = 1 :=
      s16g_mu_eq_one_of_coprime μ hFN hp hFel.isPGroup hUnits
    have hFQ : ∀ x ∈ F, ∀ v : Fin 3 ⊕ Fin 3 → K,
        StatedQuadPlus 3 K ((x : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ v) =
          StatedQuadPlus 3 K v := by
      intro x hx v
      exact hμ ⟨x, hFN hx⟩ (hμF ⟨x, hFN hx⟩ hx) v
    have : Finite (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K)) := inferInstance
    have hle : F.map (toLinEquiv (Fin 3 ⊕ Fin 3) K).toMonoidHom ≤
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K) := by
      rintro _ ⟨x, hx, rfl⟩
      refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
      rw [MulEquiv.coe_toMonoidHom, toLinEquiv_apply, coe_quadPlus]
      exact hFQ x hx v
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (toLinEquiv (Fin 3 ⊕ Fin 3) K).injective] at hdvd
    rw [hFcard] at hdvd
    rcases hKq with hK4 | hK8
    · have hpq4 : ¬ p ∣ 4 ^ 2 - 1 := by simpa [hK4] using hpq
      have hO := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadPlus (K := K) 2
      have hO' : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K)) : ℤ) =
          2 * 4 ^ 6 * (4 ^ 3 - 1) * (4 ^ 2 - 1) * (4 ^ 4 - 1) := by
        simpa [hK4, Finset.prod_Icc_succ_top] using hO
      have hdvdZ : (p : ℤ) ^ 2 ∣
          (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K)) : ℤ) := by
        exact_mod_cast hdvd
      rw [hO'] at hdvdZ
      norm_num at hdvdZ
      have hdvdN : p ^ 2 ∣ 2 ^ 13 * 3 ^ 4 * 5 ^ 2 * 7 * 17 := by
        norm_num
        exact_mod_cast hdvdZ
      exact s168e3_omega_plus_six_four_arithmetic hp hp2 hpq4 hdvdN
    · have hpq8 : ¬ p ∣ 8 ^ 2 - 1 := by simpa [hK8] using hpq
      have hO := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadPlus (K := K) 2
      have hO' : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K)) : ℤ) =
          2 * 8 ^ 6 * (8 ^ 3 - 1) * (8 ^ 2 - 1) * (8 ^ 4 - 1) := by
        simpa [hK8, Finset.prod_Icc_succ_top] using hO
      have hdvdZ : (p : ℤ) ^ 2 ∣
          (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K)) : ℤ) := by
        exact_mod_cast hdvd
      rw [hO'] at hdvdZ
      norm_num at hdvdZ
      have hdvdN : p ^ 2 ∣ 2 ^ 19 * 3 ^ 4 * 5 * 7 ^ 3 * 13 * 73 := by
        norm_num
        exact_mod_cast hdvdZ
      exact s168e3_omega_plus_six_eight_arithmetic hp hp2 hpq8 hdvdN
  have hne : ∃ a : Multiplicative (Fin 3 ⊕ Fin 3 → K), a ≠ 1 := by
    refine ⟨Multiplicative.ofAdd (Pi.single (Sum.inl ⟨0, by norm_num⟩) (1 : K)), ?_⟩
    intro h
    have h0 : (1 : K) = 0 := by
      have h1 := congrArg (fun x : Multiplicative (Fin 3 ⊕ Fin 3 → K) =>
        (Multiplicative.toAdd x) (Sum.inl ⟨0, by norm_num⟩)) h
      simp at h1
    exact one_ne_zero h0
  exact s168e3_false_of_natural_fixNc c hs Γ hRΓ hne hpσ
    (s16g_fixNc_statedOmegaPlus_two (K := K) (m := 3)
      (by rw [hK]; rcases ha with rfl | rfl <;> norm_num) (by norm_num) hp hp2 hpq)

private theorem s168e3_omega_minus_eight_four_arithmetic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ 4 ^ 2 - 1)
    (h : p ^ 2 ∣ 2 ^ 25 * 3 ^ 4 * 5 ^ 3 * 7 * 13 * 17 * 257) : False := by
  have hpN : p ∣ 2 ^ 25 * 3 ^ 4 * 5 ^ 3 * 7 * 13 * 17 * 257 :=
    (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans h
  have hvals : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 17 ∨ p = 257 := by
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
            · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp
                (hp.dvd_of_dvd_pow h))))
          · exact Or.inr (Or.inr (Or.inr (Or.inl
              ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).mp h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13)).mp h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 17)).mp h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 257)).mp h))))))
  rcases hvals with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hp2 rfl
  · exact hpq (by norm_num)
  · exact hpq (by norm_num)
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h

private theorem s168e3_omega_minus_eight_eight_arithmetic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ 8 ^ 2 - 1)
    (h : p ^ 2 ∣ 2 ^ 37 * 3 ^ 7 * 5 * 7 ^ 3 * 13 * 17 * 19 * 73 * 241) : False := by
  have hpN : p ∣ 2 ^ 37 * 3 ^ 7 * 5 * 7 ^ 3 * 13 * 17 * 19 * 73 * 241 :=
    (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans h
  have hvals : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 73 ∨ p = 241 := by
    rcases hp.dvd_mul.mp hpN with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · rcases hp.dvd_mul.mp h with h | h
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
              ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 17)).mp h))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 19)).mp h)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 73)).mp h))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 241)).mp h))))))))
  rcases hvals with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hp2 rfl
  · exact hpq (by norm_num)
  · norm_num at h
  · exact hpq (by norm_num)
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h

theorem s168e3_false_of_omega_minus_eight_natural_field_four_eight
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    {a : ℕ} (ha : a = 2 ∨ a = 3)
    (hN : NatOmegaMinus (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 8 a) : False := by
  obtain ⟨-, K, hF, hFin, b, d, hK, hirr, hR⟩ := hN
  let := hF
  let := hFin
  have ha1 : 1 ≤ a := by rcases ha with rfl | rfl <;> norm_num
  have : CharP K 2 := s16k_charP_two_of_card (a := a) ha1 hK
  let Γ : Subgroup (GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) :=
    StatedOmega (StatedQuadMinus 4 K b d)
  have hRΓ : (FFModel.nat Γ).Realizes (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) := by
    simpa only [Γ, show 8 / 2 = 4 by norm_num] using hR
  have hKq : Nat.card K = 4 ∨ Nat.card K = 8 := by
    rcases ha with rfl | rfl
    · left; rw [hK]; norm_num
    · right; rw [hK]; norm_num
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
    have hΓ : AddCommutantScalar Γ :=
      addCommutantScalar_statedOmegaMinus (K := K) (m := 4) (b := b) (c := d)
        (by norm_num) hirr
    obtain ⟨F, hFN, hFel, hFcard⟩ :=
      s168e3_exists_matrix_elem_of_natural_of_coprime c hs Γ hRΓ hΓ hpσ hAut
    obtain ⟨μ, hμ⟩ := s16g_exists_mult_omegaMinus (K := K) (m := 4) (b := b) (c := d)
      (by norm_num) hirr
    have hμF : ∀ x : ↥(Subgroup.normalizer (Γ : Set (GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K))),
        (x : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) ∈ F → μ x = 1 :=
      s16g_mu_eq_one_of_coprime μ hFN hp hFel.isPGroup hUnits
    have hFQ : ∀ x ∈ F, ∀ v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K,
        StatedQuadMinus 4 K b d
            ((x : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) *ᵥ v) =
          StatedQuadMinus 4 K b d v := by
      intro x hx v
      exact hμ ⟨x, hFN hx⟩ (hμF ⟨x, hFN hx⟩ hx) v
    have : Finite (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b d)) := inferInstance
    have hle : F.map (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K).toMonoidHom ≤
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b d) := by
      rintro _ ⟨x, hx, rfl⟩
      refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
      rw [MulEquiv.coe_toMonoidHom, toLinEquiv_apply, coe_quadMinus]
      exact hFQ x hx v
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K).injective] at hdvd
    rw [hFcard] at hdvd
    rcases hKq with hK4 | hK8
    · have hpq4 : ¬ p ∣ 4 ^ 2 - 1 := by simpa [hK4] using hpq
      have hO := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadMinus (K := K) hirr 3
      have hO' : (Nat.card
            (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b d)) : ℤ) =
          2 * 4 ^ 12 * (4 ^ 4 + 1) * (4 ^ 2 - 1) * (4 ^ 4 - 1) * (4 ^ 6 - 1) := by
        simpa [hK4, Finset.prod_Icc_succ_top] using hO
      have hdvdZ : (p : ℤ) ^ 2 ∣
          (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b d)) : ℤ) := by
        exact_mod_cast hdvd
      rw [hO'] at hdvdZ
      norm_num at hdvdZ
      have hdvdN : p ^ 2 ∣ 2 ^ 25 * 3 ^ 4 * 5 ^ 3 * 7 * 13 * 17 * 257 := by
        norm_num
        exact_mod_cast hdvdZ
      exact s168e3_omega_minus_eight_four_arithmetic hp hp2 hpq4 hdvdN
    · have hpq8 : ¬ p ∣ 8 ^ 2 - 1 := by simpa [hK8] using hpq
      have hO := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadMinus (K := K) hirr 3
      have hO' : (Nat.card
            (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b d)) : ℤ) =
          2 * 8 ^ 12 * (8 ^ 4 + 1) * (8 ^ 2 - 1) * (8 ^ 4 - 1) * (8 ^ 6 - 1) := by
        simpa [hK8, Finset.prod_Icc_succ_top] using hO
      have hdvdZ : (p : ℤ) ^ 2 ∣
          (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b d)) : ℤ) := by
        exact_mod_cast hdvd
      rw [hO'] at hdvdZ
      norm_num at hdvdZ
      have hdvdN : p ^ 2 ∣ 2 ^ 37 * 3 ^ 7 * 5 * 7 ^ 3 * 13 * 17 * 19 * 73 * 241 := by
        norm_num
        exact_mod_cast hdvdZ
      exact s168e3_omega_minus_eight_eight_arithmetic hp hp2 hpq8 hdvdN
  have hne : ∃ a : Multiplicative (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K), a ≠ 1 := by
    refine ⟨Multiplicative.ofAdd (Pi.single (Sum.inr (Sum.inr 0)) (1 : K)), ?_⟩
    intro h
    have h0 : (1 : K) = 0 := by
      have h1 := congrArg (fun x : Multiplicative (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K) =>
        (Multiplicative.toAdd x) (Sum.inr (Sum.inr 0))) h
      simp at h1
    exact one_ne_zero h0
  exact s168e3_false_of_natural_fixNc c hs Γ hRΓ hne hpσ
    (s16g_fixNc_statedOmegaMinus_two (K := K) (m := 4)
      (by rw [hK]; rcases ha with rfl | rfl <;> norm_num) (by norm_num) hirr hp hp2 hpq)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
