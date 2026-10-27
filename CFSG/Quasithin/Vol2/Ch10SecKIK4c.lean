module

public import CFSG.Quasithin.Vol2.Ch10SecKIc
public import CFSG.Quasithin.Vol2.Ch10SecQ1G2Two
public import CFSG.Quasithin.Vol2.Ch11SecA02Simple
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch10SecKIK4a

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

variable {X : Type} [Group X]

omit [Group X] in
theorem nontrivial_of_card (hX : Nat.card X = 2520) : Finite X ∧ Nontrivial X := by
  have : Finite X := Nat.finite_of_card_ne_zero (by omega)
  exact ⟨this, Finite.one_lt_card_iff_nontrivial.mp (by omega)⟩

theorem false_of_simple {Γ : Type} [Group Γ] (hΓ : IsSimpleGroup Γ) (hc : Nat.card Γ ≠ 2520)
    (hX : Nat.card X = 2520) (π : Γ →* X) (hπ : Function.Surjective π) : False := by
  have := (nontrivial_of_card hX).2
  obtain ⟨e⟩ := SecA.nonempty_mulEquiv_of_surjective hΓ π hπ
  exact hc ((Nat.card_congr e.toEquiv).trans hX)

theorem false_of_card_lt {Γ : Type*} [Group Γ] [Finite Γ] (hc : Nat.card Γ < 2520)
    (hX : Nat.card X = 2520) (π : Γ →* X) (hπ : Function.Surjective π) : False := by
  have hd := Subgroup.card_dvd_of_surjective hπ
  rw [hX] at hd
  have := Nat.le_of_dvd Nat.card_pos hd
  omega

theorem one_le_of_card {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    1 ≤ n := by
  by_contra h
  have h0 : n = 0 := by omega
  have := Finite.one_lt_card (α := K)
  rw [hK, h0] at this
  norm_num at this

theorem false_of_sl2 {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hX : Nat.card X = 2520) (π : ↥(StatedSL 2 K) →* X) (hπ : Function.Surjective π) : False := by
  have h1 := one_le_of_card hK
  have hc : Nat.card ↥(StatedSL 2 K) = 2 ^ n * (4 ^ n - 1) := by
    rw [SecA.card_statedSL, SecA.card_SL_two_pow hK]
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · have hn : n = 1 := by omega
    subst hn
    exact false_of_card_lt (by rw [hc]; norm_num) hX π hπ
  · exact false_of_simple (Ch11.SecA.isSimpleGroup_statedSL
      (Ch11.SecA.isSimpleGroup_SL2 (K := K) h2 hK)) (by rw [hc]; exact sl2_card_ne n) hX π hπ

theorem false_of_sl3 {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hX : Nat.card X = 2520) (π : ↥(StatedSL 3 K) →* X) (hπ : Function.Surjective π) : False := by
  have h1 := one_le_of_card hK
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · have hn : n = 1 := by omega
    subst hn
    refine false_of_card_lt ?_ hX π hπ
    rw [SecA.card_statedSL, SecA.card_SL_three_pow hK]
    norm_num
  · have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK
    have hnt := (nontrivial_of_card hX).2
    have htriv := SecF.C10KH.sl3_hom_trivial hK h2 (X := X) (by rw [hX]; norm_num)
      (π.comp (specialLinearGroupEquivStatedSL 3 K).toMonoidHom)
    obtain ⟨x, hx⟩ := exists_ne (1 : X)
    obtain ⟨g, rfl⟩ := hπ x
    obtain ⟨A, rfl⟩ := (specialLinearGroupEquivStatedSL 3 K).surjective g
    exact hx (htriv A)

theorem false_of_sp4 {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hX : Nat.card X = 2520) (π : ↥(StatedSp 2 K) →* X) (hπ : Function.Surjective π) : False := by
  have h1 := one_le_of_card hK
  have hc := SecA.card_Sp4_pow hK
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · have hn : n = 1 := by omega
    subst hn
    exact false_of_card_lt (by rw [hc]; norm_num) hX π hπ
  · have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK
    have h4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2
    have hsimple : IsSimpleGroup (StatedProj (StatedSp 2 K)) :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by norm_num)
        (Or.inl (Or.inr h4))
    have hbij : Function.Bijective
        (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 K) :=
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
    have hsimple' : IsSimpleGroup ↥(StatedSp 2 K) := (MulEquiv.ofBijective _ hbij).isSimpleGroup
    refine false_of_simple hsimple' ?_ hX π hπ
    rw [hc]
    intro h
    have h16 : 16 ∣ 2 ^ (4 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (4 * n) - 1)) :=
      Dvd.dvd.mul_right ((show (16 : ℕ) = 2 ^ 4 by norm_num) ▸ pow_dvd_pow 2 (by omega)) _
    rw [h] at h16
    norm_num at h16

theorem card_alt_ne {n : ℕ} (hn : 2 ≤ n) (h7 : n ≠ 7) :
    Nat.card ↥(alternatingGroup (Fin n)) ≠ 2520 := by
  rw [SecA.card_alt n hn]
  exact fun h => h7 (eq_seven_of_factorial h)

theorem false_of_alt {n : ℕ} (hn : 5 ≤ n) (h7 : n ≠ 7) (hX : Nat.card X = 2520)
    (π : ↥(alternatingGroup (Fin n)) →* X) (hπ : Function.Surjective π) : False :=
  false_of_simple (SecA.isSimpleGroup_alt hn) (card_alt_ne (by omega) h7) hX π hπ

theorem false_of_hat6 {Γ : Type} [Group Γ] (hΓ : IsHat Γ ↥(alternatingGroup (Fin 6)))
    (hX : Nat.card X = 2520) (π : Γ →* X) (hπ : Function.Surjective π) : False := by
  obtain ⟨-, hc, ⟨e⟩⟩ := hΓ
  have hcard := Lin2.OddRank.card_of_cover_alt (m := 6) (by norm_num) hc e
  have : Finite Γ := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  exact false_of_card_lt (by rw [hcard]; decide) hX π hπ

theorem center_SL_eq_bot {n : ℕ} (hn : 0 < n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) : Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) = ⊥ := by
  apply Subgroup.card_eq_one.mp
  rw [Nat.card_congr
    (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (⟨0, hn⟩ : Fin n)).toEquiv]
  apply le_antisymm
  · calc _ ≤ Nat.card Kˣ := Subgroup.card_le_card_group _
      _ = 1 := by rw [Nat.card_units, hK]
  · exact Nat.card_pos

theorem false_of_sl45 {n : ℕ} (hn : n = 4 ∨ n = 5) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (hX : Nat.card X = 2520) (π : ↥(StatedSL n K) →* X)
    (hπ : Function.Surjective π) : False := by
  have hs : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n) K) :=
    Ch11.SecA.isSimpleGroup_SL_of_center_eq_bot (by omega) (Or.inl (by omega))
      (Or.inl (by omega)) (center_SL_eq_bot (by omega) hK)
  refine false_of_simple (Ch11.SecA.isSimpleGroup_statedSL hs) ?_ hX π hπ
  rw [SecA.card_statedSL]
  rcases hn with rfl | rfl
  · rw [SecA.card_SL_four_of_two hK]
    norm_num
  · rw [SecA.card_SL_five_of_two hK]
    norm_num

theorem false_of_sl45' {n : ℕ} (hn : n = 4 ∨ n = 5) (hX : Nat.card X = 2520)
    (π : ↥(StatedSL n (ZMod 2)) →* X) (hπ : Function.Surjective π) : False :=
  false_of_sl45 hn (Nat.card_zmod 2) hX π hπ

theorem false_of_comm {E : Type} [Group E] {Q : Subgroup E} (hQ : IsSimpleGroup ↥⁅Q, Q⁆)
    (hc : Nat.card ↥⁅Q, Q⁆ ≠ 2520) (hX : Nat.card X = 2520) (hperf : commutator X = ⊤)
    (π : ↥Q →* X) (hπ : Function.Surjective π) : False := by
  have hD : (commutator ↥Q).map Q.subtype = ⁅Q, Q⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  let eD : ↥(commutator ↥Q) ≃* ↥⁅Q, Q⁆ :=
    ((commutator ↥Q).equivMapOfInjective Q.subtype Q.subtype_injective).trans
      (MulEquiv.subgroupCongr hD)
  let ρ : ↥(commutator ↥Q) →* X := π.comp (commutator ↥Q).subtype
  have hρ : Function.Surjective ρ := by
    have htop : π.range = ⊤ := MonoidHom.range_eq_top.mpr hπ
    have hr : ρ.range = commutator X := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, commutator_def, commutator_def,
        Subgroup.map_commutator, ← MonoidHom.range_eq_map, htop]
    rw [← MonoidHom.range_eq_top, hr, hperf]
  exact false_of_simple hQ hc hX (ρ.comp eD.symm.toMonoidHom) (hρ.comp eD.symm.surjective)

section G2


theorem false_of_g2d {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (hX : Nat.card X = 2520)
    (π : ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ →* X)
    (hπ : Function.Surjective π) : False := by
  refine false_of_simple (H13.isSimpleGroup_g2Two_commutator hK) ?_ hX π hπ
  rw [SecA.C10P01.card_g2Two_commutator hK]
  norm_num

theorem false_of_g2 {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hX : Nat.card X = 2520) (hperf : commutator X = ⊤)
    (π : ↥(CFSG.Open.quasithinG2 K) →* X) (hπ : Function.Surjective π) : False := by
  have h1 := one_le_of_card hK
  have hnt := (nontrivial_of_card hX).2
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · have hn : n = 1 := by omega
    subst hn
    have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
    refine false_of_comm (H13.isSimpleGroup_g2Two_commutator hK2) ?_ hX hperf π hπ
    rw [SecA.C10P01.card_g2Two_commutator hK2]
    norm_num
  · exact SecF.C10KH.false_of_g2_surj h2 hK (by rw [hX]; norm_num) π hπ

end G2

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
