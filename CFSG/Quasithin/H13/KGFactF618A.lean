module

public import CFSG.Quasithin.H13.KGFactF618Gen
public import CFSG.Quasithin.H13.KGFactL2

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Blueprint

namespace KGF618

theorem good_hatAlt {D : Type} [Group D] [Finite D] {n : ℕ} (h : F6.IsHatAlt n D)
    (hn : 2 ≤ n) (hnp : ¬ (n.factorial / 2).Prime) {d : ℕ} (hd : d ∣ 3 * (n.factorial / 2))
    (h2 : Nat.Coprime d 2) (h15 : ¬ d ∣ 15) : Good D := by
  obtain ⟨⟨hc, hs⟩, hZ, ⟨e⟩⟩ := h
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  have hQ : Nat.card (D ⧸ Subgroup.center D) = n.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  have hnc : ∃ a b : D ⧸ Subgroup.center D, a * b ≠ b * a := by
    have := hs
    exact exists_ne_comm (hQ ▸ hnp)
  refine ⟨⟨Group.isPerfect_def.2 hc, hs, hnc⟩, ne_sixty_mul_two_pow ?_ h2 h15⟩
  rw [(Subgroup.center D).card_eq_card_quotient_mul_card_subgroup, hQ, hZ, mul_comm]
  exact hd

theorem good_alt_seven {D : Type} [Group D] (e : D ≃* ↥(alternatingGroup (Fin 7))) : Good D := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  have hcard : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  refine good_of_mulEquiv e.symm (good_of_isSimpleGroup (d := 7) ?_ ?_ (by norm_num) (by norm_num))
  · rw [hcard]
    norm_num
  · rw [hcard]
    norm_num

theorem good_M12 {D : Type} [Group D]
    (e : D ≃* ↥NativeSporadic.M12) : Good D := by
  obtain ⟨_, -, hs⟩ := CFSG.Sporadic.Mathieu.fam_m12_simplicity
  have hcard := CFSG.Sporadic.Mathieu.card_M12
  refine good_of_mulEquiv e.symm (good_of_isSimpleGroup (d := 11) ?_ ?_ (by norm_num)
    (by norm_num))
  · rw [hcard]
    norm_num
  · rw [hcard]
    norm_num

theorem good_L2 {D : Type} [Group D] [Finite D] {p e : ℕ} (hp : p.Prime) (he1 : 1 ≤ e)
    (he2 : e ≤ 2) (hq : p ^ e % 16 = 7 ∨ p ^ e % 16 = 9) (hL2 : F6.IsL2 p e D) : Good D := by
  obtain ⟨-, hsimple⟩ := CFSG.LieType.Simplicity.fam_PSL_simplicity D 2 p e hL2
  obtain ⟨-, F, _, _, hF, ⟨φ⟩⟩ := hL2
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ 2 ^ e := dvd_pow_self 2 (by omega)
    omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hq7 : 7 ≤ p ^ e := by omega
  have hcard : Nat.card D = p ^ e * ((p ^ e) ^ 2 - 1) / 2 := by
    rw [Nat.card_congr (φ.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm).toEquiv,
      CFSG.GorensteinWalter.psl2_card_formula F ⟨p, e, hp, hpodd, he1, hF⟩, hF]
  have heven : 2 ∣ p ^ e * ((p ^ e) ^ 2 - 1) := by
    have h := Nat.Odd.sub_odd ((hpodd.pow (n := e)).pow (n := 2)) odd_one
    exact Dvd.dvd.mul_left (even_iff_two_dvd.1 h) _
  have hD2 : Nat.card D * 2 = p ^ e * ((p ^ e) ^ 2 - 1) := by
    rw [hcard]
    exact Nat.div_mul_cancel heven
  have hcop2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
  have hpD : p ∣ Nat.card D := by
    have h : p ∣ Nat.card D * 2 := by
      rw [hD2]
      exact Dvd.dvd.mul_right (dvd_pow_self p (by omega)) _
    exact (Nat.Coprime.dvd_mul_right hcop2).1 h
  have hnp : ¬ (Nat.card D).Prime := by
    intro hprime
    have hDp : Nat.card D = p := ((Nat.prime_dvd_prime_iff_eq hp hprime).1 hpD).symm
    have hpq : p ≤ p ^ e := Nat.le_self_pow (by omega) p
    have h48 : 48 ≤ (p ^ e) ^ 2 - 1 := by
      have : 49 ≤ (p ^ e) ^ 2 := by nlinarith
      omega
    have : p ^ e * 48 ≤ p ^ e * ((p ^ e) ^ 2 - 1) := Nat.mul_le_mul_left _ h48
    rw [← hD2, hDp] at this
    omega
  by_cases hp7 : 7 ≤ p
  · refine good_of_isSimpleGroup hnp hpD hcop2 fun h15 => ?_
    have := Nat.le_of_dvd (by norm_num) h15
    interval_cases p <;> first | omega | norm_num at hp
  ·
    have hp35 : p = 3 ∨ p = 5 := by
      interval_cases p <;> simp_all (config := { decide := true })
    have he : e = 2 := by
      rcases hp35 with rfl | rfl <;> interval_cases e <;> omega
    subst he
    have hp2D : p ^ 2 ∣ Nat.card D := by
      have h : p ^ 2 ∣ Nat.card D * 2 := by
        rw [hD2]
        exact Dvd.dvd.mul_right dvd_rfl _
      exact (Nat.Coprime.dvd_mul_right (Nat.Coprime.pow_left 2 hcop2)).1 h
    refine good_of_isSimpleGroup hnp hp2D (Nat.Coprime.pow_left 2 hcop2) ?_
    rcases hp35 with rfl | rfl <;> norm_num

theorem good_caseFour {D : Type} [Group D] [Finite D] {G₁ G₂ : Subgroup D}
    (h : F6.IsF618CaseFour G₁ G₂) : Good D := by
  obtain ⟨⟨p, hp, hp24, hL2⟩, -⟩ := h
  obtain ⟨hq, hc, -⟩ := factL2Three_holds p D hp hp24 hL2
  exact ⟨hq, hc⟩

theorem good_caseSix {D : Type} [Group D] [Finite D] {G₁ G₂ : Subgroup D}
    (h : F6.IsF618CaseSix G₁ G₂) : Good D := by
  obtain ⟨hD, -⟩ := h
  rcases hD with hA | ⟨p, e, hp, he1, he2, hq, hL2⟩
  · exact good_hatAlt hA (by norm_num) (by norm_num [Nat.factorial]) (d := 9)
      (by norm_num [Nat.factorial]) (by norm_num) (by norm_num)
  · exact good_L2 hp he1 he2 hq hL2

theorem good_caseSeven {D : Type} [Group D] [Finite D] {G₁ G₂ : Subgroup D}
    (h : F6.IsF618CaseSeven G₁ G₂) : Good D := by
  obtain ⟨hD, -⟩ := h
  rcases hD with hA | hA
  · obtain ⟨e⟩ := hA
    exact good_alt_seven e
  · exact good_hatAlt hA (by norm_num) (by norm_num [Nat.factorial]) (d := 7)
      (by norm_num [Nat.factorial]) (by norm_num) (by norm_num)

theorem good_caseTwelve {D : Type} [Group D] [Finite D]
    {G₁ G₂ : Subgroup D} (h : F6.IsF618CaseTwelve G₁ G₂) : Good D := by
  obtain ⟨⟨e⟩, -⟩ := h
  exact good_M12 e

end KGF618

end CFSG.Quasithin.H13.A5
