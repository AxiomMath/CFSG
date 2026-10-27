module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonFam

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Rank

variable {W : Type} [CommGroup W]

private theorem s16e_two_alt6_rk_alt_six {H : Subgroup (MulAut W)} {U : Subgroup W}
    (h : AlternatingNatural H U ⊥ 6) : rk ↥U = 4 := by
  have h1 := s16c1610_card_alternatingNatural_mul (n := 6) (by norm_num) h
  have hmem : CFSG.Quasithin.G6.allOnes 6 ∈ CFSG.Quasithin.G6.coreMod 6 := by
    rw [CFSG.Quasithin.G6.mem_coreMod]
    change (∑ _i : Fin 6, (1 : ZMod 2)) = 0
    decide
  have hsq : CFSG.Quasithin.G6.allOnes 6 * CFSG.Quasithin.G6.allOnes 6 = 1 := by
    apply Multiplicative.toAdd.injective
    funext i
    change (1 : ZMod 2) + 1 = 0
    decide
  have hne : CFSG.Quasithin.G6.allOnes 6 ≠ 1 := fun h0 => by
    have h1 := congrFun (congrArg Multiplicative.toAdd h0) (⟨0, by norm_num⟩ : Fin 6)
    change (1 : ZMod 2) = 0 at h1
    exact absurd h1 (by decide)
  have hord : orderOf (CFSG.Quasithin.G6.allOnes 6) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hsq) hne
  have hZ : Nat.card ↥(Subgroup.zpowers (CFSG.Quasithin.G6.allOnes 6) ⊓
      CFSG.Quasithin.G6.coreMod 6) = 2 := by
    rw [inf_eq_left.mpr (Subgroup.zpowers_le.mpr hmem), Nat.card_zpowers, hord]
  rw [hZ] at h1
  have hcard : Nat.card U = 2 ^ 4 := by
    norm_num at h1 ⊢
    omega
  exact s16c1610_rk_of_card_two_pow hcard

end Rank

section Sigma

variable {G : Type} [Group G] [Finite G]

private theorem s16e_two_alt6_card_GL_eight :
    Nat.card (GL (Fin 8) (ZMod 2)) = 5348063769211699200 := by
  rw [Matrix.card_GL_field, ZMod.card]
  decide

private theorem s16e_two_alt6_not_cube_dvd_gl8 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) : ¬ p ^ 3 ∣ Nat.card (GL (Fin 8) (ZMod 2)) := by
  rw [s16e_two_alt6_card_GL_eight]
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

theorem s16e_two_alt6_sig_eq_three (D : Data G) (hx : DataExt D)
    (h4 : 3 < CFSG.Open.evenRank G) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 1)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z 6)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    D.sig = {3} := by
  have h1217 : R1217 D := r1217_of_twelve_seventeen D hx h61 h127 h1214
  have hwStar : wStar D.M V₀ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D h1217 hset.hyp151 hV hL hs
  have hrk : rk ↥(⊤ : Subgroup (vStar D.M V₀ V hV L)) = 8 := by
    calc rk ↥(⊤ : Subgroup (vStar D.M V₀ V hV L))
        = rk ↥(wStar D.M V₀ V hV L) := by rw [hwStar]
      _ = 2 * 4 := s16c1610_rk_sumOfNat_two (N := fun H U Z => AlternatingNatural H U Z 6)
            (hN := fun I hI => s16e_two_alt6_rk_alt_six hI) hsum
      _ = 8 := by norm_num
  have hcard : Nat.card (vStar D.M V₀ V hV L) = 2 ^ 8 := by
    rw [s16e_card_eq_two_pow_rk_top (s15_Infra_vtil_sq_eq_one _ V hV), hrk]
  have hp3 : ∀ p ∈ D.sig, p = 3 := by
    intro p hp
    obtain ⟨hpprime, hp2⟩ := D.sig_prime p hp
    by_contra hp3
    have h3 := s16c1610_three_le_pRank_mBar_of_four D hx h61 h127 hset.hyp16 hV h4 hp
    obtain ⟨E, hE, -, hEcard⟩ := CFSG.SectionRank.exists_pRank hpprime.one_lt (Mbar D.M V₀ V hV)
    have hdvdE : p ^ 3 ∣ Nat.card E := by
      rw [hEcard]
      exact pow_dvd_pow p h3
    have hdvdM : p ^ 3 ∣ Nat.card (Mbar D.M V₀ V hV) :=
      hdvdE.trans (Subgroup.card_dvd_of_le hE)
    have hcard_eq := c23_card_mbar_v1Sub_eq D h1217 hset.hyp151 hV
    have hdvdM' : p ^ 3 ∣ Nat.card (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) := by
      rwa [hcard_eq]
    have hdvdAut : Nat.card (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) ∣
        Nat.card (MulAut (vStar D.M V₀ V hV L)) := Subgroup.card_subgroup_dvd_card _
    have hsq : ∀ v : vStar D.M V₀ V hV L, v ^ 2 = 1 := s15_Infra_vtil_sq_eq_one _ V hV
    have hdvdGL : Nat.card (MulAut (vStar D.M V₀ V hV L)) ∣
        Nat.card (GL (Fin 8) (ZMod 2)) :=
      CFSG.LocalAnalysis.UniquenessCase.UC6.N588.card_mulAut_dvd_card_GL
        (fun a b => mul_comm a b) hsq hcard
    exact s16e_two_alt6_not_cube_dvd_gl8 hpprime hp2 hp3 (hdvdM'.trans (hdvdAut.trans hdvdGL))
  obtain ⟨q₀, hq₀⟩ := hx.sig_nonempty
  have hq₀3 : q₀ = 3 := hp3 q₀ hq₀
  ext q
  refine ⟨fun hq => Set.mem_singleton_iff.mpr (hp3 q hq), fun hq => ?_⟩
  have hq3 : q = 3 := Set.mem_singleton_iff.1 hq
  rw [hq3, ← hq₀3]
  exact hq₀

theorem s16e_two_alt6_kbar_L0 (D : Data G) (hx : DataExt D)
    (h4 : 3 < CFSG.Open.evenRank G) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D)
    (h638 : UC6.R6_38 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥)
    (hconc : Conc4_136 D V₀ V hV L) (hs : s15 D.M V₀ V hV L = 1)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) 6)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z 6)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    IsSym ↥(kBar D.M V₀ V hV L) 3 ∧
      ∃ L₀ : Subgroup (MulAut (Vtil V₀ V hV)),
        IsInternalDirect (kBar D.M V₀ V hV L) L₀ (Mbar D.M V₀ V hV) ∧ IsSym ↥L₀ 6 := by
  have hsig := s16e_two_alt6_sig_eq_three D hx h4 h61 h127 h1214 hV hset hL hs hsum
  exact s16e_two_fam_alt6_route D hx h4 h61 h127 h1214 h638 hV hset hL hconc hs
    (by rw [hsig]; exact Set.mem_singleton 3) hA hsum

end Sigma

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
