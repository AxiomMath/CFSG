module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem7StmtsNoN
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227Lt
public import CFSG.Quasithin.EmptyFaithful.A38c13B69
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227EqAlt6
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227EqHat
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227LtA7G
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227LtA8
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227LtTen
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227LtU3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.H13.Lem1227Eq CFSG.QuasithinUnique.Vol2Native.A312L
open scoped IsMulCommutative

namespace Lem1227NoN

variable {G : Type} [Group G] {T K H M₀ : Subgroup G}

theorem e22_twoNoN (hTK : T ≤ Subgroup.normalizer (K : Set G)) (h : E2.E22CasesNoN H T M₀ K) :
    KerChar M₀ H K ∧ E22TwoAlt ↥(E2.star M₀ H K)
      (E2.IsDiagramNontrivial (E2.star M₀ H T) (E2.star M₀ H K) (E2.star M₀ H (T ⊓ K)))
      (8 < E2.autCard (E2.star M₀ H T) (E2.star M₀ H K))
      (E2.InducesOuter (E2.star M₀ H T) (E2.star M₀ H K)) := by
  unfold E2.E22CasesNoN at h
  dsimp only at h
  rcases h with ⟨-, t, ht, hne, -⟩ | ⟨-, hker, h2⟩
  · exact absurd ⟨t, ht, hne⟩ (not_exists_cjSub_ne hTK)
  · refine ⟨hker, ?_⟩
    rcases h2 with ⟨n, hB, -⟩ | ⟨n, hn, hX, hD, -⟩ |
        ⟨p, e, hp, hp3, he, h8, hX, -, hA⟩ | ⟨p, hp, hp2, hX, -⟩
    · exact Or.inl ⟨n, hB⟩
    · exact Or.inr (Or.inl ⟨n, hn, hX, hD⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨p, e, hp, hp3, he, h8, hX, hA⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨p, hp, hp2, hX⟩))

end Lem1227NoN

theorem lem1227ListEq_holdsNoN :
    Lem1227ListEqNoN := by
  intro G _ _ T K V H M₀ hH hTV hex hHdef hmin hE
  obtain ⟨hcomm, hmod⟩ := hex
  subst hHdef
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hH.normalizes
  have hKH : K ≤ K ⊔ T := le_sup_left
  have hHK : K ⊔ T ≤ Subgroup.normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer hTK
  obtain ⟨hker, hlist⟩ := Lem1227NoN.e22_twoNoN hTK hE
  have hfam := B69.e22CasesNoN_fam hE
  have hq := hH.quasisimple
  obtain ⟨hsq, hO⟩ := hyp_facts hH
  have hKV : K ≤ Subgroup.normalizer (V : Set G) := hH.irrPlus.2.2.1
  rcases hmod with ⟨n, hn, ⟨e⟩, hBN⟩ | ⟨⟨e⟩, hcard, -⟩ | ⟨⟨e⟩, hcard, -⟩ |
    ⟨n, h5, h8, ⟨φ, hφs, hφk⟩, hAN⟩ | ⟨-, φ, hφs, hφk⟩ | ⟨hLie, -⟩ |
    ⟨hq', hcen, ⟨eA⟩, hCV, hcard, hirrU⟩
  ·
    rcases hn with rfl | rfl | rfl
    · exfalso
      have hcard : Nat.card V = 8 ∨ Nat.card V = 16 :=
        Or.inl (by rw [G64.BinaryNaturalSL.card_eq hBN]; norm_num)
      obtain ⟨hnD, hnA⟩ := l32_not_D_A hH hTV hKH hHK hmin hker e hcard
      have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ :=
        Lem8.center_eq_bot_of_mulEquiv e (Out1222.center_sl_zmod_two_eq_bot 3)
      obtain ⟨e2⟩ := nonempty_star_equiv_of_center hKH hHK hmin hker e hZ
      have hN : Nat.card ↥(E2.star M₀ (K ⊔ T) K) = 168 := by
        rw [Nat.card_congr e2.toEquiv]
        exact card_sl_three_zmod_two
      rcases E22TwoAlt.of_card_168 hlist hN with ⟨-, hD⟩ | ⟨-, hA⟩
      · exact hnD hD
      · exact absurd hA (not_lt.2 hnA)
    · exfalso
      have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ :=
        Lem8.center_eq_bot_of_mulEquiv e (Out1222.center_sl_zmod_two_eq_bot 4)
      obtain ⟨e2⟩ := nonempty_star_equiv_of_center hKH hHK hmin hker e hZ
      have hN : Nat.card ↥(E2.star M₀ (K ⊔ T) K) = 20160 := by
        rw [Nat.card_congr e2.toEquiv]
        exact card_sl_four_zmod_two
      exact false_of_lieModel_four hfam (lieModel_psl_of_mulEquiv_sl_zmod_two (by norm_num) e2)
        hN
    · exfalso
      have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ :=
        Lem8.center_eq_bot_of_mulEquiv e Lem8.center_sl_five_zmod_two
      obtain ⟨e2⟩ := nonempty_star_equiv_of_center hKH hHK hmin hker e hZ
      have hN : Nat.card ↥(E2.star M₀ (K ⊔ T) K) = 9999360 := by
        rw [Nat.card_congr e2.toEquiv]
        exact Lem8.card_sl_five_zmod_two
      exact hfam.card_ne hN
  ·
    exfalso
    obtain ⟨hnD, hnA⟩ := l32_not_D_A hH hTV hKH hHK hmin hker e (Or.inr (by rw [hcard]; norm_num))
    have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ :=
      Lem8.center_eq_bot_of_mulEquiv e (Out1222.center_sl_zmod_two_eq_bot 3)
    obtain ⟨e2⟩ := nonempty_star_equiv_of_center hKH hHK hmin hker e hZ
    have hN : Nat.card ↥(E2.star M₀ (K ⊔ T) K) = 168 := by
      rw [Nat.card_congr e2.toEquiv]
      exact card_sl_three_zmod_two
    rcases E22TwoAlt.of_card_168 hlist hN with ⟨-, hD⟩ | ⟨-, hA⟩
    · exact hnD hD
    · exact absurd hA (not_lt.2 hnA)
  ·
    exfalso
    have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ :=
      Lem8.center_eq_bot_of_mulEquiv e Lem8.center_sl_five_zmod_two
    obtain ⟨e2⟩ := nonempty_star_equiv_of_center hKH hHK hmin hker e hZ
    have hN : Nat.card ↥(E2.star M₀ (K ⊔ T) K) = 9999360 := by
      rw [Nat.card_congr e2.toEquiv]
      exact Lem8.card_sl_five_zmod_two
    exact hfam.card_ne hN
  ·
    have hle := pCore_le_ker_of_surjective_alternating h5 φ hφs
    have : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; exact h5)
    obtain ⟨-, eQ, -⟩ := SteinbergBM.five_quasisimple_centerless_image hq
      (alternatingGroup_nonabelian (by omega)) (QuotientGroup.lift (CFSG.pCore 2 ↥K) φ hle)
      (QuotientGroup.lift_surjective_of_surjective _ φ hφs hle)
    obtain ⟨eS⟩ := nonempty_star_equiv hKH hHK hmin hker eQ
    obtain ⟨-, -, hodd⟩ := SteinbergBM.five_core_quotient_center_odd hq
    have hn' : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
    obtain ⟨h58, -, -⟩ := five_alternating_small_central_cover_reduction hq hodd hn' eQ
    have hcardn : Nat.card ↥(E2.star M₀ (K ⊔ T) K) = n.factorial / 2 := by
      rw [Nat.card_congr eS.toEquiv, Lem8.card_alternatingGroup_fin (by omega)]
    rcases hn' with rfl | rfl | rfl | rfl
    ·
      obtain ⟨-, ⟨eK⟩⟩ := h58 (Or.inl rfl)
      exact Or.inl ⟨by decide,
        CFSG.QuasithinUnique.Ch1.statedClassicalModel_psl_two_four_of_alternating_five _ ⟨eK⟩⟩
    ·
      exfalso
      obtain ⟨-, hD⟩ := E22TwoAlt.of_card_360 hlist (by rw [hcardn]; decide)
      exact not_isDiagramNontrivial_of_alt6 hKH hHK hmin hker hTK hTV hKV hO hAN ⟨eS⟩ hD
    ·
      exact (E22TwoAlt.false_of_card_2520 hlist (by rw [hcardn]; decide)).elim
    ·
      exact (false_of_lieModel_four hfam
        ((CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff _).mpr ⟨eS⟩)
        (by rw [hcardn]; decide)).elim
  ·
    exfalso
    have hle := pCore_le_ker_of_surjective_alternating (by norm_num) φ hφs
    have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
    obtain ⟨-, eQ, -⟩ := SteinbergBM.five_quasisimple_centerless_image hq
      (alternatingGroup_nonabelian (by norm_num)) (QuotientGroup.lift (CFSG.pCore 2 ↥K) φ hle)
      (QuotientGroup.lift_surjective_of_surjective _ φ hφs hle)
    obtain ⟨eS⟩ := nonempty_star_equiv hKH hHK hmin hker eQ
    have hN : Nat.card ↥(E2.star M₀ (K ⊔ T) K) = 2520 := by
      rw [Nat.card_congr eS.toEquiv, Lem8.card_alternatingGroup_fin (by norm_num)]
      decide
    exact E22TwoAlt.false_of_card_2520 hlist hN
  ·
    exfalso
    obtain ⟨hc6048, hZ⟩ := card_center_of_lieModel_psu hq hLie
    obtain ⟨eS⟩ := nonempty_star_equiv_of_center hKH hHK hmin hker
      (X := ↥K ⧸ CFSG.pCore 2 ↥K) (MulEquiv.refl _) hZ
    have hN : Nat.card ↥(E2.star M₀ (K ⊔ T) K) = 6048 := by
      rw [Nat.card_congr eS.toEquiv, hc6048]
    exact E22TwoAlt.false_of_card_6048 hlist hN
  ·
    exfalso
    obtain ⟨eS⟩ := nonempty_star_equiv hKH hHK hmin hker eA
    have hN : Nat.card ↥(E2.star M₀ (K ⊔ T) K) = 360 := by
      rw [Nat.card_congr eS.toEquiv, Lem8.card_alternatingGroup_fin (by norm_num)]
      decide
    obtain ⟨-, hD⟩ := E22TwoAlt.of_card_360 hlist hN
    exact not_isDiagramNontrivial_of_hat hKH hHK hmin hker hTK hTV hKV hsq hirrU hCV hcard hcen
      ⟨eS⟩ hD

open Lem1227Lt in
theorem lem1227ListLt_holdsNoN :
    Lem1227ListLtNoN := by
  intro G _ _ T K Y VY H M₀ hH hTV hex hKloc hKY hTK hq hHdef hmin hE
  obtain ⟨hcomm, hmod⟩ := hex
  have hLt : LtHyp G T K Y := ⟨hH.maximal.1, hKloc, hH.normalizes, hTK, hKY, hH.quasisimple⟩
  subst hHdef
  have hKH : K ≤ K ⊔ T := le_sup_left
  have hHK : K ⊔ T ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTK
  obtain ⟨hker, hlist⟩ := Lem1227NoN.e22_twoNoN hTK hE
  have hfam := B69.e22CasesNoN_fam hE
  rcases hmod with ⟨n, hn, ⟨e⟩, hBN⟩ | ⟨⟨e⟩, hcard, -⟩ | ⟨⟨e⟩, hcard, hirrU⟩ |
    ⟨n, h5, h8, ⟨φ, hφs, -⟩, -⟩ | ⟨-, φ, hφs, -⟩ | ⟨hLie, -⟩ |
    ⟨-, -, ⟨eA⟩, -, -, -⟩
  ·
    exfalso
    rcases hn with rfl | rfl | rfl
    · exact false_of_sl3 hLt e
    · exact false_of_natural hH hLt hTV hKH hHK hmin hker hq hlist hfam (le_refl 4)
        (by norm_num) e hBN
    · exact false_of_natural hH hLt hTV hKH hHK hmin hker hq hlist hfam (by norm_num)
        (le_refl 5) e hBN
  ·
    exact (false_of_sl3 hLt e).elim
  ·
    exact (Ten.false_of_ten hH hLt hTV hKH hHK hmin hker hq hlist hfam e hcard hirrU).elim
  ·
    have hsimple : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; exact h5)
    obtain ⟨ν, hν⟩ := exists_nu (alternatingGroup_nonabelian (n := n) (by omega)) φ hφs
    interval_cases n
    · exact (false_of_alt5 hLt ν hν).elim
    · exact (false_of_alt6 hLt ν hν).elim
    · exact A7.fam_a7 hLt hKH hHK hmin hker hq hlist ν hν
    · exact (false_of_alt8 hLt hKH hHK hmin hker hq hlist hfam ν hν).elim
  ·
    have hsimple : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
    obtain ⟨ν, hν⟩ := exists_nu (alternatingGroup_nonabelian (n := 7) (by norm_num)) φ hφs
    exact A7.fam_a7 hLt hKH hHK hmin hker hq hlist ν hν
  ·
    exact (false_of_u33 hLt hLie).elim
  ·
    have hsimple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
    exact (false_of_alt6 hLt (eA.toMonoidHom.comp (QuotientGroup.mk' _))
      (eA.surjective.comp (QuotientGroup.mk'_surjective _))).elim

end CFSG.Quasithin.H13
