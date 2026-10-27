module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c4
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214g
public import CFSG.Adapters.LieModelSmallOrders
public import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem11
public import CFSG.Sporadic.ON

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

theorem le_of_two_pow_dvd_of_not_dvd {N a k : ℕ} (hN : ¬ 2 ^ (a + 1) ∣ N) (h : 2 ^ k ∣ N) :
    k ≤ a := by
  by_contra hlt
  exact hN ((pow_dvd_pow 2 (by omega)).trans h)

theorem ordA_ne_of_two_adic {N a : ℕ} (hN : ¬ 2 ^ (a + 1) ∣ N)
    (hchk : ∀ d ∈ Finset.range (a + 3), ∀ f ∈ Finset.range (a + 1),
      2 ≤ d → 1 ≤ f → f * ((d - 1) * d / 2) ≤ a →
      CFSG.Open.ordA (d - 1) (2 ^ f) ≠ N) :
    ∀ d f : ℕ, 2 ≤ d → 1 ≤ f → CFSG.Open.ordA (d - 1) (2 ^ f) ≠ N := by
  intro d f hd hf hcard
  obtain ⟨r, -, hm⟩ := (CFSG.Timmesfeld.Orders.profile_ordA (n := d - 1) (by omega) hf).two
  have hdvd : 2 ^ (f * ((d - 1) * d / 2)) ∣ N := by
    rw [← hcard, hm, Nat.sub_add_cancel (by omega : 1 ≤ d)]
    exact Dvd.dvd.mul_right (pow_dvd_pow 2 le_rfl) r
  have hle := le_of_two_pow_dvd_of_not_dvd hN hdvd
  have hd1 : d - 1 ≤ (d - 1) * d / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    exact Nat.mul_le_mul_left _ hd
  have hfa : f ≤ a := le_trans (Nat.le_mul_of_pos_right f (by omega)) hle
  have hda : d - 1 ≤ a := le_trans (le_trans hd1 (Nat.le_mul_of_pos_left _ hf)) hle
  exact hchk d (Finset.mem_range.mpr (by omega)) f (Finset.mem_range.mpr (by omega)) hd hf hle hcard

theorem ordTwistedA_ne_of_two_adic {N a : ℕ} (hN : ¬ 2 ^ (a + 1) ∣ N)
    (hchk : ∀ d ∈ Finset.range (a + 3), ∀ f ∈ Finset.range (a + 1),
      3 ≤ d → 1 ≤ f → f * ((d - 1) * d / 2) ≤ a →
      CFSG.Open.ordTwistedA (d - 1) (2 ^ f) ≠ N) :
    ∀ d f : ℕ, 3 ≤ d → 1 ≤ f → CFSG.Open.ordTwistedA (d - 1) (2 ^ f) ≠ N := by
  intro d f hd hf hcard
  obtain ⟨r, -, hm⟩ :=
    (CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := d - 1) (by omega) hf).two
  have hdvd : 2 ^ (f * ((d - 1) * d / 2)) ∣ N := by
    rw [← hcard, hm, Nat.sub_add_cancel (by omega : 1 ≤ d)]
    exact Dvd.dvd.mul_right (pow_dvd_pow 2 le_rfl) r
  have hle := le_of_two_pow_dvd_of_not_dvd hN hdvd
  have hd1 : d - 1 ≤ (d - 1) * d / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    exact Nat.mul_le_mul_left _ (by omega)
  have hfa : f ≤ a := le_trans (Nat.le_mul_of_pos_right f (by omega)) hle
  have hda : d - 1 ≤ a := le_trans (le_trans hd1 (Nat.le_mul_of_pos_left _ hf)) hle
  exact hchk d (Finset.mem_range.mpr (by omega)) f (Finset.mem_range.mpr (by omega)) hd hf hle hcard

theorem ordBC_ne_of_two_adic {N a : ℕ} (hN : ¬ 2 ^ (a + 1) ∣ N)
    (hchk : ∀ d ∈ Finset.range (a + 1), ∀ f ∈ Finset.range (a + 1),
      2 ≤ d → 1 ≤ f → f * (d * d) ≤ a →
      CFSG.Open.ordBC d (2 ^ f) ≠ N) :
    ∀ d f : ℕ, 2 ≤ d → 1 ≤ f → CFSG.Open.ordBC d (2 ^ f) ≠ N := by
  intro d f hd hf hcard
  obtain ⟨r, -, hm⟩ := (CFSG.Timmesfeld.Orders.profile_ordBC (n := d) hf).two
  have hdvd : 2 ^ (f * (d * d)) ∣ N := by
    rw [← hcard, hm]
    exact Dvd.dvd.mul_right (pow_dvd_pow 2 le_rfl) r
  have hle := le_of_two_pow_dvd_of_not_dvd hN hdvd
  have hdd : d ≤ d * d := Nat.le_mul_of_pos_left d (by omega)
  have hfa : f ≤ a := le_trans (Nat.le_mul_of_pos_right f (Nat.mul_pos (by omega) (by omega))) hle
  have hda : d ≤ a := le_trans (le_trans hdd (Nat.le_mul_of_pos_left _ hf)) hle
  exact hchk d (Finset.mem_range.mpr (by omega)) f (Finset.mem_range.mpr (by omega)) hd hf hle hcard

theorem ordD_ne_of_two_adic {N a : ℕ} (hN : ¬ 2 ^ (a + 1) ∣ N)
    (hchk : ∀ d ∈ Finset.range (a + 2), ∀ f ∈ Finset.range (a + 1),
      4 ≤ d → 1 ≤ f → f * (d * (d - 1)) ≤ a →
      CFSG.Open.ordD d (2 ^ f) ≠ N) :
    ∀ d f : ℕ, 4 ≤ d → 1 ≤ f → CFSG.Open.ordD d (2 ^ f) ≠ N := by
  intro d f hd hf hcard
  obtain ⟨r, -, hm⟩ := (CFSG.Timmesfeld.Orders.profile_ordD (n := d) (by omega) hf).two
  have hdvd : 2 ^ (f * (d * (d - 1))) ∣ N := by
    rw [← hcard, hm]
    exact Dvd.dvd.mul_right (pow_dvd_pow 2 le_rfl) r
  have hle := le_of_two_pow_dvd_of_not_dvd hN hdvd
  have hdd : d ≤ d * (d - 1) := Nat.le_mul_of_pos_right d (by omega)
  have hfa : f ≤ a := le_trans (Nat.le_mul_of_pos_right f (Nat.mul_pos (by omega) (by omega))) hle
  have hda : d ≤ a := le_trans (le_trans hdd (Nat.le_mul_of_pos_left _ hf)) hle
  exact hchk d (Finset.mem_range.mpr (by omega)) f (Finset.mem_range.mpr (by omega)) hd hf hle hcard

theorem ordTwistedD_ne_of_two_adic {N a : ℕ} (hN : ¬ 2 ^ (a + 1) ∣ N)
    (hchk : ∀ d ∈ Finset.range (a + 2), ∀ f ∈ Finset.range (a + 1),
      4 ≤ d → 1 ≤ f → f * (d * (d - 1)) ≤ a →
      CFSG.Open.ordTwistedD d (2 ^ f) ≠ N) :
    ∀ d f : ℕ, 4 ≤ d → 1 ≤ f → CFSG.Open.ordTwistedD d (2 ^ f) ≠ N := by
  intro d f hd hf hcard
  obtain ⟨r, -, hm⟩ :=
    (CFSG.Timmesfeld.Orders.profile_ordTwistedD (n := d) (by omega) hf).two
  have hdvd : 2 ^ (f * (d * (d - 1))) ∣ N := by
    rw [← hcard, hm]
    exact Dvd.dvd.mul_right (pow_dvd_pow 2 le_rfl) r
  have hle := le_of_two_pow_dvd_of_not_dvd hN hdvd
  have hdd : d ≤ d * (d - 1) := Nat.le_mul_of_pos_right d (by omega)
  have hfa : f ≤ a := le_trans (Nat.le_mul_of_pos_right f (Nat.mul_pos (by omega) (by omega))) hle
  have hda : d ≤ a := le_trans (le_trans hdd (Nat.le_mul_of_pos_left _ hf)) hle
  exact hchk d (Finset.mem_range.mpr (by omega)) f (Finset.mem_range.mpr (by omega)) hd hf hle hcard

theorem ordG2_ne_of_two_adic {N a : ℕ} (hN : ¬ 2 ^ (a + 1) ∣ N)
    (hchk : ∀ f ∈ Finset.range (a + 1), 1 ≤ f → f * 6 ≤ a → CFSG.Open.ordG2 (2 ^ f) ≠ N) :
    ∀ f : ℕ, 1 ≤ f → CFSG.Open.ordG2 (2 ^ f) ≠ N := by
  intro f hf hcard
  obtain ⟨r, -, hm⟩ := (CFSG.Timmesfeld.Orders.profile_ordG2 hf).two
  have hdvd : 2 ^ (f * 6) ∣ N := by
    rw [← hcard, hm]
    exact Dvd.dvd.mul_right (pow_dvd_pow 2 le_rfl) r
  have hle := le_of_two_pow_dvd_of_not_dvd hN hdvd
  exact hchk f (Finset.mem_range.mpr (by omega)) hf hle hcard

theorem two_pow_mul_four_pow_sub_one_ne {N a : ℕ} (hN : ¬ 2 ^ (a + 1) ∣ N)
    (ha : ∀ e ≤ a, 2 ^ e * (4 ^ e - 1) ≠ N) (e : ℕ) : 2 ^ e * (4 ^ e - 1) ≠ N := by
  intro h
  by_cases he : e ≤ a
  · exact ha e he h
  · apply hN
    rw [← h]
    exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _

theorem not_lieModel_psl_two_of_isSpor_J1
    {X : Type} [Group X] (h : IsSpor X .J1) (e : ℕ) :
    ¬ LieModel X .PSL 2 2 e := by
  intro hm
  obtain ⟨f⟩ := h
  have hX : Nat.card X = 175560 := by
    rw [Nat.card_congr f.toEquiv]
    exact CFSG.Sporadic.J1.card_J1
  refine two_pow_mul_four_pow_sub_one_ne (N := 175560) (a := 3) (by norm_num) (by decide) e ?_
  rw [← CFSG.Quasithin.H13.Lem11.card_of_lieModel_psl_two hm, hX]

theorem not_lieModel_psl_two_of_isSpor_J2
    {X : Type} [Group X] (h : IsSpor X .J2) (e : ℕ) :
    ¬ LieModel X .PSL 2 2 e := by
  intro hm
  obtain ⟨f⟩ := h
  have hX : Nat.card X = 604800 := by
    rw [Nat.card_congr f.toEquiv]
    exact CFSG.Sporadic.J2.card_J2
  refine two_pow_mul_four_pow_sub_one_ne (N := 604800) (a := 7) (by norm_num) (by decide) e ?_
  rw [← CFSG.Quasithin.H13.Lem11.card_of_lieModel_psl_two hm, hX]

theorem not_lieModel_psl_two_of_isSpor_HS
    {X : Type} [Group X] (h : IsSpor X .HS) (e : ℕ) :
    ¬ LieModel X .PSL 2 2 e := by
  intro hm
  obtain ⟨f⟩ := h
  have hX : Nat.card X = 44352000 := by
    rw [Nat.card_congr f.toEquiv]
    exact CFSG.Sporadic.HS.card_HS
  refine two_pow_mul_four_pow_sub_one_ne (N := 44352000) (a := 9) (by norm_num) (by decide) e ?_
  rw [← CFSG.Quasithin.H13.Lem11.card_of_lieModel_psl_two hm, hX]

theorem not_lieModel_psl_two_of_isSpor_He
    {X : Type} [Group X] (h : IsSpor X .He) (e : ℕ) :
    ¬ LieModel X .PSL 2 2 e := by
  intro hm
  obtain ⟨f⟩ := h
  have hX : Nat.card X = 4030387200 := by
    rw [Nat.card_congr f.toEquiv]
    exact CFSG.Sporadic.He.card_He
  refine two_pow_mul_four_pow_sub_one_ne (N := 4030387200) (a := 10) (by norm_num) (by decide) e ?_
  rw [← CFSG.Quasithin.H13.Lem11.card_of_lieModel_psl_two hm, hX]

theorem not_lieModel_psl_two_of_isSpor_Ru
    {X : Type} [Group X] (h : IsSpor X .Ru) (e : ℕ) :
    ¬ LieModel X .PSL 2 2 e := by
  intro hm
  obtain ⟨f⟩ := h
  have hX : Nat.card X = 145926144000 := by
    rw [Nat.card_congr f.toEquiv]
    exact CFSG.Sporadic.Ru.card_Ru
  refine two_pow_mul_four_pow_sub_one_ne (N := 145926144000) (a := 14) (by norm_num) (by decide)
    e ?_
  rw [← CFSG.Quasithin.H13.Lem11.card_of_lieModel_psl_two hm, hX]

theorem not_lieModel_psl_two_of_isSpor_ONan
    {X : Type} [Group X] (h : IsSpor X .ONan) (e : ℕ) :
    ¬ LieModel X .PSL 2 2 e := by
  intro hm
  obtain ⟨f⟩ := h
  have hX : Nat.card X = 460815505920 := by
    rw [Nat.card_congr f.toEquiv]
    exact CFSG.Sporadic.ON.card_ON
  refine two_pow_mul_four_pow_sub_one_ne (N := 460815505920) (a := 9) (by norm_num) (by decide) e ?_
  rw [← CFSG.Quasithin.H13.Lem11.card_of_lieModel_psl_two hm, hX]

section OrderCertificates


theorem not_classicalEvenAltG2Der_of_card {X : Type} [Group X] [IsSimpleGroup X] {N : ℕ}
    (hcard : Nat.card X = N)
    (hA : ∀ d f : ℕ, 2 ≤ d → 1 ≤ f → CFSG.Open.ordA (d - 1) (2 ^ f) ≠ N)
    (hU : ∀ d f : ℕ, 3 ≤ d → 1 ≤ f → CFSG.Open.ordTwistedA (d - 1) (2 ^ f) ≠ N)
    (hC : ∀ d f : ℕ, 2 ≤ d → 1 ≤ f → CFSG.Open.ordBC d (2 ^ f) ≠ N)
    (hD : ∀ d f : ℕ, 4 ≤ d → 1 ≤ f → CFSG.Open.ordD d (2 ^ f) ≠ N)
    (hD2 : ∀ d f : ℕ, 4 ≤ d → 1 ≤ f → CFSG.Open.ordTwistedD d (2 ^ f) ≠ N)
    (hG2 : ∀ f : ℕ, 1 ≤ f → CFSG.Open.ordG2 (2 ^ f) ≠ N)
    {b : ℕ} (hb : N < b.factorial / 2)
    (hAlt : ∀ n ∈ Finset.range b, 2 ≤ n → n.factorial / 2 ≠ N) (h6048 : N ≠ 6048) (h1 : N ≠ 1) :
    ¬ ClassicalEvenAltG2Der X := by
  intro hc
  rcases hc with hcl | ⟨n, hG2Der⟩
  · rcases hcl with ⟨hq, t, m, f, ht, hLie⟩ | ⟨hq, n, hAlt'⟩ | ⟨n, hG2'⟩
    · have hqo : CFSG.Open.IsQuasisimple X :=
        ⟨(Group.isPerfect_def).1 hq.1, hq.2.1⟩
      obtain ⟨eQ⟩ := uc22p2214_quotCenter_of_simple (X := X) hqo
      have hLieX : CFSG.Blueprint.LieModel X t m 2 f :=
        CFSG.Blueprint.LieModel.of_mulEquiv eQ.symm hLie
      have hsc : CFSG.Open.StatedClassicalModel X t m 2 f :=
        hLieX.statedClassicalModel (by
          rcases ht with rfl | rfl | rfl | rfl | rfl <;> simp [CFSG.Blueprint.classicalTags])
      have hord := CFSG.Timmesfeld.card_statedClassicalModel_two hsc
      rcases ht with rfl | rfl | rfl | rfl | rfl
      · exact hA m f hsc.1.2.2.1 hsc.1.2.1 ((hord.1 rfl).symm.trans hcard)
      · exact hU m f hsc.1.2.2.1 hsc.1.2.1 ((hord.2.1 rfl).symm.trans hcard)
      · exact hC m f hsc.1.2.2.1 hsc.1.2.1 ((hord.2.2.1 rfl).symm.trans hcard)
      · exact hD m f hsc.1.2.2 hsc.1.2.1 ((hord.2.2.2.1 rfl).symm.trans hcard)
      · exact hD2 m f hsc.1.2.2 hsc.1.2.1 ((hord.2.2.2.2 rfl).symm.trans hcard)
    · have hqo : CFSG.Open.IsQuasisimple X :=
        ⟨(Group.isPerfect_def).1 hq.1, hq.2.1⟩
      obtain ⟨eQ⟩ := uc22p2214_quotCenter_of_simple (X := X) hqo
      obtain ⟨eAlt⟩ := hAlt'
      have hcardAlt : Nat.card (alternatingGroup (Fin n)) = N := by
        rw [← Nat.card_congr (eQ.trans eAlt).toEquiv]
        exact hcard
      by_cases hn2 : 2 ≤ n
      · have : Nontrivial (Fin n) :=
          Fintype.one_lt_card_iff_nontrivial.mp (by
            rw [Fintype.card_fin]
            omega)
        have hfac : n.factorial / 2 = N := by
          rw [← hcardAlt, nat_card_alternatingGroup, Nat.card_fin]
        by_cases hnb : n < b
        · exact hAlt n (Finset.mem_range.mpr hnb) hn2 hfac
        · have hle := Nat.div_le_div_right (c := 2) (Nat.factorial_le (not_lt.mp hnb))
          omega
      · have hbot : alternatingGroup (Fin n) = ⊥ :=
          alternatingGroup.eq_bot_of_card_le_two (by
            rw [Nat.card_fin]
            omega)
        have hc1 : Nat.card (alternatingGroup (Fin n)) = 1 := by
          rw [hbot, Subgroup.card_bot]
        exact h1 (hcardAlt.symm.trans hc1)
    · have hCE : CFSG.Blueprint.ChevalleyExceptionalModel X .G2 2 n :=
        CFSG.Blueprint.LieModel.chevalleyExceptionalModel hG2' (by decide)
      have hordG2 : Nat.card X = CFSG.Open.ordG2 (2 ^ n) := by
        simpa using CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hCE
      exact hG2 n (CFSG.Blueprint.LieModel.admissible hG2').2.1 (hordG2.symm.trans hcard)
  · rcases hG2Der with ⟨rfl, hLie⟩ | ⟨hn2, hG2'⟩
    · exact h6048 (hcard.symm.trans (CFSG.Blueprint.LieModel.card_psu_three_three hLie))
    · have hCE : CFSG.Blueprint.ChevalleyExceptionalModel X .G2 2 n :=
        CFSG.Blueprint.LieModel.chevalleyExceptionalModel hG2' (by decide)
      have hordG2 : Nat.card X = CFSG.Open.ordG2 (2 ^ n) := by
        simpa using CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hCE
      exact hG2 n (by omega) (hordG2.symm.trans hcard)

theorem not_classicalEvenAltG2Der_of_isSpor_J2
    {X : Type} [Group X] (h : IsSpor X .J2) : ¬ ClassicalEvenAltG2Der X := by
  obtain ⟨e⟩ := h
  have : IsSimpleGroup X := e.isSimpleGroup_congr.mpr CFSG.Sporadic.J2.isSimpleGroup_J2
  have hcard : Nat.card X = 604800 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J2.card_J2
  exact not_classicalEvenAltG2Der_of_card hcard
    (ordA_ne_of_two_adic (a := 7) (by norm_num) (by decide))
    (ordTwistedA_ne_of_two_adic (a := 7) (by norm_num) (by decide))
    (ordBC_ne_of_two_adic (a := 7) (by norm_num) (by decide))
    (ordD_ne_of_two_adic (a := 7) (by norm_num) (by decide))
    (ordTwistedD_ne_of_two_adic (a := 7) (by norm_num) (by decide))
    (ordG2_ne_of_two_adic (a := 7) (by norm_num) (by decide))
    (b := 10) (by decide) (by decide) (by norm_num) (by norm_num)

theorem not_classicalEvenAltG2Der_of_isSpor_HS
    {X : Type} [Group X] (h : IsSpor X .HS) : ¬ ClassicalEvenAltG2Der X := by
  obtain ⟨e⟩ := h
  have : IsSimpleGroup X := e.isSimpleGroup_congr.mpr CFSG.Sporadic.HS.isSimpleGroup_HS
  have hcard : Nat.card X = 44352000 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.HS.card_HS
  exact not_classicalEvenAltG2Der_of_card hcard
    (ordA_ne_of_two_adic (a := 9) (by norm_num) (by decide))
    (ordTwistedA_ne_of_two_adic (a := 9) (by norm_num) (by decide))
    (ordBC_ne_of_two_adic (a := 9) (by norm_num) (by decide))
    (ordD_ne_of_two_adic (a := 9) (by norm_num) (by decide))
    (ordTwistedD_ne_of_two_adic (a := 9) (by norm_num) (by decide))
    (ordG2_ne_of_two_adic (a := 9) (by norm_num) (by decide))
    (b := 12) (by decide) (by decide) (by norm_num) (by norm_num)

theorem not_classicalEvenAltG2Der_of_isSpor_He
    {X : Type} [Group X] (h : IsSpor X .He) : ¬ ClassicalEvenAltG2Der X := by
  obtain ⟨e⟩ := h
  have : IsSimpleGroup X := e.isSimpleGroup_congr.mpr CFSG.Sporadic.He.isSimpleGroup_He
  have hcard : Nat.card X = 4030387200 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.He.card_He
  exact not_classicalEvenAltG2Der_of_card hcard
    (ordA_ne_of_two_adic (a := 10) (by norm_num) (by decide))
    (ordTwistedA_ne_of_two_adic (a := 10) (by norm_num) (by decide))
    (ordBC_ne_of_two_adic (a := 10) (by norm_num) (by decide))
    (ordD_ne_of_two_adic (a := 10) (by norm_num) (by decide))
    (ordTwistedD_ne_of_two_adic (a := 10) (by norm_num) (by decide))
    (ordG2_ne_of_two_adic (a := 10) (by norm_num) (by decide))
    (b := 14) (by decide) (by decide) (by norm_num) (by norm_num)

end OrderCertificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
