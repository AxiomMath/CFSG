module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatStatement
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatAlt
public import CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (ProperFixedComponent IsAltType)
open scoped Nat

theorem card_of_lieModel_PSU_two_pow {X : Type} [Group X] {m f : ℕ}
    (h : LieModel X .PSU m 2 f) : Nat.card X = Open.ordTwistedA (m - 1) (2 ^ f) := by
  rcases h with ⟨-, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact (Timmesfeld.card_statedClassicalModel_two h).2.1 rfl
  · simp [chevalleyExceptionalTags] at ht
  · simp [reeTitsTags] at ht
  · cases ht

theorem admissible_of_lieModel_PSU {X : Type} [Group X] {m f : ℕ}
    (h : LieModel X .PSU m 2 f) : 1 ≤ f ∧ 3 ≤ m ∧ (m, 2 ^ f) ≠ (3, 2) := by
  rcases h with ⟨-, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · obtain ⟨⟨-, hf, hm, h32⟩, -⟩ := h
    exact ⟨hf, hm, h32⟩
  · simp [chevalleyExceptionalTags] at ht
  · simp [reeTitsTags] at ht
  · cases ht

theorem twistedA_factor_le {q : ℕ} (hq : 2 ≤ q) (i : ℕ) :
    (((q : ℤ) ^ i - (-1) ^ i).toNat) ≤ q ^ (i + 1) := by
  have h1 : 1 ≤ q ^ i := Nat.one_le_pow _ _ (by omega)
  have h2 : q ^ i + 1 ≤ q ^ (i + 1) := by
    rw [pow_succ]
    nlinarith
  rcases Nat.even_or_odd i with hi | hi
  · rw [Timmesfeld.Orders.toNat_pow_sub_neg_one_pow_of_even (by omega) hi]
    omega
  · rw [Timmesfeld.Orders.toNat_pow_sub_neg_one_pow_of_odd hi]
    exact h2

theorem prod_twistedA_factors_le {q : ℕ} (hq : 2 ≤ q) {n : ℕ} (hn : 1 ≤ n) :
    ∏ i ∈ Finset.Icc 2 (n + 1), (((q : ℤ) ^ i - (-1) ^ i).toNat) ≤ q ^ (n * (n + 1)) := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [show (1 + 1 : ℕ) = 2 by rfl, Finset.Icc_self, Finset.prod_singleton,
      Timmesfeld.Orders.toNat_pow_sub_neg_one_pow_of_even (by omega) even_two, one_mul]
    omega
  | succ n hn ih =>
    rw [Finset.prod_Icc_succ_top (by omega : 2 ≤ n + 1 + 1)]
    calc (∏ i ∈ Finset.Icc 2 (n + 1), (((q : ℤ) ^ i - (-1) ^ i).toNat)) *
          (((q : ℤ) ^ (n + 1 + 1) - (-1) ^ (n + 1 + 1)).toNat)
        ≤ q ^ (n * (n + 1)) * q ^ (n + 1 + 1 + 1) :=
          Nat.mul_le_mul ih (twistedA_factor_le hq _)
      _ = q ^ (n * (n + 1) + (n + 3)) := by rw [← pow_add]
      _ ≤ q ^ ((n + 1) * (n + 1 + 1)) :=
          Nat.pow_le_pow_right (by omega) (by nlinarith)

theorem ordTwistedA_two_pow_bounds {n f : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f) :
    2 ^ (f * (n * (n + 1) / 2)) ∣ Open.ordTwistedA n (2 ^ f) ∧
      0 < Open.ordTwistedA n (2 ^ f) ∧
      Open.ordTwistedA n (2 ^ f) ≤ 2 ^ (3 * (f * (n * (n + 1) / 2))) := by
  obtain ⟨r, hr, hm⟩ := (Timmesfeld.Orders.profile_ordTwistedA hn hf).two
  set q := 2 ^ f with hq
  set T := n * (n + 1) / 2 with hT
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hT2 : n * (n + 1) = 2 * T := by
    rw [hT]
    exact (Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd).symm
  refine ⟨hm ▸ Dvd.intro _ rfl, hm ▸ Nat.mul_pos (by positivity) hr.pos, ?_⟩
  have hP := prod_twistedA_factors_le hq2 (by omega : 1 ≤ n)
  calc Open.ordTwistedA n q
      ≤ q ^ T * ∏ i ∈ Finset.Icc 2 (n + 1), (((q : ℤ) ^ i - (-1) ^ i).toNat) := by
        rw [Open.ordTwistedA]
        exact Nat.div_le_self _ _
    _ ≤ q ^ T * q ^ (n * (n + 1)) := Nat.mul_le_mul_left _ hP
    _ = 2 ^ (3 * (f * T)) := by
        rw [hq, ← pow_mul, ← pow_mul, ← pow_add, hT2]
        congr 1
        ring

theorem two_pow_six_dvd_ordTwistedA {m f : ℕ} (hm : 4 ≤ m) (hf : 1 ≤ f) :
    2 ^ 6 ∣ Open.ordTwistedA (m - 1) (2 ^ f) := by
  obtain ⟨hdvd, -, -⟩ := ordTwistedA_two_pow_bounds (by omega : 2 ≤ m - 1) hf
  have hT6 : 6 ≤ (m - 1) * (m - 1 + 1) / 2 := by
    have : 3 * 4 ≤ (m - 1) * (m - 1 + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hTM : (m - 1) * (m - 1 + 1) / 2 ≤ f * ((m - 1) * (m - 1 + 1) / 2) :=
    Nat.le_mul_of_pos_left _ hf
  exact (Nat.pow_dvd_pow 2 (hT6.trans hTM)).trans hdvd

theorem two_pow_six_dvd_card_of_lieModel_PSU {X : Type} [Group X] {m f : ℕ} (hm : 4 ≤ m)
    (h : LieModel X .PSU m 2 f) : 2 ^ 6 ∣ Nat.card X := by
  rw [card_of_lieModel_PSU_two_pow h]
  exact two_pow_six_dvd_ordTwistedA hm (admissible_of_lieModel_PSU h).1

theorem ordTwistedA_three_two_eq : Open.ordTwistedA 3 (2 ^ 1) = 25920 := by decide

theorem ordTwistedA_three_four_eq : Open.ordTwistedA 3 (2 ^ 2) = 1018368000 := by decide

theorem ordTwistedA_four_two_eq : Open.ordTwistedA 4 (2 ^ 1) = 13685760 := by decide

theorem ordTwistedA_two_pow_ne_factorial_div_two {n f k : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f) :
    Open.ordTwistedA n (2 ^ f) ≠ k ! / 2 := by
  intro hk
  obtain ⟨hdvd, hpos, hle⟩ := ordTwistedA_two_pow_bounds (by omega : 2 ≤ n) hf
  set M := f * (n * (n + 1) / 2) with hM
  have hk2 : 2 ≤ k := by
    by_contra h
    interval_cases k <;> simp at hk <;> omega
  have hk! : k ! = 2 * Open.ordTwistedA n (2 ^ f) := by
    rw [hk, Nat.mul_div_cancel' (Nat.dvd_factorial (by norm_num) hk2)]
  have hdvd2 : 2 ^ (M + 1) ∣ k ! := by
    rw [hk!, pow_succ, mul_comm]
    exact Nat.mul_dvd_mul_left 2 hdvd
  have hlt : M + 1 < k := by
    have h1 := Nat.emultiplicity_two_factorial_lt (show k ≠ 0 by omega)
    have h2 := le_emultiplicity_of_pow_dvd hdvd2
    exact_mod_cast lt_of_le_of_lt h2 h1
  have hfac : (M + 2)! ≤ k ! := Nat.factorial_le (by omega)
  have hkle : k ! ≤ 2 ^ (3 * M + 1) := by
    rw [hk!, pow_succ]
    omega
  have hM12 : M ≤ 12 := by
    by_contra h
    have := LinearPilot.two_pow_lt_factorial_of_thirteen_le (show 13 ≤ M by omega)
    omega
  have hT6 : 6 ≤ n * (n + 1) / 2 := by
    have : 3 * 4 ≤ n * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hTM : n * (n + 1) / 2 ≤ M := Nat.le_mul_of_pos_left _ hf
  have hf2 : f ≤ 2 := by
    by_contra h
    have : 3 * 6 ≤ f * (n * (n + 1) / 2) := Nat.mul_le_mul (by omega) hT6
    omega
  have hn4 : n ≤ 4 := by
    by_contra h
    have : 5 * 6 ≤ n * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hk16 : k < 16 := by
    by_contra h
    have h1 : (16 : ℕ)! ≤ k ! := Nat.factorial_le (by omega)
    have h2 : 2 ^ (3 * M + 1) ≤ 2 ^ 37 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ 37 < (16 : ℕ)! := by decide
    omega
  interval_cases n <;> interval_cases f <;> simp only [hM] at hM12 hlt
  · rw [ordTwistedA_three_two_eq] at hk
    revert hk
    interval_cases k <;> decide
  · rw [ordTwistedA_three_four_eq] at hk
    revert hk
    interval_cases k <;> decide
  · rw [ordTwistedA_four_two_eq] at hk
    revert hk
    interval_cases k <;> decide
  · omega

theorem catSUmAlternating : CatSUmAlternating := by
  intro S _ _ _ _ ⟨n, hn, ⟨e⟩⟩ σ hσ m f D hm hD hDm
  have hf : 1 ≤ f := (admissible_of_lieModel_PSU hDm).1
  have hcardDZ := card_of_lieModel_PSU_two_pow hDm
  have hσ2 : σ ^ 2 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hσσ : ∀ y, σ (σ y) = y := fun y => by
    have := congrArg (fun ψ : MulAut S => ψ y) hσ2
    simpa [pow_two] using this
  set P : Subgroup S := D.map (fixedSubgroup σ).subtype with hPdef
  have hPF : P ≤ fixedSubgroup σ := map_subtype_le D
  have hPsub : P.subgroupOf (fixedSubgroup σ) = D :=
    comap_map_eq_self_of_injective (fixedSubgroup σ).subtype_injective D
  have hPne : P ≠ ⊤ := by
    intro htop
    have hσ1 : σ = 1 := by
      ext y
      exact hPF (htop ▸ mem_top y)
    rw [hσ1, orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  have hPC : ProperFixedComponent σ P :=
    ⟨hσσ, hPF, hPsub ▸ LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD, hPne⟩
  have hcardP : Nat.card P = Nat.card D :=
    card_map_of_injective (fixedSubgroup σ).subtype_injective
  have hdvdS : Nat.card (D ⧸ center D) ∣ Nat.card S :=
    (card_quotient_dvd_card (center D)).trans (hcardP ▸ card_subgroup_dvd_card P)
  have hSn : Nat.card S = n ! / 2 := by
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  by_cases hn6 : n = 6
  · subst hn6
    rw [hSn, hcardDZ, show (6 : ℕ)! / 2 = 360 by decide] at hdvdS
    exact absurd ((two_pow_six_dvd_ordTwistedA hm hf).trans hdvdS) (by decide)
  ·
    set L := P.subgroupOf (fixedSubgroup σ) with hLdef
    let eLD : L ≃* D := MulEquiv.subgroupCongr hPsub
    have hqL : IsQuasisimple L := (LocalAnalysis.ComponentInitial.isQuasisimple_congr eLD).2 hD.1
    obtain ⟨-, ⟨eZ⟩⟩ := hPC.fusionZStar_equiv_of_quasisimple hqL
    let eP : P ⧸ Open.fusionZStar P ≃* D ⧸ center D :=
      eZ.trans (QuotientGroup.congr (center L) (center D) eLD (Subgroup.map_center_eq eLD))
    obtain ⟨hPC', ⟨eT⟩⟩ := hPC.map e
    have hAlt := CFSG.ComponentClassification.CatLeaf.isAltType_of_properFixedComponent_alternating
      hn hn6 hPC'
    have hAltD : IsAltType (D ⧸ center D) := IsAltType.of_mulEquiv (eP.symm.trans eT) hAlt
    obtain ⟨Ω, _, _, hΩ, ⟨eA⟩⟩ := hAltD
    have : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have hcardΩ : Open.ordTwistedA (m - 1) (2 ^ f) = (Fintype.card Ω)! / 2 := by
      rw [← hcardDZ, Nat.card_congr eA.toEquiv, nat_card_alternatingGroup,
        Nat.card_eq_fintype_card]
    exact ordTwistedA_two_pow_ne_factorial_div_two (by omega) hf hcardΩ

end CFSG.SeitzReduction.UnitaryPilot
