module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.L2Case
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoCov
import CFSG.LocalAnalysis.ComponentClassification.HarrisEndGA
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitSchur
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

private theorem center_eq_bot_of_dvd_two_of_o2Trivial {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} (hO2 : O2Trivial L)
    (hcard : Nat.card (Subgroup.center ↥L) ∣ 2) : Subgroup.center ↥L = ⊥ := by
  rcases (Nat.dvd_prime Nat.prime_two).mp hcard with h1 | h2
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    have hPn : (((Subgroup.center ↥L).map L.subtype).subgroupOf L).Normal := by
      have hPeq : ((Subgroup.center ↥L).map L.subtype).subgroupOf L =
          Subgroup.center ↥L := by
        rw [← Subgroup.comap_subtype]
        exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
      rw [hPeq]
      infer_instance
    have hP2 : IsPGroup 2 ((Subgroup.center ↥L).map L.subtype) :=
      IsPGroup.of_card (n := 1) (by
        rw [Subgroup.card_map_of_injective L.subtype_injective, h2]
        norm_num)
    have hbot := hO2 _ (Subgroup.map_subtype_le _) hPn hP2
    have hZbot : Subgroup.center ↥L = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center ↥L) L.subtype_injective).mp hbot
    rw [hZbot] at h2
    simp at h2

@[expose] def W4Lem10_6Residual : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)) (t : CFSG.Open.StatedLieTag) (n p e : ℕ),
      L ≤ Y → (L.subgroupOf Y).Normal → Fstar Y = L →
      IsQuasisimple ↥L → O2Trivial L →
      p.Prime → p ≠ 2 → 0 < e → ¬ (t = .PSL ∧ n = 2) →
      LieModel (↥L ⧸ Subgroup.center ↥L) t n p e →
        (9 < p ^ e → E3.aParam Y = 1) ∧
        (3 < p ^ e → E3.aParam Y ≤ 2) ∧
        (p ^ e = 3 → E3.aParam Y ≤ 3)

theorem w4Lem10_6_of_residual
    (h : W4Lem10_6Residual) : W4Lem10_6 := by
  intro W _ _ hW Y L p e q hLY hLn hF hLq hO2 hp hp2 he hq hIn
  rcases hIn with ⟨t, n, p', e', hp', hp2', he', hq', hmodel⟩ | ⟨hq3, hmodel⟩
  · by_cases hpsl : t = .PSL ∧ n = 2
    · obtain ⟨rfl, rfl⟩ := hpsl
      have h6 := w4Lem10_6_psl2 hW hLY hLn hF hLq hO2 hp2' hmodel
      refine ⟨?_, ?_, ?_⟩
      · intro h9
        exact h6.1 (by rw [← hq']; exact h9)
      · intro _
        exact h6.2.trans (by norm_num)
      · intro _
        exact h6.2.trans (by norm_num)
    · have hres := h W hW Y L t n p' e' hLY hLn hF hLq hO2 hp' hp2' he' hpsl hmodel
      rw [hq']
      exact hres
  · subst hq3
    have h6 := w4Lem10_6_psl2_eight hLY hLn hF hLq hO2 hmodel
    exact ⟨fun h9 => by omega, fun h3 => by omega, fun _ => h6⟩

@[expose] def W4Lem10_5Residual : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)) (t : CFSG.Open.StatedLieTag) (n p e : ℕ),
      L ≤ Y → (L.subgroupOf Y).Normal → Fstar Y = L →
      IsQuasisimple ↥L → O2Trivial L →
      p.Prime → p ≠ 2 → 0 < e → ¬ (t = .PSL ∧ n = 2) →
      LieModel (↥L ⧸ Subgroup.center ↥L) t n p e →
        8 ≤ E3.mParam Y ∨
        (LieModel ↥L .PSL 3 3 1 ∧ 4 ≤ E3.mParam Y) ∨
        ((LieModel ↥L .PSL 4 3 1 ∨ LieModel ↥L .PSU 4 3 1 ∨
            LieModel ↥L .G2 0 3 1 ∨
            (∃ (Z : Subgroup ↥L) (hZ : Z.Normal), Z ≤ Subgroup.center ↥L ∧
              Nat.card Z = 3 ∧ LieModel (quotBy Z hZ) .G2 0 3 1) ∨
            LieModel ↥L .PSp 3 3 1) ∧
          6 ≤ E3.mParam Y) ∨
        (LieModel ↥L .PSU 3 3 1 ∨ LieModel ↥L .PSp 2 3 1 ∨
          LieModel ↥L .PSL 2 2 3 ∨
          (LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 4 3 1 ∧
            Subgroup.center ↥L ≠ ⊥)) ∨
        ((LieModel ↥L .PSL 2 5 2 ∨ LieModel ↥L .PSL 2 p 1) ∧ 4 ≤ E3.mParam Y) ∨
        (LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 5 1 ∨
          LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 7 1 ∨
          LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 3 2)

section TenFive


private theorem card_center_dvd_two_of_psl2_odd {L : Type} [Group L] [Finite L]
    (hL : CFSG.IsQuasisimple L) {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h9 : p ^ e ≠ 9) (hm : LieModel (L ⧸ Subgroup.center L) .PSL 2 p e) :
    Nat.card (Subgroup.center L) ∣ 2 := by
  have hdvd : Nat.card (Subgroup.center L) ∣
      Nat.card (CFSG.Open.griessHopfMultiplier (L ⧸ Subgroup.center L)) :=
    CFSG.Sporadic.Recognition.HeMultiplier.card_center_dvd_griess
      (S := L ⧸ Subgroup.center L) hL.1 (MulEquiv.refl _)
  have hGA := CFSG.ComponentClassification.TBLit.griessMultipliersOdd_holds
  have hcard := CFSG.ComponentClassification.HarrisLit.card_griessHopfMultiplier_eq_odd hGA
    (CFSG.ComponentClassification.HarrisLit.models_lieModel_of_lieModel_of_ne_zero
      (by norm_num : (2 : ℕ) ≠ 0) hm) hp2 (Or.inl rfl)
  have hgcd : Nat.gcd 2 (p ^ e - 1) = 2 := by
    have hoddq : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
    obtain ⟨k, hk⟩ := hoddq
    rw [hk, Nat.add_sub_cancel, Nat.gcd_eq_left (dvd_mul_right 2 k)]
  have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 2 p e = (1, 1) := by
    unfold CFSG.Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  have h2 : Nat.card (CFSG.Open.griessHopfMultiplier (L ⧸ Subgroup.center L)) = 2 := by
    rw [hcard,
      show CFSG.Blueprint.Multiplier.genericOrders .PSL 2 p e =
        (Nat.gcd 2 (p ^ e - 1), 1) from rfl, hexc, hgcd]
    norm_num
  simpa [h2] using hdvd

theorem w4Lem10_5_psl2 (h74 : W4Lem7_4) {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)} {p e : ℕ} (hLY : L ≤ Y)
    (hLn : (L.subgroupOf Y).Normal) (hF : Fstar Y = L) (hLq : IsQuasisimple ↥L)
    (hO2 : O2Trivial L) (hp : p.Prime) (hp2 : p ≠ 2) (he : 0 < e)
    (hmodel : LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 p e) :
      8 ≤ E3.mParam Y ∨
        (LieModel ↥L .PSL 3 3 1 ∧ 4 ≤ E3.mParam Y) ∨
        ((LieModel ↥L .PSL 4 3 1 ∨ LieModel ↥L .PSU 4 3 1 ∨
            LieModel ↥L .G2 0 3 1 ∨
            (∃ (Z : Subgroup ↥L) (hZ : Z.Normal), Z ≤ Subgroup.center ↥L ∧
              Nat.card Z = 3 ∧ LieModel (quotBy Z hZ) .G2 0 3 1) ∨
            LieModel ↥L .PSp 3 3 1) ∧
          6 ≤ E3.mParam Y) ∨
        (LieModel ↥L .PSU 3 3 1 ∨ LieModel ↥L .PSp 2 3 1 ∨
          LieModel ↥L .PSL 2 2 3 ∨
          (LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 4 3 1 ∧
            Subgroup.center ↥L ≠ ⊥)) ∨
        ((LieModel ↥L .PSL 2 5 2 ∨ LieModel ↥L .PSL 2 p 1) ∧ 4 ≤ E3.mParam Y) ∨
        (LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 5 1 ∨
          LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 7 1 ∨
          LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 3 2) := by
  set q := p ^ e with hq
  have hqne3 : p ^ e ≠ 3 := by
    have hAdm := (CFSG.GH74.Generic.stated_of_lieModel_PSL hmodel).1
    simp only [CFSG.Open.StatedLieAdmissible] at hAdm
    obtain ⟨-, -, -, -, hne3⟩ := hAdm
    intro h
    exact hne3 (by rw [h])
  by_cases hqle : q ≤ 9
  · have hoddq : Odd q := by rw [hq]; exact (hp.odd_of_ne_two hp2).pow
    have hqne3q : q ≠ 3 := by rw [hq]; exact hqne3
    have hq2 : 2 ≤ q := by
      rw [hq]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
        _ ≤ p ^ e := Nat.pow_le_pow_left hp.two_le e
    have hqmem : q = 5 ∨ q = 7 ∨ q = 9 := by
      obtain ⟨k, hk⟩ := hoddq
      have hk2 : 2 ≤ k := by omega
      have hk4 : k ≤ 4 := by omega
      interval_cases k
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by omega))
    rcases hqmem with hq5 | hq7 | hq9
    · have hpe5 : p = 5 ∧ e = 1 := by
        have h5 : p ^ e = 5 ^ 1 := by rw [pow_one, ← hq]; exact hq5
        exact Nat.Prime.pow_inj' hp Nat.prime_five (by omega) (by norm_num) h5
      obtain ⟨rfl, rfl⟩ := hpe5
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmodel)))))
    · have hpe7 : p = 7 ∧ e = 1 := by
        have h7 : p ^ e = 7 ^ 1 := by rw [pow_one, ← hq]; exact hq7
        exact Nat.Prime.pow_inj' hp Nat.prime_seven (by omega) (by norm_num) h7
      obtain ⟨rfl, rfl⟩ := hpe7
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmodel))))))
    · have hpe9 : p = 3 ∧ e = 2 := by
        have h9 : p ^ e = 3 ^ 2 := by norm_num; rw [← hq]; exact hq9
        exact Nat.Prime.pow_inj' hp Nat.prime_three (by omega) (by norm_num) h9
      obtain ⟨rfl, rfl⟩ := hpe9
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hmodel))))))
  · have hq9 : 9 < q := by omega
    have hZ : Subgroup.center ↥L = ⊥ :=
      center_eq_bot_of_dvd_two_of_o2Trivial hO2
        (card_center_dvd_two_of_psl2_odd hLq hp hp2 (by omega) hmodel)
    have hmodelL : LieModel ↥L .PSL 2 p e := CFSG.Timmesfeld.lieModel_of_center_eq_bot hZ hmodel
    have h74r := h74 W hW Y L p e q hLY hLn hF hp hp2 he hq hq9 hmodelL
    by_cases he1 : e = 1
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr ?_,
        h74r.2.2.2.2⟩))))
      rw [he1] at hmodelL
      exact hmodelL
    · have he2 : 1 < e := by omega
      rcases h74r.2.2.2.1 he2 with h8 | ⟨h25, -⟩
      · exact Or.inl h8
      · have hpe25 : p = 5 ∧ e = 2 := by
          have h25' : p ^ e = 5 ^ 2 := by rw [← hq, h25]; norm_num
          exact Nat.Prime.pow_inj' hp Nat.prime_five (by omega) (by norm_num) h25'
        obtain ⟨rfl, rfl⟩ := hpe25
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl ?_,
          h74r.2.2.2.2⟩))))
        exact hmodelL

theorem w4Lem10_5_of_residual (h74 : W4Lem7_4) (h : W4Lem10_5Residual) : W4Lem10_5 := by
  intro W _ _ hW Y L p e q hLY hLn hF hLq hO2 hp hp2 he hq hIn
  rcases hIn with ⟨t, n, p', e', hp', hp2', he', hq', hmodel⟩ | ⟨hq3, hmodel⟩
  · have hpq : p = p' ∧ e = e' := by
      have hpe : p ^ e = p' ^ e' := by rw [← hq, hq']
      exact Nat.Prime.pow_inj' hp hp' (by omega) (by omega) hpe
    obtain ⟨rfl, rfl⟩ := hpq
    by_cases hpsl : t = .PSL ∧ n = 2
    · obtain ⟨rfl, rfl⟩ := hpsl
      exact w4Lem10_5_psl2 h74 hW hLY hLn hF hLq hO2 hp hp2 he hmodel
    · exact h W hW Y L t n p e hLY hLn hF hLq hO2 hp hp2 he hpsl hmodel
  · subst hq3
    have hZ : Subgroup.center ↥L = ⊥ :=
      CFSG.GH74.GLS.Stage2.Signalizer.Odd87.center_eq_bot_psl2_even hLq (Or.inl rfl) hmodel
    have hmodelL : LieModel ↥L .PSL 2 2 3 := CFSG.Timmesfeld.lieModel_of_center_eq_bot hZ hmodel
    exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl hmodelL))))))

end TenFive

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
