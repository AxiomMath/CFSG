module

public import CFSG.LocalAnalysis.StandardType.GGExcLeviRankBase
public import CFSG.LocalAnalysis.StandardType.GGExcKGRankKnown

public section

namespace CFSG.StandardType.E8LeviG3

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.Assembly CFSG.ComponentClassification.CatLeafProof
open CFSG.StandardType.F4Rest
open scoped MatrixGroups


theorem pRank_le_three_of_e6_model {S : Type} [Group S] [Finite S] {n p : ℕ}
    (hQs : CFSG.IsQuasisimple S)
    (hmodel : LieModel (S ⧸ Subgroup.center S) .E6 0 2 n)
    (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ orderOf (((2 ^ n : ℕ)) : ZMod p)) :
    CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hZ : ¬ p ∣ Nat.card (Subgroup.center S) := by
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models
      (S ⧸ Subgroup.center S) .E6 0 2 n hmodel
    have hg : CFSG.Blueprint.Multiplier.genericOrders .E6 0 2 n =
        (Nat.gcd 3 (2 ^ n - 1), 1) := rfl
    have he : CFSG.Blueprint.Multiplier.exceptionalOrders .E6 0 2 n = (1, 1) := rfl
    have hcard : Nat.card (CFSG.Open.griessHopfMultiplier (S ⧸ Subgroup.center S)) =
        Nat.gcd 3 (2 ^ n - 1) := by
      rw [Nat.card_congr eM.toEquiv,
        CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_generic_exceptional', hg, he]
      norm_num
    haveI : Finite (CFSG.Open.griessHopfMultiplier (S ⧸ Subgroup.center S)) :=
      Nat.finite_of_card_ne_zero
        (by rw [hcard]; exact (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne')
    have hdvd := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hQs
      (MulEquiv.refl (S ⧸ Subgroup.center S))
    rw [hcard] at hdvd
    intro hpZ
    have h3dvd : p ∣ Nat.gcd 3 (2 ^ n - 1) := hpZ.trans hdvd
    have hp3 : p = 3 :=
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (h3dvd.trans (Nat.gcd_dvd_left _ _))
    have hpgt : 3 < p := three_lt_of_three_le_orderOf_natCast hp h3
    omega
  have hq : CFSG.Open.pRank p (⊤ : Subgroup (S ⧸ Subgroup.center S)) ≤ 3 := by
    obtain ⟨-, F', hF', hFin', hFcard', ⟨φ⟩⟩ :=
      hmodel.chevalleyExceptionalModel (by decide : StatedLieTag.E6 ∈ chevalleyExceptionalTags)
    letI : Field F' := hF'
    letI : Finite F' := hFin'
    let χ : AdjointQuotient .E6 F' ≃* adjointGroup .E6 F' :=
      (QuotientGroup.quotientMulEquivOfEq
        (center_adjointGroup_eq_bot (τ := Tag.E6) (K := F'))).trans QuotientGroup.quotientBot
    have he : CFSG.Open.pRank p (⊤ : Subgroup (S ⧸ Subgroup.center S)) =
        CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup .E6 F')) :=
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (φ.trans χ)
    rw [he]
    have hpq' : ¬ p ∣ Nat.card F' := by
      rw [hFcard']; exact not_dvd_of_three_le_orderOf_natCast hp h3
    have heord : orderOf ((Nat.card F' : ℕ) : ZMod p) =
        orderOf (((2 ^ n : ℕ)) : ZMod p) := by rw [hFcard']
    have hne1 : orderOf ((Nat.card F' : ℕ) : ZMod p) ≠ 1 := by rw [heord]; omega
    have hne2 : orderOf ((Nat.card F' : ℕ) : ZMod p) ≠ 2 := by rw [heord]; omega
    exact CFSG.SectionRank.pRank_le hp.one_lt fun E _ hE =>
      kgr_rankLE3_E6 F' hp (three_lt_of_three_le_orderOf_natCast hp h3) hpq'
        ⟨hne1, hne2⟩ E hE
  calc CFSG.Open.pRank p (⊤ : Subgroup S)
      = CFSG.Open.pRank p (⊤ : Subgroup (S ⧸ Subgroup.center S)) :=
        (CFSG.SectionRank.pRank_quotient_eq (p := p) (G := S) (Subgroup.center S) hZ).symm
    _ ≤ 3 := hq

theorem card_le_pow_three_subsystemGroup_e8E6 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ CFSG.StandardType.OrdPNS.ordQ K p)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K (Set.range e8E6Node))
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 3 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, -, hK⟩ := FiniteField.card K 2
  have hKn : Nat.card K = 2 ^ (n : ℕ) := by rw [← Fintype.card_eq_nat_card]; exact hK
  have hn : 1 ≤ (n : ℕ) := CFSG.Quasithin.R3c2.one_le_of_natCard_eq_two_pow hKn
  obtain ⟨O, C, hE'⟩ := exists_e8_chevalleyExtras K
  obtain ⟨ρ, hρ, hcomm, hψ⟩ := exists_levi_frame hE' rfl e8E6Node e8E6_adj e8E6_nadj
  have hadm : StatedLieAdmissible .E6 0 2 (n : ℕ) := ⟨Nat.prime_two, hn, rfl⟩
  obtain ⟨Ψ, hker, hrange, hqs, hmodel⟩ :=
    e6_frame_subgroup hadm hKn
      (U := fun k => CFSG.LieType.CurtisTits.rankOne (e8Datum K).rootGroup (e8E6Node k))
      hcomm hρ hψ
  have hqs' : CFSG.IsQuasisimple ↥Ψ.range := by
    rw [hrange]; exact hqs
  have hmodel' : LieModel (↥Ψ.range ⧸ Subgroup.center ↥Ψ.range) .E6 0 2 (n : ℕ) := by
    rw [hrange]; exact hmodel
  have h3' : 3 ≤ orderOf (((2 ^ (n : ℕ) : ℕ)) : ZMod p) := by
    rw [← hKn, ← CFSG.StandardType.OrdPNS.ordQ_def]
    exact h3
  have hS : CFSG.Open.pRank p (⊤ : Subgroup Ψ.range) ≤ 3 :=
    pRank_le_three_of_e6_model hqs' hmodel' hp hp2 h3'
  have hEmap : E ≤ Ψ.range.map (adjointGroup Tag.E8 K).subtype := by
    rw [hrange, map_subtype_iSup_rankOne e8E6Node]
    exact hE
  exact card_le_pow_of_le_map_subtype hp hS hEmap hEel

theorem pRank_le_three_of_e7_model {S : Type} [Group S] [Finite S] {n p : ℕ}
    (hQs : CFSG.IsQuasisimple S)
    (hmodel : LieModel (S ⧸ Subgroup.center S) .E7 0 2 n)
    (hn : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ orderOf (((2 ^ n : ℕ)) : ZMod p)) :
    CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hZ : ¬ p ∣ Nat.card (Subgroup.center S) := by
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models
      (S ⧸ Subgroup.center S) .E7 0 2 n hmodel
    have hg : CFSG.Blueprint.Multiplier.genericOrders .E7 0 2 n =
        (Nat.gcd 2 (2 ^ n - 1), 1) := rfl
    have he : CFSG.Blueprint.Multiplier.exceptionalOrders .E7 0 2 n = (1, 1) := rfl
    have hodd : Odd (2 ^ n - 1) :=
      CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (a := n) (by omega)
    have hgcd : Nat.gcd 2 (2 ^ n - 1) = 1 :=
      (Nat.coprime_two_left.mpr hodd).gcd_eq_one
    have hcard : Nat.card (CFSG.Open.griessHopfMultiplier (S ⧸ Subgroup.center S)) = 1 := by
      rw [Nat.card_congr eM.toEquiv,
        CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_generic_exceptional', hg, he, hgcd]
      norm_num
    haveI : Finite (CFSG.Open.griessHopfMultiplier (S ⧸ Subgroup.center S)) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    have hdvd := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hQs
      (MulEquiv.refl (S ⧸ Subgroup.center S))
    rw [hcard] at hdvd
    intro hpZ
    exact hp.ne_one (Nat.dvd_one.mp (hpZ.trans hdvd))
  have hq : CFSG.Open.pRank p (⊤ : Subgroup (S ⧸ Subgroup.center S)) ≤ 3 := by
    obtain ⟨-, F', hF', hFin', hFcard', ⟨φ⟩⟩ :=
      hmodel.chevalleyExceptionalModel (by decide : StatedLieTag.E7 ∈ chevalleyExceptionalTags)
    letI : Field F' := hF'
    letI : Finite F' := hFin'
    let χ : AdjointQuotient .E7 F' ≃* adjointGroup .E7 F' :=
      (QuotientGroup.quotientMulEquivOfEq
        (center_adjointGroup_eq_bot (τ := Tag.E7) (K := F'))).trans QuotientGroup.quotientBot
    have he : CFSG.Open.pRank p (⊤ : Subgroup (S ⧸ Subgroup.center S)) =
        CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup .E7 F')) :=
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (φ.trans χ)
    rw [he]
    have hpq' : ¬ p ∣ Nat.card F' := by
      rw [hFcard']; exact not_dvd_of_three_le_orderOf_natCast hp h3
    have heord : orderOf ((Nat.card F' : ℕ) : ZMod p) =
        orderOf (((2 ^ n : ℕ)) : ZMod p) := by rw [hFcard']
    have hne1 : orderOf ((Nat.card F' : ℕ) : ZMod p) ≠ 1 := by rw [heord]; omega
    have hne2 : orderOf ((Nat.card F' : ℕ) : ZMod p) ≠ 2 := by rw [heord]; omega
    exact CFSG.SectionRank.pRank_le hp.one_lt fun E _ hE =>
      kgr_rankLE3_E7 F' hp (three_lt_of_three_le_orderOf_natCast hp h3) hpq'
        ⟨hne1, hne2⟩ E hE
  calc CFSG.Open.pRank p (⊤ : Subgroup S)
      = CFSG.Open.pRank p (⊤ : Subgroup (S ⧸ Subgroup.center S)) :=
        (CFSG.SectionRank.pRank_quotient_eq (p := p) (G := S) (Subgroup.center S) hZ).symm
    _ ≤ 3 := hq

theorem card_le_pow_three_subsystemGroup_e8E7 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ CFSG.StandardType.OrdPNS.ordQ K p)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K e8LeviE7)
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 3 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, -, hK⟩ := FiniteField.card K 2
  have hKn : Nat.card K = 2 ^ (n : ℕ) := by rw [← Fintype.card_eq_nat_card]; exact hK
  have hn : 1 ≤ (n : ℕ) := CFSG.Quasithin.R3c2.one_le_of_natCard_eq_two_pow hKn
  have hadm : StatedLieAdmissible .E7 0 2 (n : ℕ) := ⟨Nat.prime_two, hn, rfl⟩
  obtain ⟨Ψ, hker, hrange, hqs, hmodel⟩ :=
    exists_psi_E7_E8 (p := 2) (f := (n : ℕ)) hadm hKn
  have hqs' : CFSG.IsQuasisimple ↥Ψ.range := by
    rw [hrange]; exact hqs
  have hmodel' : LieModel (↥Ψ.range ⧸ Subgroup.center ↥Ψ.range) .E7 0 2 (n : ℕ) := by
    rw [hrange]; exact hmodel
  have h3' : 3 ≤ orderOf (((2 ^ (n : ℕ) : ℕ)) : ZMod p) := by
    rw [← hKn, ← CFSG.StandardType.OrdPNS.ordQ_def]
    exact h3
  have hS : CFSG.Open.pRank p (⊤ : Subgroup Ψ.range) ≤ 3 :=
    pRank_le_three_of_e7_model hqs' hmodel' hn hp hp2 h3'
  have hEmap : E ≤ Ψ.range.map (adjointGroup Tag.E8 K).subtype := by
    rw [hrange, map_subtype_iSup_rankOne e8E7Node]
    exact hE
  exact card_le_pow_of_le_map_subtype hp hS hEmap hEel

end CFSG.StandardType.E8LeviG3
