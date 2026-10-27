module

public import CFSG.RankThree.GF2n.Smith81.InspOrth
public import CFSG.RankThree.GF2n.Smith81.OrthFour
import CFSG.RankThree.GF2n.Smith81.InspOrthAutCube
import CFSG.RankThree.GF2n.Smith81.InspE3
import CFSG.RankThree.GF2n.Stroth80.Sec1110Core

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG CFSG.Blueprint CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80 CFSG.Timmesfeld CFSG.Timmesfeld.Orders CFSG.CGT.Timmesfeld75
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem factorization_card_mulAut_sl2_le {X : Type} [Group X] {f : ℕ} (hf : 2 ≤ f)
    (hX : IsSLModel 2 (2 ^ f) X) :
    (Nat.card (MulAut X)).factorization 2 ≤ f + f.factorization 2 := by
  obtain ⟨-, hc, ho⟩ := sl2_model_facts hf hX
  have hX0 : Nat.card X ≠ 0 := by
    rw [hc]
    have : 4 ≤ (2 ^ f) ^ 2 := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (f * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = (2 ^ f) ^ 2 := by rw [pow_mul]
    exact mul_ne_zero (by positivity) (by omega)
  haveI : Finite X := Nat.finite_of_card_ne_zero hX0
  have hO0 : Nat.card (Outer X) ≠ 0 := Nat.card_pos.ne'
  have h := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' (mul_ne_zero hO0 hX0)).mpr
    (card_mulAut_dvd_outer_mul X) 2
  have hO := (Nat.factorization_le_iff_dvd hO0 (by omega)).mpr ho 2
  have hvX : (Nat.card X).factorization 2 = f := by
    rw [hc]
    have hodd : Odd ((2 ^ f) ^ 2 - 1) := by
      have h1 : 2 ∣ (2 ^ f) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
      have h2 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      rw [Nat.odd_iff]
      omega
    exact factorization_two_eq_of_odd rfl hodd
  rw [Nat.factorization_mul hO0 hX0, Finsupp.add_apply, hvX] at h
  omega

theorem orthE2Minus_small (h212 : Smith212OrthCoreStatement) (hK1 : K1NSLStatement)
    (hK2L : K2PSLStatement2) (hKCO : KCOmegaStatement2)
    (hKC4 : KCOmegaFourStatement) {G : Type} [Group G] [Finite G]
    {M Q Z B : Subgroup G} (hc : SmithOrthCfg M Q Z B)
    (hroot : ∀ z ∈ Z, z ≠ 1 → Timmesfeld.IsRootInvolutionSet (conjClassSet z)) {t : G} {m : ℕ}
    (hm : m ≤ 3) (hD4 : CtxD4 M Q Z B t) (hcase : CaseE2Minus M Q Z B t m) :
    ∃ f : ℕ, Nat.card Z = 2 ^ f ∧ LieModel (FStar G) .POmegaMinus (m + 2) 2 f := by
  have H := hc.ctx.hyp
  obtain ⟨z, hz, hz1, -⟩ := exists_mem_Z_ne H 1
  obtain ⟨hF, -⟩ := generalizedFitting_eq_normalClosure H hz hz1
  obtain ⟨f, k₀, hf, -⟩ := H.cp
  have hf2 : 2 ≤ f := by
    have h4 := H.q4
    rw [hf] at h4
    by_contra hlt
    push Not at hlt
    interval_cases f <;> norm_num at h4
  obtain ⟨hm2, hQ, -, -, hT⟩ := hcase
  rw [hf] at hT
  obtain ⟨hN, A, Bo, _, _, hA, hB, ⟨e⟩⟩ := hT
  obtain ⟨hBs, hBc, hBo⟩ : IsSimpleGroup Bo ∧ Nat.card Bo = ordTwistedD m (2 ^ f) ∧
      ordProj[2] (Nat.card (Outer Bo)) ≤ 4 * ordProj[2] f := by
    rcases (show m = 2 ∨ m = 3 by omega) with rfl | rfl
    · exact omegaMinus_two_model_facts hf2 hB
    · exact omegaMinus_three_model_facts hf2 hB
  obtain ⟨t', hL, hsign | hsign⟩ := orthE2_identify h212 hK1 hK2L hKCO hc hroot hD4 hm2
    (fun _ => hKC4) hQ hf e
    hA hBs hBc hBo (Or.inr rfl) hz hz1
  · exact absurd hsign.2 (not_ordD_dvd_ordTwistedD hf2 (by omega)).2
  · obtain ⟨rfl, -⟩ := hsign
    exact ⟨f, hf, LieModel.of_mulEquiv (MulEquiv.subgroupCongr hF.symm) hL⟩

theorem orthE2Plus_two (h212 : Smith212OrthCoreStatement) (hK1 : K1NSLStatement)
    (hK2L : K2PSLStatement2) (hKCO : KCOmegaStatement2)
    (hKC4 : KCOmegaFourStatement) {G : Type} [Group G] [Finite G]
    {M Q Z B : Subgroup G} (hc : SmithOrthCfg M Q Z B)
    (hroot : ∀ z ∈ Z, z ≠ 1 → Timmesfeld.IsRootInvolutionSet (conjClassSet z)) {t : G}
    (hD4 : CtxD4 M Q Z B t) (hcase : CaseE2Plus M Q Z B t 2) :
    ∃ f : ℕ, Nat.card Z = 2 ^ f ∧ LieModel (FStar G) .POmegaPlus (2 + 2) 2 f := by
  classical
  have H := hc.ctx.hyp
  obtain ⟨z, hz, hz1, -⟩ := exists_mem_Z_ne H 1
  obtain ⟨hF, -⟩ := generalizedFitting_eq_normalClosure H hz hz1
  obtain ⟨f, k₀, hf, -⟩ := H.cp
  have hf2 : 2 ≤ f := by
    have h4 := H.q4
    rw [hf] at h4
    by_contra hlt
    push Not at hlt
    interval_cases f <;> norm_num at h4
  have hf1 : 1 ≤ f := by omega
  obtain ⟨-, hQ, -, -, hT⟩ := hcase
  rw [hf] at hT
  obtain ⟨hN, A, Bo, _, _, hA, hB, ⟨e⟩⟩ := hT
  obtain ⟨K, _, _, hK, ⟨eB⟩⟩ := hB
  haveI := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  obtain ⟨e4⟩ := statedOmega_plus_four_nonempty_equiv K hK4
  let E : (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B))) ≃*
      A × (↥(StatedSL 2 K) × ↥(StatedSL 2 K)) :=
    e.trans (MulEquiv.prodCongr (MulEquiv.refl A) (eB.trans e4))
  have hS : IsSLModel 2 (2 ^ f) ↥(StatedSL 2 K) :=
    ⟨K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨hAs, hAc, -⟩ := sl2_model_facts hf2 hA
  obtain ⟨hSs, hSc, -⟩ := sl2_model_facts hf2 hS
  haveI := hAs
  haveI := hSs
  have hA0 : Nat.card A ≠ 0 := by
    rw [hAc]
    have : 4 ≤ (2 ^ f) ^ 2 := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (f * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = (2 ^ f) ^ 2 := by rw [pow_mul]
    exact mul_ne_zero (by positivity) (by omega)
  haveI : Finite A := Nat.finite_of_card_ne_zero hA0
  have h4A : 4 ∣ Nat.card A := by
    rw [hAc]
    exact Dvd.dvd.mul_right (show 2 ^ 2 ∣ 2 ^ f from pow_dvd_pow 2 hf2) _
  have h4S : 4 ∣ Nat.card ↥(StatedSL 2 K) := by
    rw [hSc]
    exact Dvd.dvd.mul_right (show 2 ^ 2 ∣ 2 ^ f from pow_dvd_pow 2 hf2) _
  have hAn := exists_not_commute_of_simple hAs h4A
  have hSn := exists_not_commute_of_simple hSs h4S
  haveI : Finite (MulAut A) :=
    Finite.of_injective (fun α : MulAut A => (α : A → A)) DFunLike.coe_injective
  haveI : Finite (MulAut ↥(StatedSL 2 K)) :=
    Finite.of_injective (fun α : MulAut ↥(StatedSL 2 K) => (α : _ → _)) DFunLike.coe_injective
  haveI : Finite (MulAut (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B)))) :=
    Finite.of_injective (fun α : MulAut (↥(Lgen M (LB M Q B)) ⧸
      Q.subgroupOf (Lgen M (LB M Q B))) => (α : _ → _)) DFunLike.coe_injective
  have hTmul : Nat.card (MulAut (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B)))) ∣
      6 * (Nat.card (MulAut A) * Nat.card (MulAut ↥(StatedSL 2 K)) *
        Nat.card (MulAut ↥(StatedSL 2 K))) := by
    rw [Nat.card_congr (MulAut.congr E).toEquiv]
    exact card_mulAut_prod_three_dvd hAn hSn hSn
  have hvA := factorization_card_mulAut_sl2_le hf2 hA
  have hvS := factorization_card_mulAut_sl2_le hf2 hS
  have hMA0 : Nat.card (MulAut A) ≠ 0 := Nat.card_pos.ne'
  have hMS0 : Nat.card (MulAut ↥(StatedSL 2 K)) ≠ 0 := Nat.card_pos.ne'
  have hAut : (Nat.card (MulAut (↥(Lgen M (LB M Q B)) ⧸
      Q.subgroupOf (Lgen M (LB M Q B))))).factorization 2 ≤
        f * (2 * (2 - 1) + 1) + (3 * f.factorization 2 + 1) := by
    have hprod0 : 6 * (Nat.card (MulAut A) * Nat.card (MulAut ↥(StatedSL 2 K)) *
        Nat.card (MulAut ↥(StatedSL 2 K))) ≠ 0 :=
      mul_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero hMA0 hMS0) hMS0)
    have h := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' hprod0).mpr hTmul 2
    have h6 : (6 : ℕ).factorization 2 = 1 := by
      rw [show (6 : ℕ) = 2 * 3 by rfl, Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [Nat.factorization_mul (by norm_num) (mul_ne_zero (mul_ne_zero hMA0 hMS0) hMS0),
      Finsupp.add_apply, h6, Nat.factorization_mul (mul_ne_zero hMA0 hMS0) hMS0,
      Finsupp.add_apply, Nat.factorization_mul hMA0 hMS0, Finsupp.add_apply] at h
    omega
  have hev : Even (2 ^ f) := (Nat.even_pow' (by omega)).mpr even_two
  have hLc : Nat.card (Lgen M (LB M Q B)) =
      Nat.card Q * (2 ^ f * ((2 ^ f) ^ 2 - 1) * ordD 2 (2 ^ f)) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Q.subgroupOf (Lgen M (LB M Q B))),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Q_le_Lgen M Q B)).toEquiv,
      Nat.card_congr E.toEquiv, Nat.card_prod, Nat.card_prod, hAc, hSc,
      ordD_two_eq_of_even hev (by positivity)]
    ring
  have hcf : f.factorization 2 + (3 * f.factorization 2 + 1) < 3 * f := by
    have h1 := Smith219Arith.four_mul_padicValNat_two_add_one_lt (by omega : 0 < f)
    rw [← Nat.factorization_def f Nat.prime_two] at h1
    omega
  have h3D4 : 2 = 2 → ¬ Nat.card Q * (2 ^ f * ((2 ^ f) ^ 2 - 1) * ordD 2 (2 ^ f)) ∣
      ordTrialityD4 (2 ^ f) := by
    intro _
    rw [hQ, hf, show 4 * 2 + 1 = 9 by rfl]
    exact not_dvd_ordTrialityD4_plus hf2
  obtain ⟨t', hL, hsign | hsign⟩ := orthE2_identify_core h212 hK1 hK2L hKCO hc hroot hD4
    (le_refl 2) (fun _ => hKC4) hQ hf (Or.inl rfl) hLc hAut hcf h3D4 hz hz1
  · obtain ⟨rfl, -⟩ := hsign
    exact ⟨f, hf, LieModel.of_mulEquiv (MulEquiv.subgroupCongr hF.symm) hL⟩
  · exact absurd hsign.2 (not_ordD_dvd_ordTwistedD hf2 (by norm_num)).1

theorem smith219OrthSmall_of (h23 : Smith23E1LgenStatement) (h212 : Smith212OrthCoreStatement)
    (hK1 : K1NSLStatement) (hK2L : K2PSLStatement2) (hKCO : KCOmegaStatement2)
    (hKC4 : KCOmegaFourStatement) :
    Smith219OrthSmallStatement := by
  intro G _ _ M Q Z B hc hroot _
  refine ⟨fun t hD4 hE => ?_, fun t hD4 hE => ?_, fun t m hm hD4 hcase => ?_,
    fun t m hm hD4 hcase => orthE2Minus_small h212 hK1 hK2L hKCO hKC4 hc hroot hm hD4 hcase⟩
  · exact orthE2Plus_two h212 hK1 hK2L hKCO hKC4 hc hroot hD4
      ⟨le_rfl, hE.1, hE.2.1, hE.2.2, (h23 G M Q Z B t hc.toCfg hD4).1 hE⟩
  · exact orthE2Minus_small h212 hK1 hK2L hKCO hKC4 hc hroot (by norm_num) hD4
      ⟨le_rfl, hE.1, hE.2.1, hE.2.2, (h23 G M Q Z B t hc.toCfg hD4).2 hE⟩
  · obtain rfl : m = 2 := le_antisymm hm hcase.1
    exact orthE2Plus_two h212 hK1 hK2L hKCO hKC4 hc hroot hD4 hcase

end CFSG.RankThree.GF2n.Smith81.Insp
