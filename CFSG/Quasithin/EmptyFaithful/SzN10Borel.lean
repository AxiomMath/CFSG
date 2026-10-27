module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InExclusive
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.EmptyFaithful.A38cAutOn
public import CFSG.Quasithin.EmptyFaithful.A38cOrders
public import CFSG.Quasithin.EmptyFaithful.S153DInputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Vol2.Ch10.SecA

theorem szN10_borel_of_lin2 {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G}
    {t : G} (ctx : Ctx15316 T Mc M V₁ V₂ Yp I L t) {n : ℕ} (hn : 1 < n) (hlin : IsLin2Type L n) :
    IsBorelIn (autOn L (omegaOneCenterOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp))))
      (autOn ((M ⊓ I) ⊓ L) (omegaOneCenterOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp)))) := by
  have hR : R153 T V₁ Yp ≤ Subgroup.normalizer (L : Set G) := ctx.c16.R_norm
  obtain ⟨h1, -, h3⟩ := ctx.c16.desc
  obtain ⟨F₀, hF₀, hFin₀, hcard₀, α, hαs, hαk, -⟩ := id hlin
  have hF₀' : Nat.card F₀ = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hcard₀
  have e₀ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* Matrix.SpecialLinearGroup (Fin 2) F₀ :=
    (QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)
  have hN : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 2 ^ n * (4 ^ n - 1) := by
    rw [Nat.card_congr e₀.toEquiv, card_SL_two_pow hF₀']
  have hShape : ShapeCard (Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) := Or.inl ⟨n, hn, hN⟩
  have hsl : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F₀) :=
    isSimpleGroup_sl_two_pow hn hcard₀
  have hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := e₀.isSimpleGroup
  have hnp : ¬ (Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)).Prime := by
    rw [hN]
    refine Nat.not_prime_mul ?_ ?_
    · have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    · have : 4 ^ 2 ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
  have hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ :=
    center_eq_bot_of_simple_of_card_not_prime hnp
  have hO : pCoreOf 2 (L ⊔ R153 T V₁ Yp) ≤ Subgroup.centralizer
      (omegaOneCenterOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp)) : Set G) := h1.1.trans inf_le_right
  have hNV : L ⊔ R153 T V₁ Yp ≤ Subgroup.normalizer
      (omegaOneCenterOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp)) : Set G) := h1.2.2.2.1
  rcases h3 with ⟨hchi, hi | hii | hiii | hiv⟩ | hb | hc | hd | he | hf | hg | hh
  · exact hi.2.2
  · exfalso
    exact Lin2.lin2_not_alt hn hlin (Or.inr rfl) hii.1
  · exfalso
    have h := card_quotPCore_of_isAltType (by norm_num) hiii.1
    exact not_shapeCard_2520 (by
      rw [← show Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 2520 by rw [h]; decide]; exact hShape)
  · exfalso
    have h := card_quotPCore_of_isAltType (by norm_num) hiv.1
    exact not_shapeCard_2520 (by
      rw [← show Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 2520 by rw [h]; decide]; exact hShape)
  ·
    exfalso
    obtain ⟨⟨m, α', hm5, hm8, -, hα', -⟩, -⟩ := hb
    have h := card_quotPCore_of_isAltBlockTypeWith (by omega) hα'
    interval_cases m
    · exact Lin2.lin2_not_alt hn hlin (Or.inr rfl)
        ((isAltType_iff_exists_isAltBlockTypeWith (by decide)).mpr ⟨α', hα'⟩)
    · exact not_shapeCard_360 (by
        rw [← show Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 360 by rw [h]; decide]; exact hShape)
    · exact not_shapeCard_2520 (by
        rw [← show Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 2520 by rw [h]; decide]; exact hShape)
    · exact not_shapeCard_20160 (by
        rw [← show Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 20160 by rw [h]; decide]; exact hShape)
  · exfalso
    have h := card_quotPCore_of_isHatA6Block hc.1
    exact not_shapeCard_1080 (h ▸ hShape)
  · exfalso
    have h := card_quotPCore_of_isExcA7Block hd.1
    exact not_shapeCard_2520 (h ▸ hShape)
  · exfalso
    rcases he.1 with hA6 | hSp
    · obtain ⟨-, α', hα'⟩ := hA6
      have h := card_quotPCore_of_isAltBlockTypeWith (by norm_num) hα'
      exact not_shapeCard_360 (by
        rw [← show Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 360 by rw [h]; decide]; exact hShape)
    · exact not_shapeCard_979200 ((card_quotPCore_of_isSp4Block hSp) ▸ hShape)
  · exfalso
    exact not_shapeCard_6048 ((card_quotPCore_of_isG2Block hf.1) ▸ hShape)
  · exfalso
    obtain ⟨⟨m, F, _, _, hm1, hF, ⟨e⟩⟩, -, -⟩ := hg
    have hF' : Nat.card F = 2 ^ m := by rw [Nat.card_eq_fintype_card]; exact hF
    have hA : Nat.card ↥(autOn L (omegaOneCenterOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp)))) =
        2 ^ (3 * m) * ((2 ^ (3 * m) - 1) * (2 ^ (2 * m) - 1)) := by
      rw [Nat.card_congr e.toEquiv, card_statedSL, card_SL_three_pow hF']
    have hnt : 1 < Nat.card ↥(autOn L
        (omegaOneCenterOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp)))) := by
      rw [hA]
      have h8 : 2 ≤ 2 ^ (3 * m) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (3 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h7 : 1 ≤ 2 ^ (3 * m) - 1 := by omega
      have h3 : 1 ≤ 2 ^ (2 * m) - 1 := by
        have : 2 ≤ 2 ^ (2 * m) := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      calc 1 < 2 ^ (3 * m) := by omega
        _ ≤ 2 ^ (3 * m) * ((2 ^ (3 * m) - 1) * (2 ^ (2 * m) - 1)) :=
          Nat.le_mul_of_pos_right _ (Nat.mul_pos h7 h3)
    have heq := card_autOn_eq_card_quot hR hO hNV hnt
    rw [hA, hN] at heq
    exact card_sl_two_ne_card_sl_three (by omega) hm1 heq.symm
  · exfalso
    obtain ⟨hSL, -, -⟩ := hh
    rcases hSL with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · have hA : Nat.card ↥(autOn L
          (omegaOneCenterOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp)))) = 20160 := by
        rw [Nat.card_congr e.toEquiv, card_statedSL,
          card_SL_four_of_two (K := ZMod 2) (by simp)]
      have heq := card_autOn_eq_card_quot hR hO hNV (by rw [hA]; norm_num)
      rw [hA] at heq
      exact not_shapeCard_20160 (heq ▸ hShape)
    · have hA : Nat.card ↥(autOn L
          (omegaOneCenterOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp)))) = 9999360 := by
        rw [Nat.card_congr e.toEquiv, card_statedSL,
          card_SL_five_of_two (K := ZMod 2) (by simp)]
      have heq := card_autOn_eq_card_quot hR hO hNV (by rw [hA]; norm_num)
      rw [hA] at heq
      exact not_shapeCard_9999360 (heq ▸ hShape)

end CFSG.Quasithin
