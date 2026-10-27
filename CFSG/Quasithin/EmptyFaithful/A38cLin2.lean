module

public import CFSG.Quasithin.EmptyFaithful.A38cAutOn
public import CFSG.Quasithin.EmptyFaithful.S153F19
public import CFSG.Quasithin.EmptyFaithful.A38cOrders

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Vol2.Ch10.SecA

theorem lin2QuotIsLin2OrA5_holds : Lin2QuotIsLin2OrA5 := by
  intro G _ _ H R M K V hR _ hC hQ
  obtain ⟨h1, -, h3⟩ := hC
  obtain ⟨n₀, F₀, _, _, hn₀, hF₀, ⟨e₀⟩⟩ := hQ
  have hF₀' : Nat.card F₀ = 2 ^ n₀ := by rw [Nat.card_eq_fintype_card]; exact hF₀
  have hN : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 2 ^ n₀ * (4 ^ n₀ - 1) := by
    rw [Nat.card_congr e₀.toEquiv, card_SL_two_pow hF₀']
  have hShape : ShapeCard (Nat.card (↥K ⧸ CFSG.pCore 2 ↥K)) := Or.inl ⟨n₀, hn₀, hN⟩
  have hsl : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F₀) := isSimpleGroup_sl_two_pow hn₀ hF₀
  have hsimple : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := e₀.isSimpleGroup
  have hnp : ¬ (Nat.card (↥K ⧸ CFSG.pCore 2 ↥K)).Prime := by
    rw [hN]
    refine Nat.not_prime_mul ?_ ?_
    · have : 2 ^ 2 ≤ 2 ^ n₀ := Nat.pow_le_pow_right (by norm_num) hn₀
      omega
    · have : 4 ^ 2 ≤ 4 ^ n₀ := Nat.pow_le_pow_right (by norm_num) hn₀
      omega
  have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ :=
    center_eq_bot_of_simple_of_card_not_prime hnp
  have hO : pCoreOf 2 (K ⊔ R) ≤ Subgroup.centralizer (V : Set G) := h1.1.trans inf_le_right
  have hNV : K ⊔ R ≤ Subgroup.normalizer (V : Set G) := h1.2.2.2.1
  rcases h3 with ⟨hchi, hi | hii | hiii | hiv⟩ | hb | hc | hd | he | hf | hg | hh
  · exact Or.inl ⟨hchi.1, hi.1⟩
  · exact Or.inr hii.1
  · exfalso
    have h := card_quotPCore_of_isAltType (by norm_num) hiii.1
    exact not_shapeCard_2520 (by rw [← show Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 2520 by rw [h]; decide]; exact hShape)
  · exfalso
    have h := card_quotPCore_of_isAltType (by norm_num) hiv.1
    exact not_shapeCard_2520 (by rw [← show Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 2520 by rw [h]; decide]; exact hShape)
  ·
    obtain ⟨⟨n, α, hn5, hn8, -, hα, -⟩, -⟩ := hb
    have h := card_quotPCore_of_isAltBlockTypeWith (by omega) hα
    interval_cases n
    · exact Or.inr ((isAltType_iff_exists_isAltBlockTypeWith (by decide)).mpr ⟨α, hα⟩)
    · exfalso
      exact not_shapeCard_360 (by rw [← show Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 360 by rw [h]; decide]; exact hShape)
    · exfalso
      exact not_shapeCard_2520 (by rw [← show Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 2520 by rw [h]; decide]; exact hShape)
    · exfalso
      exact not_shapeCard_20160 (by rw [← show Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 20160 by rw [h]; decide]; exact hShape)
  ·
    exfalso
    have h := card_quotPCore_of_isHatA6Block hc.1
    exact not_shapeCard_1080 (h ▸ hShape)
  ·
    exfalso
    have h := card_quotPCore_of_isExcA7Block hd.1
    exact not_shapeCard_2520 (h ▸ hShape)
  ·
    exfalso
    rcases he.1 with hA6 | hSp
    · obtain ⟨-, α, hα⟩ := hA6
      have h := card_quotPCore_of_isAltBlockTypeWith (by norm_num) hα
      exact not_shapeCard_360 (by rw [← show Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 360 by rw [h]; decide]; exact hShape)
    · exact not_shapeCard_979200 ((card_quotPCore_of_isSp4Block hSp) ▸ hShape)
  ·
    exfalso
    exact not_shapeCard_6048 ((card_quotPCore_of_isG2Block hf.1) ▸ hShape)
  ·
    exfalso
    obtain ⟨⟨n, F, _, _, hn1, hF, ⟨e⟩⟩, -, -⟩ := hg
    have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hF
    have hA : Nat.card ↥(autOn K V) = 2 ^ (3 * n) * ((2 ^ (3 * n) - 1) * (2 ^ (2 * n) - 1)) := by
      rw [Nat.card_congr e.toEquiv, card_statedSL, card_SL_three_pow hF']
    have hnt : 1 < Nat.card ↥(autOn K V) := by
      rw [hA]
      have h8 : 2 ≤ 2 ^ (3 * n) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h7 : 1 ≤ 2 ^ (3 * n) - 1 := by omega
      have h3 : 1 ≤ 2 ^ (2 * n) - 1 := by
        have : 2 ≤ 2 ^ (2 * n) := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      calc 1 < 2 ^ (3 * n) := by omega
        _ ≤ 2 ^ (3 * n) * ((2 ^ (3 * n) - 1) * (2 ^ (2 * n) - 1)) :=
          Nat.le_mul_of_pos_right _ (Nat.mul_pos h7 h3)
    have heq := card_autOn_eq_card_quot hR hO hNV hnt
    rw [hA, hN] at heq
    exact card_sl_two_ne_card_sl_three (by omega) hn1 heq.symm
  ·
    exfalso
    obtain ⟨hSL, -, -⟩ := hh
    rcases hSL with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · have hA : Nat.card ↥(autOn K V) = 20160 := by
        rw [Nat.card_congr e.toEquiv, card_statedSL,
          card_SL_four_of_two (K := ZMod 2) (by simp)]
      have heq := card_autOn_eq_card_quot hR hO hNV (by rw [hA]; norm_num)
      rw [hA] at heq
      exact not_shapeCard_20160 (heq ▸ hShape)
    · have hA : Nat.card ↥(autOn K V) = 9999360 := by
        rw [Nat.card_congr e.toEquiv, card_statedSL,
          card_SL_five_of_two (K := ZMod 2) (by simp)]
      have heq := card_autOn_eq_card_quot hR hO hNV (by rw [hA]; norm_num)
      rw [hA] at heq
      exact not_shapeCard_9999360 (heq ▸ hShape)

end CFSG.Quasithin
