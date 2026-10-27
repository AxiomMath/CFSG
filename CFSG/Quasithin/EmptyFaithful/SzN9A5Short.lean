module

public import CFSG.Quasithin.EmptyFaithful.SzN8Inst
public import CFSG.Quasithin.EmptyFaithful.A38cAutOn

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Vol2.Ch10.SecA

theorem a5IsShort_holds : A5IsShort := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hA
  have hR : R153 T V₁ Yp ≤ Subgroup.normalizer (L : Set G) := c.c16.R_norm
  obtain ⟨h1, -, h3⟩ := c.c16.desc
  have hN60 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 60 := by
    have h := card_quotPCore_of_isAltType (L := L) (by norm_num) hA
    rw [h]
    decide
  obtain ⟨α, hαs, hαk, -⟩ := hA
  have hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
    have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    exact (quotPCoreMulEquiv α hαs hαk).isSimpleGroup
  have hO : pCoreOf 2 (L ⊔ R153 T V₁ Yp) ≤ Subgroup.centralizer
      (omegaOneCenterOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp)) : Set G) := h1.1.trans inf_le_right
  have hNV : L ⊔ R153 T V₁ Yp ≤ Subgroup.normalizer
      (omegaOneCenterOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp)) : Set G) := h1.2.2.2.1
  rcases h3 with ⟨hchi, -⟩ | hb | hc' | hd | he | hf | hg | hh
  · exact hchi.1.1
  · obtain ⟨⟨n, α', hn5, hn8, hshort, -⟩, -⟩ := hb
    exact hshort
  · exact hc'.1.1
  · exact hd.1.1
  · rcases he.1 with h | h
    · exact h.1
    · exact h.1
  · exact hf.1.1
  ·
    exfalso
    obtain ⟨⟨n, F, _, _, hn1, hF, ⟨e⟩⟩, -, -⟩ := hg
    have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hF
    have hA : Nat.card ↥(autOn L (omegaOneCenterOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp)))) =
        2 ^ (3 * n) * ((2 ^ (3 * n) - 1) * (2 ^ (2 * n) - 1)) := by
      rw [Nat.card_congr e.toEquiv, card_statedSL, card_SL_three_pow hF']
    have h8 : 8 ≤ 2 ^ (3 * n) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 4 ≤ 2 ^ (2 * n) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hbig : 168 ≤ 2 ^ (3 * n) * ((2 ^ (3 * n) - 1) * (2 ^ (2 * n) - 1)) := by
      calc 168 = 8 * (7 * 3) := by norm_num
        _ ≤ 2 ^ (3 * n) * ((2 ^ (3 * n) - 1) * (2 ^ (2 * n) - 1)) :=
          Nat.mul_le_mul h8 (Nat.mul_le_mul (by omega) (by omega))
    have hnt : 1 < Nat.card ↥(autOn L (omegaOneCenterOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp)))) := by
      rw [hA]
      omega
    have heq := card_autOn_eq_card_quot hR hO hNV hnt
    rw [hA, hN60] at heq
    omega
  ·
    exfalso
    obtain ⟨hSL, -, -⟩ := hh
    rcases hSL with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · have hA : Nat.card ↥(autOn L (omegaOneCenterOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp)))) = 20160 := by
        rw [Nat.card_congr e.toEquiv, card_statedSL,
          card_SL_four_of_two (K := ZMod 2) (by simp)]
      have heq := card_autOn_eq_card_quot hR hO hNV (by rw [hA]; norm_num)
      rw [hA, hN60] at heq
      omega
    · have hA : Nat.card ↥(autOn L (omegaOneCenterOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp)))) = 9999360 := by
        rw [Nat.card_congr e.toEquiv, card_statedSL,
          card_SL_five_of_two (K := ZMod 2) (by simp)]
      have heq := card_autOn_eq_card_quot hR hO hNV (by rw [hA]; norm_num)
      rw [hA, hN60] at heq
      omega

end CFSG.Quasithin
