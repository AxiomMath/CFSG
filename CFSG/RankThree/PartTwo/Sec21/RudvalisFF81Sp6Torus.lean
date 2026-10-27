module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
import CFSG.RankThree.PartTwo.Sec21.HeringFFLKE9
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62Check
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two (H6)
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
open CFSG.RankThree.PartTwo.Sec4.Item434Kit

theorem kf_sp6TorusFree : KF_Sp6TorusFree := by
  intro X _ _ L hL E hEL hE R hRL hER hR3
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨θ⟩ := nonempty_mulEquiv_H6_of_stated hL
  have hf := wreathFacts_zH
  set E' : Subgroup H6 := (E.subgroupOf L).map θ.toMonoidHom with hE'
  set R' : Subgroup H6 := (R.subgroupOf L).map θ.toMonoidHom with hR'
  have hEcard : Nat.card (E.subgroupOf L) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
  have hRcard : Nat.card (R.subgroupOf L) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRL).toEquiv
  have hE'card : Nat.card E' = 27 := by
    rw [hE', Subgroup.card_map_of_injective θ.injective, hEcard, hE.2]
    norm_num
  have hR'card : Nat.card R' = Nat.card R := by
    rw [hR', Subgroup.card_map_of_injective θ.injective, hRcard]
  have hE'el : CFSG.Assembly.IsElemAbelian 3 E' := by
    obtain ⟨hEa, -⟩ := hE
    have hE0 : CFSG.Open.IsElemAbelian 3 E :=
      ⟨hEa.toIsMulCommutative, fun x hx =>
        CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := E) x hx⟩
    exact CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf hE0 L) _
  have hE'p : IsPGroup 3 E' := IsPGroup.of_card (n := 3) (by rw [hE'card]; norm_num)
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.exists_le_map_conj_of_card
    (P₀ := wreathW zH tH) (by rw [card_wreathW_zH, factorization_card_H6]; norm_num) hE'p
  have hPg : E'.map (MulAut.conj g⁻¹).toMonoidHom = baseA zH :=
    eq_baseA_of_le_wreathW hf card_wreathW_zH
      (CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.map_conj_inv_le hg)
      (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ E' hE'el)
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hE'card])
  set R'' := R'.map (MulAut.conj g⁻¹).toMonoidHom with hR''
  have hR''card : Nat.card R'' = Nat.card R := by
    rw [hR'', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hR'card]
  have hLN : E.subgroupOf L ≤ Subgroup.normalizer (R.subgroupOf L) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro r
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp (hER he) r
  have hE'N : E' ≤ Subgroup.normalizer R' := by
    rw [hE', hR', ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hLN
  have hAN : baseA zH ≤ Subgroup.normalizer (R'' : Set H6) := by
    rw [← hPg, hR'', ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hE'N
  have hbot := eq_bot_of_baseA_le_normalizer (by
    rw [hR''card]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hR3) hAN
  have hR'bot : R' = ⊥ := by
    rw [hR''] at hbot
    exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g⁻¹).injective).mp hbot
  have hRL'bot : R.subgroupOf L = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ θ.injective).mp hR'bot
  have hdis := Subgroup.subgroupOf_eq_bot.mp hRL'bot
  rw [disjoint_iff, inf_eq_left.mpr hRL] at hdis
  exact hdis

end CFSG.RankThree.PartTwo.Sec21.FF81

end
