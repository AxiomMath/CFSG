module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5Par
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniBlocks
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.H13.Ch4.U5M

open CFSG.Quasithin CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin.H13.Sec53F.Unit
open CFSG.AGLEmbedding.LeviBlock CFSG.QuasithinUnique

theorem card_center_quotient_le_of_pgroup_kernel {A B : Type*} [Group A] [Finite A]
    [Group B] [Finite B] (hA : CFSG.Open.IsQuasisimple A) (f : A →* B)
    (hf : IsPGroup 2 f.ker) : Nat.card (A ⧸ Subgroup.center A) ≤ Nat.card B := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Group.IsPerfect A := Group.isPerfect_def.mpr hA.1
  letI : IsSimpleGroup (A ⧸ Subgroup.center A) := hA.2
  let q := QuotientGroup.mk' (Subgroup.center A)
  have hN : (f.ker.map q).Normal := f.normal_ker.map q (QuotientGroup.mk'_surjective _)
  have hN2 : IsPGroup 2 (f.ker.map q) := hf.map q
  have hbot : f.ker.map q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (f.ker.map q) with hb | ht
    · exact hb
    · have hQ2 : IsPGroup 2 (A ⧸ Subgroup.center A) :=
        hN2.of_equiv ((MulEquiv.subgroupCongr ht).trans Subgroup.topEquiv)
      exact False.elim (Group.IsPerfect.not_isNilpotent (A ⧸ Subgroup.center A)
        hQ2.isNilpotent)
  have hker : f.ker ≤ Subgroup.center A := by
    have h := (Subgroup.map_eq_bot_iff (f := q) (H := f.ker)).mp hbot
    simpa only [q, QuotientGroup.ker_mk'] using h
  let t : (A ⧸ f.ker) →* (A ⧸ Subgroup.center A) :=
    QuotientGroup.map _ _ (MonoidHom.id A) hker
  have ht : Function.Surjective t := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center A) y
    exact ⟨(a : A ⧸ f.ker), rfl⟩
  calc
    Nat.card (A ⧸ Subgroup.center A) ≤ Nat.card (A ⧸ f.ker) :=
      Nat.card_le_card_of_surjective t ht
    _ = Nat.card f.range := Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    _ ≤ Nat.card B := Nat.card_le_card_of_injective f.range.subtype Subtype.val_injective

theorem card_center_quotient_le_modO2 {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (hA : CFSG.Open.IsQuasisimple A) (f : A →* B) (hf : Function.Injective f) :
    Nat.card (A ⧸ Subgroup.center A) ≤ Nat.card (B ⧸ CFSG.pCore 2 B) := by
  let q := QuotientGroup.mk' (CFSG.pCore 2 B)
  have hfk : IsPGroup 2 f.ker := by
    intro x
    refine ⟨0, ?_⟩
    apply Subtype.ext
    simpa using hf ((MonoidHom.mem_ker.mp x.2).trans (map_one f).symm)
  have hk : IsPGroup 2 (q.comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup.comap_of_ker_isPGroup f hfk
  exact card_center_quotient_le_of_pgroup_kernel hA (q.comp f) hk

theorem psl2_order_lt_psu3_order {q : ℕ} (hq : 4 ≤ q) :
    q * (q ^ 2 - 1) < CFSG.Open.ordTwistedA 2 q := by
  have hq2 : 1 ≤ q ^ 2 := by nlinarith
  have hcast : ((q ^ 2 - 1 : ℕ) : ℤ) = (q : ℤ) ^ 2 - 1 := by
    rw [Nat.cast_sub hq2, Nat.cast_pow, Nat.cast_one]
  have he2 : (((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat) = q ^ 2 - 1 := by
    norm_num only [even_two, Even.neg_pow, one_pow]
    rw [← hcast, Int.toNat_natCast]
  have he3 : (((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat) = q ^ 3 + 1 := by
    rw [show (-1 : ℤ) ^ 3 = -1 by norm_num, sub_neg_eq_add]
    norm_cast
  have hformula : CFSG.Open.ordTwistedA 2 q =
      q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / Nat.gcd 3 (q + 1) := by
    change q ^ 3 * (∏ i ∈ Finset.Icc 2 3, ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) /
      Nat.gcd 3 (q + 1) = _
    rw [show Finset.Icc 2 3 = {2, 3} from by decide]
    rw [Finset.prod_insert (by decide), Finset.prod_singleton, he2, he3]
  have hdpos : 0 < Nat.gcd 3 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hd : Nat.gcd 3 (q + 1) ≤ q ^ 3 + 1 :=
    (Nat.gcd_le_left _ (by norm_num)).trans (by nlinarith)
  have hlower : q ^ 3 * (q ^ 2 - 1) ≤ CFSG.Open.ordTwistedA 2 q := by
    rw [hformula, Nat.le_div_iff_mul_le hdpos]
    calc
      q ^ 3 * (q ^ 2 - 1) * Nat.gcd 3 (q + 1) ≤
          q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := Nat.mul_le_mul_left _ hd
      _ = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by ring
  have hq16 : 16 ≤ q ^ 2 := by nlinarith
  have hpos : 0 < q ^ 2 - 1 := by omega
  have hqq : q < q ^ 3 := by nlinarith
  exact (Nat.mul_lt_mul_of_pos_right hqq hpos).trans_le hlower


theorem card_levi_center_quotient_le {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (P N : Subgroup (hypSU h 2 1))
    (hN : CFSG.Open.IsQuasisimple N) (hNP : N ≤ perfectCore P)
    (hNZ : N ⊓ hypScalars h 2 1 = ⊥) :
    Nat.card (N ⧸ Subgroup.center N) ≤
      Nat.card (ModO2 (perfectCore (P.map (hypProj h 2 1)))) := by
  letI : Finite K := h.finite
  let q := hypProj h 2 1
  let j : N →* perfectCore (P.map q) :=
    (q.comp N.subtype).codRestrict _ (fun x => by
      rw [← map_perfectCore]
      exact Subgroup.mem_map_of_mem q (hNP x.2))
  have hj : Function.Injective j := by
    intro x y hxy
    have he : q (x : hypSU h 2 1) = q (y : hypSU h 2 1) := congrArg Subtype.val hxy
    have hz : (x : hypSU h 2 1)⁻¹ * y ∈ hypScalars h 2 1 := by
      rw [← ker_hypProj, MonoidHom.mem_ker]
      change q ((x : hypSU h 2 1)⁻¹ * y) = 1
      rw [map_mul, map_inv, he, inv_mul_cancel]
    have hm : (x : hypSU h 2 1)⁻¹ * y ∈ N ⊓ hypScalars h 2 1 :=
      ⟨N.mul_mem (N.inv_mem x.2) y.2, hz⟩
    rw [hNZ, Subgroup.mem_bot] at hm
    exact Subtype.ext (inv_mul_eq_one.mp hm)
  exact card_center_quotient_le_modO2 hN j hj

theorem line_levi_order_le {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) :
    CFSG.Open.ordA 1 (Nat.card K) ≤ Nat.card (ModO2 (perfectCore (u5LnP h))) := by
  letI : Finite K := h.finite
  have hK4 : 4 ≤ Nat.card K := by
    rw [h.card_eq_sq]
    have hq := two_lt_two_pow hf
    nlinarith
  have hq := isQuasisimple_SL_of_four_le (K := K) hK4 (m := 2) le_rfl
  have hqN : CFSG.Open.IsQuasisimple (N₁sub h) :=
    isQuasisimple_of_mulEquiv (N₁equiv h) hq
  have hb := card_levi_center_quotient_le h (u5LnStab h) (N₁sub h) hqN
    N₁sub_le_perfectCore_u5LnStab N₁sub_inf_hypScalars
  rw [← card_centerQuotient_congr (N₁equiv h), card_centerQuotient_SL (by norm_num)] at hb
  exact hb

theorem point_levi_order_le {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) :
    CFSG.Open.ordTwistedA 2 (2 ^ f) ≤ Nat.card (ModO2 (perfectCore (u5PtP h))) := by
  letI : Finite K := h.finite
  have hmq : (2 * 1 + 1, 2 ^ f) ≠ (3, 2) := by
    intro he
    have he' := congrArg Prod.snd he
    exact (ne_of_gt (two_lt_two_pow hf)) he'
  obtain ⟨hq, hcard⟩ := hypSU_facts_of_three_le (s := 1) (ε := 1) h (by norm_num) hmq
  have hqN : CFSG.Open.IsQuasisimple (N₂sub h) :=
    isQuasisimple_of_mulEquiv (N₂equiv h) hq
  have hb := card_levi_center_quotient_le h (u5PtStab h) (N₂sub h) hqN
    (N₂sub_le_perfectCore_u5PtStab hf) N₂sub_inf_hypScalars
  rw [← card_centerQuotient_congr (N₂equiv h), hcard] at hb
  exact hb


theorem ordA_one_even {q : ℕ} (hq : 1 ≤ q) (he : Even q) :
    CFSG.Open.ordA 1 q = q * (q ^ 2 - 1) := by
  have hodd : Odd (q - 1) := by
    obtain ⟨m, hm⟩ := he
    exact ⟨m - 1, by omega⟩
  have hgcd : Nat.gcd 2 (q - 1) = 1 := Nat.Coprime.gcd_eq_one
    (Nat.coprime_two_left.mpr hodd)
  simp only [CFSG.Open.ordA, Finset.Icc_self, Finset.prod_singleton]
  norm_num only
  rw [hgcd, Nat.div_one, pow_one]

theorem psl2_order_lt_square_order {q : ℕ} (hq : 4 ≤ q) (he : Even q) :
    q * (q ^ 2 - 1) < CFSG.Open.ordA 1 (q ^ 2) := by
  rw [ordA_one_even (by nlinarith) (Nat.even_pow.mpr ⟨he, by decide⟩)]
  have hq16 : 16 ≤ q ^ 2 := by nlinarith
  have hpos : 0 < q ^ 2 - 1 := by omega
  have hqq : q < q ^ 2 := by nlinarith
  have hpow : q ^ 2 ≤ (q ^ 2) ^ 2 := by nlinarith
  exact (Nat.mul_lt_mul_of_pos_right hqq hpos).trans_le
    (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hpow 1))

theorem false_of_isPSL_point {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    (hpsl : IsPSL 2 2 f (ModO2 (perfectCore (u5PtP h)))) : False := by
  have hc := F420.card_of_statedPSL_two_two hpsl
  have hp : (2 ^ f) ^ 2 = 4 ^ f := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [← hp] at hc
  have hb := point_levi_order_le h hf
  rw [hc] at hb
  exact (not_le_of_gt (psl2_order_lt_psu3_order (q := 2 ^ f) (by exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) hf))) hb

theorem false_of_isPSL_line {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    (hpsl : IsPSL 2 2 f (ModO2 (perfectCore (u5LnP h)))) : False := by
  have hc := F420.card_of_statedPSL_two_two hpsl
  have hp : (2 ^ f) ^ 2 = 4 ^ f := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [← hp] at hc
  have hb := line_levi_order_le h hf
  rw [h.card_eq_sq, hc] at hb
  have he : Even (2 ^ f) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  exact (not_le_of_gt (psl2_order_lt_square_order (q := 2 ^ f) (by exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) hf) he)) hb

end CFSG.Quasithin.H13.Ch4.U5M


