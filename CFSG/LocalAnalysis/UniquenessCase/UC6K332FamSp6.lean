module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Defs
import CFSG.LocalAnalysis.UniquenessCase.UC6K332WreathFrame
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePsp
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePspFrame
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePslNonab
import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
import CFSG.RankThree.PartTwo.Sec4.RonanK432OuterTools
import CFSG.RankThree.PartOne.FOC.SpOuter
import CFSG.LieType.SeitzGeneration.OuterSpData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open CFSG.Open CFSG.Blueprint
open CFSG.RankThree.PartTwo.Sec4.RonanK432 (ListRow OuterRow outerRow_of_fixed_card_dvd)
open CFSG.RankThree.PartOne.Sec66T (fixSub)
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

theorem orderOf_natCast_mod_three {q : ℕ} (hq : ¬ 3 ∣ q) :
    orderOf ((q : ℕ) : ZMod 3) = 1 ∨ orderOf ((q : ℕ) : ZMod 3) = 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : ((q : ℕ) : ZMod 3) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hq
  have h2 : ((q : ℕ) : ZMod 3) ^ 2 = 1 := by
    simpa using ZMod.pow_card_sub_one_eq_one hne
  exact (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h2)

theorem listRow_statedProj_sp_three {K : Type} [Field K] [Finite K] (hK3 : ¬ 3 ∣ Nat.card K) :
    ListRow (StatedProj (StatedSp 3 K)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype K := Fintype.ofFinite K
  have hp1 : Odd 3 := by decide
  have hpK : ¬ 3 ∣ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
  have hq1 : 1 < Fintype.card K := Fintype.one_lt_card
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Fintype.card K : ℕ) : ZMod 3) = e := ⟨_, rfl⟩
  have he12 : e = 1 ∨ e = 2 := by
    rw [← he]
    exact orderOf_natCast_mod_three hpK
  have hr : (if Even e then 2 * 3 else 3) / e = 3 := by
    rcases he12 with rfl | rfl <;> decide
  obtain ⟨a, ha_def⟩ : ∃ a, padicValNat 3 (Fintype.card K ^ e - 1) = a := ⟨_, rfl⟩
  have ha : 1 ≤ a := by
    rw [← ha_def, ← he]
    exact CrossNum.one_le_crossA hpK hq1
  obtain ⟨F⟩ := nonempty_spFrame K hpK 3 he ha_def hr
  have hcard : (Nat.card (StatedProj (StatedSp 3 K))).factorization 3 = a * 3 + 1 := by
    rw [factorization_card_projSp (by norm_num),
      CFSG.GroupTheory.WeirSylow.factorization_card_statedSp hp1 K hpK 3, he, ha_def, hr,
      ← Nat.factorization_def _ Nat.prime_three, Wreath.factorization_factorial_three]
  have hinj : Function.Injective ((spProj 3 K).comp F.T) :=
    spProj_comp_injective (by norm_num) F.T F.T_injective fun c => ⟨a, pow_pPow_eq_one_pi c⟩
  refine Wreath.listRow_of_blockFrame ha (F.map (spProj 3 K) hinj) ?_
  rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne', hcard]
  omega

theorem listRow_psp6 (S : Type) [Group S] [Finite S] (p f : ℕ) (h : LieModel S .PSp 3 p f)
    (hp3 : p ≠ 3) : ListRow S := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  have hK3 : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    intro hd
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hadm.1).1
      (Nat.prime_three.dvd_of_dvd_pow hd)).symm
  exact CFSG.RankThree.PartTwo.Sec4.RonanK432.ListRow.of_mulEquiv e.symm
    (listRow_statedProj_sp_three hK3)

theorem three_mul_dvd_sp_poly {a : ℕ} (ha : ¬ 3 ∣ a) :
    3 * (a ^ 3 ^ 2 * ∏ j ∈ Finset.Icc 1 3, (a ^ (2 * j) - 1)) ∣
      (a ^ 3) ^ 3 ^ 2 * ∏ j ∈ Finset.Icc 1 3, ((a ^ 3) ^ (2 * j) - 1) := by
  have hprod : ∀ x : ℕ, ∏ j ∈ Finset.Icc 1 3, (x ^ (2 * j) - 1) =
      (x ^ 2 - 1) * (x ^ 4 - 1) * (x ^ 6 - 1) := by
    intro x
    rw [show Finset.Icc 1 3 = {1, 2, 3} by decide]
    simp [Finset.prod_insert, mul_assoc]
  rw [hprod, hprod]
  have ha0 : 1 ≤ a := Nat.pos_of_ne_zero fun h => ha (h ▸ dvd_zero 3)
  obtain ⟨b, hb⟩ : ∃ b, b = a ^ 2 := ⟨_, rfl⟩
  have hb1 : 1 ≤ b := hb ▸ Nat.one_le_pow _ _ ha0
  have hb3 : b % 3 = 1 := by
    rw [hb, Nat.pow_mod]
    rcases (show a % 3 = 1 ∨ a % 3 = 2 by omega) with h | h <;> rw [h]
  have e4 : a ^ 4 = b ^ 2 := by rw [hb, ← pow_mul]
  have e6 : a ^ 6 = b ^ 3 := by rw [hb, ← pow_mul]
  have e12 : (a ^ 3) ^ 2 = b ^ 3 := by rw [hb, ← pow_mul, ← pow_mul]
  have e24 : (a ^ 3) ^ 4 = b ^ 6 := by rw [hb, ← pow_mul, ← pow_mul]
  have e36 : (a ^ 3) ^ 6 = b ^ 9 := by rw [hb, ← pow_mul, ← pow_mul]
  rw [e4, e6, e12, e24, e36, ← hb]
  obtain ⟨c, hc⟩ : 3 ∣ b ^ 2 + b + 1 := by
    have h2 : b ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hb3]
    omega
  have e1 : b ^ 3 - 1 = (b - 1) * (b ^ 2 + b + 1) := by
    have h : 1 ≤ b ^ 3 := Nat.one_le_pow _ _ hb1
    zify [hb1, h]
    ring
  have e2 : b ^ 6 - 1 = (b ^ 2 - 1) * (b ^ 4 + b ^ 2 + 1) := by
    have h : 1 ≤ b ^ 6 := Nat.one_le_pow _ _ hb1
    have h' : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ hb1
    zify [h, h']
    ring
  have e3 : b ^ 9 - 1 = (b ^ 3 - 1) * (b ^ 6 + b ^ 3 + 1) := by
    have h : 1 ≤ b ^ 9 := Nat.one_le_pow _ _ hb1
    have h' : 1 ≤ b ^ 3 := Nat.one_le_pow _ _ hb1
    zify [h, h']
    ring
  refine ⟨a ^ 18 * (c * ((b ^ 4 + b ^ 2 + 1) * (b ^ 6 + b ^ 3 + 1))), ?_⟩
  rw [e3, e2]
  generalize b ^ 3 - 1 = w at e1 ⊢
  rw [hc] at e1
  generalize b - 1 = u at e1 ⊢
  subst e1
  ring

theorem card_statedProj_sp_mul {K : Type} [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hK : Nat.card K = ℓ ^ f) {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (StatedProj (StatedSp n K)) * (if ℓ = 2 then 1 else 2) =
      Nat.card K ^ n ^ 2 * ∏ j ∈ Finset.Icc 1 n, (Nat.card K ^ (2 * j) - 1) := by
  by_cases h2 : ℓ = 2
  · subst h2
    haveI : Fintype K := Fintype.ofFinite K
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP K 2 :=
      charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
    rw [if_pos rfl, mul_one]
    exact CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo n
  · rw [if_neg h2]
    exact CFSG.ClassicalInvolution.card_statedProj_statedSp_of_two_ne_zero
      (CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hℓ h2 hK) hn

theorem card_statedProj_sp_eq {K K' : Type} [Field K] [Finite K] [Field K'] [Finite K']
    {ℓ f f' : ℕ} (hℓ : ℓ.Prime) (hK : Nat.card K = ℓ ^ f) (hK' : Nat.card K' = ℓ ^ f')
    (h : Nat.card K = Nat.card K') {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (StatedProj (StatedSp n K)) = Nat.card (StatedProj (StatedSp n K')) := by
  have hd : 0 < (if ℓ = 2 then 1 else 2) := by split_ifs <;> norm_num
  refine Nat.eq_of_mul_eq_mul_right hd ?_
  rw [card_statedProj_sp_mul hℓ hK hn, card_statedProj_sp_mul hℓ hK' hn, h]

theorem three_mul_card_dvd_statedProj_sp_three {K K₀ : Type} [Field K] [Finite K] [Field K₀]
    [Finite K₀] {ℓ f f₀ : ℕ} (hℓ : ℓ.Prime) (hK : Nat.card K = ℓ ^ f)
    (hK₀ : Nat.card K₀ = ℓ ^ f₀) (hcube : Nat.card K = Nat.card K₀ ^ 3)
    (h3 : ¬ 3 ∣ Nat.card K₀) :
    3 * Nat.card (StatedProj (StatedSp 3 K₀)) ∣ Nat.card (StatedProj (StatedSp 3 K)) := by
  have hT := card_statedProj_sp_mul hℓ hK (n := 3) (by norm_num)
  have hA := card_statedProj_sp_mul hℓ hK₀ (n := 3) (by norm_num)
  have hd : 0 < (if ℓ = 2 then 1 else 2) := by split_ifs <;> norm_num
  refine Nat.dvd_of_mul_dvd_mul_right hd ?_
  rw [mul_assoc, hA, hT, hcube]
  exact three_mul_dvd_sp_poly h3

theorem outerRow_statedProj_sp_three {K : Type} [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) :
    OuterRow (StatedProj (StatedSp 3 K)) := by
  refine outerRow_of_fixed_card_dvd
    (CFSG.LieType.SeitzGeneration.center_statedProj_statedSp_eq_bot (by norm_num))
    fun β hβ hout => ?_
  obtain ⟨σ, hσ, ⟨eF⟩⟩ := CFSG.RankThree.PartOne.FOC.fixedGroup_equiv hℓ hf hK (r := 3)
    (by norm_num) Nat.prime_three (by norm_num) hβ hout
  refine ⟨fixSub β, Nat.card (StatedProj (StatedSp 3 (descentField σ))), fun x => Iff.rfl,
    (Nat.card_congr eF.toEquiv).dvd, ?_⟩
  obtain ⟨hdvd, hkcard⟩ :=
    CFSG.RankThree.PartOne.card_semilinearFixedSubfield hℓ hf hK (rfl : orderOf σ = orderOf σ)
  have hk : Nat.card (descentField σ) = ℓ ^ (f / orderOf σ) := hkcard
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hσ) with h1 | h3
  ·
    exfalso
    rw [h1, Nat.div_one] at hk
    have hcard := card_statedProj_sp_eq hℓ hK hk (by rw [hK, hk]) (n := 3) (by norm_num)
    have htop : fixSub β = ⊤ := Subgroup.eq_top_of_card_eq _ (by
      rw [Nat.card_congr eF.toEquiv]
      exact hcard.symm)
    apply hout
    refine ⟨1, MulEquiv.ext fun x => ?_⟩
    have hx : x ∈ fixSub β := htop ▸ Subgroup.mem_top x
    rw [map_one, MulAut.one_apply]
    exact hx.symm
  · rw [h3] at hk hdvd
    have hKe : Nat.card K = Nat.card (descentField σ) ^ 3 := by
      rw [hK, hk, ← pow_mul, Nat.div_mul_cancel hdvd]
    have hq : ¬ 3 ∣ Nat.card (descentField σ) := by
      rw [hk]
      intro h
      exact hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).mp
        (Nat.prime_three.dvd_of_dvd_pow h)).symm
    exact three_mul_card_dvd_statedProj_sp_three hℓ hK hk hKe hq

theorem outerRow_psp6 (S : Type) [Group S] [Finite S] (p f : ℕ) (h : LieModel S .PSp 3 p f)
    (hp3 : p ≠ 3) : OuterRow S := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  exact CFSG.RankThree.PartTwo.Sec4.RonanK432.OuterRow.of_mulEquiv e.symm
    (outerRow_statedProj_sp_three hadm.1 hp3 hadm.2.1 hK)

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
