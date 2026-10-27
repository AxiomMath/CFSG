module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcSylowCyclic
public import CFSG.LocalAnalysis.StandardType.GGTableBTwDThree
public import CFSG.LocalAnalysis.StandardType.MarkingSmall
public import CFSG.LieType.Ree.SuzukiOrder

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.CentralCover
open CFSG.Timmesfeld.ExceptionalOrders (geomSum)

namespace TableBExc

theorem card_eq_one_of_dvd_of_not_dvd {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {X : Subgroup G} [Finite X] (hX : IsPGroup p X) {M : ℕ} (hXM : Nat.card X ∣ M)
    (hM : ¬ p ∣ M) : Nat.card X = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hX
  rcases k with _ | k
  · rw [hk, pow_zero]
  · exfalso
    exact hM (dvd_trans (dvd_pow_self p (Nat.succ_ne_zero k)) (hk ▸ hXM))

theorem not_dvd_card_suzuki {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1) :
    ¬ p ∣ (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1) := by
  have hq1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact h2 (hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow h))
    · apply h2
      have e : 2 ^ n + 1 = (2 ^ n - 1) + 2 := by omega
      rw [e] at hpq
      exact (Nat.dvd_add_right h).mp hpq
  · apply h2
    have e : (2 ^ n) ^ 2 + 1 = (2 ^ n - 1) * (2 ^ n + 1) + 2 := by
      zify [hq1]
      ring
    rw [e] at h
    exact (Nat.dvd_add_right (dvd_mul_of_dvd_right hpq _)).mp h

theorem dvd_of_largeEvenSplit_twB2 {p : ℕ} {lab : LargeEvenLabel} (ht : lab.tag = .twB2)
    (hlab : LargeEvenInLambda2 lab) (hs : LargeEvenSplit p lab) : p ∣ 2 ^ lab.n + 1 := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab hs ⊢
  subst ht
  have hn3 : 3 ≤ n := hlab.2.2.2
  rcases hs with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨hn, -⟩
  · exact absurd h id
  · exact h
  · rcases h with h | h <;> cases h
  · exact absurd (show n = 1 from hn) (by omega)

theorem largeEvenLabelAll_card_lt_twB2 {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twB2)
    (hs : LargeEvenSplit p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  have := Fact.mk hp
  have hpn := dvd_of_largeEvenSplit_twB2 ht hlab hs
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab hpn ⊢
  subst ht
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hn3 : 3 ≤ n := hlab.2.2.2
    have : 2 ∣ 1 := (Nat.dvd_add_right (dvd_pow_self 2 (by omega))).mp hpn
    omega
  obtain ⟨k, hk⟩ := hlab.2.2.1
  have hk' : n = 2 * k + 1 := hk
  have hna : 2 * ((n - 1) / 2) + 1 = n := by omega
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq'⟩ := hQ
  refine ⟨K, i1, i2, hK, hq', fun X hXI hX => ?_⟩
  have : Finite (LargeEvenSzGroup ((n - 1) / 2) K) := Subtype.finite
  have : Finite (LargeEvenCenterQuot (LargeEvenSzGroup ((n - 1) / 2) K)) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  have := TableBSymp.finite_mulAut (R := LargeEvenCenterQuot (LargeEvenSzGroup ((n - 1) / 2) K))
  have hXle : X ≤ (MulAut.conj : LargeEvenCenterQuot (LargeEvenSzGroup ((n - 1) / 2) K) →*
      MulAut (LargeEvenCenterQuot (LargeEvenSzGroup ((n - 1) / 2) K))).range :=
    fun x hx => hXI hx
  have hdvd : Nat.card X ∣ (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1) := by
    refine dvd_trans (Subgroup.card_dvd_of_le hXle) (dvd_trans (Subgroup.card_range_dvd _) ?_)
    refine dvd_trans (Subgroup.card_quotient_dvd_card _) ?_
    rw [largeEvenSzGroup_eq _ K, CFSG.LieType.Ree.suzuki_order hK, hna]
  rw [card_eq_one_of_dvd_of_not_dvd (TableB.isPGroup_of_isElemAbelian hX) hdvd
    (not_dvd_card_suzuki hp hp2 hpn)]
  exact Nat.one_lt_pow (by norm_num) hp.one_lt

local instance tableBExcNeZeroRankG2 : NeZero Tag.G2.rank := ⟨by decide⟩

@[expose] def wordG2Three : List (Fin Tag.G2.rank) := [0, 1, 0, 1]

theorem orderOf_wordG2Three : orderOf ((coxeterSystem .G2).wordProd wordG2Three) = 3 :=
  orderOf_wordProd_eq Nat.prime_three _ (by decide +kernel) ⟨0, by decide +kernel⟩

theorem card_fix_wordG2Three :
    Nat.card {x : Fin Tag.G2.rank → ZMod 3 // torusWord .G2 3 wordG2Three x = x} ≤ 3 ^ (2 - 1) :=
  card_fix_torusWord_le (τ := .G2) wordG2Three ![1] ![0] (by decide) ![![1]] (by decide +kernel)

theorem geomSum_six_mod {q : ℕ} (h : q % 3 = 1) : geomSum 6 1 q % 9 = 6 := by
  have hr : q % 9 = 1 ∨ q % 9 = 4 ∨ q % 9 = 7 := by omega
  rw [geomSum]
  simp only [one_mul]
  rw [TableBF4.geomSum_mod]
  rcases hr with h | h | h <;> rw [h] <;> decide

theorem dvd_of_largeEvenSplit_G2 {p : ℕ} {lab : LargeEvenLabel} (ht : lab.tag = .G2)
    (hlab : LargeEvenInLambda2 lab) (hs : LargeEvenSplit p lab) : p ∣ 2 ^ lab.n - 1 := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab hs ⊢
  subst ht
  have hn2 : 2 ≤ n := hlab.2.2
  rcases hs with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨hn, -⟩
  · exact h
  · exact absurd trivial h
  · rcases h with h | h <;> cases h
  · exact absurd (show n = 1 from hn) (by omega)

section G2

variable {K : Type} [Field K]

theorem card_adjointGroup_G2_eq [Finite K] :
    Nat.card (adjointGroup .G2 K) = Nat.card (torusGroup .G2 K) *
      (Nat.card K ^ 6 * (geomSum 2 1 (Nat.card K) * geomSum 6 1 (Nat.card K))) := by
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2,
    CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_G2,
    ← CFSG.Timmesfeld.ExceptionalOrders.ordG2_eq _ Nat.card_pos, mul_assoc]

theorem card_torusPow_G2 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card K - 1) : Nat.card (torusPow .G2 K p) = p ^ 2 :=
  card_torusPow_of_full (fun a => (even_power_two_Cartan_root_diagonals_inner .G2 (Or.inl rfl) K
    (ringChar.eq K 2)).1 a) hp hpq

theorem card_lt_cube_G2 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) {E : Subgroup (adjointGroup .G2 K)} (hE : IsElemAbelian p E) :
    Nat.card E < p ^ 3 := by
  have : Finite (adjointGroup .G2 K) := generated_group_finite .G2 K
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hq1 : (Nat.card K : ZMod p) = 1 := cast_eq_one_of_dvd_sub_one hq hpq
  have hV := card_torusPow_G2 hp hpq
  have hp3' : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  by_cases hp3 : p = 3
  · subst hp3
    have hG := geomSum_six_mod (mod_eq_one_of_dvd_sub_one (by norm_num) hq hpq)
    have hm2 := cast_div_eq (p := 3) (c := 2) (by norm_num) (by norm_num) hG
    have hGm : geomSum 6 1 (Nat.card K) = 3 * (geomSum 6 1 (Nat.card K) / 3) := by omega
    have hS : Nat.card (Subgroup.zpowers ((coxeterSystem .G2).wordProd wordG2Three)) = 3 := by
      rw [Nat.card_zpowers, orderOf_wordG2Three]
    have hC : Nat.card (adjointGroup .G2 K) =
        Nat.card (Subgroup.zpowers ((coxeterSystem .G2).wordProd wordG2Three)) *
          Nat.card (torusGroup .G2 K) * (Nat.card K ^ 6 * (geomSum 2 1 (Nat.card K) *
            (geomSum 6 1 (Nat.card K) / 3))) := by
      rw [card_adjointGroup_G2_eq, hS]
      nth_rewrite 1 [hGm]
      ring
    have hidx : ¬ 3 ∣ (weylX .G2 K (Subgroup.zpowers
        ((coxeterSystem .G2).wordProd wordG2Three))).index := by
      rw [index_weylX_eq hC]
      apply not_dvd_of_cast_ne_zero
      push_cast
      simp only [hq1, hm2, geomSum_cast hq1, one_pow]
      decide
    obtain ⟨g, hg⟩ := TableBF4.exists_conj_le_of_not_dvd_index Nat.prime_three hidx
      (TableB.isPGroup_of_isElemAbelian hE)
    have hcard : Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card E :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    rcases le_torusPow_or_card_lt_of_le_weylX (B := 3 ^ 3) Nat.prime_three hpq
        (isUnit_det_cartan_of_eq Nat.prime_three det_cartan_G2 (by norm_num)) hV
        (fun s hs hs1 => by
          obtain ⟨k, hk⟩ := exists_pow_eq_of_mem_zpowers Nat.prime_three orderOf_wordG2Three hs hs1
          refine ⟨k, wordG2Three, hk.symm, ?_⟩
          rw [hS]
          calc 3 * Nat.card {x : Fin Tag.G2.rank → ZMod 3 // torusWord .G2 3 wordG2Three x = x}
              ≤ 3 * 3 ^ (2 - 1) := Nat.mul_le_mul_left _ card_fix_wordG2Three
            _ < 3 ^ 3 := by norm_num)
        (TableB.isElemAbelian_map hE _) hg with h | h
    · have h1 := Subgroup.card_le_of_le h
      rw [hV, hcard] at h1
      omega
    · rwa [hcard] at h
  · have := Fact.mk hp
    have h5 : 5 ≤ p := by
      have h2 := hp.two_le
      have h4 : p ≠ 4 := by
        rintro rfl
        exact absurd hp (by decide)
      omega
    have hidx : ¬ p ∣ ((torusGroup .G2 K).subgroupOf (adjointGroup .G2 K)).index := by
      rw [index_torusGroup_eq card_adjointGroup_G2_eq]
      apply not_dvd_of_cast_ne_zero
      push_cast
      simp only [hq1, geomSum_cast hq1, one_pow, one_mul]
      intro h
      have h12 : ((12 : ℕ) : ZMod p) = 0 := by
        rw [show (12 : ℕ) = 2 * 6 by norm_num, Nat.cast_mul]
        exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at h12
      have h12' : p ∣ 2 ^ 2 * 3 := by norm_num; exact h12
      rcases (Nat.Prime.dvd_mul hp).mp h12' with h | h
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
        omega
    obtain ⟨g, hg⟩ := exists_conj_le_torusPow hp hidx hE
    have h1 := Subgroup.card_le_of_le hg
    rw [hV, Subgroup.card_map_of_injective (MulAut.conj g).injective] at h1
    omega

theorem largeEvenLabelAll_card_lt_G2 {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .G2) (hs : LargeEvenSplit p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  have hpn := dvd_of_largeEvenSplit_G2 ht hlab hs
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab hpn ⊢
  subst ht
  have hn : 1 ≤ n := hlab.1
  have hp2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq'⟩ := hQ
  refine ⟨K, i1, i2, hK, hq', fun X hXI hX => ?_⟩
  have : CharP K 2 := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  have := finite_recipeGroup .G2 K
  have hI := idImage_subset_inn_of_top .G2 K
    (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanG2_inv fun s => ⟨s, pow_one s⟩)
  obtain ⟨A, hA, hAc⟩ := TableBSymp.exists_of_subset_inn (center_recipeGroup_eq_bot .G2 K)
    (fun φ hφ => hI (hXI hφ)) hX
  have h1 := card_lt_cube_G2 hp hp2 hpq (E := A.map (recipeEquiv .G2 K).toMonoidHom)
    (TableB.isElemAbelian_map hA _)
  rw [Subgroup.card_map_of_injective (recipeEquiv .G2 K).injective, hAc] at h1
  exact h1

end G2

@[expose] def GGTableBG2TwB2Label (_p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .G2 ∨ lab.tag = .twB2

theorem largeEvenLabelAll_card_lt_G2TwB2
    {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hlab : LargeEvenInLambda2 lab) (h : GGTableBG2TwB2Label p lab)
    (hs : LargeEvenSplit p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  rcases h with ht | ht
  · exact largeEvenLabelAll_card_lt_G2 hp hlab ht hs
  · exact largeEvenLabelAll_card_lt_twB2 hp hlab ht hs

end TableBExc

theorem ggBstarInputOn_G2TwB2 :
    GGBstarInputOn TableBExc.GGTableBG2TwB2Label :=
  ggBstarInputOn_of_labelAll_card_lt fun _ _ hp hlab h hs =>
    TableBExc.largeEvenLabelAll_card_lt_G2TwB2 hp hlab h hs

theorem ggStdSubPreInputOn_G2TwB2 :
    GGStdSubPreInputOn TableBExc.GGTableBG2TwB2Label :=
  ggStdSubPreInputOn_of_labelAll_card_lt fun _ _ hp hlab h hs =>
    TableBExc.largeEvenLabelAll_card_lt_G2TwB2 hp hlab h hs

end CFSG.StandardType
