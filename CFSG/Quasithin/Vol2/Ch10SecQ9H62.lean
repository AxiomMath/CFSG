module

public import CFSG.Quasithin.Vol2.Ch10SecKITa
public import CFSG.Quasithin.Vol2.Ch11SecA11Ord
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def FactG2CoreOddIndex : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (f : ℕ), 2 ≤ f → IsG2 2 f Y → ∀ P : Subgroup Y,
    IsMaxParabolic2 (⊤ : Subgroup Y) P → ¬ 2 ∣ (perfectCore P).index

namespace Rank2

theorem odd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) := by
  have h : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨k, hk⟩ : Even (2 ^ n) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  exact ⟨k - 1, by omega⟩

theorem not_two_dvd_index_of_card {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y}
    {a B m c : ℕ} (hP : Nat.card P = 2 ^ a * B) (hm : Odd m)
    (hY : Nat.card Y * c = 2 ^ a * m) : ¬ 2 ∣ P.index := by
  intro h
  have h1 := P.index_mul_card
  have h2 : P.index * B * c = m := by
    have : 2 ^ a * (P.index * B * c) = 2 ^ a * m := by
      rw [← hY, ← h1, hP]
      ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  have h3 : 2 ∣ m := h2 ▸ (h.mul_right B).mul_right c
  exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h3)

theorem card_mul_of_isPSL3 {Y : Type} [Group Y] [Finite Y] {f : ℕ} (hf : 1 ≤ f)
    (h : IsPSL 3 2 f Y) : ∃ m c : ℕ, Odd m ∧ Nat.card Y * c = 2 ^ (3 * f) * m := by
  have hc := Ch11.SecA.card_of_isPSL (by norm_num) h
  have hI : Finset.Icc 2 3 = ({2, 3} : Finset ℕ) := by decide
  rw [hI, Finset.prod_pair (by norm_num), show 3 * (3 - 1) / 2 = 3 by norm_num] at hc
  set q := 2 ^ f with hq
  have hd : Nat.gcd 3 (q - 1) ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
    refine (Nat.gcd_dvd_right 3 (q - 1)).trans (Dvd.dvd.mul_left (Dvd.dvd.mul_right ?_ _) _)
    simpa using Nat.sub_dvd_pow_sub_pow q 1 2
  refine ⟨(q ^ 2 - 1) * (q ^ 3 - 1), Nat.gcd 3 (q - 1), ?_, ?_⟩
  · have h2 : q ^ 2 - 1 = 2 ^ (2 * f) - 1 := by rw [hq, ← pow_mul, mul_comm]
    have h3 : q ^ 3 - 1 = 2 ^ (3 * f) - 1 := by rw [hq, ← pow_mul, mul_comm]
    rw [h2, h3]
    exact (odd_two_pow_sub_one (by omega)).mul (odd_two_pow_sub_one (by omega))
  · rw [hc, Nat.div_mul_cancel hd, hq, ← pow_mul, mul_comm f 3]

theorem card_mul_of_isSL3 {Y : Type} [Group Y] [Finite Y] {f : ℕ} (hf : 1 ≤ f)
    (h : IsSL3 (2 ^ f) Y) : ∃ m c : ℕ, Odd m ∧ Nat.card Y * c = 2 ^ (3 * f) * m := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := h
  have := Fintype.ofFinite K
  set q := 2 ^ f with hq
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have hcard : Nat.card Y = (q ^ 3 - 1) * (q ^ 3 - q) * (q ^ 3 - q ^ 2) / (q - 1) := by
    rw [Nat.card_congr (φ.trans
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm).toEquiv,
      Matrix.card_SL_field, ← Nat.card_eq_fintype_card, hK]
    simp [Fin.prod_univ_three]
  have e1 : q ^ 3 - q = q * (q ^ 2 - 1) := by
    rw [Nat.mul_sub, mul_one, ← pow_succ']
  have e2 : q ^ 3 - q ^ 2 = q ^ 2 * (q - 1) := by
    rw [Nat.mul_sub, mul_one, ← pow_succ]
  have hprod : (q ^ 3 - 1) * (q ^ 3 - q) * (q ^ 3 - q ^ 2) =
      (q - 1) * (q ^ 3 * ((q ^ 3 - 1) * (q ^ 2 - 1))) := by
    rw [e1, e2]
    ring
  refine ⟨(q ^ 3 - 1) * (q ^ 2 - 1), 1, ?_, ?_⟩
  · have h2 : q ^ 2 - 1 = 2 ^ (2 * f) - 1 := by rw [hq, ← pow_mul, mul_comm]
    have h3 : q ^ 3 - 1 = 2 ^ (3 * f) - 1 := by rw [hq, ← pow_mul, mul_comm]
    rw [h2, h3]
    exact (odd_two_pow_sub_one (by omega)).mul (odd_two_pow_sub_one (by omega))
  · have hpos : 0 < q - 1 := by
      have : 2 ≤ q := by
        rw [hq]
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      omega
    rw [hcard, hprod, Nat.mul_div_cancel_left _ hpos, mul_one, hq, ← pow_mul, mul_comm f 3]

theorem card_mul_of_isPSp4 {Y : Type} [Group Y] [Finite Y] {f : ℕ} (hf : 1 ≤ f)
    (h : IsPSp4 2 f Y) : ∃ m c : ℕ, Odd m ∧ Nat.card Y * c = 2 ^ (4 * f) * m := by
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := h
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf
      hK
  have hbij : Function.Bijective (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 K) :=
    ⟨Vol2Native.A312L.proj_injective_charTwo,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective⟩
  have hcard : Nat.card Y = Nat.card K ^ (2 ^ 2) *
      ∏ j ∈ Finset.Icc 1 2, (Nat.card K ^ (2 * j) - 1) := by
    rw [Nat.card_congr φ.toEquiv, ← Nat.card_congr (Equiv.ofBijective _ hbij),
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp]
  have hI : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  rw [hI, Finset.prod_pair (by norm_num), hK] at hcard
  refine ⟨((2 ^ f) ^ (2 * 1) - 1) * ((2 ^ f) ^ (2 * 2) - 1), 1, ?_, ?_⟩
  · have h2 : (2 ^ f) ^ (2 * 1) - 1 = 2 ^ (2 * f) - 1 := by rw [← pow_mul, mul_comm]
    have h4 : (2 ^ f) ^ (2 * 2) - 1 = 2 ^ (4 * f) - 1 := by rw [← pow_mul, mul_comm]
    rw [h2, h4]
    exact (odd_two_pow_sub_one (by omega)).mul (odd_two_pow_sub_one (by omega))
  · rw [hcard, mul_one, ← pow_mul, show f * 2 ^ 2 = 4 * f by ring]

theorem not_two_dvd_index_perfectCore (hK1 : C10KH.KGRank2ParabolicOrder)
    (hG2 : FactG2CoreOddIndex) {Y : Type} [Group Y] [Finite Y] {f : ℕ} (hf : 2 ≤ f)
    (htype : IsPSL 3 2 f Y ∨ IsSL3 (2 ^ f) Y ∨ IsPSp4 2 f Y ∨ IsG2 2 f Y) {P : Subgroup Y}
    (hP : IsMaxParabolic2 (⊤ : Subgroup Y) P) : ¬ 2 ∣ (perfectCore P).index := by
  rcases htype with h | h | h | h
  · obtain ⟨m, c, hm, hY⟩ := card_mul_of_isPSL3 (by omega) h
    exact not_two_dvd_index_of_card ((hK1 Y f hf P hP).1 (Or.inl h)) hm hY
  · obtain ⟨m, c, hm, hY⟩ := card_mul_of_isSL3 (by omega) h
    exact not_two_dvd_index_of_card ((hK1 Y f hf P hP).1 (Or.inr h)) hm hY
  · obtain ⟨m, c, hm, hY⟩ := card_mul_of_isPSp4 (by omega) h
    exact not_two_dvd_index_of_card ((hK1 Y f hf P hP).2 h) hm hY
  · exact hG2 Y f hf h P hP

theorem isMaxParabolic2_top_of_map {G : Type} [Group G] {L P : Subgroup G}
    (h : IsMaxParabolic2 L P) : IsMaxParabolic2 (⊤ : Subgroup ↥L) (P.subgroupOf L) := by
  obtain ⟨hpar, hne, hmax⟩ := h
  have hPL : P ≤ L := hpar.1
  refine ⟨?_, ?_, ?_⟩
  · rw [A312.isParabolic2_top_iff, Subgroup.map_subgroupOf_eq_of_le hPL]
    exact hpar
  · intro htop
    apply hne
    have := congrArg (Subgroup.map L.subtype) htop
    rwa [Subgroup.map_subgroupOf_eq_of_le hPL, Subgroup.map_top, Subgroup.range_subtype] at this
  · intro Q' hQ' hQ'top hPQ'
    have hQ : IsParabolic2 L (Q'.map L.subtype) := (A312.isParabolic2_top_iff L Q').mp hQ'
    have hQL : Q'.map L.subtype ≠ L := by
      intro h
      apply hQ'top
      have := congrArg (fun K : Subgroup G => K.subgroupOf L) h
      simpa [A4.subgroupOf_map_subtype', Subgroup.subgroupOf_self] using this
    have hPQ : P ≤ Q'.map L.subtype := by
      have := Subgroup.map_mono (f := L.subtype) hPQ'
      rwa [Subgroup.map_subgroupOf_eq_of_le hPL] at this
    have h1 := hmax _ hQ hQL hPQ
    calc Q' = (Q'.map L.subtype).subgroupOf L := (A4.subgroupOf_map_subtype' L Q').symm
      _ = P.subgroupOf L := by rw [h1]

theorem perfectCore_subgroupOf {G : Type} [Group G] [Finite G] {L P : Subgroup G} (hPL : P ≤ L) :
    perfectCore (P.subgroupOf L) = (perfectCore P).subgroupOf L := by
  have h : (perfectCore (P.subgroupOf L)).map L.subtype = perfectCore P := by
    rw [map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hPL]
  rw [← h, A4.subgroupOf_map_subtype']

end Rank2

end CFSG.Quasithin.Vol2.Ch10.SecB
