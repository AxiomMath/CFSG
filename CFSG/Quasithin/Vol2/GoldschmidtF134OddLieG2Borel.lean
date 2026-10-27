module

public import CFSG.Quasithin.Vol2.F134LieG2Borel
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieS5
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieG2Arith
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieG2Elem

set_option linter.unusedSectionVars false

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.BorelTits CFSG.ABGLocalTools
open CFSG.Quasithin.F134.LieG2

namespace CFSG.Quasithin.H13.NQCore.G2


variable {K : Type} [Field K]

theorem not_dvd_card_borelGroup [Finite K] {τ : Tag} {n p : ℕ} (hK : Nat.card K = 2 ^ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1) :
    ¬ p ∣ Nat.card (borelGroup τ K) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [card_borelGroup, card_posUnipotent]
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p h
    have h1 := pow_card_sub_one_eq_one_of_mem_diagonalGroup (torusGroup_le_diagonalGroup x.2)
    have hd : orderOf x ∣ Nat.card K - 1 :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h1))
    rw [hx] at hd
    exact hpq hd
  · have h3 := hp.dvd_of_dvd_pow h
    rw [hK] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3))

theorem le_borelGroup_of_card_eq_prime [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    {p a : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (ha : a = 2 ∨ a = 3)
    {H : Subgroup (adjointGroup .G2 K)}
    (hUH : (posUnipotent .G2 K).subgroupOf (adjointGroup .G2 K) ≤ H)
    (hH : Nat.card H =
      p ^ a * Nat.card ((posUnipotent .G2 K).subgroupOf (adjointGroup .G2 K))) :
    H ≤ (borelGroup .G2 K).subgroupOf (adjointGroup .G2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK
  have : Finite (ModGL .G2 K) := finite_modGL
  have hBC : borelGroup .G2 K ≤ adjointGroup .G2 K :=
    ((triangular_borel_structure.{0, 0} .G2 K).2.2.2.2.2.2.2.2.2.2.2 K).1
  have hUC : posUnipotent .G2 K ≤ adjointGroup .G2 K := le_sup_right.trans hBC
  have hUcard : Nat.card (posUnipotent .G2 K) = 2 ^ (6 * n) := by
    rw [card_posUnipotent, ncard_posRoots_G2, hK, ← pow_mul, mul_comm]
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index 2 hUC card_posUnipotent
  have hU : IsSylowOf 2 ((posUnipotent .G2 K).subgroupOf (adjointGroup .G2 K)) ⊤ := by
    rw [isSylowOf_iff]
    exact ⟨le_top, hUp, by rwa [Subgroup.relIndex_top_right]⟩
  have hcardUC : Nat.card ((posUnipotent .G2 K).subgroupOf (adjointGroup .G2 K)) =
      2 ^ (6 * n) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUC).toEquiv, hUcard]
  have hq4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨E, hEU, hE2, hEcard⟩ := exists_elementaryAbelian_posUnipotent (K := K)
  have hE16 : 16 ≤ Nat.card E := by
    rw [hEcard]
    calc 16 ≤ 4 ^ 3 := by norm_num
      _ ≤ Nat.card K ^ 3 := Nat.pow_le_pow_left hq4 3
  obtain ⟨Q', hQ', hHQ', hNQ'⟩ := CFSG.Quasithin.H13.NQCore.S5.exists_proper_overgroup
    (holds_adjointGroup_tag .G2 K 2) hU hUH (fun x hx => hUH (hEU x hx)) hE2 hE16 hp hp2
    (m := 6 * n) (a := a) (by rw [hH, hcardUC, mul_comm]) (by omega)
  have hBN : borelGroup .G2 K ≤ Subgroup.normalizer (posUnipotent .G2 K : Set (ModGL .G2 K)) := by
    rw [← (borel_self_normalizers .G2 K).1]
    exact inf_le_right
  have hBQ : borelGroup .G2 K ≤ Q'.map (adjointGroup .G2 K).subtype := by
    intro b hb
    refine ⟨⟨b, hBC hb⟩, hNQ' ?_, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.1 (hBN hb) x
  have hQC : Q'.map (adjointGroup .G2 K).subtype ≤ adjointGroup .G2 K :=
    Subgroup.map_subtype_le Q'
  have hQne : Q'.map (adjointGroup .G2 K).subtype ≠ adjointGroup .G2 K := by
    intro hQeq
    refine hQ' (eq_top_iff.2 fun x _ => ?_)
    have hx : (x : ModGL .G2 K) ∈ Q'.map (adjointGroup .G2 K).subtype := by
      rw [hQeq]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [show y = x from Subtype.ext hyx] at hy
  have hHQ : H.map (adjointGroup .G2 K).subtype ≤ Q'.map (adjointGroup .G2 K).subtype :=
    Subgroup.map_mono hHQ'
  obtain ⟨i, hi⟩ := exists_le_parabolicSubgroup_singleton rfl hBQ hQC hQne
  have hUH' : posUnipotent .G2 K ≤ H.map (adjointGroup .G2 K).subtype := fun u hu =>
    ⟨⟨u, hUC hu⟩, hUH hu, rfl⟩
  rcases le_borelGroup_or_dvd (hHQ.trans hi) hUH' with hB | hdvd
  · exact fun x hx => hB ⟨x, hx, rfl⟩
  exfalso
  have hcardH' : Nat.card (H.map (adjointGroup .G2 K).subtype) =
      p ^ a * Nat.card (posUnipotent .G2 K) := by
    rw [Subgroup.card_map_of_injective (adjointGroup .G2 K).subtype_injective, hH, hcardUC, hUcard]
  have hrel : (posUnipotent .G2 K).relIndex (H.map (adjointGroup .G2 K).subtype) = p ^ a := by
    have h := Subgroup.relIndex_mul_card (posUnipotent .G2 K)
      (H.map (adjointGroup .G2 K).subtype)
    rw [inf_eq_left.2 hUH', hcardH'] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  rw [hrel] at hdvd
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hj0 : j ≠ 0 := by
    rintro rfl
    simp at hj'
    omega
  have hpdvd : p ∣ Nat.card K + 1 := hj' ▸ dvd_pow_self p hj0
  have hpq : ¬ p ∣ Nat.card K - 1 := by
    intro h
    have h2 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hpdvd h
    have e : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
    rw [e] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  have hpB := not_dvd_card_borelGroup (τ := .G2) hK hp hp2 hpq
  have hdivP : p ^ a ∣ Nat.card (parabolicSubgroup .G2 K {i}) := by
    have h1 : Nat.card (H.map (adjointGroup .G2 K).subtype) ∣
        Nat.card (parabolicSubgroup .G2 K {i}) :=
      Subgroup.card_dvd_of_le (hHQ.trans hi)
    rw [hcardH'] at h1
    exact (Dvd.intro _ rfl).trans h1
  rw [card_parabolicSubgroup_singleton, hj'] at hdivP
  have hcop : Nat.Coprime (p ^ a) (Nat.card (borelGroup .G2 K)) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpB)
  have haj : a ≤ j :=
    (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 (hcop.dvd_of_dvd_mul_left hdivP)
  obtain rfl : j = a := le_antisymm hj haj
  exact two_pow_add_one_ne_prime_pow (n := n) (j := j) hp5 (hp.odd_of_ne_two hp2) (by omega)
    (by omega) (by rw [← hK]; exact hj')

end CFSG.Quasithin.H13.NQCore.G2
