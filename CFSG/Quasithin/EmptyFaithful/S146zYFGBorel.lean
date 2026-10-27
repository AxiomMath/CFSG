module

public import CFSG.Quasithin.Vol2.F134LieG2Borel
public import CFSG.Quasithin.EmptyFaithful.S146zYFGCore

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.BorelTits CFSG.ABGLocalTools
open CFSG.Quasithin.F134.LieF4 CFSG.Quasithin.F134.LieG2

section Torus

variable {τ : Tag} {K : Type} [Field K]

theorem not_five_dvd_card_borelGroup_of_card_four
    [Finite K] (hK : Nat.card K = 4) :
    ¬ 5 ∣ Nat.card (borelGroup τ K) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [card_borelGroup, card_posUnipotent, hK]
  intro h
  rcases (Nat.Prime.dvd_mul (by norm_num)).1 h with h | h
  · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 h
    have h1 := pow_card_sub_one_eq_one_of_mem_diagonalGroup (torusGroup_le_diagonalGroup x.2)
    rw [hK] at h1
    have h3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h1))
    rw [hx] at h3
    norm_num at h3
  · have := Nat.Prime.dvd_of_dvd_pow (by norm_num) h
    norm_num at this

end Torus

section G2


variable {K : Type} [Field K]

theorem le_borelGroup_of_card_eq_twentyFive [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) {H P : Subgroup (ModGL .G2 K)}
    (hHC : H ≤ adjointGroup .G2 K) (hUH : posUnipotent .G2 K ≤ H)
    (hH : Nat.card H = 25 * Nat.card (posUnipotent .G2 K)) (hPH : P ≤ H) (hP : Nat.card P = 25)
    (hexp : ∀ x ∈ P, x ^ 5 = 1) : H ≤ borelGroup .G2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK
  have : Finite (ModGL .G2 K) := finite_modGL
  set C := adjointGroup .G2 K with hC
  have hBC : borelGroup .G2 K ≤ C :=
    ((triangular_borel_structure.{0, 0} .G2 K).2.2.2.2.2.2.2.2.2.2.2 K).1
  have hUC : posUnipotent .G2 K ≤ C := le_sup_right.trans hBC
  have hUcard : Nat.card (posUnipotent .G2 K) = 2 ^ (6 * n) := by
    rw [card_posUnipotent, ncard_posRoots_G2, hK, ← pow_mul, mul_comm]
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index 2 hUC card_posUnipotent
  have hU : IsSylowOf 2 ((posUnipotent .G2 K).subgroupOf C) ⊤ := by
    rw [isSylowOf_iff]
    exact ⟨le_top, hUp, by rwa [Subgroup.relIndex_top_right]⟩
  have hUH' : (posUnipotent .G2 K).subgroupOf C ≤ H.subgroupOf C := fun x hx => hUH hx
  obtain ⟨V, hV, hV2, hHV⟩ := exists_normalizing_isPGroup_two_ne_bot_of_card
    (H := H.subgroupOf C) (P := P.subgroupOf C) (k := 6 * n)
    (by rw [card_subgroupOf_of_le hHC, hH, hUcard]) (by omega)
    (fun x hx => hPH hx) (by rw [card_subgroupOf_of_le (hPH.trans hHC), hP])
    (fun x hx => Subtype.ext (by simpa using hexp _ hx))
  obtain ⟨Q', hQ', hHQ', hNQ'⟩ := exists_proper_overgroup_of_normal_isPGroup
    (holds_adjointGroup_tag .G2 K 2) hU hUH' hV hV2 hHV
  have hBN : borelGroup .G2 K ≤ Subgroup.normalizer (posUnipotent .G2 K : Set (ModGL .G2 K)) := by
    rw [← (borel_self_normalizers .G2 K).1]
    exact inf_le_right
  have hBQ : borelGroup .G2 K ≤ Q'.map C.subtype := by
    intro b hb
    refine ⟨⟨b, hBC hb⟩, hNQ' ?_, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.1 (hBN hb) x
  have hQC : Q'.map C.subtype ≤ C := Subgroup.map_subtype_le Q'
  have hQne : Q'.map C.subtype ≠ C := by
    intro hQeq
    refine hQ' (eq_top_iff.2 fun x _ => ?_)
    have hx : (x : ModGL .G2 K) ∈ Q'.map C.subtype := by
      rw [hQeq]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [show y = x from Subtype.ext hyx] at hy
  have hHQ : H ≤ Q'.map C.subtype := fun h hh => ⟨⟨h, hHC hh⟩, hHQ' hh, rfl⟩
  obtain ⟨i, hi⟩ := exists_le_parabolicSubgroup_singleton rfl hBQ hQC hQne
  rcases le_borelGroup_or_dvd (hHQ.trans hi) hUH with hB | hdvd
  · exact hB
  exfalso
  have hrel : (posUnipotent .G2 K).relIndex H = 25 := by
    have h := Subgroup.relIndex_mul_card (posUnipotent .G2 K) H
    rw [inf_eq_left.2 hUH, hH] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  rw [hrel] at hdvd
  have hq4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).1
    (show Nat.card K + 1 ∣ 5 ^ 2 by simpa using hdvd)
  have hq : Nat.card K = 4 := by
    interval_cases j
    · simp at hj'
      omega
    · simp at hj'
      omega
    · exfalso
      have h3 : 3 ∣ 2 ^ n := ⟨8, by rw [← hK]; simp at hj'; omega⟩
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
  have h25 : 25 ∣ Nat.card (parabolicSubgroup .G2 K {i}) :=
    (Dvd.intro _ hH.symm).trans (Subgroup.card_dvd_of_le (hHQ.trans hi))
  rw [card_parabolicSubgroup_singleton, hq] at h25
  exact not_five_dvd_card_borelGroup_of_card_four (τ := .G2) hq
    (Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 5) (show 5 * 5 ∣ _ * 5 from h25))

end G2

end CFSG.Quasithin.S146zY
