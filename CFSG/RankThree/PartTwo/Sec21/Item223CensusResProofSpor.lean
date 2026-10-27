module

public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofOrders
public import CFSG.RankThree.PartTwo.KFacts.K426RestMcL
public import CFSG.RankThree.Native.ONThreeFusion
public import CFSG.RankThree.Native.ONThreeCentralizer

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Blueprint

namespace Item223CensusResProof

theorem noOrderMersenne223_of_centralizer {S : Type} [Group S]
    (h : ∀ x : S, orderOf x = 3 → ∀ m : ℕ, 1 < m → Odd m →
      ¬ (2 ^ m - 1) ∣ Nat.card (Subgroup.centralizer ({x} : Set S))) :
    NoOrderMersenne223 S := by
  intro s m hm1 hmo hs
  have hM : 2 ^ m - 1 ≠ 0 := by
    have : 2 ≤ 2 ^ m := Nat.le_self_pow (by omega) 2
    omega
  have hu : orderOf (s ^ (2 ^ m - 1)) = 3 := by
    rw [orderOf_pow_of_dvd hM (by rw [hs]; exact Dvd.intro_left 3 rfl), hs,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hM)]
  have hc : orderOf (s ^ 3) = 2 ^ m - 1 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hs]; exact Dvd.intro _ rfl), hs,
      Nat.mul_div_cancel_left _ (by norm_num)]
  have hmem : s ^ 3 ∈ Subgroup.centralizer ({s ^ (2 ^ m - 1)} : Set S) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Commute.pow_pow_self s 3 (2 ^ m - 1)).eq
  refine h _ hu m hm1 hmo ?_
  have := Subgroup.orderOf_dvd_natCard _ hmem
  rwa [hc] at this

theorem not_two_pow_sub_one_dvd {N b : ℕ} (hN0 : 0 < N) (hb : N < 2 ^ b - 1)
    (hcheck : ∀ m < b, 1 < m → Odd m → ¬ (2 ^ m - 1) ∣ N) :
    ∀ m : ℕ, 1 < m → Odd m → ¬ (2 ^ m - 1) ∣ N := by
  intro m hm1 hmo hdvd
  by_cases hmb : m < b
  · exact hcheck m hmb hm1 hmo hdvd
  · have h1 : 2 ^ b ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 := Nat.le_of_dvd hN0 hdvd
    omega

theorem not_dvd_29160 : ∀ m : ℕ, 1 < m → Odd m → ¬ (2 ^ m - 1) ∣ 29160 :=
  not_two_pow_sub_one_dvd (b := 15) (by norm_num) (by norm_num) (by decide)

theorem not_dvd_972 : ∀ m : ℕ, 1 < m → Odd m → ¬ (2 ^ m - 1) ∣ 972 :=
  not_two_pow_sub_one_dvd (b := 10) (by norm_num) (by norm_num) (by decide)

theorem not_dvd_3240 : ∀ m : ℕ, 1 < m → Odd m → ¬ (2 ^ m - 1) ∣ 3240 :=
  not_two_pow_sub_one_dvd (b := 12) (by norm_num) (by norm_num) (by decide)

theorem noOrderMersenne223_McL :
    NoOrderMersenne223 NativeSporadic.McL := by
  refine noOrderMersenne223_of_centralizer fun x hx m hm1 hmo => ?_
  rcases KFacts.K426Rest.mclThreeCentralizerCard x hx with h | h
  · rw [h]
    exact not_dvd_29160 m hm1 hmo
  · rw [h]
    exact not_dvd_972 m hm1 hmo

theorem card_centralizer_ON_three
    (x : NativeSporadic.ON) (hx : orderOf x = 3) :
    Nat.card (Subgroup.centralizer ({x} : Set NativeSporadic.ON)) = 3240 := by
  obtain ⟨k, hk⟩ := CFSG.RankThree.Native.onThree_fusion
    CFSG.RankThree.Native.orderOf_onThreeElt hx
  have hx' : x = k⁻¹⁻¹ * CFSG.RankThree.Native.onThreeElt * k⁻¹ := by
    rw [inv_inv, ← hk]
  rw [hx', CFSG.RankThree.Native.card_centralizer_conj_eq,
    CFSG.RankThree.Native.card_centralizer_onThreeElt]

theorem noOrderMersenne223_ON :
    NoOrderMersenne223 NativeSporadic.ON := by
  refine noOrderMersenne223_of_centralizer fun x hx m hm1 hmo => ?_
  rw [card_centralizer_ON_three x hx]
  exact not_dvd_3240 m hm1 hmo

end Item223CensusResProof

open Item223CensusResProof

theorem census223McLONOrders_holds :
    Census223McLONOrders :=
  ⟨noOrderMersenne223_McL, noOrderMersenne223_ON⟩

end CFSG.RankThree.PartTwo.Sec21
