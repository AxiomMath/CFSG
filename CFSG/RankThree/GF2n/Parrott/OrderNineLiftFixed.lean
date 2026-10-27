module

public import CFSG.RankThree.GF2n.Parrott.OrderNineLift
public import CFSG.RankThree.GF2n.Parrott.LiftOrderThree

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.GH74.KGroups

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

noncomputable def lift9 (x : QA45.originalSubgroup) (hx : orderOf x = 9) : ↥(H z) :=
  let y := lift D x
  let k := orderOf ((y : ↥(H z)) ^ 9)
  y ^ k

theorem qH_lift9 (x : QA45.originalSubgroup) (hx : orderOf x = 9) :
    qH D (lift9 D x hx) = x ^ orderOf ((lift D x : ↥(H z)) ^ 9) := by
  unfold lift9
  dsimp only
  rw [map_pow, qH_lift]

theorem orderOf_lift9 (x : QA45.originalSubgroup) (hx : orderOf x = 9) :
    orderOf (lift9 D x hx) = 9 := by
  classical
  unfold lift9
  dsimp only
  set y : ↥(H z) := lift D x with hy
  set k : ℕ := orderOf (y ^ 9) with hk
  have hqy : qH D y = x := by rw [hy, qH_lift]
  have h9dvd : 9 ∣ orderOf y := by
    have h := orderOf_map_dvd (qH D) y
    rwa [hqy, hx] at h
  have hk_eq : k = orderOf y / 9 := by
    rw [hk, orderOf_pow_of_dvd (x := y) (n := 9) (by norm_num) h9dvd]
  rw [hk_eq]
  exact orderOf_pow_orderOf_div (x := y) (n := 9) (orderOf_pos y).ne' h9dvd

theorem exists_order_nine_root_sigma1 :
    ∃ y σ : ↥(H z), orderOf y = 9 ∧ y ^ 3 = σ ∧ orderOf σ = 3 ∧
      qH D σ = (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) := by
  classical
  obtain ⟨x9, hx9ord, hx9cube⟩ := exists_order_nine_cube_sigma1
  set y0 : ↥(H z) := lift9 D x9 hx9ord with hy0def
  have hy0ord : orderOf y0 = 9 := orderOf_lift9 D x9 hx9ord
  have h3dvd : 3 ∣ orderOf y0 := by rw [hy0ord]; norm_num
  have hs0ord : orderOf (y0 ^ 3) = 3 := by
    rw [orderOf_pow_of_dvd (x := y0) (n := 3) (by norm_num) h3dvd, hy0ord]
  set k : ℕ := orderOf ((lift D x9 : ↥(H z)) ^ 9) with hk
  have hqy0 : qH D y0 = x9 ^ k := qH_lift9 D x9 hx9ord
  have h9dvd' : 9 ∣ orderOf (lift D x9 : ↥(H z)) := by
    have h := orderOf_map_dvd (qH D) (lift D x9)
    rw [qH_lift, hx9ord] at h
    exact h
  have hk_eq : k = orderOf (lift D x9 : ↥(H z)) / 9 := by
    rw [hk, orderOf_pow_of_dvd (x := (lift D x9 : ↥(H z))) (n := 9) (by norm_num) h9dvd']
  have hk9 : ¬ (3 ∣ k) := by
    intro h3k
    have hmem : (lift D x9 : ↥(H z)) ^ 9 ∈ (J z).subgroupOf (H z) := by
      rw [← ker_qH D, MonoidHom.mem_ker, map_pow, qH_lift]
      simpa [hx9ord] using pow_orderOf_eq_one x9
    have h2 : IsPGroup 2 ((J z).subgroupOf (H z)) := isPGroup_J_subgroupOf (z := z)
    obtain ⟨n, hn⟩ := h2.exists_card_eq
    have hdvdord : orderOf (⟨(lift D x9 : ↥(H z)) ^ 9, hmem⟩ :
        ↥((J z).subgroupOf (H z))) ∣ Nat.card ↥((J z).subgroupOf (H z)) :=
      orderOf_dvd_natCard (⟨(lift D x9 : ↥(H z)) ^ 9, hmem⟩ :
        ↥((J z).subgroupOf (H z)))
    rw [hn] at hdvdord
    rw [Subgroup.orderOf_mk, ← hk] at hdvdord
    have h3dvd : 3 ∣ 2 ^ n := h3k.trans hdvdord
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3dvd
    norm_num at h32
  have hkmod : k % 3 = 1 ∨ k % 3 = 2 := by
    have hlt : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hne : k % 3 ≠ 0 := by
      intro h0
      exact hk9 (Nat.dvd_of_mod_eq_zero h0)
    omega
  have hq3 : (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) ^ 3 = 1 := by
    rw [← hx9cube, ← pow_mul]
    simpa [hx9ord] using pow_orderOf_eq_one x9
  have hqs0 : qH D (y0 ^ 3) = (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) ^ k := by
    rw [map_pow, hqy0, ← pow_mul, Nat.mul_comm k 3, ← hx9cube, ← pow_mul]
  by_cases hcase : qH D (y0 ^ 3) = (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup)
  · exact ⟨y0, y0 ^ 3, hy0ord, rfl, hs0ord, hcase⟩
  ·
    have hk2 : k % 3 = 2 := by
      rcases hkmod with h1 | h2
      · exfalso
        apply hcase
        have hkdec : k = 3 * (k / 3) + 1 := by omega
        rw [hqs0, hkdec, pow_add, pow_mul, hq3, one_pow, one_mul, pow_one]
      · exact h2
    have hqs0inv : qH D ((y0 ^ 3)⁻¹) = (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) := by
      rw [map_inv, hqs0]
      have hkdec : k = 3 * (k / 3) + 2 := by omega
      rw [hkdec, pow_add, pow_mul, hq3, one_pow, one_mul]
      have h3' : (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) ^ 3 = 1 := hq3
      have hinv : ((⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) ^ 2)⁻¹ =
          (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) := by
        apply inv_eq_of_mul_eq_one_left
        calc (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) *
              (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) ^ 2
            = (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) ^ (1 + 2) := by
              rw [pow_add, pow_one]
          _ = (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) ^ 3 := by norm_num
          _ = 1 := h3'
      exact hinv
    refine ⟨y0⁻¹, (y0 ^ 3)⁻¹, ?_, ?_, ?_, hqs0inv⟩
    · rw [orderOf_inv, hy0ord]
    · group
    · rw [orderOf_inv, hs0ord]

end CFSG.RankThree.GF2n.Parrott
