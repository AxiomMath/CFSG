module

import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeOCSetup
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeOCL34Model
import CFSG.Adapters.LinearCatalogStated
import CFSG.Quasithin.Vol2.Ch12Sec6P31LieI
import CFSG.GH74.GLS.SP.GenOrder
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.ThreeOC

open CFSG.ComponentClassification.PSL3Four
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem pow_two_mem_of_pow_mem {G : Type*} [Group G] {H : Subgroup G}
    (hH : ∀ β : G, β ^ 4 ∈ H → β ^ 2 ∈ H) (β : G) (j : ℕ) (h : β ^ (2 ^ (j + 1)) ∈ H) :
    β ^ 2 ∈ H := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    apply ih
    have h4 : (β ^ 2 ^ j) ^ 4 ∈ H := by
      rwa [← pow_mul, show 2 ^ j * 4 = 2 ^ (j + 1 + 1) by ring]
    have h2 := hH _ h4
    rwa [← pow_mul, show 2 ^ j * 2 = 2 ^ (j + 1) by ring] at h2

variable {X : Type} [Group X] [Finite X]

theorem oc_l34Row {N K Q T : Subgroup X} [K.Normal]
    (hKC : Subgroup.centralizer (K : Set X) = ⊥)
    (hI : IsoLie ↥K (.A 2 ⟨2, 2, Nat.prime_two, by norm_num⟩)) (hQN : Q ≤ N) (hQK : Q ≤ K)
    (hnorm : N ≤ Subgroup.normalizer (Q : Set X))
    (hNK : N ⊓ K = K ⊓ Subgroup.normalizer (Q : Set X)) (hidx : ∃ k : ℕ, K.index = 2 ^ k)
    (hQ9 : Nat.card ↥Q = 9) (hT : T ≤ K ⊓ Subgroup.normalizer (Q : Set X)) (hQT : Q ⊓ T = ⊥)
    (hsup : Q ⊔ T = K ⊓ Subgroup.normalizer (Q : Set X))
    (hT8 : Nonempty (↥T ≃* QuaternionGroup 2)) :
    Nat.card ↥(CFSG.pPrimeCore 3 ↥N) ≤ 2 ∧ CentralizerHasPElementOutside 3 N := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hidx
  obtain ⟨hv, ⟨e⟩⟩ := hI
  have hPSL : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥K .PSL 3 2 2 :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
  obtain ⟨θ⟩ := nonempty_equiv_of_stated ↥K hPSL
  obtain ⟨ψ, hψi, hψS, hψc⟩ := exists_embedding_R hKC θ
  have hQ3 : IsPGroup 3 ↥Q := IsPGroup.of_card (n := 2) (by rw [hQ9]; norm_num)
  have hT8' : Nat.card ↥T = 8 := by
    obtain ⟨f⟩ := hT8
    rw [Nat.card_congr f.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hΓ : Nat.card ↥(N ⊓ K) = 2 ^ 3 * 3 ^ 2 := by
    rw [hNK, ← hsup, CFSG.GH74.GLS.SP.card_sup_of_inf_eq_bot (hT.trans inf_le_right) hQT, hQ9,
      hT8']
    norm_num
  refine ⟨?_, centralizerHasPElementOutside_of_pow_eq_one Nat.prime_three (k + 3) 2
    fun y hy => ?_⟩
  swap
  · have h := pow_index_mul_card_eq_one (K := K) hy
    rwa [hk, hΓ, ← mul_assoc, ← pow_add] at h
  set Y := CFSG.pPrimeCore 3 ↥N with hY
  have hcopY : Nat.Coprime (Nat.card ↥Y) 3 := (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥N)).symm
  have h2el : ∀ y ∈ Y, y ^ (2 ^ (k + 3)) = 1 := by
    intro y hy
    have hu : ((y ^ 2 ^ k : ↥N) : X) ∈ N ⊓ K :=
      ⟨(y ^ 2 ^ k).2, by rw [Subgroup.coe_pow, ← hk]; exact K.pow_index_mem _⟩
    have h72 : ((y ^ 2 ^ k : ↥N) : X) ^ (2 ^ 3 * 3 ^ 2) = 1 := by
      rw [← hΓ]
      exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨_, hu⟩ : ↥(N ⊓ K))))
    have hY' := orderOf_dvd_natCard (⟨_, Y.pow_mem hy (2 ^ k)⟩ : ↥Y)
    rw [Subgroup.orderOf_mk] at hY'
    have hd : orderOf (y ^ 2 ^ k) ∣ 2 ^ 3 :=
      ((hcopY.coprime_dvd_left hY').pow_right 2).dvd_of_dvd_mul_right
        (orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h72)))
    rw [pow_add, pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.1 hd
  have hsq : ∀ y ∈ Y, ((y : ↥N) : X) ^ 2 ∈ K := by
    intro y hy
    have hβ : (MulAut.conjNormal ((y : ↥N) : X) : MulAut ↥K) ^ 2 ^ (k + 2 + 1) ∈
        (MulAut.conj : ↥K →* MulAut ↥K).range := by
      rw [← map_pow, ← Subgroup.coe_pow, h2el y hy, Subgroup.coe_one, map_one]
      exact Subgroup.one_mem _
    obtain ⟨c, hc⟩ := pow_two_mem_of_pow_mem
      (CFSG.Quasithin.H13.S126P31.psl34_out_exp hPSL) _ (k + 2) hβ
    rw [← map_pow] at hc
    have hcen : (c : X)⁻¹ * ((y : ↥N) : X) ^ 2 ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have h := congrArg (fun f : MulAut ↥K => ((f ⟨n, hn⟩ : ↥K) : X)) hc
      simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h
      calc n * ((c : X)⁻¹ * ((y : ↥N) : X) ^ 2) =
          (c : X)⁻¹ * ((c : X) * n * (c : X)⁻¹) * ((y : ↥N) : X) ^ 2 := by group
        _ = (c : X)⁻¹ * (((y : ↥N) : X) ^ 2 * n * (((y : ↥N) : X) ^ 2)⁻¹) *
            ((y : ↥N) : X) ^ 2 := by rw [h]
        _ = (c : X)⁻¹ * ((y : ↥N) : X) ^ 2 * n := by group
    rw [hKC, Subgroup.mem_bot, inv_mul_eq_one] at hcen
    rw [← hcen]
    exact c.2
  have hinv : ∀ y ∈ Y, orderOf y = 2 →
      ((ψ ((y : ↥N) : X) : ↥R) : Equiv.Perm (Fin 42)) ∉ S ∧
        ((ψ ((y : ↥N) : X) : ↥R) : Equiv.Perm (Fin 42)) * r₄⁻¹ ∈ S := by
    intro y hy hy2
    refine not_mem_S_and_mul_r₄_inv_mem_S ?_ (nine_dvd_card_fixed θ (hψc ((y : ↥N) : X)) hQK hQ9
      fun q hq => commute_of_mem_pPrimeCore hQN hQ3 hnorm hy hq)
    rw [orderOf_injective ψ hψi, Subgroup.orderOf_coe, hy2]
  have hYK : ∀ y ∈ Y, ((y : ↥N) : X) ∈ K → y = 1 := by
    intro y hy hyK
    by_contra hy1
    obtain ⟨i, hi, hoi⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one (h2el y hy))
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact hy1 (orderOf_eq_one_iff.1 (by simpa using hoi))
    have hdvd : 2 ^ (i - 1) ∣ orderOf y := by rw [hoi]; exact pow_dvd_pow 2 (Nat.sub_le i 1)
    have hz2 : orderOf (y ^ 2 ^ (i - 1)) = 2 := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hoi,
        Nat.pow_div (Nat.sub_le i 1) two_pos, Nat.sub_sub_self (Nat.one_le_iff_ne_zero.2 hi0),
        pow_one]
    refine (hinv _ (Y.pow_mem hy _) hz2).1 ((hψS _).2 ?_)
    rw [Subgroup.coe_pow]
    exact K.pow_mem hyK _
  have hsq1 : ∀ y ∈ Y, y ^ 2 = 1 := fun y hy =>
    hYK _ (Y.pow_mem hy 2) (by rw [Subgroup.coe_pow]; exact hsq y hy)
  have huniq : ∀ a ∈ Y, ∀ b ∈ Y, a ≠ 1 → b ≠ 1 → a = b := by
    intro a ha b hb ha1 hb1
    have hab := S.mul_mem (hinv a ha (orderOf_eq_prime (hsq1 a ha) ha1)).2
      (S.inv_mem (hinv b hb (orderOf_eq_prime (hsq1 b hb) hb1)).2)
    rw [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left] at hab
    have hab' : ((ψ ((a * b⁻¹ : ↥N) : X) : ↥R) : Equiv.Perm (Fin 42)) ∈ S := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv] using hab
    exact mul_inv_eq_one.1 (hYK _ (Y.mul_mem ha (Y.inv_mem hb)) ((hψS _).1 hab'))
  have hf : Function.Injective (fun y : ↥Y => decide (y = 1)) := by
    intro a b h
    by_cases ha : a = 1 <;> by_cases hb : b = 1
    · rw [ha, hb]
    · simp [ha, hb] at h
    · simp [ha, hb] at h
    · exact Subtype.ext (huniq _ a.2 _ b.2 (fun h' => ha (Subtype.ext h'))
        (fun h' => hb (Subtype.ext h')))
  have h2 := Nat.card_le_card_of_injective _ hf
  rwa [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h2

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.ThreeOC
