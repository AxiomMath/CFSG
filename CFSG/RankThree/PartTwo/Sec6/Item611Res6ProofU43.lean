module

public import CFSG.RankThree.PartTwo.Sec6.Item611Res6ProofU43RepA
public import CFSG.RankThree.PartTwo.Sec6.Item611Res6ProofU43RepB
public import CFSG.RankThree.PartTwo.Sec6.Item611Res6ProofU43RepC
public import CFSG.RankThree.PartTwo.Sec6.Item611Res6ProofU43RepD
public import CFSG.RankThree.PartTwo.Sec6.Item611Res6ProofU43T2
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemU43
public import CFSG.RankThree.PartTwo.Sec6.Item611Res5ProofL43

public section

namespace CFSG.RankThree.PartTwo.Sec6.Res611Res6.U43P

open CFSG.LieType.Multipliers.U43

theorem factorization_three_card_X₀ : (Nat.card X₀).factorization 3 = 6 := by
  have h : (3265920 : ℕ) = 3 ^ 6 * 4480 := by norm_num
  rw [card_X₀, h, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three]
  simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 3 ∣ 4480 by norm_num)]

theorem factorization_two_card_X₀ : (Nat.card X₀).factorization 2 = 7 := by
  have h : (3265920 : ℕ) = 2 ^ 7 * 25515 := by norm_num
  rw [card_X₀, h, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two]
  simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 25515 by norm_num)]

@[expose] def ClassCond (c : ℕ) : Prop :=
  ∃ a b : ℕ, c = 2 ^ a * 3 ^ b ∧ (a ≤ 1 ∧ 3 ≤ b ∨ a = 2 ∧ 4 ≤ b ∨ a = 3 ∧ 5 ≤ b)

theorem card_centralizer_dvd (g : X₀) :
    Nat.card (Subgroup.centralizer ({g} : Set X₀)) ∣ 3265920 := by
  rw [← card_X₀]
  exact Subgroup.card_subgroup_dvd_card _

section Certs


theorem pow_dvd_card_of_le_p3 {Q : Subgroup X₀} (hQ : Q ≤ p3.H) {e : ℕ}
    (h : 3 ^ e ≤ Nat.card Q) : 3 ^ e ∣ Nat.card Q := by
  have hdvd : Nat.card Q ∣ 3 ^ 6 := by
    have := Subgroup.card_dvd_of_le hQ
    rwa [card_p3, show (729 : ℕ) = 3 ^ 6 by norm_num] at this
  obtain ⟨k, hk, hQk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  rw [hQk] at h ⊢
  exact Nat.pow_dvd_pow 3 ((Nat.pow_le_pow_iff_right (by norm_num)).mp h)

theorem classCond_A : ClassCond (Nat.card (Subgroup.centralizer ({ev (repW 1)} : Set X₀))) := by
  set c := Nat.card (Subgroup.centralizer ({ev (repW 1)} : Set X₀))
  have h729 : 729 ∣ c := by
    have := Subgroup.card_dvd_of_le (p3.H_le_centralizer p3_chkComGens_A)
    rwa [card_p3] at this
  have h2 : 2 ∣ c := by
    have := Subgroup.orderOf_dvd_natCard _ (mem_centralizer_of_chkCom chkCom_uA)
    rwa [orderOf_ev_of_chkInvolution chkInvolution_uA] at this
  have hle : c * 560 ≤ 3265920 := by
    have := card_centralizer_mul_le_of_conjList chkConjList_A
    rwa [length_conjA, card_X₀] at this
  have hd : c ∣ 3265920 := card_centralizer_dvd _
  have h1458 : 1458 ∣ c := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h729 h2
  obtain ⟨m, hm⟩ := h1458
  rw [hm] at hle hd
  have hm4 : m ≤ 4 := by omega
  interval_cases m
  · omega
  · exact ⟨1, 6, by rw [hm]; norm_num, Or.inl ⟨le_rfl, by norm_num⟩⟩
  · exact ⟨2, 6, by rw [hm]; norm_num, Or.inr (Or.inl ⟨rfl, by norm_num⟩)⟩
  · norm_num at hd
  · exact ⟨3, 6, by rw [hm]; norm_num, Or.inr (Or.inr ⟨rfl, by norm_num⟩)⟩

theorem classCond_of_fix {r : ℕ} {FL ωs hs ks : List ℕ} {e : ℕ} (he : e = 4 ∨ e = 5)
    (hfix : chkFixData r FL ωs hs = true) (hks : p3.chkComIdx r ks = true)
    (hlen : 3 ^ e ≤ ks.length) (hNM : 3265920 < 3 ^ e * 5 * (ωs.length * hs.length)) :
    ClassCond (Nat.card (Subgroup.centralizer ({ev r} : Set X₀))) := by
  set c := Nat.card (Subgroup.centralizer ({ev r} : Set X₀))
  have hle : c * (ωs.length * hs.length) ≤ 3265920 := by
    have := card_centralizer_mul_le_of_fixData hfix
    rwa [card_X₀] at this
  have h3 : 3 ^ e ∣ c := by
    have hQ := p3.le_card_inf_centralizer p3_chkBase p3_chkTree p3_chkSorted hks
    have h1 := pow_dvd_card_of_le_p3 (Q := p3.H ⊓ Subgroup.centralizer ({ev r} : Set X₀))
      inf_le_left (hlen.trans hQ)
    exact h1.trans (Subgroup.card_dvd_of_le inf_le_right)
  have hd : c ∣ 3265920 := card_centralizer_dvd _
  obtain ⟨m, hm⟩ := h3
  have hm4 : m ≤ 4 := by
    by_contra hlt
    push Not at hlt
    have : 3 ^ e * 5 * (ωs.length * hs.length) ≤ c * (ωs.length * hs.length) :=
      Nat.mul_le_mul_right _ (by rw [hm]; exact Nat.mul_le_mul_left _ hlt)
    omega
  rcases he with rfl | rfl <;> rw [hm] at hd <;> interval_cases m <;> norm_num at hd
  · exact ⟨0, 4, by rw [hm]; norm_num, Or.inl ⟨by norm_num, by norm_num⟩⟩
  · exact ⟨1, 4, by rw [hm]; norm_num, Or.inl ⟨le_rfl, by norm_num⟩⟩
  · exact ⟨0, 5, by rw [hm]; norm_num, Or.inl ⟨by norm_num, by norm_num⟩⟩
  · exact ⟨2, 4, by rw [hm]; norm_num, Or.inr (Or.inl ⟨rfl, le_rfl⟩)⟩
  · exact ⟨0, 5, by rw [hm]; norm_num, Or.inl ⟨by norm_num, by norm_num⟩⟩
  · exact ⟨1, 5, by rw [hm]; norm_num, Or.inl ⟨le_rfl, by norm_num⟩⟩
  · exact ⟨0, 6, by rw [hm]; norm_num, Or.inl ⟨by norm_num, by norm_num⟩⟩
  · exact ⟨2, 5, by rw [hm]; norm_num, Or.inr (Or.inl ⟨rfl, by norm_num⟩)⟩

theorem classCond_repW {l : ℕ} (h1 : 1 ≤ l) (h4 : l ≤ 4) :
    ClassCond (Nat.card (Subgroup.centralizer ({ev (repW l)} : Set X₀))) := by
  interval_cases l
  · exact classCond_A
  · obtain ⟨h1, h2, h3⟩ := lengths_B
    exact classCond_of_fix (Or.inr rfl) chkFixData_B p3_chkComIdx_B (by rw [h3]; norm_num)
      (by rw [h1, h2]; norm_num)
  · obtain ⟨h1, h2, h3⟩ := lengths_C
    exact classCond_of_fix (Or.inr rfl) chkFixData_C p3_chkComIdx_C (by rw [h3]; norm_num)
      (by rw [h1, h2]; norm_num)
  · obtain ⟨h1, h2, h3⟩ := lengths_D
    exact classCond_of_fix (Or.inl rfl) chkFixData_D p3_chkComIdx_D (by rw [h3]; norm_num)
      (by rw [h1, h2]; norm_num)

theorem classCond_of_orderOf_eq_three {z : X₀} (hz : orderOf z = 3) :
    ClassCond (Nat.card (Subgroup.centralizer ({z} : Set X₀))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz3 : z ^ 3 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz] at this
  obtain ⟨g, hg⟩ := Res611Res6.exists_conj_mem_of_card
    (P := p3.H) (by rw [card_p3, factorization_three_card_X₀]; norm_num) hz3
  obtain ⟨k, hk, hke⟩ := p3.exists_eq_elem p3_chkBase p3_chkTree p3_chkClosed (by decide) hg
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [p3.elem_zero] at hke
    have : z = 1 := by
      have := congrArg (fun y => g * y * g⁻¹) hke
      simpa [mul_assoc] using this
    rw [this, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hk3 : p3.elem k ^ 3 = 1 := by
    have e3 : (g⁻¹ * z * g) ^ 3 = g⁻¹ * z ^ 3 * g := by
      have := conj_pow (a := g⁻¹) (b := z) (i := 3)
      rwa [inv_inv] at this
    rw [← hke, e3, hz3]
    group
  obtain ⟨l, hl1, hl4, c, hc⟩ := p3_exists_conj_rep hk hk0 hk3
  have e : (c * g⁻¹) * z * (c * g⁻¹)⁻¹ = ev (repW l) := by
    rw [← hc, ← hke]
    group
  have := classCond_repW hl1 hl4
  rwa [← e, Res611Res6.card_centralizer_conj] at this

theorem not_dvd_card_centralizer_x :
    ¬ 27 ∣ Nat.card (Subgroup.centralizer ({ev 1} : Set X₀)) := by
  set c := Nat.card (Subgroup.centralizer ({ev 1} : Set X₀))
  have h128 : 128 ∣ c := by
    have := Subgroup.card_dvd_of_le (t2.H_le_centralizer t2_chkComGens)
    rwa [card_t2] at this
  have hle : c * 1000 ≤ 3265920 := by
    have := card_centralizer_mul_le_of_conjList chkConjList_x
    rwa [length_conjX, card_X₀] at this
  intro h27
  have h3456 : 3456 ∣ c := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h128 h27
  obtain ⟨m, hm⟩ := h3456
  have hc0 : 0 < c := Nat.card_pos
  rcases m with _ | m
  · omega
  · omega

theorem not_dvd_card_centralizer_of_orderOf_eq_two {t : X₀} (ht : orderOf t = 2) :
    ¬ 27 ∣ Nat.card (Subgroup.centralizer ({t} : Set X₀)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht] at this
  obtain ⟨g, hg⟩ := Res611Res6.exists_conj_mem_of_card
    (P := t2.H) (by rw [card_t2, factorization_two_card_X₀]; norm_num) ht2
  obtain ⟨k, hk, hke⟩ := t2.exists_eq_elem t2_chkBase t2_chkTree t2_chkClosed (by decide) hg
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [t2.elem_zero] at hke
    have : t = 1 := by
      have := congrArg (fun y => g * y * g⁻¹) hke
      simpa [mul_assoc] using this
    rw [this, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hk2 : t2.elem k ^ 2 = 1 := by
    have e2 : (g⁻¹ * t * g) ^ 2 = g⁻¹ * t ^ 2 * g := by
      have := conj_pow (a := g⁻¹) (b := t) (i := 2)
      rwa [inv_inv] at this
    rw [← hke, e2, ht2]
    group
  obtain ⟨hl1, hl, c, hc⟩ := t2.exists_conj_rep t2_chkBase t2_chkTree t2_chkClass (by norm_num)
    hk hk0 hk2
  have hl1' : lk t2Cls k = 1 := by simp at hl; omega
  rw [hl1'] at hc
  have e : (c * g⁻¹) * t * (c * g⁻¹)⁻¹ = ev 1 := by
    rw [show ([1] : List ℕ).getD (1 - 1) 0 = 1 from rfl] at hc
    rw [← hc, ← hke]
    group
  rw [← Res611Res6.card_centralizer_conj (c * g⁻¹) t, e]
  exact not_dvd_card_centralizer_x

end Certs

end CFSG.RankThree.PartTwo.Sec6.Res611Res6.U43P

namespace CFSG.RankThree.PartTwo.Sec6

open Res611Res6.U43P Res611Res5.L43

theorem kU43ThreeClassData_holds : KU43ThreeClassData := by
  set e := Sec4.Item434RemU43.projSUEquivUX
  refine ⟨fun z hz => ?_, fun t ht => ?_⟩
  · have hz' : orderOf (e z) = 3 := by rw [MulEquiv.orderOf_eq, hz]
    rw [← card_centralizer_mulEquiv e z]
    obtain ⟨a, b, h, hab⟩ := classCond_of_orderOf_eq_three hz'
    exact ⟨a, b, h, hab⟩
  · have ht' : orderOf (e t) = 2 := by rw [MulEquiv.orderOf_eq, ht]
    rw [← card_centralizer_mulEquiv e t]
    exact not_dvd_card_centralizer_of_orderOf_eq_two ht'

theorem kCentCharThreeU43_holds : KCentCharThreeU43 :=
  kCentCharThreeU43_of kU43ThreeClassData_holds

end CFSG.RankThree.PartTwo.Sec6
