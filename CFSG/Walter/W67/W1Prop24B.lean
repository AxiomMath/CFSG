module

public import CFSG.Walter.W67.W1Prop24A
public import CFSG.Walter.W67.Transport

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_sup_mul_card_inf_of_normal (A B : Subgroup G) [A.Normal] :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  have h1 := Subgroup.relIndex_mul_card (H := A) (K := A ⊔ B)
  rw [Subgroup.relIndex_sup_left, inf_eq_left.mpr le_sup_left] at h1
  have h2 := Subgroup.relIndex_mul_card (H := A) (K := B)
  rw [← h1, ← h2]
  ring

theorem Hyp.nonempty_iso_three (h : Hyp G) (hq : h.q = 3) :
    Nonempty (h.K ≃* PSL(2, GaloisField 3 1)) := by
  have key : ∀ {p f p' f' : ℕ} [Fact p.Prime] [Fact p'.Prime], p = p' → f = f' →
      Nonempty (h.K ≃* PSL(2, GaloisField p f)) →
        Nonempty (h.K ≃* PSL(2, GaloisField p' f')) := by
    intro p f p' f' _ _ hp hf e
    subst hp hf
    exact e
  exact key (h.p_eq_three hq) (h.f_eq_one hq) ⟨h.iso⟩

theorem odd_card_pPrimeCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.pPrimeCore 2 X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := CFSG.pPrimeCore_coprime_card (p := 2) (G := X)
  rwa [Nat.coprime_two_left] at this

namespace Frame

variable {h : Hyp G} (fr : Frame h)

theorem K_le_normalizer_S_of_three
    (hq : h.q = 3) :
    h.K ≤ Subgroup.normalizer ((fr.S : Subgroup G) : Set G) :=
  h.K_le_H.trans (fr.H_le_normalizer_S_of_three hq)

structure YData (Y : Subgroup G) : Prop where
  normal : Y.Normal
  inf_eq_bot : Y ⊓ CFSG.pPrimeCore 2 G = ⊥
  le_centralizer : Y ≤ Subgroup.centralizer (CFSG.pPrimeCore 2 G : Set G)
  S_le : (fr.S : Subgroup G) ≤ Y
  not_three_dvd :
    ¬ 3 ∣ Nat.card (Y ⊓ Subgroup.normalizer ((fr.S : Subgroup G) : Set G) : Subgroup G)

namespace YData

variable {fr} {Y : Subgroup G} (hY : fr.YData Y) (hq : h.q = 3)
  (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
include hY hq

theorem not_three_dvd_card_inf_K :
    ¬ 3 ∣ Nat.card (Y ⊓ h.K : Subgroup G) := fun h3 =>
  hY.not_three_dvd (h3.trans (Subgroup.card_dvd_of_le
    (inf_le_inf_left _ (fr.K_le_normalizer_S_of_three hq))))

include hidx

theorem K_inf_sup_le :
    h.K ⊓ (Y ⊔ CFSG.pPrimeCore 2 G) ≤ Y := by
  have := hY.normal
  set O := CFSG.pPrimeCore 2 G
  have hO : Odd (Nat.card O) := odd_card_pPrimeCore G
  rintro x ⟨hxK, hxYO⟩
  have hON : O ≤ Subgroup.normalizer (Y : Set G) := by
    rw [Subgroup.normalizer_eq_top]; exact le_top
  obtain ⟨y, hy, o, ho, rfl⟩ := (mem_sup_iff_of_le_normalizer hON).mp hxYO
  have hoC : o ∈ fr.CS := fr.pPrimeCore_le_CS_of_three hq hidx ho
  have hoN : o ∈ Subgroup.normalizer ((fr.S : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _ hoC
  have hyo : Commute y o := (Subgroup.mem_centralizer_iff.mp (hY.le_centralizer hy) o ho).symm
  have hyN : y ∈ Y ⊓ Subgroup.normalizer ((fr.S : Subgroup G) : Set G) := by
    refine ⟨hy, ?_⟩
    have := mul_mem (fr.K_le_normalizer_S_of_three hq hxK) (inv_mem hoN)
    rwa [mul_inv_cancel_right] at this
  have h12 : (y * o) ^ 12 = 1 := by
    have := Subgroup.orderOf_dvd_natCard h.K hxK
    rw [h.card_K_of_three hq] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this
  rw [hyo.mul_pow] at h12
  have hy12 : y ^ 12 = 1 := by
    have hmem : y ^ 12 ∈ Y ⊓ O := by
      refine ⟨pow_mem hy 12, ?_⟩
      rw [eq_inv_of_mul_eq_one_left h12]
      exact O.inv_mem (O.pow_mem ho 12)
    rw [hY.inf_eq_bot] at hmem
    exact hmem
  have ho12 : o ^ 12 = 1 := by
    rw [hy12, one_mul] at h12
    exact h12
  have hy4 : y ^ 4 = 1 := by
    have h1 : orderOf y ∣ 4 * 3 := orderOf_dvd_of_pow_eq_one hy12
    have h2 : ¬ 3 ∣ orderOf y := fun h3 =>
      hY.not_three_dvd (h3.trans (Subgroup.orderOf_dvd_natCard _ hyN))
    have h3 : Nat.Coprime (orderOf y) 3 :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h2)
    exact orderOf_dvd_iff_pow_eq_one.mp (h3.dvd_of_dvd_mul_right h1)
  have ho3 : o ^ 3 = 1 := by
    have h1 : orderOf o ∣ 4 * 3 := orderOf_dvd_of_pow_eq_one ho12
    have h2 : Odd (orderOf o) := Odd.of_dvd_nat hO (Subgroup.orderOf_dvd_natCard _ ho)
    have h3 : Nat.Coprime (orderOf o) 4 := by
      rw [show (4 : ℕ) = 2 ^ 2 by rfl]
      exact Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr h2)
    exact orderOf_dvd_iff_pow_eq_one.mp (h3.dvd_of_dvd_mul_left h1)
  have hx4 : y ^ 4 * o ^ 4 = o := by
    rw [hy4, one_mul, show (4 : ℕ) = 3 + 1 by rfl, pow_succ, ho3, one_mul]
  have hoK : o ∈ h.K := by
    rw [← hx4, ← hyo.mul_pow]
    exact pow_mem hxK 4
  have ho1 : o = 1 := by
    have : o ∈ h.K ⊓ O := ⟨hoK, ho⟩
    rw [h.K_inf_eq_bot_of_odd O hO] at this
    exact this
  rw [ho1, mul_one]
  exact hy

omit hidx in
theorem inf_K_eq_T : Y ⊓ h.K = fr.T := by
  have hTle : fr.T ≤ Y ⊓ h.K := le_inf (fr.T_le_S.trans hY.S_le) fr.T_le_K
  refine (Subgroup.eq_of_le_of_card_ge hTle ?_).symm
  rw [fr.card_T]
  have hdvd : Nat.card (Y ⊓ h.K : Subgroup G) ∣ 4 * 3 := by
    rw [show 4 * 3 = 12 by rfl, ← h.card_K_of_three hq]
    exact Subgroup.card_dvd_of_le inf_le_right
  have h4 : 4 ∣ Nat.card (Y ⊓ h.K : Subgroup G) := by
    rw [← fr.card_T]
    exact Subgroup.card_dvd_of_le hTle
  have hn3 := hY.not_three_dvd_card_inf_K hq
  obtain ⟨m, hm⟩ := h4
  rw [hm] at hdvd hn3 ⊢
  have hm3 : m ∣ 3 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
  rcases (Nat.dvd_prime Nat.prime_three).mp hm3 with rfl | rfl
  · omega
  · exact absurd (dvd_mul_left 3 4) hn3

omit hidx in
theorem card_sup_K :
    Nat.card (Y ⊔ h.K : Subgroup G) = 3 * Nat.card Y := by
  have := hY.normal
  have h1 := card_sup_mul_card_inf_of_normal Y h.K
  rw [hY.inf_K_eq_T hq, fr.card_T, h.card_K_of_three hq] at h1
  omega

theorem sup_K_inf_eq_bot :
    (Y ⊔ h.K) ⊓ CFSG.pPrimeCore 2 G = ⊥ := by
  have := hY.normal
  rw [eq_bot_iff]
  rintro z ⟨hzL, hzO⟩
  have hKN : h.K ≤ Subgroup.normalizer (Y : Set G) := by
    rw [Subgroup.normalizer_eq_top]; exact le_top
  obtain ⟨y, hy, k, hk, rfl⟩ := (mem_sup_iff_of_le_normalizer hKN).mp hzL
  have hkYO : k ∈ Y ⊔ CFSG.pPrimeCore 2 G := by
    have : k = y⁻¹ * (y * k) := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left (inv_mem hy)) (Subgroup.mem_sup_right hzO)
  have hkY := hY.K_inf_sup_le hq hidx ⟨hk, hkYO⟩
  have : y * k ∈ Y ⊓ CFSG.pPrimeCore 2 G := ⟨mul_mem hy hkY, hzO⟩
  rw [hY.inf_eq_bot] at this
  exact this

theorem sup_K_le_centralizer :
    Y ⊔ h.K ≤ Subgroup.centralizer (CFSG.pPrimeCore 2 G : Set G) :=
  sup_le hY.le_centralizer
    (Subgroup.le_centralizer_iff.mp (fr.pPrimeCore_le_centralizer_K_of_three hq hidx))

theorem assembly
    (hEO : fr.E ≤ CFSG.pPrimeCore 2 G)
    (hcard : Nat.card G ≤ 3 * Nat.card Y * Nat.card (CFSG.pPrimeCore 2 G)) :
    (Y ⊔ h.K).Normal ∧ (Y ⊔ h.K) ⊔ CFSG.pPrimeCore 2 G = ⊤ ∧
      (Y ⊔ h.K) ⊓ CFSG.pPrimeCore 2 G = ⊥ ∧
      CFSG.pPrimeCore 2 G ≤ Subgroup.centralizer ((Y ⊔ h.K : Subgroup G) : Set G) ∧
      (Y ⊔ h.K) ⊓ h.H = Subgroup.zpowers h.J ⊔ h.K := by
  set O := CFSG.pPrimeCore 2 G
  set L := Y ⊔ h.K
  have hLO : L ⊓ O = ⊥ := hY.sup_K_inf_eq_bot hq hidx
  have hLC : L ≤ Subgroup.centralizer (O : Set G) := hY.sup_K_le_centralizer hq hidx
  have hOC : O ≤ Subgroup.centralizer (L : Set G) := Subgroup.le_centralizer_iff.mp hLC
  have htop : L ⊔ O = ⊤ := by
    apply Subgroup.eq_top_of_le_card
    have hc : ∀ x ∈ L, ∀ y ∈ O, x * y = y * x := fun x hx y hy =>
      (Subgroup.mem_centralizer_iff.mp (hLC hx) y hy).symm
    obtain ⟨h1, -⟩ := card_sup_mul_card_inf_of_commute L O hc
    rw [hLO, Subgroup.card_bot, mul_one, hY.card_sup_K hq] at h1
    rw [h1]
    exact hcard
  have hON : O ≤ Subgroup.normalizer (L : Set G) :=
    hOC.trans (Subgroup.centralizer_le_normalizer _)
  refine ⟨⟨fun l hl g => ?_⟩, htop, hLO, hOC, ?_⟩
  · obtain ⟨l', hl', o, ho, rfl⟩ := (mem_sup_iff_of_le_normalizer hON).mp
      (htop ▸ Subgroup.mem_top g)
    have hol : o * l * o⁻¹ = l := by
      rw [(Subgroup.mem_centralizer_iff.mp (hOC ho) l hl).symm, mul_inv_cancel_right]
    rw [show l' * o * l * (l' * o)⁻¹ = l' * (o * l * o⁻¹) * l'⁻¹ by group, hol]
    exact mul_mem (mul_mem hl' hl) (inv_mem hl')
  · apply le_antisymm
    · rintro x ⟨hxL, hxH⟩
      have hdp := fr.isInternalDirectProduct_H
      rw [← hdp.1] at hxH
      have hKEN : h.K ⊔ fr.E ≤
          Subgroup.normalizer ((Subgroup.zpowers h.J : Subgroup G) : Set G) := by
        intro m hm
        refine JT.mem_normalizer_of_conj_mem fun j hj => ?_
        rcases eq_one_or_eq_of_mem_zpowers h.orderOf_J hj with rfl | rfl
        · rw [mul_one, mul_inv_cancel]; exact one_mem _
        · have hc := Subgroup.mem_centralizer_iff.mp (hdp.2.2 (Subgroup.mem_zpowers h.J)) m hm
          rw [hc, mul_inv_cancel_right]
          exact Subgroup.mem_zpowers _
      obtain ⟨j, hj, m, hm, rfl⟩ := (mem_sup_iff_of_le_normalizer hKEN).mp hxH
      obtain ⟨k, hk, e, he, rfl⟩ := (mem_sup_iff_of_le_normalizer fr.E_le_normalizer_K).mp hm
      have hjL : j ∈ L := by
        rcases eq_one_or_eq_of_mem_zpowers h.orderOf_J hj with rfl | rfl
        · exact one_mem _
        · exact Subgroup.mem_sup_left (hY.S_le fr.J_mem)
      have heL : e ∈ L := by
        have : e = (j * k)⁻¹ * (j * (k * e)) := by group
        rw [this]
        exact mul_mem (inv_mem (mul_mem hjL (Subgroup.mem_sup_right hk))) hxL
      have he1 : e = 1 := by
        have : e ∈ L ⊓ O := ⟨heL, hEO he⟩
        rw [hLO] at this
        exact this
      rw [he1, mul_one]
      exact mul_mem (Subgroup.mem_sup_left hj) (Subgroup.mem_sup_right hk)
    · exact sup_le ((Subgroup.zpowers_le).mpr ⟨Subgroup.mem_sup_left (hY.S_le fr.J_mem),
        h.J_mem_H⟩) (le_inf le_sup_right h.K_le_H)

end YData

end Frame

end CFSG.Walter.W67
