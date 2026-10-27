module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2SQA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL2S

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem mul_injective_of_inf_eq_bot {P K K' : Subgroup D} (hK : K ≤ P) (hK' : K' ≤ P)
    (hint : K ⊓ K' = ⊥) :
    Function.Injective (fun p : ↥K × ↥K' =>
      (⟨(p.1 : D) * p.2, P.mul_mem (hK p.1.2) (hK' p.2.2)⟩ : ↥P)) := by
  rintro ⟨⟨k₁, hk₁⟩, ⟨k₁', hk₁'⟩⟩ ⟨⟨k₂, hk₂⟩, ⟨k₂', hk₂'⟩⟩ heq
  have h0 : k₁ * k₁' = k₂ * k₂' := congrArg Subtype.val heq
  have h1 : k₂⁻¹ * k₁ = k₂' * k₁'⁻¹ := by
    calc k₂⁻¹ * k₁ = k₂⁻¹ * (k₁ * k₁') * k₁'⁻¹ := by group
      _ = k₂⁻¹ * (k₂ * k₂') * k₁'⁻¹ := by rw [h0]
      _ = k₂' * k₁'⁻¹ := by group
  have h2 : k₂⁻¹ * k₁ ∈ K ⊓ K' :=
    ⟨K.mul_mem (K.inv_mem hk₂) hk₁, h1 ▸ K'.mul_mem hk₂' (K'.inv_mem hk₁')⟩
  rw [hint, Subgroup.mem_bot] at h2
  have h3 : k₂ = k₁ := inv_mul_eq_one.mp h2
  have h4 : k₂' * k₁'⁻¹ = 1 := by rw [← h1, h2]
  have h5 : k₂' = k₁' := mul_inv_eq_one.mp h4
  subst h3
  subst h5
  rfl

theorem card_mul_le_of_inf_eq_bot [Finite D] {P K K' : Subgroup D} (hK : K ≤ P) (hK' : K' ≤ P)
    (hint : K ⊓ K' = ⊥) : Nat.card K * Nat.card K' ≤ Nat.card P := by
  have := Nat.card_le_card_of_injective _ (mul_injective_of_inf_eq_bot hK hK' hint)
  rwa [Nat.card_prod] at this

theorem exists_mul_of_card_le [Finite D] {P K K' : Subgroup D} (hK : K ≤ P) (hK' : K' ≤ P)
    (hint : K ⊓ K' = ⊥) (hcard : Nat.card P ≤ Nat.card K * Nat.card K') {r : D} (hr : r ∈ P) :
    ∃ k ∈ K, ∃ k' ∈ K', r = k * k' := by
  have hbij := (mul_injective_of_inf_eq_bot hK hK' hint).bijective_of_nat_card_le
    (by rwa [Nat.card_prod])
  obtain ⟨⟨⟨k, hk⟩, ⟨k', hk'⟩⟩, hkk⟩ := hbij.2 ⟨r, hr⟩
  exact ⟨k, hk, k', hk', (congrArg Subtype.val hkk).symm⟩


@[expose] def kerK (B V : Subgroup D) : Subgroup D :=
  pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D)

section Main

variable [Finite D] (h : Hyp2 A B z V)

include h

theorem Hyp2.exists_y : ∃ y ∈ A, y ∉ A ⊓ B := by
  obtain ⟨y, hyA, hy3⟩ := h.gold.vertex_left.exists_order_three
  exact ⟨y, hyA, h.gold.vertex_left.not_mem_of_orderOf hy3⟩

theorem Hyp2.card_kerK_sq_le {y : D} (hyA : y ∈ A) (hyT : y ∉ A ⊓ B) :
    Nat.card ↥(kerK B V) * Nat.card ↥(kerK B V) ≤ Nat.card ↥(pCoreOf 2 A) := by
  have hint := h.K_inf_conj_eq_bot hyA hyT
  have h1 := card_mul_le_of_inf_eq_bot h.K_le_QA (h.conjSub_K_le_QA hyA) hint
  rwa [card_conjSub] at h1

theorem Hyp2.card_kerK_le_eight : Nat.card ↥(kerK B V) ≤ 8 := by
  obtain ⟨y, hyA, hyT⟩ := h.exists_y
  have h1 := h.card_kerK_sq_le hyA hyT
  have h2 := h.card_T_QA
  have h3 := h.card_T_QB
  have h4 : Nat.card ↥(pCoreOf 2 B) ≤ 8 * Nat.card ↥(kerK B V) := h.card_QB_le
  have hpos : 0 < Nat.card ↥(kerK B V) := Nat.card_pos
  by_contra hcon
  push Not at hcon
  have h5 : Nat.card ↥(pCoreOf 2 A) ≤ 8 * Nat.card ↥(kerK B V) := by omega
  nlinarith


theorem Hyp2.card_kerK_ne_eight : Nat.card ↥(kerK B V) ≠ 8 := by
  intro h8
  obtain ⟨y, hyA, hyT⟩ := h.exists_y
  have hint : kerK B V ⊓ conjSub y (kerK B V) = ⊥ := h.K_inf_conj_eq_bot hyA hyT
  have hKQ : kerK B V ≤ pCoreOf 2 A := h.K_le_QA
  have hK'Q : conjSub y (kerK B V) ≤ pCoreOf 2 A := h.conjSub_K_le_QA hyA
  have hQK : pCoreOf 2 A ≤ Subgroup.normalizer ((kerK B V : Subgroup D) : Set D) :=
    h.QA_le_normalizer_K
  have hQK' : pCoreOf 2 A ≤ Subgroup.normalizer ((conjSub y (kerK B V) : Subgroup D) : Set D) :=
    h.QA_le_normalizer_conjSub_K hyA
  have hcardK' : Nat.card ↥(conjSub y (kerK B V)) = 8 := by rw [card_conjSub]; exact h8
  have hmul : 8 * 8 ≤ Nat.card ↥(pCoreOf 2 A) := by
    have := card_mul_le_of_inf_eq_bot hKQ hK'Q hint
    rwa [h8, hcardK'] at this
  have hT1 := h.card_T_QA
  have hT2 := h.card_T_QB
  have hQB : Nat.card ↥(pCoreOf 2 B) ≤ 8 * Nat.card ↥(kerK B V) := h.card_QB_le
  rw [h8] at hQB
  have hQA64 : Nat.card ↥(pCoreOf 2 A) = 8 * 8 := by omega
  have hr : ∀ r ∈ pCoreOf 2 A, ∃ k ∈ kerK B V, ∃ k' ∈ conjSub y (kerK B V), r = k * k' :=
    fun r hr => exists_mul_of_card_le hKQ hK'Q hint (by rw [hQA64, h8, hcardK']) hr
  have hKK' : ∀ k ∈ kerK B V, ∀ k' ∈ conjSub y (kerK B V), k * k' = k' * k := by
    intro k hk k' hk'
    have h1 : k' * k⁻¹ * k'⁻¹ ∈ kerK B V :=
      (Subgroup.mem_normalizer_iff.mp (hQK (hK'Q hk')) k⁻¹).mp ((kerK B V).inv_mem hk)
    have h2 : k * k' * k⁻¹ ∈ conjSub y (kerK B V) :=
      (Subgroup.mem_normalizer_iff.mp (hQK' (hKQ hk)) k').mp hk'
    have h3 : k * k' * k⁻¹ * k'⁻¹ ∈ kerK B V ⊓ conjSub y (kerK B V) := by
      refine ⟨?_, ?_⟩
      · have := (kerK B V).mul_mem hk h1
        have e : k * (k' * k⁻¹ * k'⁻¹) = k * k' * k⁻¹ * k'⁻¹ := by group
        rwa [e] at this
      · exact (conjSub y (kerK B V)).mul_mem h2 ((conjSub y (kerK B V)).inv_mem hk')
    rw [hint, Subgroup.mem_bot] at h3
    calc k * k' = (k * k' * k⁻¹ * k'⁻¹) * (k' * k) := by group
      _ = k' * k := by rw [h3, one_mul]
  have hKab : ∀ p ∈ kerK B V, ∀ q ∈ kerK B V, p * q = q * p := by
    intro p hp q hq
    refine comm_of_card_le_two_mul (C := centerOf (conjClosure V B)) (K := kerK B V)
      h.center_U_le_K ?_ ?_ hp hq
    · intro c hc k hk
      exact Subgroup.mem_centralizer_iff.mp hk.2 c hc.1
    · rw [h8, h.card_center_U]
  have hinvK : ∀ e ∈ kerK B V, e * e = 1 → e ∈ Subgroup.zpowers z := by
    intro e he he2
    have heZ : e ∈ centerOf (pCoreOf 2 A) := by
      refine ⟨hKQ he, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
      obtain ⟨k, hk, k', hk', rfl⟩ := hr q hq
      calc k * k' * e = k * (k' * e) := by group
        _ = k * (e * k') := by rw [← hKK' e he k' hk']
        _ = (k * e) * k' := by group
        _ = (e * k) * k' := by rw [hKab k hk e he]
        _ = e * (k * k') := by group
    have heV : e ∈ V := h.mem_V_of_center_QA heZ he2
    exact h.K_inf_V.le ⟨he, heV⟩
  have hz'K' : y * z * y⁻¹ ∈ conjSub y (kerK B V) :=
    mul_mem_conjSub (h.center_U_le_K h.z_mem_center_U)
  have hinvK' : ∀ e' ∈ conjSub y (kerK B V), e' * e' = 1 →
      e' ∈ Subgroup.zpowers (y * z * y⁻¹) := by
    intro e' he' he'2
    have h1 : y⁻¹ * e' * y ∈ kerK B V := mem_conjSub.mp he'
    have h2 : (y⁻¹ * e' * y) * (y⁻¹ * e' * y) = 1 := by
      calc (y⁻¹ * e' * y) * (y⁻¹ * e' * y) = y⁻¹ * (e' * e') * y := by group
        _ = 1 := by rw [he'2]; group
    rcases h.mem_zpowers (hinvK _ h1 h2) with h3 | h3
    · have : e' = 1 := by
        calc e' = y * (y⁻¹ * e' * y) * y⁻¹ := by group
          _ = 1 := by rw [h3]; group
      rw [this]; exact Subgroup.one_mem _
    · have : e' = y * z * y⁻¹ := by
        calc e' = y * (y⁻¹ * e' * y) * y⁻¹ := by group
          _ = y * z * y⁻¹ := by rw [h3]
      rw [this]; exact Subgroup.mem_zpowers _
  have hRle : pCoreOf 2 A ⊓ pCoreOf 2 B ≤ Subgroup.zpowers (y * z * y⁻¹) ⊔ kerK B V := by
    intro r hr'
    obtain ⟨k, hk, k', hk', rfl⟩ := hr r hr'.1
    have hsq : (k * k') * (k * k') ∈ kerK B V := h.sq_mem_K hr'.2
    have hkk' : (k * k') * (k * k') = (k * k) * (k' * k') := by
      calc (k * k') * (k * k') = k * (k' * k) * k' := by group
        _ = k * (k * k') * k' := by rw [← hKK' k hk k' hk']
        _ = (k * k) * (k' * k') := by group
    have hk'2 : k' * k' ∈ kerK B V := by
      have e : k' * k' = (k * k)⁻¹ * ((k * k') * (k * k')) := by
        rw [hkk']; group
      rw [e]
      exact (kerK B V).mul_mem ((kerK B V).inv_mem ((kerK B V).mul_mem hk hk)) hsq
    have hk'1 : k' * k' = 1 := by
      have : k' * k' ∈ kerK B V ⊓ conjSub y (kerK B V) :=
        ⟨hk'2, (conjSub y (kerK B V)).mul_mem hk' hk'⟩
      rwa [hint, Subgroup.mem_bot] at this
    exact (Subgroup.zpowers (y * z * y⁻¹) ⊔ kerK B V).mul_mem (Subgroup.mem_sup_right hk)
      (Subgroup.mem_sup_left (hinvK' k' hk' hk'1))
  have hz'N : Subgroup.zpowers (y * z * y⁻¹) ≤
      Subgroup.normalizer ((kerK B V : Subgroup D) : Set D) :=
    Subgroup.zpowers_le.mpr (hQK (hK'Q hz'K'))
  have hc1 := GoldAmN.card_sup_le_of_le_normalizer (Subgroup.zpowers (y * z * y⁻¹)) (kerK B V) hz'N
  have hz'2 : (y * z * y⁻¹) * (y * z * y⁻¹) = 1 := by
    calc (y * z * y⁻¹) * (y * z * y⁻¹) = y * (z * z) * y⁻¹ := by group
      _ = 1 := by rw [h.z_mul_z]; group
  have hc2 := card_zpowers_le_two' hz'2
  have hRcard := Subgroup.card_le_of_le hRle
  have hT3 := h.card_T_R
  rw [h8] at hc1
  omega


theorem Hyp2.card_kerK : Nat.card ↥(kerK B V) = 4 := by
  have hT := h.isPGroup_T
  have hKT : kerK B V ≤ A ⊓ B := inf_le_left.trans h.QB_le_T
  obtain ⟨n, hn⟩ := (hT.to_le hKT).exists_card_eq
  have h4 : 4 ≤ Nat.card ↥(kerK B V) := h.four_le_card_K
  have h8 := h.card_kerK_le_eight
  have hne := h.card_kerK_ne_eight
  rw [hn] at h4 h8 hne ⊢
  have hn2 : 2 ≤ n := by
    by_contra hcon
    push Not at hcon
    interval_cases n <;> omega
  have hn3 : n ≤ 3 := by
    by_contra hcon
    push Not at hcon
    have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hcon
    omega
  interval_cases n
  · norm_num
  · exact absurd rfl hne

theorem Hyp2.kerK_eq_center_U : kerK B V = centerOf (conjClosure V B) :=
  (Subgroup.eq_of_le_of_card_ge h.center_U_le_K
    (by
      show Nat.card ↥(kerK B V) ≤ Nat.card ↥(centerOf (conjClosure V B))
      rw [h.card_kerK, h.card_center_U])).symm

theorem Hyp2.card_T_eq : Nat.card ↥(A ⊓ B) = 32 ∨ Nat.card ↥(A ⊓ B) = 64 := by
  have hT := h.isPGroup_T
  obtain ⟨n, hn⟩ := hT.exists_card_eq
  have h1 := h.card_T_QB
  have h2 : Nat.card ↥(pCoreOf 2 B) ≤ 8 * Nat.card ↥(kerK B V) := h.card_QB_le
  have h3 := h.card_kerK
  have hUQ : Nat.card ↥(conjClosure V B) ≤ Nat.card ↥(pCoreOf 2 B) :=
    Subgroup.card_le_of_le h.U_le
  have h4 := h.card_U
  have hlo : 32 ≤ Nat.card ↥(A ⊓ B) := by omega
  have hhi : Nat.card ↥(A ⊓ B) ≤ 64 := by omega
  rw [hn] at hlo hhi ⊢
  have hn5 : 5 ≤ n := by
    by_contra hcon
    push Not at hcon
    have : 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hn6 : n ≤ 6 := by
    by_contra hcon
    push Not at hcon
    have : 2 ^ 7 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hcon
    omega
  interval_cases n
  · left; norm_num
  · right; norm_num

theorem Hyp2.card_QB_eq : Nat.card ↥(pCoreOf 2 B) = 16 ∨ Nat.card ↥(pCoreOf 2 B) = 32 := by
  have h1 := h.card_T_QB
  rcases h.card_T_eq with h2 | h2 <;> [left; right] <;> omega

end Main

end GoldAmL2S

end F6

end CFSG.Quasithin
