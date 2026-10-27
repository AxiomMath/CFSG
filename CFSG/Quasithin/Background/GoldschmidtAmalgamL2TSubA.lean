module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2SHyp

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL2S

open scoped Pointwise

namespace F6

namespace GoldAmL2T

variable {D : Type*} [Group D]

theorem card_sup_mul_card_inf_of_le_normalizer {A B : Subgroup D}
    (h : A ≤ Subgroup.normalizer (B : Set D)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have h1 := F1.relIndex_sup_eq_of_le_normalizer h
  have h2 := Subgroup.relIndex_mul_card B (A ⊔ B)
  have h3 := Subgroup.relIndex_mul_card B A
  have h4 : B ⊓ (A ⊔ B) = B := inf_of_le_left le_sup_right
  rw [h4, h1] at h2
  rw [← h2, ← h3, inf_comm B A]
  ring

theorem card_sup_mul_card_inf_of_le_normalizer' {A B : Subgroup D}
    (h : A ≤ Subgroup.normalizer (B : Set D)) :
    Nat.card ↥(B ⊔ A) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  rw [sup_comm]; exact card_sup_mul_card_inf_of_le_normalizer h

theorem card_eq_relIndex_mul {X Y : Subgroup D} (h : X ≤ Y) :
    Nat.card ↥Y = X.relIndex Y * Nat.card ↥X := by
  have := Subgroup.relIndex_mul_card X Y
  rw [inf_of_le_left h] at this
  exact this.symm

theorem le_normalizer_of_conj_mem {H M : Subgroup D}
    (h : ∀ g ∈ H, ∀ m ∈ M, g * m * g⁻¹ ∈ M) : H ≤ Subgroup.normalizer (M : Set D) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h g hg x, fun hx => ?_⟩
  have := h g⁻¹ (H.inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem units_eq_one_of_pow_three {u : ℤˣ} (h : u ^ 3 = 1) : u = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · rfl
  · exact absurd h (by decide)

variable [Finite D] in
theorem eq_bot_of_card_dvd_three {P K : Subgroup D} (hP : IsPGroup 2 ↥P) (hK : K ≤ P)
    (h3 : Nat.card ↥K ∣ 3) : K = ⊥ := by
  obtain ⟨k, hk⟩ := (hP.to_le hK).exists_card_eq
  rw [hk] at h3
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact Subgroup.eq_bot_of_card_eq K (by simpa using hk)
  · have : 2 ∣ 3 := (dvd_pow_self 2 hk0.ne').trans h3
    omega

theorem pCore_perm_three : CFSG.Open.pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : (CFSG.Open.pCore 2 (Equiv.Perm (Fin 3))).Normal :=
    CFSG.LieType.BorelTits.pCore_normal 2
  have hP : IsPGroup 2 ↥(CFSG.Open.pCore 2 (Equiv.Perm (Fin 3))) :=
    CFSG.LieType.BorelTits.pCore_isPGroup 2
  have key : ∀ σ : Equiv.Perm (Fin 3), σ ≠ 1 →
      ∃ τ : Equiv.Perm (Fin 3), σ * (τ * σ * τ⁻¹) ≠ 1 ∧ (σ * (τ * σ * τ⁻¹)) ^ 3 = 1 := by
    decide +kernel
  rw [eq_bot_iff]
  intro σ hσ
  by_contra hne
  obtain ⟨τ, h1, h2⟩ := key σ (by simpa using hne)
  have hσ' : σ * (τ * σ * τ⁻¹) ∈ CFSG.Open.pCore 2 (Equiv.Perm (Fin 3)) :=
    Subgroup.mul_mem _ hσ (hnorm.conj_mem σ hσ τ)
  obtain ⟨k, hk⟩ := hP ⟨_, hσ'⟩
  have hk' : (σ * (τ * σ * τ⁻¹)) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h3 : orderOf (σ * (τ * σ * τ⁻¹)) ∣ 3 := orderOf_dvd_of_pow_eq_one h2
  have h4 : orderOf (σ * (τ * σ * τ⁻¹)) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h5 : orderOf (σ * (τ * σ * τ⁻¹)) ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd h3 h4
  have h6 : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
  rw [h6, Nat.dvd_one, orderOf_eq_one_iff] at h5
  exact h1 h5

structure SubData [Finite D] (H T N W : Subgroup D) (w : D) : Prop where
  vertex : Vertex H T
  N_le : N ≤ pCoreOf 2 H
  N_norm : H ≤ Subgroup.normalizer (N : Set D)
  card_Q : Nat.card ↥(pCoreOf 2 H) = 2 * Nat.card ↥N
  W_le : W ≤ T
  W_inf_Q : W ⊓ pCoreOf 2 H ≤ N
  card_W : Nat.card ↥W = 2 * Nat.card ↥(W ⊓ N)
  w_mem : w ∈ H
  w_order : orderOf w = 3
  centralizer_le : H ⊓ Subgroup.centralizer (N : Set D) ≤ pCoreOf 2 H

namespace SubData

variable [Finite D] {H T N W : Subgroup D} {w : D} (d : SubData H T N W w)

include d

theorem N_le_T : N ≤ T := d.N_le.trans d.vertex.pCoreOf_le

theorem N_le_H : N ≤ H := d.N_le_T.trans d.vertex.T_le

theorem W_le_H : W ≤ H := d.W_le.trans d.vertex.T_le

theorem W_norm_N : W ≤ Subgroup.normalizer (N : Set D) := d.W_le_H.trans d.N_norm

theorem zpowers_norm_N : Subgroup.zpowers w ≤ Subgroup.normalizer (N : Set D) :=
  Subgroup.zpowers_le.mpr (d.N_norm d.w_mem)

theorem w_cube : w * w * w = 1 := by
  have := pow_orderOf_eq_one w
  rw [d.w_order, pow_three'] at this
  exact this

theorem zpowers_inf_T : Subgroup.zpowers w ⊓ T = ⊥ := by
  refine eq_bot_of_card_dvd_three d.vertex.isPGroup (inf_le_right : Subgroup.zpowers w ⊓ T ≤ T) ?_
  have := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers w ⊓ T ≤ Subgroup.zpowers w)
  rwa [Nat.card_zpowers, d.w_order] at this

theorem card_H : Nat.card ↥H = 12 * Nat.card ↥N := by
  have h1 := card_eq_relIndex_mul (pCoreOf_le 2 H)
  rw [d.vertex.relIndex_pCoreOf, d.card_Q] at h1
  omega

theorem card_M : Nat.card ↥(N ⊔ Subgroup.zpowers w) = 3 * Nat.card ↥N := by
  have h1 := card_sup_mul_card_inf_of_le_normalizer' d.zpowers_norm_N
  have h2 : Subgroup.zpowers w ⊓ N = ⊥ :=
    le_bot_iff.mp (d.zpowers_inf_T ▸ inf_le_inf_left _ d.N_le_T)
  rw [h2, Subgroup.card_bot, Nat.card_zpowers, d.w_order] at h1
  omega

theorem M_inf_T_le : (N ⊔ Subgroup.zpowers w) ⊓ T ≤ N := by
  rintro m ⟨hmM, hmT⟩
  have hm : m ∈ (N : Set D) * (Subgroup.zpowers w : Set D) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left N _ d.zpowers_norm_N]; exact hmM
  obtain ⟨n, hn, p, hp, hnp⟩ := Set.mem_mul.mp hm
  subst hnp
  have hpT : p ∈ T := by
    have := T.mul_mem (T.inv_mem (d.N_le_T hn)) hmT
    simpa using this
  have : p ∈ Subgroup.zpowers w ⊓ T := ⟨hp, hpT⟩
  rw [d.zpowers_inf_T, Subgroup.mem_bot] at this
  rw [this, mul_one]
  exact hn

end SubData

end GoldAmL2T

end F6

end CFSG.Quasithin
