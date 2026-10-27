module

public import CFSG.Sporadic.Recognition.JankoWongThreeSylow

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS

theorem exists_fixed_of_sq_eq_one_odd {α : Type*} [Finite α] {f : α → α}
    (hf : ∀ x, f (f x) = x) (hodd : Odd (Nat.card α)) : ∃ x, f x = x := by
  classical
  by_contra hno
  push Not at hno
  have : Fintype α := Fintype.ofFinite α
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let g : Function.End α := f
  have hg2 : g ^ 2 ^ 1 = 1 := by
    funext x
    simp only [pow_one, pow_two]
    exact hf x
  have hfix : Function.fixedPoints g = ∅ := by
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    exact hno x
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := g) (p := 2) (n := 1) hg2
  have : IsEmpty ↑(Function.fixedPoints g) := Set.isEmpty_coe_sort.mpr hfix
  have hz0 : Fintype.card ↑(Function.fixedPoints g) = 0 := Fintype.card_eq_zero
  rw [hz0] at hmod
  have h0 : Fintype.card α % 2 = 0 := hmod
  rw [← Nat.card_eq_fintype_card] at h0
  obtain ⟨k, hk⟩ := hodd
  omega

theorem odd_card_support_of_orderOf {c : Perm (Fin 8)} {p : ℕ} (hp : p = 5 ∨ p = 7)
    (hc : orderOf c = p) : Odd c.support.card := by
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hall : ∀ n ∈ c.cycleType, n = p := by
    intro n hn
    have hd : n ∣ p := hc ▸ dvd_of_mem_cycleType hn
    have h2 := two_le_of_mem_cycleType hn
    rcases (Nat.dvd_prime hprime).mp hd with h | h
    · omega
    · exact h
  have hrep : c.cycleType = Multiset.replicate (Multiset.card c.cycleType) p :=
    Multiset.eq_replicate.mpr ⟨rfl, hall⟩
  have hsum : c.support.card = p * Multiset.card c.cycleType := by
    rw [← sum_cycleType]
    conv_lhs => rw [hrep]
    rw [Multiset.sum_replicate]; simp [mul_comm]
  have hle : c.support.card ≤ 8 := by
    have := Finset.card_le_univ c.support
    simpa using this
  have hne : Multiset.card c.cycleType ≠ 0 := by
    intro h0
    have hc1 : c = 1 := cycleType_eq_zero.mp (Multiset.card_eq_zero.mp h0)
    rw [hc1, orderOf_one] at hc
    rcases hp with rfl | rfl <;> omega
  have hk1 : Multiset.card c.cycleType = 1 := by
    rcases hp with rfl | rfl <;> rw [hsum] at hle <;> omega
  rw [hsum, hk1]
  rcases hp with rfl | rfl <;> decide

theorem exists_fixed_of_inverts {σ c : Perm (Fin 8)} (hσ : σ ^ 2 = 1) {p : ℕ}
    (hp : p = 5 ∨ p = 7) (hc : orderOf c = p) (hinv : σ * c * σ⁻¹ = c⁻¹) : ∃ x, σ x = x := by
  have hodd := odd_card_support_of_orderOf hp hc
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    have := congrArg (fun q : Perm (Fin 8) => q x) hσ
    simpa [pow_two] using this
  have h1 : σ * c = c⁻¹ * σ := by
    calc σ * c = (σ * c * σ⁻¹) * σ := by group
      _ = c⁻¹ * σ := by rw [hinv]
  have hmem : ∀ x, x ∈ c.support → σ x ∈ c.support := by
    intro x hx
    rw [mem_support] at hx ⊢
    intro hcx
    apply hx
    have h2 : σ (c x) = c⁻¹ (σ x) := by
      have := congrArg (fun q : Perm (Fin 8) => q x) h1
      simpa using this
    have h3 : c⁻¹ (σ x) = σ x := (Equiv.Perm.inv_eq_iff_eq).mpr hcx.symm
    rw [h3] at h2
    exact σ.injective h2
  let f : c.support → c.support := fun x => ⟨σ x, hmem x x.2⟩
  have hf : ∀ x, f (f x) = x := fun x => Subtype.ext (hσσ x)
  have hcard : Odd (Nat.card c.support) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact hodd
  obtain ⟨x, hx⟩ := exists_fixed_of_sq_eq_one_odd hf hcard
  exact ⟨x, congrArg Subtype.val hx⟩

namespace IsCover8

variable {E : Type*} [Group E] {ρ : E →* Perm (Fin 8)} {z : E}

theorem false_of_involution_inverts (h : IsCover8 ρ z) {e r : E} (he : e ^ 2 = 1)
    (hr : orderOf r = 5 ∨ orderOf r = 7) (hinv : e * r * e⁻¹ = r⁻¹) : False := by
  have hr2 : r ^ 2 ≠ 1 := fun h2 => by
    have := orderOf_dvd_of_pow_eq_one h2
    rcases hr with hr | hr <;> rw [hr] at this <;> norm_num at this
  have hsq_of_inv : r = r⁻¹ → False := fun hrr => hr2 (by
    rw [pow_two]; nth_rewrite 1 [hrr]; exact inv_mul_cancel r)
  have he1 : e ≠ 1 := fun e1 => hsq_of_inv (by simpa [e1] using hinv)
  have hez : e ≠ z := fun ez => hsq_of_inv (by
    rw [ez] at hinv
    rw [← hinv]
    calc r = r * z * z⁻¹ := by group
      _ = z * r * z⁻¹ := by rw [h.mul_z_comm r])
  have hty := h.type2222_of_involution he he1 hez
  have hfpf := fpf_of_type2222 hty
  have hσ : ρ e ^ 2 = 1 := by rw [← map_pow, he, map_one]
  have hc1 : ρ r ≠ 1 := fun e1 => by
    rcases h.mem_ker_iff.mp e1 with e2 | e2
    · rw [e2, orderOf_one] at hr; rcases hr with hr | hr <;> omega
    · exact hr2 (by rw [e2]; exact h.sq_eq_one)
  have hord : ∃ p : ℕ, (p = 5 ∨ p = 7) ∧ orderOf (ρ r) = p := by
    have hdvd : orderOf (ρ r) ∣ orderOf r := orderOf_map_dvd ρ r
    have hne1 : orderOf (ρ r) ≠ 1 := fun e1 => hc1 (orderOf_eq_one_iff.mp e1)
    rcases hr with hr | hr
    · rw [hr] at hdvd
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with e1 | e1
      · exact absurd e1 hne1
      · exact ⟨5, Or.inl rfl, e1⟩
    · rw [hr] at hdvd
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hdvd with e1 | e1
      · exact absurd e1 hne1
      · exact ⟨7, Or.inr rfl, e1⟩
  obtain ⟨p, hp, hpo⟩ := hord
  have hinv' : ρ e * ρ r * (ρ e)⁻¹ = (ρ r)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hinv, map_inv]
  obtain ⟨x, hx⟩ := exists_fixed_of_inverts hσ hp hpo hinv'
  exact hfpf x hx

end IsCover8

@[expose] def permT : Perm (Fin 8) := swap 0 3 * swap 1 4 * swap 2 5 * swap 6 7

@[expose] def permD : Perm (Fin 8) := swap 0 3 * swap 1 5 * swap 2 4 * swap 6 7

theorem permT_sq : permT ^ 2 = 1 := by unfold permT; decide
theorem permD_sq : permD ^ 2 = 1 := by unfold permD; decide

theorem cycleType_permT : permT.cycleType = {2, 2, 2, 2} := by
  unfold permT
  exact cycleType_type2222_of_card (by decide) (by decide)

theorem cycleType_permD : permD.cycleType = {2, 2, 2, 2} := by
  unfold permD
  exact cycleType_type2222_of_card (by decide) (by decide)

theorem cycleType_permD_mul_permT : (permD * permT).cycleType = {2, 2} := by
  unfold permD permT
  exact cycleType_type22_of_card (by decide) (by decide)

theorem permT_comm : permT * (permA3 * permB3) = (permA3 * permB3) * permT := by
  unfold permT permA3 permB3; decide

theorem permD_inverts : permD * (permA3 * permB3) * permD⁻¹ = (permA3 * permB3)⁻¹ := by
  unfold permD permA3 permB3; decide

namespace Setup

variable {G : Type} [Group G] [Finite G]

theorem exists_dihedral_data (S : Setup G) {a b : S.H} (ha : S.ρ a = permA3)
    (hb : S.ρ b = permB3) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hab : a * b = b * a) :
    ∃ t d : S.H, t ^ 2 = 1 ∧ d ^ 2 = 1 ∧ S.ρ t = permT ∧ S.ρ d = permD ∧
      t * (a * b) = (a * b) * t ∧ d * (a * b) * d⁻¹ = (a * b)⁻¹ ∧ (d * t) ^ 2 = zIn S.z := by
  have hx3 : (a * b) ^ 3 = 1 := by rw [Commute.mul_pow hab, ha3, hb3, one_mul]
  have hρx : S.ρ (a * b) = permA3 * permB3 := by rw [map_mul, ha, hb]
  obtain ⟨t, ht⟩ := S.cover.exists_lift (p := permT)
    (sign_of_type2222 cycleType_permT)
  obtain ⟨d, hd⟩ := S.cover.exists_lift (p := permD)
    (sign_of_type2222 cycleType_permD)
  have ht2 : t ^ 2 = 1 := S.cover.sq_eq_one_of_type2222_lift (by rw [ht]; exact cycleType_permT)
  have hd2 : d ^ 2 = 1 := S.cover.sq_eq_one_of_type2222_lift (by rw [hd]; exact cycleType_permD)
  refine ⟨t, d, ht2, hd2, ht, hd, ?_, ?_, ?_⟩
  · refine S.cover.commute_of_cube hx3 ?_
    rw [hρx, ht]; exact permT_comm
  · have h3 : (d * (a * b) * d⁻¹) ^ 3 = 1 := by
      have : (d * (a * b) * d⁻¹) ^ 3 = d * (a * b) ^ 3 * d⁻¹ := by simp [pow_succ, mul_assoc]
      rw [this, hx3]; simp
    have h3' : ((a * b)⁻¹) ^ 3 = 1 := by rw [inv_pow, hx3, inv_one]
    refine S.cover.eq_of_cube_one h3 h3' ?_
    rw [map_mul, map_mul, map_inv, hd, hρx, map_inv, hρx]
    exact permD_inverts
  · refine S.cover.sq_eq_z_of_type22 ?_
    rw [map_mul, hd, ht]; exact cycleType_permD_mul_permT

end Setup

end CFSG.Sporadic.Recognition.JankoWong
