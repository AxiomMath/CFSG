module

public import CFSG.RankThree.PartTwo.Sec21.FF84S31Vstar
import CFSG.RankThree.PartTwo.Sec21.FF84S3A7K

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open Equiv Equiv.Perm Subgroup

theorem two_pow_order_iff (y : P8) : (∃ k : ℕ, orderOf y = 2 ^ k) ↔ y ^ 8 = 1 := by
  constructor
  · rintro ⟨k, hk⟩
    rw [← orderOf_dvd_iff_pow_eq_one, ← Equiv.Perm.lcm_cycleType]
    refine Multiset.lcm_dvd.2 fun a ha => ?_
    have h1 : a ∣ orderOf y := by
      rw [← Equiv.Perm.lcm_cycleType]
      exact Multiset.dvd_lcm ha
    rw [hk] at h1
    obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    have hle : 2 ^ i ≤ 8 := by
      have h8 := Multiset.le_sum_of_mem ha
      have hs := Equiv.Perm.sum_cycleType_le y
      rw [Fintype.card_fin] at hs
      omega
    have hi3 : i ≤ 3 := by
      by_contra h
      have h16 : 2 ^ 4 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at h16
      omega
    exact (pow_dvd_pow 2 hi3).trans (by norm_num)
  · intro h
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h :
      orderOf y ∣ 2 ^ 3)
    exact ⟨i, hi⟩

theorem mem_G_of {g : P8} (h1 : g * τ₀ = τ₀ * g) (h2 : Equiv.Perm.sign g = 1) :
    g ∈ Subgroup.centralizer ({τ₀} : Set P8) ⊓ A8s :=
  Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 h1,
    Equiv.Perm.mem_alternatingGroup.2 h2⟩

theorem mem_A6tau_of_comm {a b r : P8} (ha : a ∈ Subgroup.centralizer ({τ₀} : Set P8) ⊓ A8s)
    (hb : b ∈ Subgroup.centralizer ({τ₀} : Set P8) ⊓ A8s) (h : a * b * a⁻¹ * b⁻¹ = r) :
    r ∈ A6tau := by
  unfold A6tau
  refine Subgroup.mem_map.2 ⟨_, Subgroup.commutator_mem_commutator
    (Subgroup.mem_top (⟨a, ha⟩ : ↥(Subgroup.centralizer ({τ₀} : Set P8) ⊓ A8s)))
    (Subgroup.mem_top (⟨b, hb⟩ : ↥(Subgroup.centralizer ({τ₀} : Set P8) ⊓ A8s))), ?_⟩
  rw [← h]
  rfl

def A7R : List P8 :=
  [List.formPerm [3, 4, 5], List.formPerm [1, 2, 3, 4, 5], List.formPerm [1, 3, 5, 2, 4]]

theorem A7R_mem : ∀ r ∈ A7R, r ∈ A6tau := by
  intro r hr
  simp only [A7R, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact mem_A6tau_of_comm (a := List.formPerm [3, 5, 4]) (b := Equiv.swap 4 5 * Equiv.swap 6 7)
      (mem_G_of (by decide) (by decide)) (mem_G_of (by decide) (by decide)) (by decide)
  · exact mem_A6tau_of_comm (a := List.formPerm [3, 4, 5]) (b := Equiv.swap 1 4 * Equiv.swap 2 3)
      (mem_G_of (by decide) (by decide)) (mem_G_of (by decide) (by decide)) (by decide)
  · exact mem_A6tau_of_comm (a := List.formPerm [2, 3, 5]) (b := Equiv.swap 1 3 * Equiv.swap 4 5)
      (mem_G_of (by decide) (by decide)) (mem_G_of (by decide) (by decide)) (by decide)

def e62 : Fin 6 ⊕ Fin 2 ≃ Fin 8 := finSumFinEquiv

def iotaC (qq : Perm (Fin 6) × Perm (Fin 2)) : P8 :=
  e62.permCongr (Equiv.Perm.sumCongr qq.1 qq.2)

theorem iotaC_apply_inl (qq : Perm (Fin 6) × Perm (Fin 2)) (i : Fin 6) :
    iotaC qq (e62 (Sum.inl i)) = e62 (Sum.inl (qq.1 i)) := by
  simp [iotaC, Equiv.permCongr_apply, Equiv.Perm.sumCongr_apply]

theorem iotaC_apply_inr (qq : Perm (Fin 6) × Perm (Fin 2)) (j : Fin 2) :
    iotaC qq (e62 (Sum.inr j)) = e62 (Sum.inr (qq.2 j)) := by
  simp [iotaC, Equiv.permCongr_apply, Equiv.Perm.sumCongr_apply]

theorem iotaC_injective : Function.Injective iotaC := by
  rintro ⟨p, q⟩ ⟨p', q'⟩ h
  have hp : p = p' := by
    refine Equiv.ext fun i => ?_
    have h' := congrArg (fun σ : P8 => σ (e62 (Sum.inl i))) h
    simp only [iotaC_apply_inl] at h'
    simpa using e62.injective h'
  have hq : q = q' := by
    refine Equiv.ext fun j => ?_
    have h' := congrArg (fun σ : P8 => σ (e62 (Sum.inr j))) h
    simp only [iotaC_apply_inr] at h'
    simpa using e62.injective h'
  rw [hp, hq]

theorem iotaC_comm_tau : ∀ qq : Perm (Fin 6) × Perm (Fin 2), iotaC qq * τ₀ = τ₀ * iotaC qq := by
  intro qq
  have ht : τ₀ = iotaC (1, Equiv.swap 0 1) := by decide +kernel
  have hq : qq.2 * Equiv.swap 0 1 = Equiv.swap 0 1 * qq.2 := by
    have key : ∀ q : Perm (Fin 2), q * Equiv.swap 0 1 = Equiv.swap 0 1 * q := by decide
    exact key qq.2
  rw [ht]
  unfold iotaC
  rw [← Equiv.permCongr_mul, ← Equiv.permCongr_mul, Equiv.Perm.sumCongr_mul,
    Equiv.Perm.sumCongr_mul, mul_one, one_mul, hq]

theorem iotaC_surj (σ : P8) (hσ : σ ∈ Subgroup.centralizer ({τ₀} : Set P8)) :
    ∃ qq, iotaC qq = σ := by
  have hs : (τ₀ : P8).IsSwap := ⟨6, 7, by decide, rfl⟩
  have hcard : Nat.card (Perm (Fin 6) × Perm (Fin 2)) =
      Nat.card ↥(Subgroup.centralizer ({τ₀} : Set P8)) := by
    rw [card_centralizer_cycle2 (isSwap_iff_cycleType.1 hs), Nat.card_prod, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_perm, Fintype.card_fin,
      Fintype.card_fin]
    decide
  let F : Perm (Fin 6) × Perm (Fin 2) → ↥(Subgroup.centralizer ({τ₀} : Set P8)) :=
    fun qq => ⟨iotaC qq, Subgroup.mem_centralizer_singleton_iff.2 (iotaC_comm_tau qq)⟩
  have hF : Function.Injective F := fun a b h => iotaC_injective (congrArg Subtype.val h)
  letI := Fintype.ofFinite (Perm (Fin 6) × Perm (Fin 2))
  letI := Fintype.ofFinite ↥(Subgroup.centralizer ({τ₀} : Set P8))
  have hbij := (Fintype.bijective_iff_injective_and_card F).2
    ⟨hF, by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; exact hcard⟩
  obtain ⟨qq, hqq⟩ := hbij.2 ⟨σ, hσ⟩
  exact ⟨qq, congrArg Subtype.val hqq⟩

theorem A7_core_decide : ∀ qq : Perm (Fin 6) × Perm (Fin 2), iotaC qq ^ 8 = 1 → iotaC qq ≠ 1 →
    iotaC qq ≠ τ₀ → ∃ r ∈ A7R, (iotaC qq * (r * iotaC qq * r⁻¹)) ^ 8 ≠ 1 := by
  intro qq h8 h1 hτ
  rcases S3A7K.core (iotaC qq) (iotaC_comm_tau qq) h8 h1 hτ with h | h | h
  · exact ⟨S3A7K.r₁, by simp only [A7R, S3A7K.r₁, List.mem_cons, true_or], h⟩
  · exact ⟨S3A7K.r₂, by simp only [A7R, S3A7K.r₂, List.mem_cons, true_or, or_true], h⟩
  · exact ⟨S3A7K.r₃, by simp only [A7R, S3A7K.r₃, List.mem_cons, true_or, or_true], h⟩

theorem A7_core (x : P8) (hx : x * τ₀ = τ₀ * x) (h8 : x ^ 8 = 1) (h1 : x ≠ 1) (hτ : x ≠ τ₀) :
    ∃ r ∈ A7R, (x * (r * x * r⁻¹)) ^ 8 ≠ 1 := by
  obtain ⟨qq, rfl⟩ := iotaC_surj x (Subgroup.mem_centralizer_singleton_iff.2 hx)
  exact A7_core_decide qq h8 h1 hτ

theorem A7_tau : A7TauStmt := by
  unfold A7TauStmt
  intro x hx h2 hnot
  have h8 : x ^ 8 = 1 := (two_pow_order_iff x).1 h2
  have h1 : x ≠ 1 := fun h => hnot (by rw [h]; exact Subgroup.one_mem _)
  have hτ : x ≠ τ₀ := fun h => hnot (by rw [h]; exact Subgroup.mem_zpowers _)
  obtain ⟨r, hr, hne⟩ := A7_core x hx h8 h1 hτ
  exact ⟨r, A7R_mem r hr, fun hk => hne ((two_pow_order_iff _).1 hk)⟩

end CFSG.RankThree.PartTwo.Sec21.FF84.S3
