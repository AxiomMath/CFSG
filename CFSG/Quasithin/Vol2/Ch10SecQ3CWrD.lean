module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Tools

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

theorem eq_one_of_unipotent {B : Type*} [Group B] {C : Subgroup B} [Finite C]
    (hC : Odd (Nat.card C)) {u : MulAut B} {k : ℕ} (hu : u ^ 2 ^ k = 1)
    (hfix : ∀ c ∈ C, u c = c) (hq : ∀ b : B, u b * b⁻¹ ∈ C) : u = 1 := by
  have key : ∀ (n : ℕ) (b : B), (u ^ n) b = (u b * b⁻¹) ^ n * b := by
    intro n b
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hfix _ (hq b), pow_succ]
      group
  refine MulEquiv.ext fun b => ?_
  have h1 := key (2 ^ k) b
  rw [hu, MulAut.one_apply] at h1
  have h1' : (u b * b⁻¹) ^ 2 ^ k = 1 := mul_right_cancel (h1.symm.trans (one_mul b).symm)
  have h2 : orderOf (u b * b⁻¹) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1'
  have h3 : orderOf (u b * b⁻¹) ∣ Nat.card C := Subgroup.orderOf_dvd_natCard C (hq b)
  have h4 : orderOf (u b * b⁻¹) = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    rcases j with _ | j
    · simpa using hj
    · exfalso
      rw [hj, pow_succ] at h3
      exact (Nat.not_even_iff_odd.mpr hC) (even_iff_two_dvd.mpr (dvd_of_mul_left_dvd h3))
  rw [orderOf_eq_one_iff, mul_inv_eq_one] at h4
  rw [h4, MulAut.one_apply]

theorem card_le_four_of_stab {B : Type*} [Group B] [Finite B] (hB : Nat.card B = 9)
    (C : Subgroup B) (hC : Nat.card C = 3) (A : Subgroup (MulAut B)) (hA : IsPGroup 2 A)
    (hAC : ∀ a ∈ A, ∀ c ∈ C, a c ∈ C) : Nat.card A ≤ 4 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ x y : B, x * y = y * x :=
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hB]; norm_num)).is_comm.comm
  have hCn : C.Normal := ⟨fun n hn g => by rw [hcomm g n, mul_inv_cancel_right]; exact hn⟩
  have hmap : ∀ a ∈ A, C.map (a : MulAut B).toMonoidHom = C := fun a ha => by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨c, hc, rfl⟩
      exact hAC a ha c hc
    · rw [Subgroup.card_map_of_injective a.injective]
  have hCq : Nat.card (B ⧸ C) = 3 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup C
    rw [hB, hC] at this
    omega
  have : IsCyclic C := isCyclic_of_prime_card hC
  have : IsCyclic (B ⧸ C) := isCyclic_of_prime_card hCq
  have h1 : Nat.card (MulAut C) = 2 := by
    rw [IsCyclic.card_mulAut, hC]
    decide
  have h2 : Nat.card (MulAut (B ⧸ C)) = 2 := by
    rw [IsCyclic.card_mulAut, hCq]
    decide
  let ρ : A → MulAut C × MulAut (B ⧸ C) := fun a =>
    ((a.1.subgroupMap C).trans (MulEquiv.subgroupCongr (hmap a.1 a.2)),
      QuotientGroup.congr C C a.1 (hmap a.1 a.2))
  have hρ : Function.Injective ρ := by
    rintro ⟨a, ha⟩ ⟨a', ha'⟩ h
    simp only [ρ, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hfix : ∀ c ∈ C, (a⁻¹ * a') c = c := fun c hc => by
      have h0 := congrArg (fun φ : MulAut C => ((φ ⟨c, hc⟩ : C) : B)) h1
      have : a c = a' c := h0
      rw [MulAut.mul_apply, ← this, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    have hq : ∀ b : B, (a⁻¹ * a') b * b⁻¹ ∈ C := fun b => by
      have h0 := congrArg (fun φ : MulAut (B ⧸ C) => φ (b : B ⧸ C)) h2
      have h0' : ((a b : B) : B ⧸ C) = ((a' b : B) : B ⧸ C) := h0
      have h3 : (a b)⁻¹ * a' b ∈ C := QuotientGroup.eq.mp h0'
      have h4 := hAC _ (A.inv_mem ha) _ h3
      rw [map_mul, map_inv, MulAut.inv_apply, MulEquiv.symm_apply_apply] at h4
      rw [MulAut.mul_apply, MulAut.inv_apply, hcomm]
      exact h4
    obtain ⟨k, hk⟩ := hA ⟨a⁻¹ * a', A.mul_mem (A.inv_mem ha) ha'⟩
    have hk' : (a⁻¹ * a') ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hodd : Odd (Nat.card C) := by rw [hC]; decide
    have := eq_one_of_unipotent hodd hk' hfix hq
    exact Subtype.ext (inv_mul_eq_one.mp this)
  have : Finite (MulAut C × MulAut (B ⧸ C)) := Nat.finite_of_card_ne_zero (by
    rw [Nat.card_prod, h1, h2]; norm_num)
  calc Nat.card A ≤ Nat.card (MulAut C × MulAut (B ⧸ C)) := Nat.card_le_card_of_injective ρ hρ
    _ = 4 := by rw [Nat.card_prod, h1, h2]

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
