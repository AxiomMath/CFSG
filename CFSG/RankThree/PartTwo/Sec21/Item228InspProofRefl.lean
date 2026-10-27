module

public import CFSG.RankThree.PartTwo.Sec21.Item22Refl

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item228InspProof

open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec21

section Refl

variable {P : Type*} [Group P]

theorem apply_comm_of_commute {φ ψ : MulAut P} (hc : ψ * φ = φ * ψ) (a : P) :
    φ (ψ a) = ψ (φ a) := by
  have h := congrArg (fun χ : MulAut P => χ a) hc
  simpa [MulAut.mul_apply] using h.symm

theorem eq_one_of_eq_inv (hP3 : ∀ a : P, a ^ 3 = 1) {u : P} (h : u = u⁻¹) : u = 1 := by
  have h3 := hP3 u
  have h2 : u * u = 1 := by
    calc u * u = u * u⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel u
  calc u = u ^ 3 * (u * u)⁻¹ := by group
    _ = 1 := by rw [h3, h2, inv_one, one_mul]

theorem commOf_ne_of_commute [Finite P] (hP : ∀ a b : P, a * b = b * a)
    (hP3 : ∀ a : P, a ^ 3 = 1) {φ ψ : MulAut P} (hφ : IsReflectionOn φ) (hψ : IsReflectionOn ψ)
    (hc : ψ * φ = φ * ψ) (hne : φ ≠ ψ) : commOf φ ≠ commOf ψ := by
  intro hC
  apply hne
  have hψψ := apply_apply_of_orderOf_eq_two hψ.1
  have hle : fixedSubgroupOf ψ ≤ fixedSubgroupOf φ := by
    intro b hb
    rw [mem_fixedSubgroupOf] at hb ⊢
    have hu : b⁻¹ * φ b ∈ commOf ψ := hC ▸ mem_commOf φ b
    have hψu : ψ (b⁻¹ * φ b) = b⁻¹ * φ b := by
      rw [map_mul, map_inv, hb, ← apply_comm_of_commute hc, hb]
    have hinv := inv_of_mem_commOf hP hψψ hu
    rw [hψu] at hinv
    have h1 := eq_one_of_eq_inv hP3 hinv
    rw [inv_mul_eq_one] at h1
    exact h1.symm
  have heq : fixedSubgroupOf φ = fixedSubgroupOf ψ := by
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    have h1 := card_eq_three_mul_card_fixed hP hφ
    have h2 := card_eq_three_mul_card_fixed hP hψ
    omega
  exact eq_of_fixed_eq_of_commOf_eq hP hP3 hφ.1 hψ.1 heq hC

theorem inf_commOf_eq_bot_of_commute [Finite P] (hP : ∀ a b : P, a * b = b * a)
    (hP3 : ∀ a : P, a ^ 3 = 1) {φ ψ : MulAut P} (hφ : IsReflectionOn φ) (hψ : IsReflectionOn ψ)
    (hc : ψ * φ = φ * ψ) (hne : φ ≠ ψ) : commOf φ ⊓ commOf ψ = ⊥ := by
  have hdvd : Nat.card (commOf φ ⊓ commOf ψ : Subgroup P) ∣ 3 := by
    rw [← hφ.2]
    exact Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact Subgroup.card_eq_one.mp h1
  · exfalso
    apply commOf_ne_of_commute hP hP3 hφ hψ hc hne
    have e1 : commOf φ ⊓ commOf ψ = commOf φ :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hφ.2])
    have e2 : commOf φ ⊓ commOf ψ = commOf ψ :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hψ.2])
    rw [← e1, e2]

theorem commOf_le_fixedSubgroupOf_of_commute [Finite P] (hP : ∀ a b : P, a * b = b * a)
    (hP3 : ∀ a : P, a ^ 3 = 1) {φ ψ : MulAut P} (hφ : IsReflectionOn φ) (hψ : IsReflectionOn ψ)
    (hc : ψ * φ = φ * ψ) (hne : φ ≠ ψ) : commOf ψ ≤ fixedSubgroupOf φ := by
  intro w hw
  have hmaps : φ w ∈ commOf ψ := by
    rw [← range_commHom hP] at hw ⊢
    obtain ⟨a, rfl⟩ := hw
    exact ⟨φ a, by rw [commHom_apply, commHom_apply, map_mul, map_inv,
      apply_comm_of_commute hc]⟩
  have hu : w⁻¹ * φ w ∈ commOf φ ⊓ commOf ψ :=
    ⟨mem_commOf φ w, (commOf ψ).mul_mem ((commOf ψ).inv_mem hw) hmaps⟩
  rw [inf_commOf_eq_bot_of_commute hP hP3 hφ hψ hc hne, Subgroup.mem_bot, inv_mul_eq_one] at hu
  exact (mem_fixedSubgroupOf φ w).mpr hu.symm

theorem commute_of_commOf_le (hP : ∀ a b : P, a * b = b * a) (hP3 : ∀ a : P, a ^ 3 = 1)
    {φ ψ : MulAut P} (hφ : orderOf φ = 2) (h₁ : commOf φ ≤ fixedSubgroupOf ψ)
    (h₂ : commOf ψ ≤ fixedSubgroupOf φ) : ψ * φ = φ * ψ := by
  have hφφ := apply_apply_of_orderOf_eq_two hφ
  ext a
  rw [MulAut.mul_apply, MulAut.mul_apply]
  set b := a * φ a with hbdef
  set w := (φ a)⁻¹ * a with hwdef
  have hb : φ b = b := by
    rw [hbdef, map_mul, hφφ]
    exact hP _ _
  have hwC : w ∈ commOf φ := by
    have h := (commOf φ).inv_mem (mem_commOf φ a)
    rwa [mul_inv_rev, inv_inv] at h
  have hφw : φ w = w⁻¹ := inv_of_mem_commOf hP hφφ hwC
  have hψw : ψ w = w := (mem_fixedSubgroupOf ψ w).mp (h₁ hwC)
  have hψb : φ (ψ b) = ψ b := by
    have hv : b⁻¹ * ψ b ∈ fixedSubgroupOf φ := h₂ (mem_commOf ψ b)
    rw [mem_fixedSubgroupOf, map_mul, map_inv, hb] at hv
    calc φ (ψ b) = b * (b⁻¹ * φ (ψ b)) := by group
      _ = b * (b⁻¹ * ψ b) := by rw [hv]
      _ = ψ b := by group
  have ha : a = (b * w) ^ 2 := eq_sq_of_exponent_three hP3 φ a
  have e1 : ψ (φ ((b * w) ^ 2)) = (ψ b * w⁻¹) ^ 2 := by
    rw [map_pow, map_mul, hb, hφw, map_pow, map_mul, map_inv, hψw]
  have e2 : φ (ψ ((b * w) ^ 2)) = (ψ b * w⁻¹) ^ 2 := by
    rw [map_pow, map_mul, hψw, map_pow, map_mul, hψb, hφw]
  rw [ha, e1, e2]

end Refl

section Join

variable {G : Type*} [Group G]

theorem sup_commute_pow_three {H₁ H₂ : Subgroup G} (hc₁ : ∀ x ∈ H₁, ∀ y ∈ H₁, x * y = y * x)
    (hc₂ : ∀ x ∈ H₂, ∀ y ∈ H₂, x * y = y * x) (hc₁₂ : ∀ x ∈ H₁, ∀ y ∈ H₂, x * y = y * x)
    (he₁ : ∀ x ∈ H₁, x ^ 3 = 1) (he₂ : ∀ x ∈ H₂, x ^ 3 = 1) :
    (∀ x ∈ H₁ ⊔ H₂, ∀ y ∈ H₁ ⊔ H₂, x * y = y * x) ∧ ∀ x ∈ H₁ ⊔ H₂, x ^ 3 = 1 := by
  have hcomm : ((H₁ : Set G) ∪ H₂).Pairwise Commute := by
    rintro y (hy | hy) z (hz | hz) -
    · exact hc₁ y hy z hz
    · exact hc₁₂ y hy z hz
    · exact (hc₁₂ z hz y hy).symm
    · exact hc₂ y hy z hz
  have hab := Subgroup.isMulCommutative_closure hcomm
  have hsup : H₁ ⊔ H₂ = Subgroup.closure ((H₁ : Set G) ∪ H₂) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  rw [hsup]
  refine ⟨fun x hx y hy => congrArg Subtype.val (hab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩), ?_⟩
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact he₁ y hy
    · exact he₂ y hy
  | one => exact one_pow 3
  | mul y z hy hz ihy ihz =>
    have hyz : Commute y z := congrArg Subtype.val (hab.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
    rw [hyz.mul_pow, ihy, ihz, one_mul]
  | inv y hy ihy => rw [inv_pow, ihy, inv_one]

end Join

end CFSG.RankThree.PartTwo.Sec21.Item228InspProof
