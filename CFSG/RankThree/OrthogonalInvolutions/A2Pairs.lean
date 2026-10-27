module

public import CFSG.RankThree.GF2n.Smith81.OrthRootInvol

public section

namespace CFSG.RankThree.OrthogonalInvolutions

open Module QuadraticMap
open CFSG.RankThree.GF2n.Smith81 (IsOrthA2 exists_pair_scalar_of_isOrthA2
  isOrthA2_mul_sq_of_scalar_zero)

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem finrank_commSpace_inf_eq_one_of_commute [CharP K 2] [FiniteDimensional K V]
    {α β : V ≃ₗ[K] V} (hββ : β * β = 1) (hα2 : finrank K (commSpace α) = 2)
    (hc : Commute α β) (hmove : ∃ u ∈ commSpace α, β u ≠ u) :
    finrank K ↥(commSpace α ⊓ commSpace β) = 1 := by
  obtain ⟨u, hu, hβu⟩ := hmove
  obtain ⟨v, rfl⟩ := mem_commSpace.mp hu
  have hβα : β (α v) = α (β v) := by
    rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, hc.eq]
  have hmem : β (α v - v) - (α v - v) ∈ commSpace α ⊓ commSpace β := by
    refine ⟨mem_commSpace.mpr ⟨β v - v, ?_⟩, sub_mem_commSpace β _⟩
    rw [map_sub, map_sub, hβα]
    abel
  have hne : β (α v - v) - (α v - v) ≠ 0 := sub_ne_zero.mpr hβu
  have hle : finrank K ↥(commSpace α ⊓ commSpace β) ≤ 2 := by
    rw [← hα2]
    exact Submodule.finrank_mono inf_le_left
  have hpos : 1 ≤ finrank K ↥(commSpace α ⊓ commSpace β) := by
    rw [Submodule.one_le_finrank_iff]
    intro hbot
    rw [hbot] at hmem
    exact hne ((Submodule.mem_bot K).mp hmem)
  have hne2 : finrank K ↥(commSpace α ⊓ commSpace β) ≠ 2 := by
    intro h2
    have heq : commSpace α ⊓ commSpace β = commSpace α :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (h2.trans hα2.symm)
    exact hβu (mem_fixSpace.mp (commSpace_le_fixSpace hββ (heq.ge hu).2))
  omega

private theorem smul_eq_zero_of_mem_commSpace_of_mem_fixSpace [CharP K 2]
    {α β : V ≃ₗ[K] V} {d : K}
    (h1 : ((α : V →ₗ[K] V) - 1) * ((β : V →ₗ[K] V) - 1) * ((α : V →ₗ[K] V) - 1) =
      d • ((α : V →ₗ[K] V) - 1))
    {u : V} (hu : u ∈ commSpace α) (huβ : u ∈ fixSpace β) : d • u = 0 := by
  obtain ⟨v, rfl⟩ := mem_commSpace.mp hu
  have hβu : β (α v - v) = α v - v := mem_fixSpace.mp huβ
  have h := LinearMap.congr_fun h1 v
  simp only [Module.End.mul_apply, LinearMap.smul_apply] at h
  rw [show ((α : V →ₗ[K] V) - 1) v = α v - v from rfl] at h
  rw [show ((β : V →ₗ[K] V) - 1) (α v - v) = β (α v - v) - (α v - v) from rfl,
    hβu, sub_self] at h
  simpa using h.symm

private theorem pair_scalar_ne_zero [CharP K 2] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) {α β : V ≃ₗ[K] V}
    (hα : IsOrthA2 Q α) (hβ : IsOrthA2 Q β) (hodd : Odd (orderOf (α * β)))
    (hne : α * β ≠ 1) {d : K}
    (h1 : ((α : V →ₗ[K] V) - 1) * ((β : V →ₗ[K] V) - 1) * ((α : V →ₗ[K] V) - 1) =
      d • ((α : V →ₗ[K] V) - 1))
    (h2 : ((β : V →ₗ[K] V) - 1) * ((α : V →ₗ[K] V) - 1) * ((β : V →ₗ[K] V) - 1) =
      d • ((β : V →ₗ[K] V) - 1)) : d ≠ 0 := by
  rintro rfl
  rw [zero_smul] at h1 h2
  have hfour : (α * β) ^ 4 = 1 := by
    by_cases hsq : (α * β) ^ 2 = 1
    · rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, hsq, one_mul]
    · rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]
      exact (isOrthA2_mul_sq_of_scalar_zero hQ hα hβ h1 h2 hsq).1.mul_self
  have hdvd : orderOf (α * β) ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one hfour
  obtain ⟨k, hk, hk4⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  interval_cases k
  · rw [pow_zero] at hk4
    exact hne (orderOf_eq_one_iff.mp hk4)
  · rw [pow_one] at hk4
    obtain ⟨m, hm⟩ := hodd
    rw [hk4] at hm
    omega
  · norm_num at hk4
    obtain ⟨m, hm⟩ := hodd
    rw [hk4] at hm
    omega

private theorem eq_zero_of_mem_commSpace_of_forall_polar_eq_zero [CharP K 2]
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) {α β : V ≃ₗ[K] V}
    (hβ : IsOrthA2 Q β) {d : K}
    (h1 : ((α : V →ₗ[K] V) - 1) * ((β : V →ₗ[K] V) - 1) * ((α : V →ₗ[K] V) - 1) =
      d • ((α : V →ₗ[K] V) - 1))
    (hd : d ≠ 0) {u : V} (hu : u ∈ commSpace α)
    (horth : ∀ b ∈ commSpace β, polar Q u b = 0) : u = 0 := by
  have huβ : u ∈ fixSpace β := by
    rw [fixSpace_eq_orthogonal_commSpace hQ hβ.mem hβ.mul_self,
      LinearMap.BilinForm.mem_orthogonal_iff]
    intro b hb
    rw [polarBilin_apply_apply, polar_comm]
    exact horth b hb
  exact (smul_eq_zero.mp
    (smul_eq_zero_of_mem_commSpace_of_mem_fixSpace h1 hu huβ)).resolve_left hd

private theorem inf_commSpace_eq_bot [CharP K 2] {α β : V ≃ₗ[K] V} {d : K}
    (hββ : β * β = 1)
    (h1 : ((α : V →ₗ[K] V) - 1) * ((β : V →ₗ[K] V) - 1) * ((α : V →ₗ[K] V) - 1) =
      d • ((α : V →ₗ[K] V) - 1)) (hd : d ≠ 0) :
    commSpace α ⊓ commSpace β = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  rw [Submodule.mem_bot]
  exact (smul_eq_zero.mp (smul_eq_zero_of_mem_commSpace_of_mem_fixSpace h1 hu.1
    (commSpace_le_fixSpace hββ hu.2))).resolve_left hd

private theorem eq_zero_of_mem_sup_of_forall_polar_eq_zero [CharP K 2]
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) {α β : V ≃ₗ[K] V}
    (hα : IsOrthA2 Q α) (hβ : IsOrthA2 Q β) {d : K}
    (h1 : ((α : V →ₗ[K] V) - 1) * ((β : V →ₗ[K] V) - 1) * ((α : V →ₗ[K] V) - 1) =
      d • ((α : V →ₗ[K] V) - 1))
    (h2 : ((β : V →ₗ[K] V) - 1) * ((α : V →ₗ[K] V) - 1) * ((β : V →ₗ[K] V) - 1) =
      d • ((β : V →ₗ[K] V) - 1))
    (hd : d ≠ 0) {x : V} (hx : x ∈ commSpace α ⊔ commSpace β)
    (hx0 : ∀ y ∈ commSpace α ⊔ commSpace β, polar Q x y = 0) : x = 0 := by
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
  have huβ : ∀ b ∈ commSpace β, polar Q u b = 0 := by
    intro b hb
    have h := hx0 b (Submodule.mem_sup_right hb)
    rw [polar_add_left, polar_commSpace_eq_zero hβ.mem hβ.mul_self hw hb, add_zero] at h
    exact h
  have hwα : ∀ a ∈ commSpace α, polar Q w a = 0 := by
    intro a ha
    have h := hx0 a (Submodule.mem_sup_left ha)
    rw [polar_add_left, polar_commSpace_eq_zero hα.mem hα.mul_self hu ha, zero_add] at h
    exact h
  have hu0 : u = 0 := eq_zero_of_mem_commSpace_of_forall_polar_eq_zero hQ hβ h1 hd hu huβ
  have hw0 : w = 0 := eq_zero_of_mem_commSpace_of_forall_polar_eq_zero hQ hα h2 hd hw hwα
  rw [hu0, hw0, add_zero]

theorem commSpace_inf_eq_bot_of_odd_orderOf_mul [CharP K 2] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) {α β : V ≃ₗ[K] V}
    (hα : IsOrthA2 Q α) (hβ : IsOrthA2 Q β) (hodd : Odd (orderOf (α * β))) (hne : α * β ≠ 1) :
    commSpace α ⊓ commSpace β = ⊥ ∧ ∀ x ∈ commSpace α ⊔ commSpace β,
      (∀ y ∈ commSpace α ⊔ commSpace β, polar Q x y = 0) → x = 0 := by
  obtain ⟨d, h1, h2⟩ := exists_pair_scalar_of_isOrthA2 hQ hα hβ
  have hd : d ≠ 0 := pair_scalar_ne_zero hQ hα hβ hodd hne h1 h2
  exact ⟨inf_commSpace_eq_bot hβ.mul_self h1 hd,
    fun x hx hx0 => eq_zero_of_mem_sup_of_forall_polar_eq_zero hQ hα hβ h1 h2 hd hx hx0⟩

theorem le_sup_of_finrank_inf_eq_one [FiniteDimensional K V] {A B₁ B₂ : Submodule K V}
    (hA : finrank K A = 2) (h₁ : finrank K ↥(A ⊓ B₁) = 1) (h₂ : finrank K ↥(A ⊓ B₂) = 1)
    (h₁₂ : B₁ ⊓ B₂ = ⊥) : A ≤ B₁ ⊔ B₂ := by
  have hbot : (A ⊓ B₁) ⊓ (A ⊓ B₂) = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf inf_le_right inf_le_right).trans h₁₂.le)
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (A ⊓ B₁) (A ⊓ B₂)
  rw [hbot, finrank_bot, h₁, h₂] at hdim
  have heq : (A ⊓ B₁) ⊔ (A ⊓ B₂) = A :=
    Submodule.eq_of_le_of_finrank_eq (sup_le inf_le_left inf_le_left) (by omega)
  calc A = (A ⊓ B₁) ⊔ (A ⊓ B₂) := heq.symm
    _ ≤ B₁ ⊔ B₂ := sup_le_sup inf_le_right inf_le_right

end CFSG.RankThree.OrthogonalInvolutions
