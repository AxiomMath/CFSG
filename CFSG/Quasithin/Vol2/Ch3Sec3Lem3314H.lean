module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3314C

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.Ins314

open CFSG.Quasithin CFSG.Quasithin.H13.CZL32

instance : DecidablePred (· ∈ bSub) := fun _ => decidable_of_iff _ mem_bSub.symm

instance : DecidablePred (· ∈ L3.ptSub e1) := fun _ => decidable_of_iff _ L3.mem_ptSub.symm

instance : DecidablePred (· ∈ L3.stabSub P12) := fun _ => decidable_of_iff _ L3.mem_stabSub.symm

theorem mem_bSub_of_conjSub_eq {g : L3.Γ} (h : conjSub g bSub = bSub) : g ∈ bSub :=
  mem_bSub_of_normalizes fun _ hb => h ▸ mul_mem_conjSub hb

theorem exists_conjSub_eq_bSub {P : Subgroup L3.Γ} (hP : Nat.card P = 8) :
    ∃ γ : L3.Γ, P = conjSub γ bSub := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ P.index := by
    have := Subgroup.card_mul_index P
    rw [hP, card_L3Γ] at this
    omega
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := 3) (by rw [hP]; rfl)
  obtain ⟨γ, hγ⟩ := MulAction.exists_smul_eq L3.Γ (isPGroup_bSub.toSylow not_two_dvd_index_bSub)
    (hP2.toSylow hidx)
  refine ⟨γ, ?_⟩
  have h1 := congrArg (fun S : Sylow 2 L3.Γ => (S : Subgroup L3.Γ)) hγ
  simp only [IsPGroup.toSylow_coe, Sylow.coe_subgroup_smul] at h1
  rw [← h1]
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_conjSub]
  simp [MulAut.smul_def]

@[expose] def sylOf (c : L3.Γ) (j : Fin 3) : Subgroup L3.Γ := conjSub (c ^ (j : ℕ)) bSub

theorem conjSub_bSub_self {b : L3.Γ} (hb : b ∈ bSub) : conjSub b bSub = bSub := by
  ext x
  rw [mem_conjSub]
  constructor
  · intro h
    have := bSub.mul_mem (bSub.mul_mem hb h) (bSub.inv_mem hb)
    simpa [mul_assoc] using this
  · intro h
    exact bSub.mul_mem (bSub.mul_mem (bSub.inv_mem hb) h) hb

theorem conjSub_bSub_of_mem {c γ : L3.Γ} {j : Fin 3} (h : (c ^ (j : ℕ))⁻¹ * γ ∈ bSub) :
    conjSub γ bSub = sylOf c j := by
  have e : γ = c ^ (j : ℕ) * ((c ^ (j : ℕ))⁻¹ * γ) := by group
  rw [e, conjSub_mul, conjSub_bSub_self h, sylOf]

theorem card_sylOf (c : L3.Γ) (j : Fin 3) : Nat.card (sylOf c j) = 8 := by
  rw [sylOf, conjSub, Subgroup.card_map_of_injective (MulAut.conj _).injective, card_bSub]

variable {Q : Subgroup L3.Γ} {c : L3.Γ}

theorem sylOf_le (hBQ : bSub ≤ Q) (hc : c ∈ Q) (j : Fin 3) : sylOf c j ≤ Q := by
  intro x hx
  have h := hBQ (mem_conjSub.mp hx)
  have e : x = c ^ (j : ℕ) * ((c ^ (j : ℕ))⁻¹ * x * c ^ (j : ℕ)) * (c ^ (j : ℕ))⁻¹ := by group
  rw [e]
  exact Q.mul_mem (Q.mul_mem (Q.pow_mem hc _) h) (Q.inv_mem (Q.pow_mem hc _))

theorem exists_conjSub_sylOf (hcos : ∀ y ∈ Q, ∃ j : Fin 3, (c ^ (j : ℕ))⁻¹ * y ∈ bSub)
    (hc : c ∈ Q) {γ : L3.Γ} (hγ : γ ∈ Q) (i : Fin 3) :
    ∃ j, conjSub γ (sylOf c i) = sylOf c j := by
  obtain ⟨j, hj⟩ := hcos _ (Q.mul_mem hγ (Q.pow_mem hc i))
  exact ⟨j, by rw [sylOf, ← conjSub_mul, conjSub_bSub_of_mem hj]⟩

theorem sylOf_injective (hdist : ∀ i j : Fin 3, i ≠ j → (c ^ (j : ℕ))⁻¹ * c ^ (i : ℕ) ∉ bSub) :
    Function.Injective (sylOf c) := by
  intro i j h
  by_contra hij
  apply hdist i j hij
  apply mem_bSub_of_conjSub_eq
  rw [conjSub_mul, ← sylOf, h, sylOf, ← conjSub_mul, inv_mul_cancel, conjSub_one]

theorem eq_sylOf (hsyl : ∀ γ : L3.Γ, (∀ b ∈ bSub, γ * b * γ⁻¹ ∈ Q) → γ ∈ Q)
    (hcos : ∀ y ∈ Q, ∃ j : Fin 3, (c ^ (j : ℕ))⁻¹ * y ∈ bSub) {P : Subgroup L3.Γ}
    (hP : Nat.card P = 8) (hPQ : P ≤ Q) : ∃ j, P = sylOf c j := by
  obtain ⟨γ, rfl⟩ := exists_conjSub_eq_bSub hP
  obtain ⟨j, hj⟩ := hcos γ (hsyl γ fun b hb => hPQ (mul_mem_conjSub hb))
  exact ⟨j, conjSub_bSub_of_mem hj⟩

theorem exists_perm (hperm : ∀ α : Equiv.Perm (Fin 3), ∃ γ : L3.Γ, γ ∈ Q ∧
      ∀ i : Fin 3, (c ^ ((α i : Fin 3) : ℕ))⁻¹ * γ * c ^ (i : ℕ) ∈ bSub)
    (α : Equiv.Perm (Fin 3)) :
    ∃ γ ∈ Q, ∀ i, conjSub γ (sylOf c i) = sylOf c (α i) := by
  obtain ⟨γ, hγ, h⟩ := hperm α
  refine ⟨γ, hγ, fun i => ?_⟩
  rw [sylOf, ← conjSub_mul]
  exact conjSub_bSub_of_mem (by rw [← mul_assoc]; exact h i)

theorem sq_eq_one (hker : ∀ γ : L3.Γ, (∀ i : Fin 3, (c ^ (i : ℕ))⁻¹ * γ * c ^ (i : ℕ) ∈ bSub) →
      γ * γ = 1) {γ : L3.Γ} (h : ∀ i, conjSub γ (sylOf c i) = sylOf c i) : γ * γ = 1 := by
  refine hker γ fun i => mem_bSub_of_conjSub_eq ?_
  have h1 := h i
  rw [sylOf, ← conjSub_mul] at h1
  rw [conjSub_mul, conjSub_mul, ← conjSub_mul γ, h1, conjSub_conjSub_inv]

theorem perm1_check : ∀ α : Equiv.Perm (Fin 3), ∃ γ : L3.Γ, γ ∈ L3.ptSub e1 ∧
    ∀ i : Fin 3, (c1 ^ ((α i : Fin 3) : ℕ))⁻¹ * γ * c1 ^ (i : ℕ) ∈ bSub := by
  decide +kernel

theorem perm2_check : ∀ α : Equiv.Perm (Fin 3), ∃ γ : L3.Γ, γ ∈ L3.stabSub P12 ∧
    ∀ i : Fin 3, (c2 ^ ((α i : Fin 3) : ℕ))⁻¹ * γ * c2 ^ (i : ℕ) ∈ bSub := by
  decide +kernel

theorem ker1_check : ∀ γ : L3.Γ,
    (∀ i : Fin 3, (c1 ^ (i : ℕ))⁻¹ * γ * c1 ^ (i : ℕ) ∈ bSub) → γ * γ = 1 := by
  decide +kernel

theorem ker2_check : ∀ γ : L3.Γ,
    (∀ i : Fin 3, (c2 ^ (i : ℕ))⁻¹ * γ * c2 ^ (i : ℕ) ∈ bSub) → γ * γ = 1 := by
  decide +kernel

theorem syl1_check : ∀ γ : L3.Γ, (∀ b : L3.Γ, b ∈ bSub → γ * b * γ⁻¹ ∈ L3.ptSub e1) →
    γ ∈ L3.ptSub e1 := by
  decide +kernel

theorem syl2_check : ∀ γ : L3.Γ, (∀ b : L3.Γ, b ∈ bSub → γ * b * γ⁻¹ ∈ L3.stabSub P12) →
    γ ∈ L3.stabSub P12 := by
  decide +kernel

theorem zB_mem_sylOf₁ : ∀ i : Fin 3, (c1 ^ (i : ℕ))⁻¹ * zB * c1 ^ (i : ℕ) ∈ bSub := by
  decide +kernel

theorem zB_mem_sylOf₂ : ∀ i : Fin 3, (c2 ^ (i : ℕ))⁻¹ * zB * c2 ^ (i : ℕ) ∈ bSub := by
  decide +kernel

theorem zB_ne_one : zB ≠ 1 := by decide

theorem hcos₁ : ∀ y ∈ L3.ptSub e1, ∃ j : Fin 3, (c1 ^ (j : ℕ))⁻¹ * y ∈ bSub :=
  fun _ hy => exists_coset1 hy

theorem hcos₂ : ∀ y ∈ L3.stabSub P12, ∃ j : Fin 3, (c2 ^ (j : ℕ))⁻¹ * y ∈ bSub :=
  fun _ hy => exists_coset2 hy

theorem hdist₁ : ∀ i j : Fin 3, i ≠ j → (c1 ^ (j : ℕ))⁻¹ * c1 ^ (i : ℕ) ∉ bSub :=
  fun i j hij h => distinct1_check i j hij (mem_bSub.mp h)

theorem hdist₂ : ∀ i j : Fin 3, i ≠ j → (c2 ^ (j : ℕ))⁻¹ * c2 ^ (i : ℕ) ∉ bSub :=
  fun i j hij h => distinct2_check i j hij (mem_bSub.mp h)

theorem bSub_le_stabSub : bSub ≤ L3.stabSub P12 := inf_le_right

theorem zB_mem_sylOf_c1 (i : Fin 3) : zB ∈ sylOf c1 i := mem_conjSub.mpr (zB_mem_sylOf₁ i)

theorem zB_mem_sylOf_c2 (i : Fin 3) : zB ∈ sylOf c2 i := mem_conjSub.mpr (zB_mem_sylOf₂ i)

end CFSG.Quasithin.H13.Ins314
