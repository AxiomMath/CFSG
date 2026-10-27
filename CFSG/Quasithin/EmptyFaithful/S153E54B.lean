module

public import CFSG.Quasithin.EmptyFaithful.S153E54A
public import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.Quasithin

namespace S153E54

open CFSG.Quasithin.S152O4

section Uniq

variable {Γ : Type*} [Group Γ]

@[expose] def prodHom (K₁ K₂ : Subgroup Γ) (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) :
    ↥K₁ × ↥K₂ →* Γ :=
  MonoidHom.noncommCoprod K₁.subtype K₂.subtype
    (fun a b => (hc a a.2 b b.2 : Commute (a : Γ) b))

theorem prodHom_apply (K₁ K₂ : Subgroup Γ) (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (u : ↥K₁ × ↥K₂) : prodHom K₁ K₂ hc u = (u.1 : Γ) * u.2 := rfl

theorem prodHom_inj (K₁ K₂ : Subgroup Γ) (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (h : K₁ ⊓ K₂ = ⊥) : Function.Injective (prodHom K₁ K₂ hc) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, b⟩ hab
  rw [prodHom_apply] at hab
  have hab' : (a : Γ) * b = 1 := hab
  have h1 : (a : Γ) ∈ K₁ ⊓ K₂ := ⟨a.2, by
    have : (a : Γ) = (b : Γ)⁻¹ := eq_inv_of_mul_eq_one_left hab'
    rw [this]; exact K₂.inv_mem b.2⟩
  rw [h, Subgroup.mem_bot] at h1
  have h2 : (b : Γ) = 1 := by rw [h1, one_mul] at hab'; exact hab'
  exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)

theorem exists_prodHom (K₁ K₂ : Subgroup Γ) (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) {x : Γ}
    (hx : x ∈ K₁ ⊔ K₂) : ∃ u : ↥K₁ × ↥K₂, prodHom K₁ K₂ hc u = x := by
  have hN : K₂ ≤ Subgroup.normalizer (K₁ : Set Γ) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro a
    have key : ∀ b ∈ K₂, ∀ a ∈ K₁, b * a * b⁻¹ = a := fun b hb a ha => by
      rw [← hc a ha b hb]; group
    constructor
    · intro ha
      rw [key b hb a ha]; exact ha
    · intro ha
      have h2 := key b⁻¹ (K₂.inv_mem hb) _ ha
      have e : b⁻¹ * (b * a * b⁻¹) * b⁻¹⁻¹ = a := by group
      rw [e] at h2
      rw [h2]; exact ha
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left K₁ K₂ hN
  have hx' : x ∈ ((K₁ ⊔ K₂ : Subgroup Γ) : Set Γ) := hx
  rw [hmul] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), by rw [prodHom_apply]⟩

theorem card_sup_of_comm {K₁ K₂ : Subgroup Γ} (hK : K₁ ⊓ K₂ = ⊥)
    (hKc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) :
    Nat.card ↥(K₁ ⊔ K₂) = Nat.card ↥K₁ * Nat.card ↥K₂ := by
  have hinj := prodHom_inj K₁ K₂ hKc hK
  have hrange : (prodHom K₁ K₂ hKc).range = K₁ ⊔ K₂ := by
    apply le_antisymm
    · rintro _ ⟨⟨a, b⟩, rfl⟩
      rw [prodHom_apply]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left a.2) (Subgroup.mem_sup_right b.2)
    · intro x hx
      obtain ⟨u, hu⟩ := exists_prodHom K₁ K₂ hKc hx
      exact ⟨u, hu⟩
  rw [← hrange, ← Nat.card_prod]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem gen_rel {L : Subgroup Γ} (e : ↥L ≃* DihedralGroup 3) :
    ∃ a s : Γ, a ∈ L ∧ s ∈ L ∧ a ≠ 1 ∧ a ^ 3 = 1 ∧ s ≠ 1 ∧ s ^ 2 = 1 ∧ s * a * s⁻¹ = a⁻¹ ∧
      ∀ x ∈ L, ∃ k : ℕ, x = a ^ k ∨ x = a ^ k * s := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := dih_rel
  refine ⟨(e.symm (DihedralGroup.r 1) : Γ), (e.symm (DihedralGroup.sr 0) : Γ),
    (e.symm _).2, (e.symm _).2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply h1
    have : e.symm (DihedralGroup.r 1) = 1 := Subtype.ext h
    simpa using congrArg e this
  · have : (e.symm (DihedralGroup.r 1)) ^ 3 = 1 := by rw [← map_pow, h2, map_one]
    exact congrArg Subtype.val this
  · intro h
    apply h3
    have : e.symm (DihedralGroup.sr 0) = 1 := Subtype.ext h
    simpa using congrArg e this
  · have : (e.symm (DihedralGroup.sr 0)) ^ 2 = 1 := by rw [← map_pow, h4, map_one]
    exact congrArg Subtype.val this
  · have : e.symm (DihedralGroup.sr 0) * e.symm (DihedralGroup.r 1) *
        (e.symm (DihedralGroup.sr 0))⁻¹ = (e.symm (DihedralGroup.r 1))⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul, h5, map_inv]
    exact congrArg Subtype.val this
  · intro x hx
    obtain ⟨k, hk⟩ := dih_cases (e ⟨x, hx⟩)
    refine ⟨(k : ℕ), ?_⟩
    rcases hk with hk | hk
    · left
      have : (⟨x, hx⟩ : ↥L) = (e.symm (DihedralGroup.r 1)) ^ (k : ℕ) := by
        rw [← map_pow, ← hk, MulEquiv.symm_apply_apply]
      exact congrArg Subtype.val this
    · right
      have : (⟨x, hx⟩ : ↥L) =
          (e.symm (DihedralGroup.r 1)) ^ (k : ℕ) * e.symm (DihedralGroup.sr 0) := by
        rw [← map_pow, ← map_mul, ← hk, MulEquiv.symm_apply_apply]
      exact congrArg Subtype.val this

theorem nat_card_of_equiv {L : Subgroup Γ} (e : ↥L ≃* DihedralGroup 3) : Nat.card ↥L = 6 := by
  rw [Nat.card_congr e.toEquiv, nat_card_dih]

theorem unique_decomp {K₁ K₂ L₁ L₂ : Subgroup Γ}
    (hK : K₁ ⊓ K₂ = ⊥) (hKc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hLc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hsup : K₁ ⊔ K₂ = L₁ ⊔ L₂)
    (eK₁ : ↥K₁ ≃* DihedralGroup 3) (eK₂ : ↥K₂ ≃* DihedralGroup 3)
    (eL₁ : ↥L₁ ≃* DihedralGroup 3) (eL₂ : ↥L₂ ≃* DihedralGroup 3) :
    (L₁ = K₁ ∧ L₂ = K₂) ∨ (L₁ = K₂ ∧ L₂ = K₁) := by
  have hιinj := prodHom_inj K₁ K₂ hKc hK
  set ι := prodHom K₁ K₂ hKc with hι
  set E : ↥K₁ × ↥K₂ ≃* Gam := MulEquiv.prodCongr eK₁ eK₂ with hE
  obtain ⟨a, σ, haL, hσL, ha1, ha3, hσ1, hσ2, hσa, hLgen⟩ := gen_rel eL₁
  obtain ⟨b, τ, hbL, hτL, hb1, hb3, hτ1, hτ2, hτb, hMgen⟩ := gen_rel eL₂
  have hΩ : ∀ x ∈ L₁ ⊔ L₂, ∃ u : ↥K₁ × ↥K₂, ι u = x := fun x hx =>
    exists_prodHom K₁ K₂ hKc (hsup ▸ hx)
  obtain ⟨ua, hua⟩ := hΩ a (Subgroup.mem_sup_left haL)
  obtain ⟨uσ, huσ⟩ := hΩ σ (Subgroup.mem_sup_left hσL)
  obtain ⟨ub, hub⟩ := hΩ b (Subgroup.mem_sup_right hbL)
  obtain ⟨uτ, huτ⟩ := hΩ τ (Subgroup.mem_sup_right hτL)
  have hone : ι 1 = 1 := map_one ι
  have h1 : ∀ u : ↥K₁ × ↥K₂, ι u ≠ 1 → E u ≠ 1 := fun u hu h => hu (by
    have : u = 1 := E.injective (by rw [h, map_one])
    rw [this, hone])
  have hp : ∀ (u : ↥K₁ × ↥K₂) (n : ℕ), (ι u) ^ n = 1 → (E u) ^ n = 1 := fun u n hu => by
    have : u ^ n = 1 := hιinj (by rw [map_pow, hu, hone])
    rw [← map_pow, this, map_one]
  have hcomm : ∀ u v : ↥K₁ × ↥K₂, ι u * ι v = ι v * ι u → E u * E v = E v * E u :=
    fun u v h => by
      have : u * v = v * u := hιinj (by rw [map_mul, map_mul, h])
      rw [← map_mul, ← map_mul, this]
  have hconj : ∀ u v : ↥K₁ × ↥K₂, ι u * ι v * (ι u)⁻¹ = (ι v)⁻¹ →
      E u * E v * (E u)⁻¹ = (E v)⁻¹ :=
    fun u v h => by
      have : u * v * u⁻¹ = v⁻¹ := hιinj (by rw [map_mul, map_mul, map_inv, map_inv, h])
      rw [← map_inv, ← map_mul, ← map_mul, this, map_inv]
  have key := lemmaG (E ua) (h1 ua (hua ▸ ha1)) (hp ua 3 (hua ▸ ha3)) (E uσ)
    (h1 uσ (huσ ▸ hσ1)) (hp uσ 2 (huσ ▸ hσ2)) (hconj uσ ua (by rw [hua, huσ]; exact hσa))
    (E ub) (h1 ub (hub ▸ hb1)) (hp ub 3 (hub ▸ hb3))
    (hcomm ua ub (by rw [hua, hub]; exact hLc a haL b hbL))
    (hcomm uσ ub (by rw [huσ, hub]; exact hLc σ hσL b hbL))
    (E uτ) (h1 uτ (huτ ▸ hτ1)) (hp uτ 2 (huτ ▸ hτ2)) (hconj uτ ub (by rw [hub, huτ]; exact hτb))
    (hcomm ua uτ (by rw [hua, huτ]; exact hLc a haL τ hτL))
    (hcomm uσ uτ (by rw [huσ, huτ]; exact hLc σ hσL τ hτL))
  have hmem₁ : ∀ (u : ↥K₁ × ↥K₂), (E u).2 = 1 → ι u ∈ K₁ := fun u hu => by
    have h : u.2 = 1 := by
      have : eK₂ u.2 = 1 := hu
      simpa using this
    rw [prodHom_apply, h]
    simp
  have hmem₂ : ∀ (u : ↥K₁ × ↥K₂), (E u).1 = 1 → ι u ∈ K₂ := fun u hu => by
    have h : u.1 = 1 := by
      have : eK₁ u.1 = 1 := hu
      simpa using this
    rw [prodHom_apply, h]
    simp
  have c₁ := nat_card_of_equiv eK₁
  have c₂ := nat_card_of_equiv eK₂
  have d₁ := nat_card_of_equiv eL₁
  have d₂ := nat_card_of_equiv eL₂
  have : Finite ↥K₁ := Nat.finite_of_card_ne_zero (by rw [c₁]; norm_num)
  have : Finite ↥K₂ := Nat.finite_of_card_ne_zero (by rw [c₂]; norm_num)
  rcases key with ⟨k1, k2, k3, k4⟩ | ⟨k1, k2, k3, k4⟩
  · left
    have haK : a ∈ K₁ := hua ▸ hmem₁ ua k1
    have hσK : σ ∈ K₁ := huσ ▸ hmem₁ uσ k2
    have hbK : b ∈ K₂ := hub ▸ hmem₂ ub k3
    have hτK : τ ∈ K₂ := huτ ▸ hmem₂ uτ k4
    have hle₁ : L₁ ≤ K₁ := fun x hx => by
      obtain ⟨k, hk | hk⟩ := hLgen x hx
      · rw [hk]; exact K₁.pow_mem haK k
      · rw [hk]; exact K₁.mul_mem (K₁.pow_mem haK k) hσK
    have hle₂ : L₂ ≤ K₂ := fun x hx => by
      obtain ⟨k, hk | hk⟩ := hMgen x hx
      · rw [hk]; exact K₂.pow_mem hbK k
      · rw [hk]; exact K₂.mul_mem (K₂.pow_mem hbK k) hτK
    exact ⟨Subgroup.eq_of_le_of_card_ge hle₁ (by rw [c₁, d₁]),
      Subgroup.eq_of_le_of_card_ge hle₂ (by rw [c₂, d₂])⟩
  · right
    have haK : a ∈ K₂ := hua ▸ hmem₂ ua k1
    have hσK : σ ∈ K₂ := huσ ▸ hmem₂ uσ k2
    have hbK : b ∈ K₁ := hub ▸ hmem₁ ub k3
    have hτK : τ ∈ K₁ := huτ ▸ hmem₁ uτ k4
    have hle₁ : L₁ ≤ K₂ := fun x hx => by
      obtain ⟨k, hk | hk⟩ := hLgen x hx
      · rw [hk]; exact K₂.pow_mem haK k
      · rw [hk]; exact K₂.mul_mem (K₂.pow_mem haK k) hσK
    have hle₂ : L₂ ≤ K₁ := fun x hx => by
      obtain ⟨k, hk | hk⟩ := hMgen x hx
      · rw [hk]; exact K₁.pow_mem hbK k
      · rw [hk]; exact K₁.mul_mem (K₁.pow_mem hbK k) hτK
    exact ⟨Subgroup.eq_of_le_of_card_ge hle₁ (by rw [c₂, d₁]),
      Subgroup.eq_of_le_of_card_ge hle₂ (by rw [c₁, d₂])⟩

end Uniq

end S153E54

end CFSG.Quasithin
