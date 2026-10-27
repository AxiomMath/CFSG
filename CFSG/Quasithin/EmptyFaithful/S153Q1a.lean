module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.S143Aux

public section

namespace CFSG.Quasithin

namespace S153Q

namespace Q1

open Equiv

theorem eq_one_of_transfer {Q : Type*} [Group Q] [Finite Q] [Group.IsPerfect Q]
    (P : Subgroup Q) (hP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) {ζ : Q}
    (hζc : ζ ∈ Subgroup.center Q) (hcop : Nat.Coprime P.index (orderOf ζ)) : ζ = 1 := by
  classical
  let _ : CommGroup ↥P :=
    { (inferInstance : Group ↥P) with
      mul_comm := fun a b => Subtype.ext (hP a a.2 b b.2) }
  let τ : Q →* ↥P := MonoidHom.transfer (MonoidHom.id ↥P)
  have h1 : τ ζ = 1 := by
    have hk : commutator Q ≤ τ.ker := Abelianization.commutator_subset_ker τ
    rw [Group.IsPerfect.commutator_eq_top] at hk
    exact hk (Subgroup.mem_top ζ)
  have h2 := MonoidHom.transfer_eq_pow (MonoidHom.id ↥P) ζ (fun k g₀ _ => by
      have hc : ζ ^ k ∈ Subgroup.center Q := Subgroup.pow_mem _ hζc k
      rw [Subgroup.mem_center_iff] at hc
      rw [mul_assoc, ← hc g₀]; group)
  have h3 : ζ ^ P.index = 1 := by
    have := congrArg Subtype.val (h2.symm.trans h1)
    simpa using this
  have h4 : orderOf ζ ∣ Nat.gcd P.index (orderOf ζ) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) dvd_rfl
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h4
  exact h4

@[expose] def c1 : Perm (Fin 6) := swap 0 1 * swap 1 2

@[expose] def c2 : Perm (Fin 6) := swap 3 4 * swap 4 5

@[expose] def d9 (p : Fin 3 × Fin 3) : Perm (Fin 6) := c1 ^ (p.1 : ℕ) * c2 ^ (p.2 : ℕ)

theorem d9_mul : ∀ p q : Fin 3 × Fin 3, ∃ r, d9 p * d9 q = d9 r := by decide

theorem d9_inv : ∀ p : Fin 3 × Fin 3, ∃ r, (d9 p)⁻¹ = d9 r := by decide

theorem d9_one : d9 (0, 0) = 1 := by decide

theorem d9_inj : Function.Injective d9 := by decide

theorem d9_sign : ∀ p : Fin 3 × Fin 3, Perm.sign (d9 p) = 1 := by decide

theorem c_facts : Perm.sign c1 = 1 ∧ Perm.sign c2 = 1 ∧ c1 * c2 * c1⁻¹ * c2⁻¹ = 1 ∧
    c1⁻¹ * (swap 4 5 * c1 * swap 4 5) = 1 ∧ c2 * (swap 4 5 * c2 * swap 4 5) = 1 := by decide

@[expose] def D9 : Subgroup (Perm (Fin 6)) where
  carrier := Set.range d9
  mul_mem' := by
    rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    obtain ⟨r, hr⟩ := d9_mul p q
    exact ⟨r, hr.symm⟩
  one_mem' := ⟨(0, 0), d9_one⟩
  inv_mem' := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨r, hr⟩ := d9_inv p
    exact ⟨r, hr.symm⟩

theorem card_D9 : Nat.card D9 = 9 := by
  have : Nat.card (Fin 3 × Fin 3) = Nat.card D9 := Nat.card_congr (Equiv.ofInjective d9 d9_inj)
  rw [← this, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin]

theorem D9_le : D9 ≤ alternatingGroup (Fin 6) := by
  rintro _ ⟨p, rfl⟩
  exact Perm.mem_alternatingGroup.2 (d9_sign p)

theorem relIndex_D9 : D9.relIndex (alternatingGroup (Fin 6)) = 40 := by
  have h := Subgroup.relIndex_mul_card D9 (alternatingGroup (Fin 6))
  rw [inf_eq_left.2 D9_le, card_D9, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin] at h
  have : (Nat.factorial 6) / 2 = 360 := by decide
  omega

section Cover

variable {Q : Type*} [Group Q] [Finite Q] [Group.IsPerfect Q]
  (hZ : Nat.card (Subgroup.center Q) = 3) (φ : Q →* Perm (Fin 6))
  (hker : ∀ q, φ q = 1 → q ∈ Subgroup.center Q) (hrange : φ.range = alternatingGroup (Fin 6))
include hZ hker hrange

theorem comm_ne {X Y : Q} (hX : φ X = c1) (hY : φ Y = c2) : X * Y ≠ Y * X := by
  intro hXY
  have hc : Commute X Y := hXY
  have key : ∀ a ∈ D9.comap φ, ∃ p : Fin 3 × Fin 3,
      (X ^ (p.1 : ℕ) * Y ^ (p.2 : ℕ))⁻¹ * a ∈ Subgroup.center Q := by
    intro a ha
    obtain ⟨p, hp⟩ := ha
    refine ⟨p, hker _ ?_⟩
    rw [map_mul, map_inv, map_mul, map_pow, map_pow, hX, hY]
    show (d9 p)⁻¹ * φ a = 1
    rw [hp, inv_mul_cancel]
  have hP : ∀ a ∈ D9.comap φ, ∀ b ∈ D9.comap φ, a * b = b * a := by
    intro a ha b hb
    obtain ⟨p, hpa⟩ := key a ha
    obtain ⟨q, hqb⟩ := key b hb
    have hxy : Commute (X ^ (p.1 : ℕ) * Y ^ (p.2 : ℕ)) (X ^ (q.1 : ℕ) * Y ^ (q.2 : ℕ)) := by
      have h1 : Commute (X ^ (p.1 : ℕ)) (X ^ (q.1 : ℕ) * Y ^ (q.2 : ℕ)) :=
        (Commute.pow_pow_self X _ _).mul_right (hc.pow_pow _ _)
      have h2 : Commute (Y ^ (p.2 : ℕ)) (X ^ (q.1 : ℕ) * Y ^ (q.2 : ℕ)) :=
        (hc.symm.pow_pow _ _).mul_right (Commute.pow_pow_self Y _ _)
      exact h1.mul_left h2
    generalize X ^ (p.1 : ℕ) * Y ^ (p.2 : ℕ) = x at hpa hxy
    generalize X ^ (q.1 : ℕ) * Y ^ (q.2 : ℕ) = y at hqb hxy
    generalize hκ : x⁻¹ * a = κ at hpa
    generalize hκ' : y⁻¹ * b = κ' at hqb
    have ea : a = x * κ := by rw [← hκ]; group
    have eb : b = y * κ' := by rw [← hκ']; group
    rw [ea, eb]
    have e1 : κ * y = y * κ := (Subgroup.mem_center_iff.mp hpa y).symm
    have e2 : κ' * x = x * κ' := (Subgroup.mem_center_iff.mp hqb x).symm
    have e3 : κ * κ' = κ' * κ := (Subgroup.mem_center_iff.mp hpa κ').symm
    calc x * κ * (y * κ') = x * (κ * y) * κ' := by group
      _ = x * y * (κ * κ') := by rw [e1]; group
      _ = y * x * (κ' * κ) := by rw [hxy.eq, e3]
      _ = y * (κ' * x) * κ := by rw [e2]; group
      _ = y * κ' * (x * κ) := by group
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Q) 3 (by rw [hZ])
  have hidx : (D9.comap φ).index = 40 := by
    rw [Subgroup.index_comap, hrange, relIndex_D9]
  have h1 := eq_one_of_transfer (D9.comap φ) hP ζ.2
    (by rw [hidx, Subgroup.orderOf_coe, hζ]; norm_num)
  have h2 : orderOf (ζ : Q) = 3 := by rw [Subgroup.orderOf_coe, hζ]
  rw [h1, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem inv_of_cover (α : Q →* Q) (hα : ∀ q, φ (α q) = swap 4 5 * φ q * swap 4 5)
    {ζ : Q} (hζ : ζ ∈ Subgroup.center Q) : α ζ = ζ⁻¹ := by
  obtain ⟨X, hX⟩ : c1 ∈ φ.range := by rw [hrange]; exact Perm.mem_alternatingGroup.2 c_facts.1
  obtain ⟨Y, hY⟩ : c2 ∈ φ.range := by
    rw [hrange]; exact Perm.mem_alternatingGroup.2 c_facts.2.1
  set γ := X * Y * X⁻¹ * Y⁻¹ with hγ
  have hγc : γ ∈ Subgroup.center Q := hker _ (by
    rw [hγ, map_mul, map_mul, map_mul, map_inv, map_inv, hX, hY]; exact c_facts.2.2.1)
  have hγ1 : γ ≠ 1 := by
    intro h
    apply comm_ne hZ φ hker hrange hX hY
    calc X * Y = γ * Y * X := by rw [hγ]; group
      _ = Y * X := by rw [h, one_mul]
  have hκ₁ : X⁻¹ * α X ∈ Subgroup.center Q := hker _ (by
    rw [map_mul, map_inv, hα, hX]; exact c_facts.2.2.2.1)
  have hκ₂ : Y * α Y ∈ Subgroup.center Q := hker _ (by
    rw [map_mul, hα, hY]; exact c_facts.2.2.2.2)
  have hαγ : α γ = γ⁻¹ := by
    generalize hk₁ : X⁻¹ * α X = κ₁ at hκ₁
    generalize hk₂ : Y * α Y = κ₂ at hκ₂
    have eX : α X = X * κ₁ := by rw [← hk₁]; group
    have eY : α Y = Y⁻¹ * κ₂ := by rw [← hk₂]; group
    have e1 := Subgroup.mem_center_iff.mp hκ₁
    have e2 := Subgroup.mem_center_iff.mp hκ₂
    have e3 := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hγc)
    have s1 : X * κ₁ * (Y⁻¹ * κ₂) * (X * κ₁)⁻¹ = X * (Y⁻¹ * κ₂) * X⁻¹ := by
      calc X * κ₁ * (Y⁻¹ * κ₂) * (X * κ₁)⁻¹ = X * (κ₁ * (Y⁻¹ * κ₂)) * κ₁⁻¹ * X⁻¹ := by group
        _ = X * ((Y⁻¹ * κ₂) * κ₁) * κ₁⁻¹ * X⁻¹ := by rw [← e1 (Y⁻¹ * κ₂)]
        _ = X * (Y⁻¹ * κ₂) * X⁻¹ := by group
    have s2 : X * (Y⁻¹ * κ₂) * X⁻¹ * (Y⁻¹ * κ₂)⁻¹ = X * Y⁻¹ * X⁻¹ * Y := by
      calc X * (Y⁻¹ * κ₂) * X⁻¹ * (Y⁻¹ * κ₂)⁻¹ = X * Y⁻¹ * (κ₂ * X⁻¹) * κ₂⁻¹ * Y := by group
        _ = X * Y⁻¹ * (X⁻¹ * κ₂) * κ₂⁻¹ * Y := by rw [← e2 X⁻¹]
        _ = X * Y⁻¹ * X⁻¹ * Y := by group
    have s3 : X * Y⁻¹ * X⁻¹ * Y = γ⁻¹ := by
      have h : X * Y⁻¹ * X⁻¹ * Y = Y⁻¹ * γ⁻¹ * Y := by rw [hγ]; group
      rw [h, e3 Y⁻¹]
      group
    rw [hγ, map_mul, map_mul, map_mul, map_inv, map_inv, eX, eY, s1, s2, ← hγ, s3]
  have hγ3 : γ ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := Subgroup.center Q) (x := ⟨γ, hγc⟩)
    rw [hZ] at h
    exact congrArg Subtype.val h
  have hord : orderOf γ = 3 := orderOf_eq_prime hγ3 hγ1
  have hZγ : Subgroup.center Q = Subgroup.zpowers γ := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hγc) ?_).symm
    rw [Nat.card_zpowers, hord, hZ]
  rw [hZγ] at hζ
  obtain ⟨k, rfl⟩ := hζ
  simp only
  rw [map_zpow, hαγ, inv_zpow]

end Cover

end Q1

end S153Q

end CFSG.Quasithin
