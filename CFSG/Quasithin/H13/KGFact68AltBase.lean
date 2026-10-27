module

public import CFSG.Quasithin.H13.KGFact68Base

public section

namespace CFSG.Quasithin.H13.KG68

open Equiv Equiv.Perm

section Quot

variable {X : Type} [Group X] (N : Subgroup X) [N.Characteristic]

@[expose] noncomputable def quotAut (α : MulAut X) : MulAut (X ⧸ N) :=
  QuotientGroup.congr N N α (Subgroup.characteristic_iff_map_eq.mp inferInstance α)

theorem quotAut_mk (α : MulAut X) (x : X) :
    quotAut N α (x : X ⧸ N) = ((α x : X) : X ⧸ N) :=
  rfl

theorem quotAut_mul (α β : MulAut X) : quotAut N (α * β) = quotAut N α * quotAut N β := by
  ext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rfl

theorem quotAut_one : quotAut N (1 : MulAut X) = 1 := by
  ext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rfl

variable {N} in
theorem eq_one_of_quotAut_eq_one (hN : N ≤ Subgroup.center X) (hperf : commutator X = ⊤)
    {α : MulAut X} (h : quotAut N α = 1) : α = 1 := by
  have hc : ∀ x : X, x⁻¹ * α x ∈ Subgroup.center X := by
    intro x
    have h1 := congrArg (fun φ : MulAut (X ⧸ N) => φ (x : X ⧸ N)) h
    simp only [quotAut_mk, MulAut.one_apply] at h1
    exact hN ((QuotientGroup.eq).mp h1.symm)
  let θ : X →* ↥(Subgroup.center X) :=
    { toFun := fun x => ⟨x⁻¹ * α x, hc x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => by
        apply Subtype.ext
        show (x * y)⁻¹ * α (x * y) = x⁻¹ * α x * (y⁻¹ * α y)
        have hz := Subgroup.mem_center_iff.mp (hc x) y⁻¹
        rw [map_mul]
        calc (x * y)⁻¹ * (α x * α y) = y⁻¹ * (x⁻¹ * α x) * α y := by group
          _ = (x⁻¹ * α x) * y⁻¹ * α y := by rw [hz]
          _ = x⁻¹ * α x * (y⁻¹ * α y) := by group }
  have hker : commutator X ≤ θ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (Subgroup.mem_center_iff.mp (θ b).2 (θ a : X))
  ext x
  have h1 : θ x = 1 := by
    rw [← MonoidHom.mem_ker]
    exact hker (hperf ▸ Subgroup.mem_top x)
  have h2 : x⁻¹ * α x = 1 := congrArg Subtype.val h1
  rw [inv_mul_eq_one] at h2
  exact h2.symm

end Quot

section Six

@[expose] def alt6c : alternatingGroup (Fin 6) :=
  ⟨swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def alt6d : alternatingGroup (Fin 6) :=
  ⟨swap 0 1 * swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def alt6P : Subgroup (alternatingGroup (Fin 6)) where
  carrier := {x | x = 1 ∨ x = alt6c ∨ x = alt6c ^ 2 ∨ x = alt6c ^ 3 ∨ x = alt6d ∨
    x = alt6d * alt6c ∨ x = alt6d * alt6c ^ 2 ∨ x = alt6d * alt6c ^ 3}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro x y hx hy
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide +kernel
  inv_mem' := by
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide +kernel

private theorem alt6P_list_card :
    ([1, alt6c, alt6c ^ 2, alt6c ^ 3, alt6d, alt6d * alt6c, alt6d * alt6c ^ 2,
      alt6d * alt6c ^ 3] : List (alternatingGroup (Fin 6))).toFinset.card = 8 := by
  decide +kernel

theorem card_alt6P : Nat.card alt6P = 8 := by
  classical
  rw [← alt6P_list_card, ← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  simp only [List.mem_toFinset, List.mem_cons, List.mem_nil_iff, or_false]
  rfl

theorem alt6c_mem : alt6c ∈ alt6P := Or.inr (Or.inl rfl)

theorem alt6d_mem : alt6d ∈ alt6P := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

theorem card_alt6P_eq : Nat.card alt6P =
    2 ^ (Nat.card (alternatingGroup (Fin 6))).factorization 2 := by
  rw [card_alt6P, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h : (Nat.factorial 6 / 2).factorization 2 = 3 := by
    rw [show Nat.factorial 6 / 2 = 2 ^ 3 * 45 by decide,
      Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
    simp [Nat.prime_two.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 45)]
  rw [h]
  norm_num

@[expose] noncomputable def alt6Sylow : Sylow 2 (alternatingGroup (Fin 6)) :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  Sylow.ofCard alt6P card_alt6P_eq

theorem alt6Sylow_coe : ((alt6Sylow : Sylow 2 (alternatingGroup (Fin 6))) :
    Subgroup (alternatingGroup (Fin 6))) = alt6P :=
  Sylow.coe_ofCard _ _

end Six

section Seven

@[expose] def alt7c : alternatingGroup (Fin 7) :=
  ⟨swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def alt7d : alternatingGroup (Fin 7) :=
  ⟨swap 0 1 * swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def alt7P : Subgroup (alternatingGroup (Fin 7)) where
  carrier := {x | x = 1 ∨ x = alt7c ∨ x = alt7c ^ 2 ∨ x = alt7c ^ 3 ∨ x = alt7d ∨
    x = alt7d * alt7c ∨ x = alt7d * alt7c ^ 2 ∨ x = alt7d * alt7c ^ 3}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro x y hx hy
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide +kernel
  inv_mem' := by
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide +kernel

private theorem alt7P_list_card :
    ([1, alt7c, alt7c ^ 2, alt7c ^ 3, alt7d, alt7d * alt7c, alt7d * alt7c ^ 2,
      alt7d * alt7c ^ 3] : List (alternatingGroup (Fin 7))).toFinset.card = 8 := by
  decide +kernel

theorem card_alt7P : Nat.card alt7P = 8 := by
  classical
  rw [← alt7P_list_card, ← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  simp only [List.mem_toFinset, List.mem_cons, List.mem_nil_iff, or_false]
  rfl

theorem alt7c_mem : alt7c ∈ alt7P := Or.inr (Or.inl rfl)

theorem alt7d_mem : alt7d ∈ alt7P := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

theorem card_alt7P_eq : Nat.card alt7P =
    2 ^ (Nat.card (alternatingGroup (Fin 7))).factorization 2 := by
  rw [card_alt7P, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h : (Nat.factorial 7 / 2).factorization 2 = 3 := by
    rw [show Nat.factorial 7 / 2 = 2 ^ 3 * 315 by decide,
      Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
    simp [Nat.prime_two.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 315)]
  rw [h]
  norm_num

@[expose] noncomputable def alt7Sylow : Sylow 2 (alternatingGroup (Fin 7)) :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  Sylow.ofCard alt7P card_alt7P_eq

theorem alt7Sylow_coe : ((alt7Sylow : Sylow 2 (alternatingGroup (Fin 7))) :
    Subgroup (alternatingGroup (Fin 7))) = alt7P :=
  Sylow.coe_ofCard _ _

end Seven

end CFSG.Quasithin.H13.KG68
