module

public import CFSG.Quasithin.H13.A5Z1367g
public import CFSG.Quasithin.EmptyFaithful.SzN2Lin

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace A5SN

open Equiv

@[expose] def D : Fin 8 → Perm (Fin 5) :=
  ![1, swap 0 1 * swap 1 2 * swap 2 3, swap 0 2 * swap 1 3, swap 2 3 * swap 1 2 * swap 0 1,
    swap 0 2, swap 1 3, swap 0 1 * swap 2 3, swap 0 3 * swap 1 2]

theorem D_mul : ∀ i j : Fin 8, ∃ k : Fin 8, D i * D j = D k := by decide

theorem D_inv : ∀ i : Fin 8, ∃ k : Fin 8, (D i)⁻¹ = D k := by decide

theorem D_inj : Function.Injective D := by decide

theorem key : ∀ y : Perm (Fin 5), (∃ i : Fin 8, y * D 1 * y⁻¹ = D i) →
    (∃ i : Fin 8, y * D 4 * y⁻¹ = D i) → y ^ 3 = 1 → y = 1 := by
  decide +kernel

@[expose] def P₀ : Subgroup (Perm (Fin 5)) where
  carrier := {x | ∃ i, x = D i}
  mul_mem' := by
    rintro x y ⟨i, rfl⟩ ⟨j, rfl⟩
    exact D_mul i j
  one_mem' := ⟨0, rfl⟩
  inv_mem' := by
    rintro x ⟨i, rfl⟩
    exact D_inv i

theorem card_P₀ : Nat.card P₀ = 8 := by
  let f : Fin 8 → P₀ := fun i => ⟨D i, i, rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun i j h => D_inj (congrArg Subtype.val h), ?_⟩
    rintro ⟨x, i, rfl⟩
    exact ⟨i, rfl⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem isSylowTwoOf_P₀ : IsSylowTwoOf P₀ ⊤ := by
  refine ⟨le_top, IsPGroup.of_card (n := 3) (by rw [card_P₀]; norm_num), ?_⟩
  show ¬ 2 ∣ P₀.relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  have h := P₀.card_mul_index
  rw [card_P₀, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  have h15 : P₀.index = 15 := by
    have : (Nat.factorial 5) = 120 := by decide
    omega
  rw [h15]
  decide

end A5SN

theorem factSylowNormS5 : FactSylowNormS5 := by
  intro P hP hidx x hx h3
  have hPs : IsSylowTwoOf P ⊤ := ⟨le_top, hP, by
    show ¬ 2 ∣ P.relIndex ⊤
    rwa [Subgroup.relIndex_top_right]⟩
  obtain ⟨φ, hφ⟩ := SzN2.exists_mulEquiv_map_eq A5SN.isSylowTwoOf_P₀ hPs
  have hy : φ x ∈ Subgroup.normalizer (A5SN.P₀ : Set (Equiv.Perm (Fin 5))) := by
    rw [← hφ]
    exact Subgroup.le_normalizer_map _ ⟨x, hx, rfl⟩
  have hy3 : orderOf (φ x) = 3 := by rw [MulEquiv.orderOf_eq]; exact h3
  have hpow : φ x ^ 3 = 1 := hy3 ▸ pow_orderOf_eq_one _
  have hne : φ x ≠ 1 := fun h => by
    rw [h, orderOf_one] at hy3
    exact absurd hy3 (by norm_num)
  exact hne (A5SN.key (φ x) ((Subgroup.mem_normalizer_iff.mp hy _).mp ⟨1, rfl⟩)
    ((Subgroup.mem_normalizer_iff.mp hy _).mp ⟨4, rfl⟩) hpow)

theorem not_three_dvd_two_pow_sub_one {m : ℕ} (hm : Odd m) : ¬ 3 ∣ 2 ^ m - 1 := by
  obtain ⟨k, rfl⟩ := hm
  have h1 : 2 ^ (2 * k + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * k + 1) = x at h1 ⊢
  omega

theorem factSylowNormSL3 : FactSylowNormSL3 := by
  intro F _ _ m hm hF
  have hchar : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow hF
  have h3 : ¬ 3 ∣ Nat.card F - 1 := hF ▸ not_three_dvd_two_pow_sub_one hm
  have hSL : ∀ P : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F), IsPGroup 2 P →
      ¬ 2 ∣ P.index → ∀ x ∈ Subgroup.normalizer (P : Set (Matrix.SpecialLinearGroup (Fin 3) F)),
        orderOf x ≠ 3 := by
    intro P hP hidx x hx
    have hPs : IsSylowTwoOf P ⊤ := ⟨le_top, hP, by
    show ¬ 2 ∣ P.relIndex ⊤
    rwa [Subgroup.relIndex_top_right]⟩
    obtain ⟨φ, hφ⟩ := SzN2.exists_mulEquiv_map_eq
      (SzN2.isSylowTwoOf_unitriangular (K := F) (n := 3) (by norm_num)) hPs
    have hb : φ x ∈ upperTriangular 3 F := by
      rw [← normalizer_unitriangular, ← hφ]
      exact Subgroup.le_normalizer_map _ ⟨x, hx, rfl⟩
    rw [← MulEquiv.orderOf_eq φ]
    exact SzN2.orderOf_ne_three_of_mem_upperTriangular ⟨m, hF⟩ h3 hb
  intro P hP hidx x hx h
  exact false_of_sylowNorm (statedSLEquivSL 3 F) hSL hP hidx hx h

end CFSG.Quasithin.H13.A5
