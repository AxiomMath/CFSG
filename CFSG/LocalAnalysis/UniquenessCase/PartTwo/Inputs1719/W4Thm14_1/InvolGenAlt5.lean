module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.InvolGenAut
public import CFSG.Quasithin.SteinbergCBAlternatingAut
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.SmallGroups

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Equiv Equiv.Perm CFSG.Quasithin.SteinbergCB

namespace InvolGenAlt5

@[expose] def c5 : Fin 5 → Perm (Fin 5) :=
  ![swap 0 4 * swap 4 1 * swap 1 2 * swap 2 3, swap 0 2 * swap 2 4 * swap 4 1 * swap 1 3,
    swap 0 1 * swap 1 4 * swap 4 3 * swap 3 2, swap 0 2 * swap 2 4 * swap 4 3 * swap 3 1,
    swap 0 3 * swap 3 4 * swap 4 2 * swap 2 1]

theorem c5_mem : ∀ i, c5 i ∈ alternatingGroup (Fin 5) := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

@[expose] def encP (σ : Perm (Fin 5)) : ℕ :=
  (σ 0 : ℕ) + 5 * (σ 1 : ℕ) + 25 * (σ 2 : ℕ) + 125 * (σ 3 : ℕ) + 625 * (σ 4 : ℕ)

@[expose] def tabA5 : List (ℕ × Fin 5 × Fin 5 × Fin 5) :=
  [(2430, 2, 0, 3), (2830, 0, 1, 3), (1730, 1, 0, 2), (2910, 0, 1, 2), (2410, 1, 1, 2),
    (2690, 1, 0, 2), (1490, 0, 0, 1), (1070, 0, 1, 3), (970, 3, 0, 4), (2926, 2, 0, 1),
    (2426, 0, 0, 2), (2826, 1, 0, 0), (1726, 0, 0, 2), (2882, 1, 0, 2), (2382, 0, 0, 3),
    (2642, 0, 0, 2), (1022, 4, 0, 0), (2558, 0, 1, 2), (1358, 2, 0, 1), (2538, 2, 0, 1),
    (698, 3, 0, 4), (434, 0, 1, 2), (334, 1, 0, 1), (414, 1, 0, 0), (194, 2, 0, 0)]

@[expose] def lookA5 (σ : Perm (Fin 5)) : Fin 5 × Fin 5 × Fin 5 :=
  (tabA5.lookup (encP σ)).getD (0, 0, 0)

@[expose] def kA5 (σ z : Perm (Fin 5)) : Perm (Fin 5) := z * σ * z⁻¹ * σ

theorem alt5_check : ∀ σ : Perm (Fin 5), σ * σ = 1 → σ ≠ 1 →
    kA5 σ (c5 (lookA5 σ).1) ^ 3 = 1 ∧ kA5 σ (c5 (lookA5 σ).1) ≠ 1 ∧
      (kA5 σ (c5 (lookA5 σ).1) * kA5 σ (c5 (lookA5 σ).2.1) * kA5 σ (c5 (lookA5 σ).2.2)) ^ 5 = 1 ∧
      kA5 σ (c5 (lookA5 σ).1) * kA5 σ (c5 (lookA5 σ).2.1) * kA5 σ (c5 (lookA5 σ).2.2) ≠ 1 := by
  decide +kernel

theorem coe_mul_conjPerm_inv {σ : Perm (Fin 5)} (hσ : σ * σ = 1) (y : alternatingGroup (Fin 5)) :
    ((y * (conjPerm 5 σ y)⁻¹ : alternatingGroup (Fin 5)) : Perm (Fin 5)) = kA5 σ y := by
  have hσi : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
  rw [Subgroup.coe_mul, Subgroup.coe_inv, conjPerm_apply, kA5]
  calc (y : Perm (Fin 5)) * (σ * y * σ⁻¹)⁻¹ = y * σ * (y : Perm (Fin 5))⁻¹ * σ⁻¹ := by group
    _ = _ := by rw [hσi]

theorem eq_top_of_orderOf {K : Subgroup (alternatingGroup (Fin 5))} {a b : alternatingGroup (Fin 5)}
    (ha : a ∈ K) (hb : b ∈ K) (ha3 : (a : Perm (Fin 5)) ^ 3 = 1) (ha1 : (a : Perm (Fin 5)) ≠ 1)
    (hb5 : (b : Perm (Fin 5)) ^ 5 = 1) (hb1 : (b : Perm (Fin 5)) ≠ 1) : K = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set K' := K.map (alternatingGroup (Fin 5)).subtype
  have hmem : ∀ x ∈ K, (x : Perm (Fin 5)) ∈ K' := fun x hx => Subgroup.mem_map_of_mem _ hx
  have h3 : 3 ∣ Nat.card K' := by
    have := Subgroup.orderOf_dvd_natCard K' (hmem a ha)
    rwa [orderOf_eq_prime ha3 ha1] at this
  have h5 : 5 ∣ Nat.card K' := by
    have := Subgroup.orderOf_dvd_natCard K' (hmem b hb)
    rwa [orderOf_eq_prime hb5 hb1] at this
  have hle := CFSG.Quasithin.F53.alt5_le_of_dvd K'
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h5)
  exact eq_top_iff.2 fun g _ =>
    (Subgroup.mem_map_iff_mem (Subgroup.subtype_injective _)).1 (hle g.2)

end InvolGenAlt5

open InvolGenAlt5 in
theorem involGenAut_alt5 : InvolGenAut (alternatingGroup (Fin 5)) := by
  intro α hαα hα1
  obtain ⟨σ, rfl⟩ := conjPerm_surjective (n := 5) (Or.inl rfl) α
  have hσσ : σ * σ = 1 := conjPerm_injective (n := 5) (by norm_num) (by rw [map_mul, hαα, map_one])
  have hσ1 : σ ≠ 1 := fun h => hα1 (by rw [h, map_one])
  obtain ⟨h3, h3', h5, h5'⟩ := alt5_check σ hσσ hσ1
  have e := coe_mul_conjPerm_inv hσσ
  set y₁ : alternatingGroup (Fin 5) := ⟨c5 (lookA5 σ).1, c5_mem _⟩
  set y₂ : alternatingGroup (Fin 5) := ⟨c5 (lookA5 σ).2.1, c5_mem _⟩
  set y₃ : alternatingGroup (Fin 5) := ⟨c5 (lookA5 σ).2.2, c5_mem _⟩
  refine ⟨y₁, y₂, y₃, eq_top_of_orderOf (a := y₁ * (conjPerm 5 σ y₁)⁻¹)
    (b := y₁ * (conjPerm 5 σ y₁)⁻¹ * (y₂ * (conjPerm 5 σ y₂)⁻¹) * (y₃ * (conjPerm 5 σ y₃)⁻¹))
    (Subgroup.subset_closure (by simp)) (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
      (Subgroup.subset_closure (by simp))) ?_ ?_ ?_ ?_⟩
  · rw [e]; exact h3
  · rw [e]; exact h3'
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, e, e, e]; exact h5
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, e, e, e]; exact h5'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
