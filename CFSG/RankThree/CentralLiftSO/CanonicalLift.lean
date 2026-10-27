module

public import CFSG.RankThree.CentralLift.LinearRootRelations

public section

namespace CFSG.RankThree.CentralLiftSO.Lift

open Matrix CFSG.LieType.CentralExt
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (sl2Diag sl2W coe_sl2Diag coe_sl2W)
open CFSG.LieType.Chevalley (uSL vSL coe_uSL coe_vSL)
open CFSG.RankThree.CentralLift.LinearRoots (uSL_add uSL_zero)

section SL2

variable {k : Type} [Field k]

theorem vSL_add (a b : k) : vSL (a + b) = vSL a * vSL b := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun x y => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_vSL, coe_vSL, coe_vSL]
  fin_cases x <;> fin_cases y <;> simp [mul_apply, Fin.sum_univ_two, add_comm]

theorem vSL_zero : vSL (0 : k) = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun x y => ?_
  rw [coe_vSL]
  fin_cases x <;> fin_cases y <;> simp

theorem uSL_inv (t : k) : (uSL t)⁻¹ = uSL (-t) :=
  inv_eq_of_mul_eq_one_right (by rw [← uSL_add, add_neg_cancel, uSL_zero])

theorem vSL_inv (t : k) : (vSL t)⁻¹ = vSL (-t) :=
  inv_eq_of_mul_eq_one_right (by rw [← vSL_add, add_neg_cancel, vSL_zero])

theorem uSL_pow (t : k) (n : ℕ) : uSL t ^ n = uSL ((n : k) * t) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, uSL_zero]
  | succ n ih => rw [pow_succ, ih, ← uSL_add, Nat.cast_succ, add_mul, one_mul]

theorem vSL_pow (t : k) (n : ℕ) : vSL t ^ n = vSL ((n : k) * t) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, vSL_zero]
  | succ n ih => rw [pow_succ, ih, ← vSL_add, Nat.cast_succ, add_mul, one_mul]

theorem uSL_mul_sl2W {t : k} (ht : t ≠ 0) :
    uSL t * (sl2W : SpecialLinearGroup (Fin 2) k) =
      vSL t⁻¹ * sl2Diag (Units.mk0 t ht) * uSL (-t⁻¹) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun x y => ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL, coe_sl2W, coe_sl2Diag,
    Units.val_mk0, Units.val_inv_eq_inv_val]
  fin_cases x <;> fin_cases y <;> simp [mul_apply, Fin.sum_univ_two, ht]

variable {E : Type*} [Group E] [Fact (ringChar k).Prime]

theorem exists_orderOf_map_uSL (φ : SpecialLinearGroup (Fin 2) k →* E) (t : k) :
    ∃ n : ℕ, orderOf (φ (uSL t)) = ringChar k ^ n := by
  refine exists_orderOf_eq_pow_of_pow_eq_one (n := 1) ?_
  rw [pow_one, ← map_pow, uSL_pow, CharP.cast_eq_zero, zero_mul, uSL_zero, map_one]

theorem exists_orderOf_map_vSL (φ : SpecialLinearGroup (Fin 2) k →* E) (t : k) :
    ∃ n : ℕ, orderOf (φ (vSL t)) = ringChar k ^ n := by
  refine exists_orderOf_eq_pow_of_pow_eq_one (n := 1) ?_
  rw [pow_one, ← map_pow, vSL_pow, CharP.cast_eq_zero, zero_mul, vSL_zero, map_one]

end SL2

section Lift

variable {E G : Type*} [Group E] [Group G] {π : E →* G} {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
theorem exists_orderOf_conj (e : E) {x : E} (hx : ∃ n : ℕ, orderOf x = p ^ n) :
    ∃ n : ℕ, orderOf (e * x * e⁻¹) = p ^ n := by
  obtain ⟨n, hn⟩ := hx
  exact ⟨n, by rw [← hn]; exact MulEquiv.orderOf_eq (MulAut.conj e) x⟩

omit [Fact p.Prime] in
theorem mem_normalizer_of_conj {S : Subgroup E} {e : E} (h1 : ∀ x ∈ S, e * x * e⁻¹ ∈ S)
    (h2 : ∀ x ∈ S, e⁻¹ * x * e ∈ S) : e ∈ Subgroup.normalizer (S : Set E) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  simpa [mul_assoc] using h2 _ hx

variable [Finite E] (hcen : π.ker ≤ Subgroup.center E)
include hcen

theorem mem_liftSubgroup_of {V : Subgroup G} (hV : IsPGroup p V) {x : E} (hx : π x ∈ V)
    (hxo : ∃ n : ℕ, orderOf x = p ^ n) : x ∈ liftSubgroup p π V :=
  (mem_liftSubgroup_iff hcen hV).2 ⟨hx, hxo⟩

theorem liftSubgroup_mono {V W : Subgroup G} (hW : IsPGroup p W) (hVW : V ≤ W) :
    liftSubgroup p π V ≤ liftSubgroup p π W := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := (mem_liftSubgroup_iff hcen (hW.to_le hVW)).1 hx
  exact mem_liftSubgroup_of hcen hW (hVW hx1) hx2

theorem conj_mem_liftSubgroup {V W : Subgroup G} (hV : IsPGroup p V) (hW : IsPGroup p W) {e : E}
    (he : ∀ u ∈ V, π e * u * (π e)⁻¹ ∈ W) {x : E} (hx : x ∈ liftSubgroup p π V) :
    e * x * e⁻¹ ∈ liftSubgroup p π W := by
  obtain ⟨hx1, hx2⟩ := (mem_liftSubgroup_iff hcen hV).1 hx
  refine mem_liftSubgroup_of hcen hW ?_ (exists_orderOf_conj e hx2)
  rw [map_mul, map_mul, map_inv]
  exact he _ hx1

theorem eq_one_of_mem_liftSubgroup_of_mem_ker (hC : ¬p ∣ Nat.card π.ker) {V : Subgroup G}
    (hV : IsPGroup p V) {x : E} (hx : x ∈ liftSubgroup p π V) (hx1 : π x = 1) : x = 1 := by
  obtain ⟨-, n, hn⟩ := (mem_liftSubgroup_iff hcen hV).1 hx
  exact eq_one_of_mem_ker hC hx1 (n := n) (by rw [← hn, pow_orderOf_eq_one])

theorem map_liftSubgroup (hπ : Function.Surjective π) (hC : ¬p ∣ Nat.card π.ker)
    {V : Subgroup G} (hV : IsPGroup p V) : (liftSubgroup p π V).map π = V := by
  refine le_antisymm (Subgroup.map_le_iff_le_comap.2 (liftSubgroup_le_comap hcen hV))
    fun u hu => ?_
  exact ⟨_, pLift_mem_liftSubgroup hπ hcen hC hV hu,
    map_pLift hπ hC (exists_orderOf_eq_pow_of_mem hV ⟨u, hu⟩)⟩

end Lift

end CFSG.RankThree.CentralLiftSO.Lift
