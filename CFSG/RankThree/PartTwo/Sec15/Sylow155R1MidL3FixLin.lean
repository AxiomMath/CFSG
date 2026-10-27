module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import CFSG.GroupTheory.AutomorphismAction.MapEqOfMapsTo

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1.L3Fix

section Cyclic

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem add_self_eq_zero_of_charTwo [CharP F 2] (v : V) : v + v = 0 := by
  rw [← two_smul F v, CharTwo.two_eq_zero, zero_smul]

def fixSp (y : V →ₗ[F] V) : Submodule F V where
  carrier := {v | y v = v}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_add, ha, hb]
  zero_mem' := by simp
  smul_mem' c v hv := by
    simp only [Set.mem_setOf_eq] at hv ⊢
    rw [map_smul, hv]

def kerSum (y : V →ₗ[F] V) : Submodule F V where
  carrier := {v | v + y v + y (y v) = 0}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
    calc a + b + (y a + y b) + (y (y a) + y (y b))
        = (a + y a + y (y a)) + (b + y b + y (y b)) := by abel
      _ = 0 := by rw [ha, hb, add_zero]
  zero_mem' := by simp
  smul_mem' c v hv := by
    simp only [Set.mem_setOf_eq, map_smul] at hv ⊢
    rw [← smul_add, ← smul_add, hv, smul_zero]

theorem mem_fixSp {y : V →ₗ[F] V} {v : V} : v ∈ fixSp y ↔ y v = v := Iff.rfl

theorem mem_kerSum {y : V →ₗ[F] V} {v : V} : v ∈ kerSum y ↔ v + y v + y (y v) = 0 :=
  Iff.rfl

variable [CharP F 2] {y : V →ₗ[F] V}

theorem sum_mem_fixSp (hy3 : ∀ v, y (y (y v)) = v) (v : V) : v + y v + y (y v) ∈ fixSp y := by
  rw [mem_fixSp, map_add, map_add, hy3]
  abel

theorem sum'_mem_kerSum (hy3 : ∀ v, y (y (y v)) = v) (v : V) : y v + y (y v) ∈ kerSum y := by
  simp only [mem_kerSum, map_add, hy3]
  have h1 := add_self_eq_zero_of_charTwo (F := F) v
  have h2 := add_self_eq_zero_of_charTwo (F := F) (y v)
  have h3 := add_self_eq_zero_of_charTwo (F := F) (y (y v))
  calc y v + y (y v) + (y (y v) + v) + (v + y v)
      = (v + v) + (y v + y v) + (y (y v) + y (y v)) := by abel
    _ = 0 := by rw [h1, h2, h3]; simp

theorem isCompl_fixSp_kerSum (hy3 : ∀ v, y (y (y v)) = v) : IsCompl (fixSp y) (kerSum y) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    rw [mem_fixSp] at hx
    rw [mem_kerSum, hx, hx] at hx'
    have h := add_self_eq_zero_of_charTwo (F := F) x
    rw [h, zero_add] at hx'
    exact hx'
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hv : v = (v + y v + y (y v)) + (y v + y (y v)) := by
      have h1 := add_self_eq_zero_of_charTwo (F := F) (y v)
      have h2 := add_self_eq_zero_of_charTwo (F := F) (y (y v))
      calc v = v + ((y v + y v) + (y (y v) + y (y v))) := by rw [h1, h2]; simp
        _ = _ := by abel
    rw [hv]
    exact Submodule.add_mem_sup (sum_mem_fixSp hy3 v) (sum'_mem_kerSum hy3 v)

theorem sum_mem_of_invariant {U : Submodule F V} (hU : ∀ u ∈ U, y u ∈ U) {u : V} (hu : u ∈ U) :
    u + y u + y (y u) ∈ U :=
  U.add_mem (U.add_mem hu (hU u hu)) (hU _ (hU u hu))

theorem sum'_mem_of_invariant {U : Submodule F V} (hU : ∀ u ∈ U, y u ∈ U) {u : V} (hu : u ∈ U) :
    y u + y (y u) ∈ U :=
  U.add_mem (hU u hu) (hU _ (hU u hu))

theorem kerSum_invariant {w : V} (hw : w ∈ kerSum y) : y w ∈ kerSum y := by
  rw [mem_kerSum] at hw ⊢
  rw [← map_add, ← map_add, hw, map_zero]

theorem linearIndependent_pair (hω : ∀ ω : F, ω ^ 2 + ω + 1 ≠ 0) {w : V} (hw : w ∈ kerSum y)
    (hw0 : w ≠ 0) : LinearIndependent F ![w, y w] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    rw [zero_smul, add_zero] at hst
    rcases smul_eq_zero.mp hst with h | h
    · exact ⟨h, rfl⟩
    · exact absurd h hw0
  · exfalso
    have hyw : y w = (-(s / t)) • w := by
      have : t • y w = -(s • w) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]
        exact hst
      calc y w = t⁻¹ • (t • y w) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = t⁻¹ • (-(s • w)) := by rw [this]
        _ = (-(s / t)) • w := by
          rw [smul_neg, smul_smul, ← neg_smul]
          congr 1
          rw [div_eq_inv_mul]
    set c : F := -(s / t) with hc
    have hyyw : y (y w) = c ^ 2 • w := by
      rw [hyw, map_smul, hyw, smul_smul, sq]
    have hw' : w + y w + y (y w) = 0 := hw
    rw [hyyw, hyw] at hw'
    have : (1 + c + c ^ 2) • w = 0 := by
      rw [add_smul, add_smul, one_smul]
      exact hw'
    rcases smul_eq_zero.mp this with h | h
    · exact hω c (by rw [← h]; ring)
    · exact hw0 h

section Classification

variable [FiniteDimensional F V]

theorem two_le_finrank_of_invariant (hω : ∀ ω : F, ω ^ 2 + ω + 1 ≠ 0) {U : Submodule F V}
    (hU : ∀ u ∈ U, y u ∈ U) (hUk : U ≤ kerSum y) (hU0 : U ≠ ⊥) : 2 ≤ Module.finrank F U := by
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  have hli := linearIndependent_pair hω (y := y) (hUk hu) hu0
  have hT : Module.finrank F (Submodule.span F (Set.range ![u, y u])) = 2 := by
    rw [finrank_span_eq_card hli]
    simp
  have hle : Submodule.span F (Set.range ![u, y u]) ≤ U := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hu
    · exact hU u hu
  rw [← hT]
  exact Submodule.finrank_mono hle

variable (hy3 : ∀ v, y (y (y v)) = v) (hω : ∀ ω : F, ω ^ 2 + ω + 1 ≠ 0)
  (hV : Module.finrank F V = 3) (hy1 : ∃ v, y v ≠ v) (hfix : ∃ v, v ≠ 0 ∧ y v = v)
include hy3 hω hV hy1 hfix

theorem finrank_fixSp_kerSum :
    Module.finrank F (fixSp y) = 1 ∧ Module.finrank F (kerSum y) = 2 := by
  have hsum := Submodule.finrank_add_eq_of_isCompl (isCompl_fixSp_kerSum hy3)
  rw [hV] at hsum
  have h1 : 1 ≤ Module.finrank F (fixSp y) := by
    rw [Submodule.one_le_finrank_iff]
    obtain ⟨v, hv0, hv⟩ := hfix
    intro h
    have : v ∈ fixSp y := hv
    rw [h, Submodule.mem_bot] at this
    exact hv0 this
  have h2 : 2 ≤ Module.finrank F (kerSum y) := by
    refine two_le_finrank_of_invariant hω (fun u hu => kerSum_invariant hu) le_rfl ?_
    intro h
    obtain ⟨v, hv⟩ := hy1
    apply hv
    have e1 : ∀ v, y (y v) = y v := fun v => by
      have hmem := sum'_mem_kerSum hy3 v
      rw [h, Submodule.mem_bot] at hmem
      exact add_left_cancel (hmem.trans (add_self_eq_zero_of_charTwo (F := F) (y v)).symm)
    have h3 := e1 (y v)
    rw [hy3, e1 v] at h3
    exact h3.symm
  omega

theorem eq_bot_or_eq_fixSp {S : Submodule F V} (hS : S ≤ fixSp y) : S = ⊥ ∨ S = fixSp y := by
  by_cases h : S = ⊥
  · exact Or.inl h
  · refine Or.inr (Submodule.eq_of_le_of_finrank_eq hS ?_)
    have h1 : 1 ≤ Module.finrank F S := Submodule.one_le_finrank_iff.mpr h
    have h2 := Submodule.finrank_mono hS
    have h3 := (finrank_fixSp_kerSum hy3 hω hV hy1 hfix).1
    omega

theorem eq_bot_or_eq_kerSum {S : Submodule F V} (hS : ∀ u ∈ S, y u ∈ S) (hSk : S ≤ kerSum y) :
    S = ⊥ ∨ S = kerSum y := by
  by_cases h : S = ⊥
  · exact Or.inl h
  · refine Or.inr (Submodule.eq_of_le_of_finrank_eq hSk ?_)
    have h1 := two_le_finrank_of_invariant hω hS hSk h
    have h2 := Submodule.finrank_mono hSk
    have h3 := (finrank_fixSp_kerSum hy3 hω hV hy1 hfix).2
    omega

theorem invariant_cases {U : Submodule F V} (hU : ∀ u ∈ U, y u ∈ U) :
    U = ⊥ ∨ U = fixSp y ∨ U = kerSum y ∨ U = ⊤ := by
  have hdec : U ≤ (U ⊓ fixSp y) ⊔ (U ⊓ kerSum y) := by
    intro u hu
    have hv : u = (u + y u + y (y u)) + (y u + y (y u)) := by
      have h1 := add_self_eq_zero_of_charTwo (F := F) (y u)
      have h2 := add_self_eq_zero_of_charTwo (F := F) (y (y u))
      calc u = u + ((y u + y u) + (y (y u) + y (y u))) := by rw [h1, h2]; simp
        _ = _ := by abel
    rw [hv]
    exact Submodule.add_mem_sup
      ⟨sum_mem_of_invariant hU hu, sum_mem_fixSp hy3 u⟩
      ⟨sum'_mem_of_invariant hU hu, sum'_mem_kerSum hy3 u⟩
  have h1 := eq_bot_or_eq_fixSp hy3 hω hV hy1 hfix (inf_le_right : U ⊓ fixSp y ≤ fixSp y)
  have h2 := eq_bot_or_eq_kerSum hy3 hω hV hy1 hfix
    (fun u hu => ⟨hU u hu.1, kerSum_invariant hu.2⟩ : ∀ u ∈ U ⊓ kerSum y, y u ∈ U ⊓ kerSum y)
    (inf_le_right : U ⊓ kerSum y ≤ kerSum y)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · left
    rw [h1, h2, bot_sup_eq] at hdec
    exact le_bot_iff.mp hdec
  · right; right; left
    rw [h1, h2, bot_sup_eq] at hdec
    refine le_antisymm hdec ?_
    rw [← h2]
    exact inf_le_left
  · right; left
    rw [h1, h2, sup_bot_eq] at hdec
    refine le_antisymm hdec ?_
    rw [← h1]
    exact inf_le_left
  · right; right; right
    rw [eq_top_iff, ← (isCompl_fixSp_kerSum hy3).sup_eq_top]
    exact sup_le (h1 ▸ inf_le_left) (h2 ▸ inf_le_left)

theorem eq_of_inf_ne_bot_of_invariant {U U' : Submodule F V} (hU : ∀ u ∈ U, y u ∈ U)
    (hU' : ∀ u ∈ U', y u ∈ U') (hU0 : U ≠ ⊥) (hU1 : U ≠ ⊤) (hU'0 : U' ≠ ⊥) (hU'1 : U' ≠ ⊤)
    (h : U ⊓ U' ≠ ⊥) : U = U' := by
  have hc := isCompl_fixSp_kerSum (y := y) hy3
  rcases invariant_cases hy3 hω hV hy1 hfix hU with h1 | h1 | h1 | h1 <;>
    rcases invariant_cases hy3 hω hV hy1 hfix hU' with h2 | h2 | h2 | h2 <;>
    first
    | exact absurd h1 hU0
    | exact absurd h1 hU1
    | exact absurd h2 hU'0
    | exact absurd h2 hU'1
    | exact h1.trans h2.symm
    | (exfalso; apply h; rw [h1, h2]; exact hc.inf_eq_bot)
    | (exfalso; apply h; rw [h1, h2]; exact hc.symm.inf_eq_bot)

theorem eq_zero_of_sq_eq_zero_of_comm {M : V →ₗ[F] V} (hM : ∀ v, M (M v) = 0)
    (hcomm : ∀ v, M (y v) = y (M v)) : M = 0 := by
  by_contra hne
  have hr : LinearMap.range M ≤ LinearMap.ker M := by
    rintro _ ⟨v, rfl⟩
    exact hM v
  have hr0 : LinearMap.range M ≠ ⊥ := by
    intro h
    apply hne
    ext v
    have : M v ∈ LinearMap.range M := ⟨v, rfl⟩
    rw [h, Submodule.mem_bot] at this
    simpa using this
  have hk1 : LinearMap.ker M ≠ ⊤ := by
    intro h
    apply hne
    ext v
    have : v ∈ LinearMap.ker M := by rw [h]; trivial
    simpa using this
  have heq : LinearMap.range M = LinearMap.ker M := by
    refine eq_of_inf_ne_bot_of_invariant hy3 hω hV hy1 hfix ?_ ?_ hr0
      (fun h => hk1 (top_le_iff.mp (h ▸ hr))) (fun h => hr0 (le_bot_iff.mp (h ▸ hr))) hk1
      (by rwa [inf_eq_left.mpr hr])
    · rintro _ ⟨v, rfl⟩
      exact ⟨y v, hcomm v⟩
    · intro u hu
      rw [LinearMap.mem_ker] at hu ⊢
      rw [hcomm, hu, map_zero]
  have hrn := LinearMap.finrank_range_add_finrank_ker M
  rw [hV, ← heq] at hrn
  omega

end Classification

end Cyclic

section SL3

open scoped MatrixGroups
open Matrix

variable {F : Type*} [Field F]

theorem exists_fixed_mem [Finite F] [CharP F 2] {R : Subgroup SL(3, F)} (hR : IsPGroup 2 R)
    {W : Submodule F (Fin 3 → F)} (hW0 : W ≠ ⊥)
    (hW : ∀ g ∈ R, ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W) :
    ∃ w ∈ W, w ≠ 0 ∧ ∀ g ∈ R, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI act : MulAction R W :=
    { smul := fun g w => ⟨(g : Matrix (Fin 3) (Fin 3) F) *ᵥ (w : Fin 3 → F), hW g g.2 w w.2⟩
      one_smul := fun w => Subtype.ext (by
        change ((1 : R) : Matrix (Fin 3) (Fin 3) F) *ᵥ (w : Fin 3 → F) = w
        simp)
      mul_smul := fun g h w => Subtype.ext (by
        change ((g * h : R) : Matrix (Fin 3) (Fin 3) F) *ᵥ (w : Fin 3 → F) =
          (g : Matrix (Fin 3) (Fin 3) F) *ᵥ ((h : Matrix (Fin 3) (Fin 3) F) *ᵥ (w : Fin 3 → F))
        rw [Matrix.mulVec_mulVec]
        rfl) }
  haveI : Module.Finite F W := Module.Finite.of_finite
  have h2 : 2 ∣ Nat.card W := by
    rw [Module.natCard_eq_pow_finrank (K := F)]
    have hF : 2 ∣ Nat.card F := by
      haveI := Fintype.ofFinite F
      rw [Nat.card_eq_fintype_card]
      exact (CharP.cast_eq_zero_iff F 2 _).mp (FiniteField.cast_card_eq_zero F)
    exact dvd_pow hF (by rwa [Ne, Submodule.finrank_eq_zero])
  have h0 : (0 : W) ∈ MulAction.fixedPoints R W := by
    rw [MulAction.mem_fixedPoints]
    intro g
    refine Subtype.ext ?_
    change (g : Matrix (Fin 3) (Fin 3) F) *ᵥ (0 : Fin 3 → F) = 0
    exact Matrix.mulVec_zero _
  obtain ⟨b, hb, hb0⟩ := hR.exists_fixed_point_of_prime_dvd_card_of_fixed_point W h2 h0
  refine ⟨b.1, b.2, fun h => hb0 (Subtype.ext h.symm), fun g hg => ?_⟩
  exact congrArg Subtype.val (MulAction.mem_fixedPoints.mp hb ⟨g, hg⟩)

theorem exists_fixed_vector_of_orderOf_three [Finite F] (hK : Nat.card F % 3 = 2) {y : SL(3, F)}
    (hy : orderOf y = 3) :
    ∃ v : Fin 3 → F, v ≠ 0 ∧ (y : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  have hmod := hP.card_modEq_card_fixedPoints (Fin 3 → F)
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at hmod
  unfold Nat.ModEq at hmod
  rw [Nat.pow_mod, hK] at hmod
  by_contra hcon
  push Not at hcon
  have hsub : Subsingleton (MulAction.fixedPoints (Subgroup.zpowers y) (Fin 3 → F)) := by
    refine ⟨fun a b => Subtype.ext ?_⟩
    have ha : (y : Matrix (Fin 3) (Fin 3) F) *ᵥ a.1 = a.1 := by
      have := MulAction.mem_fixedPoints.mp a.2 ⟨y, Subgroup.mem_zpowers y⟩
      exact this
    have hb : (y : Matrix (Fin 3) (Fin 3) F) *ᵥ b.1 = b.1 := by
      have := MulAction.mem_fixedPoints.mp b.2 ⟨y, Subgroup.mem_zpowers y⟩
      exact this
    have ha0 : a.1 = 0 := by
      by_contra h
      exact hcon a.1 h ha
    have hb0 : b.1 = 0 := by
      by_contra h
      exact hcon b.1 h hb
    rw [ha0, hb0]
  have hle : Nat.card (MulAction.fixedPoints (Subgroup.zpowers y) (Fin 3 → F)) ≤ 1 :=
    Finite.card_le_one_iff_subsingleton.mpr hsub
  omega

theorem no_root_of_mod_three [Finite F] [CharP F 2] (hK : Nat.card F % 3 = 2) (ω : F) :
    ω ^ 2 + ω + 1 ≠ 0 := by
  intro h
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at h
  have h3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * h
  have hu3 : (Units.mk0 ω hω0) ^ 3 = 1 := Units.ext (by simpa using h3)
  have h1 : orderOf (Units.mk0 ω hω0) ∣ 3 := orderOf_dvd_of_pow_eq_one hu3
  have h2 : orderOf (Units.mk0 ω hω0) ∣ Nat.card F - 1 :=
    Nat.card_units F ▸ orderOf_dvd_natCard _
  have hω1 : ω = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h' | h'
    · have := orderOf_eq_one_iff.1 h'
      simpa using congrArg Units.val this
    · rw [h'] at h2
      omega
  rw [hω1] at h
  have h11 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rw [one_pow, h11, zero_add] at h
  exact one_ne_zero h

theorem order_three_data [Finite F] (hK : Nat.card F % 3 = 2) {y : SL(3, F)} (hy : orderOf y = 3) :
    (∀ v, toLin' (y : Matrix (Fin 3) (Fin 3) F) (toLin' (y : Matrix (Fin 3) (Fin 3) F)
        (toLin' (y : Matrix (Fin 3) (Fin 3) F) v)) = v) ∧
      (∃ v, toLin' (y : Matrix (Fin 3) (Fin 3) F) v ≠ v) ∧
      (∃ v, v ≠ 0 ∧ toLin' (y : Matrix (Fin 3) (Fin 3) F) v = v) := by
  refine ⟨fun v => ?_, ?_, ?_⟩
  · have h := pow_orderOf_eq_one y
    rw [hy] at h
    have h2 : (y : Matrix (Fin 3) (Fin 3) F) * ((y : Matrix (Fin 3) (Fin 3) F) * y) = 1 := by
      have := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F)) h
      simpa [pow_succ, mul_assoc] using this
    simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  · by_contra hcon
    push Not at hcon
    have h1 : (y : Matrix (Fin 3) (Fin 3) F) = 1 := by
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun v => ?_
      rw [hcon v, Matrix.toLin'_one, LinearMap.id_apply]
    have : y = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hy
    omega
  · obtain ⟨v, hv0, hv⟩ := exists_fixed_vector_of_orderOf_three hK hy
    exact ⟨v, hv0, by simpa using hv⟩

theorem eq_zero_of_mul_self_eq_zero_of_commute [Finite F] [CharP F 2] (hK : Nat.card F % 3 = 2)
    {y : SL(3, F)} (hy : orderOf y = 3) {M : Matrix (Fin 3) (Fin 3) F} (hM : M * M = 0)
    (hcomm : M * (y : Matrix (Fin 3) (Fin 3) F) = (y : Matrix (Fin 3) (Fin 3) F) * M) :
    M = 0 := by
  obtain ⟨hy3, hy1, hfix⟩ := order_three_data hK hy
  have h := eq_zero_of_sq_eq_zero_of_comm hy3 (no_root_of_mod_three hK)
    (Module.finrank_fin_fun F) hy1 hfix (M := toLin' M)
    (fun v => by simp [Matrix.mulVec_mulVec, hM])
    (fun v => by simp [Matrix.mulVec_mulVec, hcomm])
  exact toLin'.map_eq_zero_iff.mp h

end SL3

section Scalar

open scoped MatrixGroups
open Matrix

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem exists_smul_one_of_pow_two_pow (hK : Nat.card F % 3 = 2) {y : SL(3, F)}
    (hy : orderOf y = 3) :
    ∀ (k : ℕ) {B : Matrix (Fin 3) (Fin 3) F},
      B * (y : Matrix (Fin 3) (Fin 3) F) = (y : Matrix (Fin 3) (Fin 3) F) * B →
      (∃ c : F, B ^ 2 ^ k = c • (1 : Matrix (Fin 3) (Fin 3) F)) →
      ∃ c : F, B = c • (1 : Matrix (Fin 3) (Fin 3) F) := by
  intro k
  induction k with
  | zero =>
    intro B _ h
    simpa using h
  | succ k ih =>
    intro B hcomm h
    obtain ⟨c, hc⟩ := h
    have hB2 : (B ^ 2) ^ 2 ^ k = c • (1 : Matrix (Fin 3) (Fin 3) F) := by
      rw [← pow_mul, ← pow_succ']
      exact hc
    have hcomm2 : B ^ 2 * (y : Matrix (Fin 3) (Fin 3) F) = (y : Matrix (Fin 3) (Fin 3) F) * B ^ 2 :=
      (Commute.pow_left (show Commute B (y : Matrix (Fin 3) (Fin 3) F) from hcomm) 2).eq
    obtain ⟨s, hs⟩ := ih hcomm2 ⟨c, hB2⟩
    haveI := Fintype.ofFinite F
    obtain ⟨t, ht⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) s
    have hBB : B * B = (t * t) • (1 : Matrix (Fin 3) (Fin 3) F) := by
      rw [← sq, hs, ht]
    have e1 := add_self_eq_zero_of_charTwo (F := F) ((t * t) • (1 : Matrix (Fin 3) (Fin 3) F))
    have e2 := add_self_eq_zero_of_charTwo (F := F) (t • B)
    have hM : (B + t • (1 : Matrix (Fin 3) (Fin 3) F)) * (B + t • (1 : Matrix (Fin 3) (Fin 3) F)) =
        0 := by
      calc (B + t • (1 : Matrix (Fin 3) (Fin 3) F)) * (B + t • (1 : Matrix (Fin 3) (Fin 3) F))
          = B * B + (t • B + t • B) + (t * t) • (1 : Matrix (Fin 3) (Fin 3) F) := by
            simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, smul_smul,
              smul_add]
            abel
        _ = ((t * t) • (1 : Matrix (Fin 3) (Fin 3) F) + (t * t) • (1 : Matrix (Fin 3) (Fin 3) F)) +
            (t • B + t • B) := by
            rw [hBB]
            abel
        _ = 0 := by rw [e1, e2, add_zero]
    have hMy : (B + t • (1 : Matrix (Fin 3) (Fin 3) F)) * (y : Matrix (Fin 3) (Fin 3) F) =
        (y : Matrix (Fin 3) (Fin 3) F) * (B + t • (1 : Matrix (Fin 3) (Fin 3) F)) := by
      rw [add_mul, mul_add, hcomm, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    have h0 := eq_zero_of_mul_self_eq_zero_of_commute hK hy hM hMy
    refine ⟨t, ?_⟩
    calc B = (B + t • (1 : Matrix (Fin 3) (Fin 3) F)) + t • (1 : Matrix (Fin 3) (Fin 3) F) := by
          rw [add_assoc, add_self_eq_zero_of_charTwo (F := F), add_zero]
      _ = t • (1 : Matrix (Fin 3) (Fin 3) F) := by rw [h0, zero_add]

end Scalar

section Graph

open scoped MatrixGroups
open Matrix

variable {F : Type*} [Field F]

def fixSL (S : Subgroup SL(3, F)) : Submodule F (Fin 3 → F) where
  carrier := {v | ∀ g ∈ S, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    intro g hg
    rw [Matrix.mulVec_add, ha g hg, hb g hg]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    intro g _
    exact Matrix.mulVec_zero _
  smul_mem' c v hv := by
    simp only [Set.mem_setOf_eq] at hv ⊢
    intro g hg
    rw [Matrix.mulVec_smul, hv g hg]

theorem fixSL_ne_bot [Finite F] [CharP F 2] {S : Subgroup SL(3, F)} (hS : IsPGroup 2 S) :
    fixSL S ≠ ⊥ := by
  obtain ⟨w, -, hw0, hw⟩ := exists_fixed_mem hS (W := ⊤) top_ne_bot
    (fun _ _ _ _ => Submodule.mem_top)
  intro h
  have : w ∈ fixSL S := hw
  rw [h, Submodule.mem_bot] at this
  exact hw0 this

theorem fixSL_ne_top {S : Subgroup SL(3, F)} (hS : S ≠ ⊥) : fixSL S ≠ ⊤ := by
  intro h
  apply hS
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one]
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_one, LinearMap.id_apply]
  have : v ∈ fixSL S := by rw [h]; trivial
  exact this g hg

theorem mulVec_mem_fixSL {S : Subgroup SL(3, F)} {z : SL(3, F)} (hz3 : z * z * z = 1)
    (hz : ∀ r ∈ S, z * r * z⁻¹ ∈ S) {v : Fin 3 → F} (hv : v ∈ fixSL S) :
    (z : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ fixSL S := by
  intro g hg
  have hinv : z⁻¹ = z * z := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hz3)
  have h3 : z⁻¹ * z⁻¹ = z := by rw [← _root_.mul_inv_rev, ← hinv, inv_inv]
  have h1 : z * (z * g * z⁻¹) * z⁻¹ ∈ S := hz _ (hz g hg)
  have h2 : z * (z * g * z⁻¹) * z⁻¹ = z⁻¹ * g * z := by
    calc z * (z * g * z⁻¹) * z⁻¹ = (z * z) * g * (z⁻¹ * z⁻¹) := by group
      _ = z⁻¹ * g * z := by rw [← hinv, h3]
  have h4 : g * z = z * (z⁻¹ * g * z) := by group
  have h5 : z⁻¹ * g * z ∈ S := by rw [← h2]; exact h1
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, h4,
    Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hv _ h5]

def perp (T : Submodule F (Fin 3 → F)) : Submodule F (Fin 3 → F) :=
  LinearMap.BilinForm.orthogonal (dotProductBilin F F : LinearMap.BilinForm F (Fin 3 → F)) T

theorem mem_perp {T : Submodule F (Fin 3 → F)} {u : Fin 3 → F} :
    u ∈ perp T ↔ ∀ w ∈ T, w ⬝ᵥ u = 0 := by
  simp [perp]

theorem dotProductBilin_nondegenerate :
    (dotProductBilin F F : LinearMap.BilinForm F (Fin 3 → F)).Nondegenerate := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · funext i
    simpa using hx (Pi.single i 1)
  · funext i
    simpa using hy (Pi.single i 1)

theorem finrank_perp (T : Submodule F (Fin 3 → F)) :
    Module.finrank F (perp T) = 3 - Module.finrank F T := by
  rw [perp, LinearMap.BilinForm.finrank_orthogonal dotProductBilin_nondegenerate,
    Module.finrank_fin_fun]

theorem dotProduct_mulVec_eq (A : Matrix (Fin 3) (Fin 3) F) (w u : Fin 3 → F) :
    w ⬝ᵥ (A *ᵥ u) = (Aᵀ *ᵥ w) ⬝ᵥ u := by
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

theorem mulVec_conj_fix {Bm Bi D : Matrix (Fin 3) (Fin 3) F} (hBi : Bi * Bm = 1)
    {w : Fin 3 → F} (h : D *ᵥ w = w) : (Bm * D * Bi) *ᵥ (Bm *ᵥ w) = Bm *ᵥ w := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (Bm * D) Bi Bm, hBi, Matrix.mul_one,
    ← Matrix.mulVec_mulVec, h]

theorem mulVec_conj_fix' {Bm Bi D : Matrix (Fin 3) (Fin 3) F} (hBi : Bi * Bm = 1)
    {v : Fin 3 → F} (h : (Bm * D * Bi) *ᵥ v = v) : D *ᵥ (Bi *ᵥ v) = Bi *ᵥ v := by
  calc D *ᵥ (Bi *ᵥ v) = (Bi * (Bm * D * Bi)) *ᵥ v := by
        rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hBi, Matrix.one_mul]
    _ = Bi *ᵥ v := by rw [← Matrix.mulVec_mulVec, h]

theorem false_of_graph [Finite F] [CharP F 2] (hK : Nat.card F % 3 = 2) {y : SL(3, F)}
    (hy : orderOf y = 3) {R : Subgroup SL(3, F)} (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥)
    (hyR : ∀ r ∈ R, y * r * y⁻¹ ∈ R) (δ β : SL(3, F) ≃* SL(3, F))
    (B : Matrix.GeneralLinearGroup (Fin 3) F)
    (hδ : ∀ g : SL(3, F), (δ g : Matrix (Fin 3) (Fin 3) F) =
      ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)ᵀ)
    (hβ : ∀ g : SL(3, F), (β g : Matrix (Fin 3) (Fin 3) F) =
      (B : Matrix (Fin 3) (Fin 3) F) * (δ g : Matrix (Fin 3) (Fin 3) F) *
        ((B⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
    (hβR : ∀ r ∈ R, β r ∈ R) : False := by
  have hy3 : y * y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hy] at h
    simpa [pow_succ] using h
  have hyinv : y⁻¹ = y * y := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hy3)
  set R' : Subgroup SL(3, F) := R.map δ.toMonoidHom with hR'
  have hR'2 : IsPGroup 2 R' := hR2.map δ.toMonoidHom
  have hR'1 : R' ≠ ⊥ := by
    intro h
    apply hR1
    rw [eq_bot_iff]
    intro g hg
    have hmem : δ g ∈ R' := ⟨g, hg, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    apply δ.injective
    rw [hmem, map_one]
  have hδy3 : δ y * δ y * δ y = 1 := by rw [← map_mul, ← map_mul, hy3, map_one]
  have hR'y : ∀ r ∈ R', δ y * r * (δ y)⁻¹ ∈ R' := by
    rintro _ ⟨r, hr, rfl⟩
    exact ⟨y * r * y⁻¹, hyR r hr, by simp⟩
  have hδyy : (δ y : Matrix (Fin 3) (Fin 3) F) * (δ y : Matrix (Fin 3) (Fin 3) F) =
      (y : Matrix (Fin 3) (Fin 3) F)ᵀ := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← map_mul, ← hyinv, hδ, inv_inv]
  set T : Submodule F (Fin 3 → F) := fixSL R' with hT
  have hTy : ∀ w ∈ T, ((y : Matrix (Fin 3) (Fin 3) F))ᵀ *ᵥ w ∈ T := by
    intro w hw
    have h1 := mulVec_mem_fixSL hδy3 hR'y hw
    have h2 := mulVec_mem_fixSL hδy3 hR'y h1
    rw [← hδyy, ← Matrix.mulVec_mulVec]
    exact h2
  set Mv : Submodule F (Fin 3 → F) := perp T with hMv
  have hMvy : ∀ u ∈ Mv, (y : Matrix (Fin 3) (Fin 3) F) *ᵥ u ∈ Mv := by
    intro u hu
    rw [hMv, mem_perp] at hu ⊢
    intro w hw
    rw [dotProduct_mulVec_eq]
    exact hu _ (hTy w hw)
  have hMvR : ∀ g ∈ R, ∀ u ∈ Mv, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ u ∈ Mv := by
    intro g hg u hu
    rw [hMv, mem_perp] at hu ⊢
    intro w hw
    rw [dotProduct_mulVec_eq]
    have hgT : (g : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ w = w := by
      have := hw (δ g⁻¹) ⟨g⁻¹, R.inv_mem hg, rfl⟩
      rwa [hδ, inv_inv] at this
    rw [hgT]
    exact hu w hw
  set Fx : Submodule F (Fin 3 → F) := fixSL R with hFx
  have hFxy : ∀ u ∈ Fx, (y : Matrix (Fin 3) (Fin 3) F) *ᵥ u ∈ Fx :=
    fun u hu => mulVec_mem_fixSL hy3 hyR hu
  have hFx0 : Fx ≠ ⊥ := fixSL_ne_bot hR2
  have hFx1 : Fx ≠ ⊤ := fixSL_ne_top hR1
  have hT0 : T ≠ ⊥ := fixSL_ne_bot hR'2
  have hT1 : T ≠ ⊤ := fixSL_ne_top hR'1
  have hdimT1 : 1 ≤ Module.finrank F T := Submodule.one_le_finrank_iff.mpr hT0
  have hdimT2 : Module.finrank F T < 3 := by
    have := Submodule.finrank_lt hT1
    rwa [Module.finrank_fin_fun] at this
  have hdimMv : Module.finrank F Mv = 3 - Module.finrank F T := finrank_perp T
  have hMv0 : Mv ≠ ⊥ := by
    intro h
    have : Module.finrank F Mv = 0 := by rw [h]; exact finrank_bot F _
    omega
  have hMv1 : Mv ≠ ⊤ := by
    intro h
    have : Module.finrank F Mv = 3 := by rw [h, finrank_top, Module.finrank_fin_fun]
    omega
  obtain ⟨w, hwMv, hw0, hwR⟩ := exists_fixed_mem hR2 hMv0 hMvR
  have hinf : Fx ⊓ Mv ≠ ⊥ := by
    intro h
    have : w ∈ Fx ⊓ Mv := ⟨hwR, hwMv⟩
    rw [h, Submodule.mem_bot] at this
    exact hw0 this
  obtain ⟨hy3', hy1, hfix⟩ := order_three_data hK hy
  have hEq : Fx = Mv := by
    refine eq_of_inf_ne_bot_of_invariant hy3' (no_root_of_mod_three hK) (Module.finrank_fin_fun F)
      hy1 hfix ?_ ?_ hFx0 hFx1 hMv0 hMv1 hinf
    · intro u hu
      simpa [Matrix.toLin'_apply] using hFxy u hu
    · intro u hu
      simpa [Matrix.toLin'_apply] using hMvy u hu
  have hBi : ((B⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (B : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hBi' : (B : Matrix (Fin 3) (Fin 3) F) *
      ((B⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hf : Function.Injective (Matrix.toLin' (B : Matrix (Fin 3) (Fin 3) F)) := by
    intro a b hab
    have := congrArg (fun v => ((B⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) *ᵥ v) hab
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hBi] using this
  have hmap : Fx = T.map (Matrix.toLin' (B : Matrix (Fin 3) (Fin 3) F)) := by
    apply le_antisymm
    · intro v hv
      refine ⟨((B⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v,
        ?_, ?_⟩
      · rintro _ ⟨g, hg, rfl⟩
        have h1 := hv (β g) (hβR g hg)
        rw [hβ] at h1
        exact mulVec_conj_fix' hBi h1
      · rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hBi', Matrix.one_mulVec]
    · rintro _ ⟨w, hw, rfl⟩ r hr
      have hr' : r ∈ R.map β.toMonoidHom := by
        rw [CFSG.GroupTheory.map_eq_of_mapsTo β hβR]
        exact hr
      obtain ⟨g, hg, rfl⟩ := hr'
      change ((β g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        (Matrix.toLin' (B : Matrix (Fin 3) (Fin 3) F) w) = _
      rw [Matrix.toLin'_apply, hβ]
      exact mulVec_conj_fix hBi (hw (δ g) ⟨g, hg, rfl⟩)
  have hdimF : Module.finrank F Fx = Module.finrank F T := by
    rw [hmap]
    exact (Submodule.equivMapOfInjective _ hf T).finrank_eq.symm
  have hdimEq : Module.finrank F Fx = Module.finrank F Mv := by rw [hEq]
  omega

end Graph

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1.L3Fix
