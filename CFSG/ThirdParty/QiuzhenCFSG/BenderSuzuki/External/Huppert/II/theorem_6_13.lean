module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_11
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Transvection.Basic

import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Algebra.Group.AddChar
import Mathlib.LinearAlgebra.SpecialLinearGroup

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert II.6.13

The statement follows Volume I, physical page 202.  It is stated for an
arbitrary field; the cardinal convention `Nat.card K = 0` for infinite `K`
ensures that the two exclusions are exactly `PSL(2,2)` and `PSL(2,3)`.
-/

namespace CFSG.BenderSuzuki
namespace External

open scoped LinearAlgebra.Projectivization
open scoped commutatorElement

universe u

private def huppert613_elementarySL
    {K : Type u} [Field K] {m : Type*} [Fintype m] [DecidableEq m]
    (t : Matrix.TransvectionStruct m K) :
    Matrix.SpecialLinearGroup m K :=
  ⟨t.toMatrix, t.det⟩

private def huppert613_pairDiagonalValue
    {K : Type u} [Field K] {m : Type*} [DecidableEq m]
    (p i : m) (a : Kˣ) (k : m) : K :=
  if k = p then (a⁻¹ : K) else if k = i then (a : K) else 1

private theorem huppert613_transvection_mulVec
    {K : Type u} [Field K] {m : Type*} [Fintype m] [DecidableEq m]
    (i j : m) (c : K) (v : m → K) :
    Matrix.mulVec (Matrix.transvection i j c) v =
      Function.update v i (v i + c * v j) := by
  ext k
  by_cases hki : k = i
  · subst k
    simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec]
  · simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec, hki]

private theorem huppert613_diagonal_mulVec_apply
    {K : Type u} [Field K] {m : Type*} [Fintype m] [DecidableEq m]
    (d : m → K) (v : m → K) (k : m) :
    Matrix.mulVec (Matrix.diagonal d) v k = d k * v k := by
  simp [Matrix.mulVec]

private theorem huppert613_pairDiagonal_eq
    {K : Type u} [Field K] {m : Type*} [Fintype m] [DecidableEq m]
    (p i : m) (hpi : p ≠ i) (a : Kˣ) :
    Matrix.diagonal (huppert613_pairDiagonalValue p i a) =
      Matrix.transvection p i (a⁻¹ : K) *
        Matrix.transvection i p (-(a : K)) *
        Matrix.transvection p i (a⁻¹ : K) *
        Matrix.transvection p i (-1 : K) *
      Matrix.transvection i p (1 : K) *
        Matrix.transvection p i (-1 : K) := by
  classical
  apply Matrix.mulVec_injective
  funext v
  simp only [← Matrix.mulVec_mulVec, huppert613_transvection_mulVec]
  ext k
  by_cases hkp : k = p
  · subst k
    rw [huppert613_diagonal_mulVec_apply]
    simp [huppert613_pairDiagonalValue, hpi, hpi.symm]
    field_simp
    ring
  · by_cases hki : k = i
    · subst k
      rw [huppert613_diagonal_mulVec_apply]
      simp [huppert613_pairDiagonalValue, hpi, hpi.symm]
      field_simp
      ring
    · rw [huppert613_diagonal_mulVec_apply]
      simp [huppert613_pairDiagonalValue, hkp, hki]

private def huppert613_pairDiagonalSL
    {K : Type u} [Field K] {m : Type*} [Fintype m] [DecidableEq m]
    (p i : m) (hpi : p ≠ i) (a : Kˣ) :
    Matrix.SpecialLinearGroup m K :=
  ⟨Matrix.diagonal (huppert613_pairDiagonalValue p i a), by
    rw [huppert613_pairDiagonal_eq p i hpi a]
    simp [Matrix.det_transvection_of_ne, hpi, hpi.symm]⟩

private theorem huppert613_pairDiagonalSL_mem_closure
    {K : Type u} [Field K] {m : Type*} [Fintype m] [DecidableEq m]
    (p i : m) (hpi : p ≠ i) (a : Kˣ) :
    huppert613_pairDiagonalSL p i hpi a ∈
      Subgroup.closure
        (Set.range (huppert613_elementarySL (K := K) (m := m))) := by
  let t1 : Matrix.TransvectionStruct m K := ⟨p, i, hpi, (a⁻¹ : K)⟩
  let t2 : Matrix.TransvectionStruct m K := ⟨i, p, hpi.symm, -(a : K)⟩
  let t3 : Matrix.TransvectionStruct m K := ⟨p, i, hpi, (a⁻¹ : K)⟩
  let t4 : Matrix.TransvectionStruct m K := ⟨p, i, hpi, (-1 : K)⟩
  let t5 : Matrix.TransvectionStruct m K := ⟨i, p, hpi.symm, (1 : K)⟩
  let t6 : Matrix.TransvectionStruct m K := ⟨p, i, hpi, (-1 : K)⟩
  have heq :
      huppert613_pairDiagonalSL p i hpi a =
        huppert613_elementarySL t1 * huppert613_elementarySL t2 *
          huppert613_elementarySL t3 * huppert613_elementarySL t4 *
          huppert613_elementarySL t5 * huppert613_elementarySL t6 := by
    apply Subtype.ext
    exact huppert613_pairDiagonal_eq p i hpi a
  rw [heq]
  let H := Subgroup.closure
    (Set.range (huppert613_elementarySL (K := K) (m := m)))
  have ht (t : Matrix.TransvectionStruct m K) :
      huppert613_elementarySL t ∈ H :=
    Subgroup.subset_closure (Set.mem_range_self t)
  exact
    H.mul_mem
      (H.mul_mem
        (H.mul_mem
          (H.mul_mem
            (H.mul_mem (ht t1) (ht t2)) (ht t3))
          (ht t4))
        (ht t5))
      (ht t6)

private theorem huppert613_list_prod_diagonal
    {K : Type u} [Field K] {m ι : Type*} [Fintype m] [DecidableEq m]
    (L : List ι) (f : ι → m → K) :
    (L.map fun i => Matrix.diagonal (f i)).prod =
      Matrix.diagonal (fun k => (L.map fun i => f i k).prod) := by
  induction L with
  | nil => simp
  | cons i L ih =>
      simp only [List.map_cons, List.prod_cons, ih]
      rw [Matrix.diagonal_mul_diagonal]


private theorem huppert613_coe_pairDiagonal_list_prod
    {K : Type u} [Field K] {m : Type*} [Fintype m] [DecidableEq m]
    (p : m) (u : m → Kˣ) (L : List {i : m // i ≠ p}) :
    (((L.map fun (i : {i : m // i ≠ p}) =>
        huppert613_pairDiagonalSL p i (Ne.symm i.property) (u i)).prod :
      Matrix.SpecialLinearGroup m K) : Matrix m m K) =
      (L.map fun (i : {i : m // i ≠ p}) =>
        Matrix.diagonal (huppert613_pairDiagonalValue p i (u i))).prod := by
  induction L with
  | nil => simp
  | cons i L ih =>
      simp only [List.map_cons, List.prod_cons, Matrix.SpecialLinearGroup.coe_mul]
      change
        Matrix.diagonal (huppert613_pairDiagonalValue p i (u i)) *
            (((L.map fun (j : {j : m // j ≠ p}) =>
              huppert613_pairDiagonalSL p j (Ne.symm j.property) (u j)).prod :
              Matrix.SpecialLinearGroup m K) : Matrix m m K) =
          Matrix.diagonal (huppert613_pairDiagonalValue p i (u i)) *
            (L.map fun (j : {j : m // j ≠ p}) =>
              Matrix.diagonal (huppert613_pairDiagonalValue p j (u j))).prod
      rw [ih]

private theorem huppert613_diagonalSL_mem_closure
    {K : Type u} [Field K] {m : Type*} [Fintype m] [DecidableEq m]
    (p : m) (D : m → K) (hdet : Matrix.det (Matrix.diagonal D) = 1) :
    (⟨Matrix.diagonal D, hdet⟩ : Matrix.SpecialLinearGroup m K) ∈
      Subgroup.closure
        (Set.range (huppert613_elementarySL (K := K) (m := m))) := by
  classical
  have hprod : ∏ i, D i = 1 := by
    simpa [Matrix.det_diagonal] using hdet
  have hDne (i : m) : D i ≠ 0 := by
    intro hi
    have hz : ∏ j, D j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [hprod] at hz
    exact one_ne_zero hz
  let u : m → Kˣ := fun i => Units.mk0 (D i) (hDne i)
  have huprod : ∏ i, u i = 1 := by
    apply Units.ext
    simpa [u] using hprod
  let indices : List {i : m // i ≠ p} :=
    (Finset.univ : Finset {i : m // i ≠ p}).toList
  have hindices_prod (g : {i : m // i ≠ p} → K) :
      (indices.map g).prod = ∏ i, g i := by
    simp [indices, Finset.prod_map_toList]
  let factors : List (Matrix.SpecialLinearGroup m K) :=
    indices.map fun (i : {i : m // i ≠ p}) =>
      huppert613_pairDiagonalSL p i (Ne.symm i.property) (u i)
  let H := Subgroup.closure
    (Set.range (huppert613_elementarySL (K := K) (m := m)))
  have hfactors_mem : factors.prod ∈ H := by
    apply H.list_prod_mem
    intro x hx
    simp only [factors, List.mem_map] at hx
    rcases hx with ⟨(i : {i : m // i ≠ p}), _hi, rfl⟩
    exact huppert613_pairDiagonalSL_mem_closure p i (Ne.symm i.property) (u i)
  have hu_rest : ∏ i : {i : m // i ≠ p}, u i = (u p)⁻¹ := by
    have h := huprod
    rw [Fintype.prod_eq_mul_prod_subtype_ne u p] at h
    exact (mul_eq_one_iff_eq_inv').mp h
  have hu_inv_rest : ∏ i : {i : m // i ≠ p}, (u i)⁻¹ = u p := by
    calc
      ∏ i : {i : m // i ≠ p}, (u i)⁻¹ =
          (∏ i : {i : m // i ≠ p}, u i)⁻¹ := by
        symm
        exact
          (map_prod (invMonoidHom : Kˣ →* Kˣ)
            (fun i : {i : m // i ≠ p} => u i) Finset.univ)
      _ = u p := by rw [hu_rest, inv_inv]
  have hfactors_eq :
      factors.prod =
        (⟨Matrix.diagonal D, hdet⟩ : Matrix.SpecialLinearGroup m K) := by
    apply Subtype.ext
    change ((factors.prod : Matrix.SpecialLinearGroup m K) : Matrix m m K) =
      Matrix.diagonal D
    calc
      ((factors.prod : Matrix.SpecialLinearGroup m K) : Matrix m m K) =
          (indices.map fun (i : {i : m // i ≠ p}) =>
            Matrix.diagonal (huppert613_pairDiagonalValue p i (u i))).prod := by
        dsimp only [factors]
        exact huppert613_coe_pairDiagonal_list_prod p u indices
      _ = Matrix.diagonal (fun k =>
          (indices.map fun (i : {i : m // i ≠ p}) =>
            huppert613_pairDiagonalValue p i (u i) k).prod) :=
        huppert613_list_prod_diagonal indices
          (fun i => huppert613_pairDiagonalValue p i (u i))
      _ = Matrix.diagonal D := by
        apply congrArg Matrix.diagonal
        funext k
        by_cases hkp : k = p
        · subst k
          rw [hindices_prod]
          have hcoe := congrArg Units.val hu_inv_rest
          simpa [huppert613_pairDiagonalValue, u] using hcoe
        · let kI : {i : m // i ≠ p} := ⟨k, hkp⟩
          rw [hindices_prod]
          simp [huppert613_pairDiagonalValue, hkp,
            show ∀ i : {i : m // i ≠ p}, k = i ↔ kI = i by
              intro i
              exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩,
            u, kI]
  rw [← hfactors_eq]
  exact hfactors_mem

private theorem huppert613_elementarySL_inv
    {K : Type u} [Field K] {m : Type*} [Fintype m] [DecidableEq m]
    (t : Matrix.TransvectionStruct m K) :
    (huppert613_elementarySL t)⁻¹ = huppert613_elementarySL t.inv := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  exact t.mul_inv

private theorem huppert613_steinberg_commutator
    {K : Type u} [Field K] {m : Type*} [Fintype m] [DecidableEq m]
    (i j k : m) (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j)
    (a b : K) :
    ⁅huppert613_elementarySL ⟨i, k, hik, a⟩,
        huppert613_elementarySL ⟨k, j, hkj, b⟩⁆ =
      huppert613_elementarySL ⟨i, j, hij, a * b⟩ := by
  rw [commutatorElement_def, huppert613_elementarySL_inv,
    huppert613_elementarySL_inv]
  apply Subtype.ext
  change
    Matrix.transvection i k a * Matrix.transvection k j b *
        Matrix.transvection i k (-a) * Matrix.transvection k j (-b) =
      Matrix.transvection i j (a * b)
  apply Matrix.mulVec_injective
  funext v
  simp only [← Matrix.mulVec_mulVec, huppert613_transvection_mulVec]
  ext r
  by_cases hri : r = i
  · subst r
    simp [hik, Ne.symm hij, Ne.symm hik, Ne.symm hkj]
    ring
  · by_cases hrk : r = k
    · subst r
      simp [hri, hik, Ne.symm hij, Ne.symm hkj]
    · simp [hri, hrk]

private theorem huppert613_exists_unit_sq_ne_one
    {K : Type u} [Field K]
    (h2 : Nat.card K ≠ 2) (h3 : Nat.card K ≠ 3) :
    ∃ a : Kˣ, (a : K) ^ 2 ≠ 1 := by
  classical
  cases finite_or_infinite K with
  | inl hfinite =>
      letI : Finite K := hfinite
      letI : Fintype K := Fintype.ofFinite K
      have htwo : 2 ≤ Fintype.card K := by
        let f : Bool → K := fun b => if b then 1 else 0
        have hf : Function.Injective f := by
          intro b c hbc
          cases b <;> cases c <;> simp [f] at hbc ⊢
        simpa using Fintype.card_le_of_injective f hf
      have hcard2 : Fintype.card K ≠ 2 := by
        simpa [Nat.card_eq_fintype_card] using h2
      have hcard3 : Fintype.card K ≠ 3 := by
        simpa [Nat.card_eq_fintype_card] using h3
      have hfour : 4 ≤ Fintype.card K := by omega
      let s : Finset K := {0, 1, -1}
      have hs_card : s.card ≤ 3 := by
        dsimp [s]
        calc
          ({0, 1, -1} : Finset K).card ≤ ({1, -1} : Finset K).card + 1 :=
            Finset.card_insert_le _ _
          _ ≤ ({-1} : Finset K).card + 2 := by
            have h := Finset.card_insert_le (1 : K) ({-1} : Finset K)
            omega
          _ ≤ 3 := by simp
      have hs_lt : s.card < (Finset.univ : Finset K).card := by
        simpa using hs_card.trans_lt (by omega : 3 < Fintype.card K)
      obtain ⟨a, _ha_univ, ha⟩ :=
        Finset.exists_mem_notMem_of_card_lt_card hs_lt
      have ha_all : a ≠ 0 ∧ a ≠ 1 ∧ a ≠ -1 := by
        simpa [s] using ha
      have ha0 : a ≠ 0 := ha_all.1
      have ha1 : a ≠ 1 := ha_all.2.1
      have haneg1 : a ≠ -1 := ha_all.2.2
      refine ⟨Units.mk0 a ha0, ?_⟩
      simpa using (sq_ne_one_iff.mpr ⟨ha1, haneg1⟩)
  | inr hinfinite =>
      letI : Infinite K := hinfinite
      obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset K)
      have ha_all : a ≠ 0 ∧ a ≠ 1 ∧ a ≠ -1 := by
        simpa using ha
      have ha0 : a ≠ 0 := ha_all.1
      have ha1 : a ≠ 1 := ha_all.2.1
      have haneg1 : a ≠ -1 := ha_all.2.2
      refine ⟨Units.mk0 a ha0, ?_⟩
      simpa using (sq_ne_one_iff.mpr ⟨ha1, haneg1⟩)

private theorem huppert613_pairDiagonalSL_inv
    {K : Type u} [Field K] {m : Type*} [Fintype m] [DecidableEq m]
    (p i : m) (hpi : p ≠ i) (a : Kˣ) :
    (huppert613_pairDiagonalSL p i hpi a)⁻¹ =
      huppert613_pairDiagonalSL p i hpi a⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change
    Matrix.diagonal (huppert613_pairDiagonalValue p i a) *
        Matrix.diagonal (huppert613_pairDiagonalValue p i a⁻¹) = 1
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  apply congrArg Matrix.diagonal
  funext r
  by_cases hrp : r = p
  · subst r
    simp [huppert613_pairDiagonalValue]
  · by_cases hri : r = i
    · subst r
      simp [huppert613_pairDiagonalValue, Ne.symm hpi]
    · simp [huppert613_pairDiagonalValue, hrp, hri]

private theorem huppert613_pairDiagonalSL_conj
    {K : Type u} [Field K] {m : Type*} [Fintype m] [DecidableEq m]
    (p i : m) (hpi : p ≠ i) (a : Kˣ) (c : K) :
    huppert613_pairDiagonalSL p i hpi a *
          huppert613_elementarySL ⟨p, i, hpi, c⟩ *
          (huppert613_pairDiagonalSL p i hpi a)⁻¹ =
      huppert613_elementarySL
        ⟨p, i, hpi, ((a⁻¹ : Kˣ) : K) ^ 2 * c⟩ := by
  rw [huppert613_pairDiagonalSL_inv]
  apply Subtype.ext
  change
    Matrix.diagonal (huppert613_pairDiagonalValue p i a) *
          Matrix.transvection p i c *
          Matrix.diagonal (huppert613_pairDiagonalValue p i a⁻¹) =
      Matrix.transvection p i (((a⁻¹ : Kˣ) : K) ^ 2 * c)
  apply Matrix.mulVec_injective
  funext v
  simp only [← Matrix.mulVec_mulVec, huppert613_transvection_mulVec]
  ext r
  simp_rw [huppert613_diagonal_mulVec_apply]
  by_cases hrp : r = p
  · subst r
    simp [huppert613_pairDiagonalValue, Ne.symm hpi]
    field_simp [Units.ne_zero a]
  · by_cases hri : r = i
    · subst r
      simp [huppert613_diagonal_mulVec_apply, huppert613_pairDiagonalValue,
        Ne.symm hpi]
    · simp [huppert613_diagonal_mulVec_apply, huppert613_pairDiagonalValue, hrp, hri]

private theorem huppert613_elementarySL_mem_commutator_fin_two
    {K : Type u} [Field K]
    (h2 : Nat.card K ≠ 2) (h3 : Nat.card K ≠ 3)
    (t : Matrix.TransvectionStruct (Fin 2) K) :
    huppert613_elementarySL t ∈
      commutator (Matrix.SpecialLinearGroup (Fin 2) K) := by
  rcases t with ⟨p, i, hpi, c⟩
  obtain ⟨a, ha⟩ := huppert613_exists_unit_sq_ne_one h2 h3
  let q : K := ((a⁻¹ : Kˣ) : K) ^ 2
  have hq : q ≠ 1 := by
    intro h
    apply ha
    have hK : (a : K)⁻¹ ^ 2 = 1 := by
      simpa [q] using h
    field_simp [Units.ne_zero a] at hK
    exact hK.symm
  let y : K := c / (q - 1)
  let D := huppert613_pairDiagonalSL p i hpi a
  let E := huppert613_elementarySL
    (⟨p, i, hpi, y⟩ : Matrix.TransvectionStruct (Fin 2) K)
  have hcomm : ⁅D, E⁆ =
      huppert613_elementarySL
        (⟨p, i, hpi, c⟩ : Matrix.TransvectionStruct (Fin 2) K) := by
    rw [commutatorElement_def]
    change
      huppert613_pairDiagonalSL p i hpi a *
          huppert613_elementarySL ⟨p, i, hpi, y⟩ *
          (huppert613_pairDiagonalSL p i hpi a)⁻¹ *
          (huppert613_elementarySL ⟨p, i, hpi, y⟩)⁻¹ =
        huppert613_elementarySL ⟨p, i, hpi, c⟩
    rw [huppert613_pairDiagonalSL_conj, huppert613_elementarySL_inv]
    apply Subtype.ext
    change
      Matrix.transvection p i (q * y) * Matrix.transvection p i (-y) =
        Matrix.transvection p i c
    rw [Matrix.transvection_mul_transvection_same p i hpi]
    congr 1
    dsimp [y]
    field_simp [sub_ne_zero.mpr hq]
    ring
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator
    (H₁ := (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)))
    (H₂ := (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)))
    (Subgroup.mem_top D) (Subgroup.mem_top E)

private def huppert613_basisVector
    {K : Type u} [Field K] {m : Type*} [DecidableEq m] (i : m) : m → K :=
  Pi.single i 1

private def huppert613_coord
    {K : Type u} [Field K] {m : Type*} (j : m) : Module.Dual K (m → K) :=
  LinearMap.proj j

private theorem huppert613_toLin_elementarySL
    {K : Type u} [Field K] {m : Type*} [Fintype m] [DecidableEq m]
    (i j : m) (hij : i ≠ j) (c : K) :
    Matrix.SpecialLinearGroup.toLin'_equiv
        (huppert613_elementarySL
          (⟨i, j, hij, c⟩ : Matrix.TransvectionStruct m K)) =
      (⟨LinearEquiv.transvection (f := c • huppert613_coord j)
          (v := huppert613_basisVector i) (by
            simp [huppert613_coord, huppert613_basisVector, hij.symm]),
        LinearEquiv.transvection.det_eq_one (by
          simp [huppert613_coord, huppert613_basisVector, hij.symm])⟩ :
        _root_.SpecialLinearGroup K (m → K)) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  ext k
  change Matrix.mulVec (Matrix.transvection i j c) v k = _
  rw [huppert613_transvection_mulVec]
  by_cases hki : k = i
  · subst k
    simp [LinearMap.transvection.apply,
      huppert613_coord, huppert613_basisVector]
  · simp [LinearMap.transvection.apply,
      huppert613_coord, huppert613_basisVector, hki]

private theorem huppert613_basisVector_ne_zero
    {K : Type u} [Field K] {m : Type*} [DecidableEq m] (i : m) :
    huppert613_basisVector (K := K) i ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp [huppert613_basisVector] at hi

private theorem huppert613_projective_basis_ne
    {K : Type u} [Field K] {m : Type*} [DecidableEq m]
    (i j : m) (hij : i ≠ j) :
    Projectivization.mk K (huppert613_basisVector (K := K) i)
        (huppert613_basisVector_ne_zero i) ≠
      Projectivization.mk K (huppert613_basisVector (K := K) j)
        (huppert613_basisVector_ne_zero j) := by
  intro h
  rcases (Projectivization.mk_eq_mk_iff K _ _ _ _).1 h with ⟨s, hs⟩
  have hi := congrFun hs i
  simp [huppert613_basisVector, hij] at hi

set_option backward.isDefEq.respectTransparency false in
/-- Huppert II.6.13: `PSL(n,K)` is simple apart from `PSL(2,2)` and `PSL(2,3)`. -/
public theorem huppert_II_6_13
    {K : Type u} [Field K] (n : ℕ) (hn : 2 ≤ n)
    (h22 : n ≠ 2 ∨ Nat.card K ≠ 2)
    (h23 : n ≠ 2 ∨ Nat.card K ≠ 3) :
    IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) K) := by
  classical
  let SL := Matrix.SpecialLinearGroup (Fin n) K
  let PSL := Matrix.ProjectiveSpecialLinearGroup (Fin n) K
  let P := ℙ K (Fin n → K)
  let transvections : Set SL :=
    Set.range (huppert613_elementarySL (K := K) (m := Fin n))
  have htransvection_generation :
      Subgroup.closure transvections = ⊤ := by
    apply top_unique
    intro A _
    let H := Subgroup.closure transvections
    let PMatrix : Matrix (Fin n) (Fin n) K → Prop := fun M =>
      ∃ hM : Matrix.det M = 1, (⟨M, hM⟩ : SL) ∈ H
    have hP : PMatrix (A : Matrix (Fin n) (Fin n) K) := by
      apply Matrix.diagonal_transvection_induction PMatrix
      · intro D hdet
        have hD : Matrix.det (Matrix.diagonal D) = 1 := hdet.trans A.property
        exact ⟨hD, huppert613_diagonalSL_mem_closure
          (⟨0, by omega⟩ : Fin n) D hD⟩
      · intro t
        refine ⟨t.det, ?_⟩
        have heq :
            (⟨t.toMatrix, t.det⟩ : SL) = huppert613_elementarySL t := by
          apply Subtype.ext
          rfl
        rw [heq]
        exact Subgroup.subset_closure (Set.mem_range_self t)
      · rintro M N ⟨hM, hMmem⟩ ⟨hN, hNmem⟩
        have hMN : Matrix.det (M * N) = 1 := by simp [hM, hN]
        refine ⟨hMN, ?_⟩
        exact H.mul_mem hMmem hNmem
    rcases hP with ⟨hA, hAmem⟩
    have hAEq :
        (⟨(A : Matrix (Fin n) (Fin n) K), hA⟩ : SL) = A :=
      Subtype.ext rfl
    rw [← hAEq]
    exact hAmem
  have hSLperfect : commutator SL = ⊤ := by
    apply top_unique
    rw [← htransvection_generation, Subgroup.closure_le]
    rintro _ ⟨t, rfl⟩
    by_cases hn2 : n = 2
    · subst n
      simp only [ne_eq, not_true_eq_false, false_or] at h22 h23
      exact huppert613_elementarySL_mem_commutator_fin_two h22 h23 t
    · rcases t with ⟨i, j, hij, c⟩
      obtain ⟨k, hki, hkj⟩ :=
        Fin.exists_ne_and_ne_of_two_lt i j (by omega)
      have hstein := huppert613_steinberg_commutator
        i j k hij hki.symm hkj c 1
      simp only [mul_one] at hstein
      rw [← hstein]
      exact Subgroup.commutator_mem_commutator
        (H₁ := (⊤ : Subgroup SL)) (H₂ := (⊤ : Subgroup SL))
        (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hperfect : commutator PSL = ⊤ := by
    let q : SL →* PSL :=
      QuotientGroup.mk' (Subgroup.center SL)
    have hqtop : (⊤ : Subgroup SL).map q = ⊤ :=
      Subgroup.map_top_of_surjective q
        (QuotientGroup.mk'_surjective (Subgroup.center SL))
    calc
      commutator PSL = (commutator SL).map q := by
        symm
        rw [_root_.commutator_def, _root_.commutator_def,
          Subgroup.map_commutator, hqtop]
      _ = ⊤ := by rw [hSLperfect, hqtop]
  have hprojective_action :=
    huppert_II_6_11_projective_action (K := K) n hn
  rcases hprojective_action with
    ⟨rho, hrho, hrho_apply, htwo_transitive⟩
  have hroot_subgroup :
      ∃ (a : P) (T : Subgroup PSL),
        let U := (MulAction.stabilizer (Equiv.Perm P) a).comap rho
        T ≤ U ∧ (T.subgroupOf U).Normal ∧
          IsSolvable T ∧ Subgroup.normalClosure (T : Set PSL) = ⊤ := by
    let V := Fin n → K
    let q : SL →* PSL := QuotientGroup.mk' (Subgroup.center SL)
    let w : V := huppert613_basisVector (K := K) (⟨0, by omega⟩ : Fin n)
    have hw : w ≠ 0 := by
      intro h
      have h0 : (1 : K) = 0 := by
        calc
          1 = w (⟨0, by omega⟩ : Fin n) := by
            simp [w, huppert613_basisVector]
          _ = 0 := by rw [h]; rfl
      exact one_ne_zero h0
    let a : P := Projectivization.mk K w hw
    let A := LinearMap.ker ((Module.Dual.eval K V) w)
    have haf (f : A) : (f : Module.Dual K V) w = 0 := by
      have hf := f.property
      change ((Module.Dual.eval K V) w) (f : Module.Dual K V) = 0 at hf
      simpa only [Module.Dual.eval_apply] using hf
    let rootV : AddChar A (_root_.SpecialLinearGroup K V) :=
      { toFun := fun f =>
          ⟨LinearEquiv.transvection (haf f),
            LinearEquiv.transvection.det_eq_one (haf f)⟩
        map_zero_eq_one' := by
          apply Subtype.ext
          apply LinearEquiv.ext
          intro x
          simp
        map_add_eq_mul' := by
          intro f g
          apply Subtype.ext
          apply LinearEquiv.ext
          intro x
          exact
            (LinearMap.transvection.comp_of_right_eq_apply (haf f)).symm }
    let eSL := Matrix.SpecialLinearGroup.toLin'_equiv
      (R := K) (n := Fin n)
    let rootSL : AddChar A SL :=
      eSL.symm.toMonoidHom.compAddChar rootV
    let rootPSL : AddChar A PSL := q.compAddChar rootSL
    let T : Subgroup PSL :=
      { carrier := Set.range rootPSL
        one_mem' := ⟨0, rootPSL.map_zero_eq_one⟩
        mul_mem' := by
          rintro x y ⟨f, rfl⟩ ⟨g, rfl⟩
          exact ⟨f + g, rootPSL.map_add_eq_mul f g⟩
        inv_mem' := by
          rintro x ⟨f, rfl⟩
          exact ⟨-f, rootPSL.map_neg_eq_inv f⟩ }
    let U := (MulAction.stabilizer (Equiv.Perm P) a).comap rho
    have hTle : T ≤ U := by
      intro x hx
      rcases hx with ⟨f, rfl⟩
      change rho (rootPSL f) a = a
      rw [show rootPSL f = q (rootSL f) by rfl, hrho_apply]
      have heroot : eSL (rootSL f) = rootV f := by
        change eSL (eSL.symm (rootV f)) = rootV f
        exact eSL.apply_symm_apply (rootV f)
      have hlin : Matrix.SpecialLinearGroup.toLin' (rootSL f) =
          (rootV f : V ≃ₗ[K] V) := congrArg Subtype.val heroot
      rw [show (Matrix.GeneralLinearGroup.toLin
          ((rootSL f : SL) : GL (Fin n) K)).toLinearEquiv =
          Matrix.SpecialLinearGroup.toLin' (rootSL f) by rfl, hlin]
      change Projectivization.mk K ((rootV f : V ≃ₗ[K] V) w) _ =
        Projectivization.mk K w hw
      have hfix : (rootV f : V ≃ₗ[K] V) w = w := by
        change w + (f : Module.Dual K V) w • w = w
        rw [haf f, zero_smul, add_zero]
      apply (Projectivization.mk_eq_mk_iff K _ _ _ _).2
      refine ⟨1, ?_⟩
      simpa using hfix.symm
    refine ⟨a, T, hTle, ?_, ?_, ?_⟩
    · apply (Subgroup.normal_subgroupOf_iff hTle).2
      intro x g hx hg
      rcases hx with ⟨f, rfl⟩
      rcases QuotientGroup.mk'_surjective (Subgroup.center SL) g with ⟨B, rfl⟩
      change rho (q B) a = a at hg
      rw [show q B = QuotientGroup.mk' (Subgroup.center SL) B by rfl,
        hrho_apply] at hg
      let eB : V ≃ₗ[K] V := (eSL B : _root_.SpecialLinearGroup K V)
      rw [show (Matrix.GeneralLinearGroup.toLin
          ((B : SL) : GL (Fin n) K)).toLinearEquiv = eB by rfl] at hg
      change Projectivization.mk K (eB w) _ =
        Projectivization.mk K w hw at hg
      rcases (Projectivization.mk_eq_mk_iff K _ _ _ _).1 hg with ⟨s, hs⟩
      have hsK : (s : K) • w = eB w := by
        simpa [Units.smul_def] using hs
      have hs_inv : eB.symm w = ((s⁻¹ : Kˣ) : K) • w := by
        apply eB.injective
        rw [eB.apply_symm_apply, map_smul, ← hsK]
        simp [smul_smul]
      let fB : Module.Dual K V :=
        (s : K) • ((f : Module.Dual K V) ∘ₗ eB.symm)
      have hfB : fB w = 0 := by
        simp [fB, hs_inv, haf f]
      let fA : A := ⟨fB, by
        change ((Module.Dual.eval K V) w) fB = 0
        simpa only [Module.Dual.eval_apply] using hfB⟩
      have hSLconj : B * rootSL f * B⁻¹ = rootSL fA := by
        apply eSL.injective
        simp only [map_mul, map_inv]
        have hroot (u : A) : eSL (rootSL u) = rootV u := by
          change eSL (eSL.symm (rootV u)) = rootV u
          exact eSL.apply_symm_apply (rootV u)
        rw [hroot f, hroot fA]
        apply Subtype.ext
        apply LinearEquiv.ext
        intro z
        change eB ((LinearEquiv.transvection (haf f)) (eB.symm z)) =
          (LinearEquiv.transvection (haf fA)) z
        simp only [LinearEquiv.transvection.apply, map_add,
          eB.apply_symm_apply]
        rw [map_smul]
        change z + (f : Module.Dual K V) (eB.symm z) • eB w =
          z + fB z • w
        rw [← hsK]
        simp [fB, smul_smul, mul_comm]
      refine ⟨fA, ?_⟩
      change rootPSL fA = q B * rootPSL f * (q B)⁻¹
      rw [show rootPSL fA = q (rootSL fA) by rfl,
        show rootPSL f = q (rootSL f) by rfl, ← map_inv, ← map_mul, ← map_mul,
        hSLconj]
    · apply isSolvable_of_comm
      rintro ⟨x, ⟨f, rfl⟩⟩ ⟨y, ⟨g, rfl⟩⟩
      apply Subtype.ext
      change rootPSL f * rootPSL g = rootPSL g * rootPSL f
      rw [← rootPSL.map_add_eq_mul, add_comm, rootPSL.map_add_eq_mul]
    · let N := Subgroup.normalClosure (T : Set PSL)
      letI : N.Normal := Subgroup.normalClosure_normal
      have himage : q '' transvections ⊆ N := by
        rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
        rcases t with ⟨i, j, hij, c⟩
        let i0 : Fin n := ⟨0, by omega⟩
        let i1 : Fin n := ⟨1, by omega⟩
        let vi : V := huppert613_basisVector i
        let vj : V := huppert613_basisVector j
        have hvi : vi ≠ 0 := huppert613_basisVector_ne_zero i
        have hvj : vj ≠ 0 := huppert613_basisVector_ne_zero j
        let b : P := Projectivization.mk K (huppert613_basisVector i1)
          (huppert613_basisVector_ne_zero i1)
        let ai : P := Projectivization.mk K vi hvi
        let aj : P := Projectivization.mk K vj hvj
        have hab : a ≠ b := by
          simpa [a, b, w, i0] using
            (huppert613_projective_basis_ne (K := K) i0 i1 (by simp [i0, i1]))
        have haiaj : ai ≠ aj := by
          simpa [ai, aj, vi, vj] using
            (huppert613_projective_basis_ne (K := K) i j hij)
        obtain ⟨g, hga, _hgb⟩ :=
          htwo_transitive a b ai aj hab haiaj
        obtain ⟨B, rfl⟩ :=
          QuotientGroup.mk'_surjective (Subgroup.center SL) g
        let eB : V ≃ₗ[K] V := (eSL B : _root_.SpecialLinearGroup K V)
        rw [hrho_apply, show (Matrix.GeneralLinearGroup.toLin
            ((B : SL) : GL (Fin n) K)).toLinearEquiv = eB by rfl] at hga
        change Projectivization.mk K (eB w) _ =
          Projectivization.mk K vi hvi at hga
        rcases (Projectivization.mk_eq_mk_iff K _ _ _ _).1 hga with ⟨s, hs⟩
        have hsK : (s : K) • vi = eB w := by
          simpa [Units.smul_def] using hs
        let ft : Module.Dual K V := c • huppert613_coord j
        have hft : ft vi = 0 := by
          change c * ((Pi.single i (1 : K) : Fin n → K) j) = 0
          rw [Pi.single_eq_of_ne hij.symm, mul_zero]
        let fpre : Module.Dual K V :=
          ((s⁻¹ : Kˣ) : K) • (ft ∘ₗ eB)
        have hfpre : fpre w = 0 := by
          change ((s⁻¹ : Kˣ) : K) * ft (eB w) = 0
          rw [← hsK]
          simp [hft]
        let fp : A := ⟨fpre, by
          change ((Module.Dual.eval K V) w) fpre = 0
          simpa only [Module.Dual.eval_apply] using hfpre⟩
        have hSLconj :
            B * rootSL fp * B⁻¹ =
              huppert613_elementarySL
                (⟨i, j, hij, c⟩ : Matrix.TransvectionStruct (Fin n) K) := by
          apply eSL.injective
          simp only [map_mul, map_inv]
          have hroot : eSL (rootSL fp) = rootV fp := by
            change eSL (eSL.symm (rootV fp)) = rootV fp
            exact eSL.apply_symm_apply (rootV fp)
          rw [hroot, huppert613_toLin_elementarySL]
          apply Subtype.ext
          apply LinearEquiv.ext
          intro z
          change eB ((LinearEquiv.transvection (haf fp)) (eB.symm z)) =
            (LinearEquiv.transvection hft) z
          simp only [LinearEquiv.transvection.apply, map_add,
            eB.apply_symm_apply]
          rw [map_smul]
          change z + fpre (eB.symm z) • eB w = z + ft z • vi
          rw [← hsK]
          simp [fpre, smul_smul, mul_assoc]
          congr 1
          field_simp [Units.ne_zero s]
        have hrootN : rootPSL fp ∈ N :=
          Subgroup.subset_normalClosure ⟨fp, rfl⟩
        have hconjN :
            q B * rootPSL fp * (q B)⁻¹ ∈ N :=
          Subgroup.normalClosure_normal.conj_mem _ hrootN (q B)
        have hqconj := congrArg q hSLconj
        change q B * rootPSL fp * (q B)⁻¹ =
          q (huppert613_elementarySL
            (⟨i, j, hij, c⟩ : Matrix.TransvectionStruct (Fin n) K)) at hqconj
        rw [← hqconj]
        exact hconjN
      have hqtop : (⊤ : Subgroup SL).map q = ⊤ :=
        Subgroup.map_top_of_surjective q
          (QuotientGroup.mk'_surjective (Subgroup.center SL))
      apply top_unique
      calc
        (⊤ : Subgroup PSL) = (⊤ : Subgroup SL).map q := hqtop.symm
        _ = (Subgroup.closure transvections).map q := by
          rw [htransvection_generation]
        _ = Subgroup.closure (q '' transvections) :=
          MonoidHom.map_closure q transvections
        _ ≤ N := (Subgroup.closure_le N).2 himage
  have hiwasawa_application : IsSimpleGroup PSL := by
    letI : MulAction PSL P := MulAction.compHom P rho
    have htwo : MulAction.IsMultiplyPretransitive PSL P 2 := by
      rw [MulAction.is_two_pretransitive_iff]
      intro a b c d hab hcd
      obtain ⟨g, hga, hgb⟩ := htwo_transitive a b c d hab hcd
      exact ⟨g, hga, hgb⟩
    letI : MulAction.IsMultiplyPretransitive PSL P 2 := htwo
    letI : MulAction.IsPretransitive PSL P :=
      MulAction.isPretransitive_of_is_two_pretransitive
    letI : MulAction.IsPreprimitive PSL P :=
      MulAction.isPreprimitive_of_is_two_pretransitive htwo
    letI : FaithfulSMul PSL P := faithfulSMul_iff.mpr (by
      intro g hg
      apply hrho
      apply Equiv.ext
      intro x
      have hgx := hg x
      change rho g x = x at hgx
      simpa using hgx)
    let i0 : Fin n := ⟨0, by omega⟩
    let i1 : Fin n := ⟨1, by omega⟩
    let p0 : P := Projectivization.mk K (huppert613_basisVector i0)
      (huppert613_basisVector_ne_zero i0)
    let p1 : P := Projectivization.mk K (huppert613_basisVector i1)
      (huppert613_basisVector_ne_zero i1)
    have hp01 : p0 ≠ p1 := by
      simpa [p0, p1] using
        (huppert613_projective_basis_ne (K := K) i0 i1 (by simp [i0, i1]))
    obtain ⟨g, hg, _⟩ :=
      htwo_transitive p0 p1 p1 p0 hp01 hp01.symm
    have hg1 : g ≠ 1 := by
      intro hgone
      subst g
      simp at hg
      exact hp01 hg
    letI : Nontrivial PSL := ⟨⟨g, 1, hg1⟩⟩
    rcases hroot_subgroup with
      ⟨a, T, hTle, hTnormal, hTsolvable, hTgenerates⟩
    have hUeq :
        (MulAction.stabilizer (Equiv.Perm P) a).comap rho =
          MulAction.stabilizer PSL a := by
      ext x
      rfl
    exact huppert_II_6_12 hperfect a T
      (by rw [← hUeq]; exact hTle)
      (by rw [← hUeq]; exact hTnormal)
      hTsolvable hTgenerates
  exact hiwasawa_application

end External
end CFSG.BenderSuzuki
