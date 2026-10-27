module

public import CFSG.OddTranspositions.PartThree.Eleven.Five.Refl
import CFSG.OddTranspositions.PartThree.Eleven.Five.Hom
import CFSG.ClassicalInvolution.Orders.OrthogonalNeg
import TauCeti.LinearAlgebra.Matrix.OneSubVecMulVec
import TauCeti.Algebra.Group.Units.Basic
import TauCeti.FieldTheory.SquareClassGroup.Basic

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix QuadraticMap CFSG.ClassicalInvolution
open CFSG.ClassicalGroups.Orthogonal (reflect reflect_mem_orthogonalGroup
  reflect_eq_reflection)

set_option backward.isDefEq.respectTransparency false

private instance : Invertible (2 : ZMod 5) := invertibleOfNonzero (by decide)

private def w5 : Fin 5 → ZMod 5 := ![1, 1, 1, 1, -1]

private noncomputable def Qplus : QuadraticForm (ZMod 5) (Fin 5 → ZMod 5) :=
  QuadraticMap.weightedSumSquares (ZMod 5) w5

private theorem w5_castSucc (i : Fin 4) : w5 i.castSucc = 1 := by
  fin_cases i <;> decide

private theorem w5_last : w5 (Fin.last 4) = -1 := by
  decide

private theorem Qplus_apply (x : Fin 5 → ZMod 5) : Qplus x = fiveForm 4 true x x := by
  rw [Qplus, QuadraticMap.weightedSumSquares_apply]
  conv_lhs => rw [Fin.sum_univ_castSucc]
  rw [fiveForm]
  simp only [w5_castSucc, w5_last, smul_eq_mul, one_mul, ↓reduceIte]
  ring_nf

private theorem fiveForm_add_left (x y z : Fin 5 → ZMod 5) :
    fiveForm 4 true (x + y) z = fiveForm 4 true x z + fiveForm 4 true y z := by
  simp only [fiveForm, Pi.add_apply, add_mul, ↓reduceIte]
  rw [Finset.sum_add_distrib]
  ring

private theorem fiveForm_add_right (x y z : Fin 5 → ZMod 5) :
    fiveForm 4 true x (y + z) = fiveForm 4 true x y + fiveForm 4 true x z := by
  simp only [fiveForm, Pi.add_apply, mul_add, ↓reduceIte]
  rw [Finset.sum_add_distrib]
  ring

private theorem Qplus_polar (x y : Fin 5 → ZMod 5) :
    QuadraticMap.polar Qplus x y = 2 * fiveForm 4 true x y := by
  show Qplus (x + y) - Qplus x - Qplus y = 2 * fiveForm 4 true x y
  rw [Qplus_apply, Qplus_apply, Qplus_apply]
  simp only [fiveForm_add_left, fiveForm_add_right]
  rw [fiveForm_comm 4 true y x]
  ring

private theorem Qplus_nondegenerate : Qplus.Nondegenerate :=
  QuadraticMap.nondegenerate_weightedSumSquares (w := w5) fun i => by
    rw [isRegular_iff_ne_zero]
    fin_cases i <;> decide

private theorem Qplus_single (i : Fin 5) :
    Qplus (Pi.single i (1 : ZMod 5)) = w5 i := by
  rw [Qplus, QuadraticMap.weightedSumSquares_apply, Fintype.sum_eq_single i]
  · simp
  · intro j hj
    simp [hj]

private theorem fiveFormVec_dotProduct {n : ℕ} {ε : Bool} (x : Fin (n + 1) → ZMod 5) :
    fiveFormVec n ε x ⬝ᵥ x = fiveForm n ε x x := by
  unfold fiveFormVec fiveForm dotProduct
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.castSucc_ne_last, ↓reduceIte]
  ring

private noncomputable def iota : GL (Fin 5) (ZMod 5) →*
    ((Fin 5 → ZMod 5) ≃ₗ[ZMod 5] (Fin 5 → ZMod 5)) :=
  fiveGLEquiv.toMonoidHom

private theorem iota_apply (g : GL (Fin 5) (ZMod 5)) (x : Fin 5 → ZMod 5) :
    iota g x = (g : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x := by
  change fiveGLEquiv g x = _
  rw [fiveGLEquiv_apply]

private theorem iota_mem_O {g : GL (Fin 5) (ZMod 5)}
    (hg : g ∈ fiveReflectionGroup 4 true false) :
    iota g ∈ TauCeti.QuadraticMap.orthogonalGroup Qplus := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro m
  rw [iota_apply, Qplus_apply, Qplus_apply]
  exact fiveForm_mulVec_of_mem hg m m

private theorem iota_fiveReflOf (v : Fin 5 → ZMod 5) [Invertible (Qplus v)] :
    (iota (fiveReflOf 4 true v) :
        (Fin 5 → ZMod 5) ≃ₗ[ZMod 5] (Fin 5 → ZMod 5)) =
      (TauCeti.QuadraticMap.reflectionOrthogonal Qplus v :
        (Fin 5 → ZMod 5) ≃ₗ[ZMod 5] (Fin 5 → ZMod 5)) := by
  rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal]
  ext y
  rw [iota_apply, fiveReflOf_mulVec, TauCeti.QuadraticMap.reflection_apply, Qplus_polar]
  congr 1
  rw [invOf_eq_inv, Qplus_apply, fiveForm_comm 4 true v y]
  ring_nf

private theorem iota_neg_one :
    (iota (-1 : GL (Fin 5) (ZMod 5)) :
        (Fin 5 → ZMod 5) ≃ₗ[ZMod 5] (Fin 5 → ZMod 5)) =
      (QuadraticMap.negOrthogonal Qplus :
        (Fin 5 → ZMod 5) ≃ₗ[ZMod 5] (Fin 5 → ZMod 5)) := by
  rw [QuadraticMap.coe_negOrthogonal]
  ext x
  rw [iota_apply,
    show (-1 : GL (Fin 5) (ZMod 5)) = -(1 : GL (Fin 5) (ZMod 5)) from rfl,
    Units.val_neg, Units.val_one, Matrix.neg_mulVec, Matrix.one_mulVec]
  rfl

private noncomputable def reflO (v : Fin 5 → ZMod 5) :
    TauCeti.QuadraticMap.orthogonalGroup Qplus :=
  ⟨reflect Qplus v, reflect_mem_orthogonalGroup Qplus v⟩

private def bl : List (Fin 5 → ZMod 5) :=
  [Pi.single 0 1, Pi.single 1 1, Pi.single 2 1, Pi.single 3 1, Pi.single 4 1]

private theorem bl_ne_zero : ∀ a ∈ bl, Qplus a ≠ 0 := by
  intro a ha
  simp only [bl, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl <;>
    (rw [Qplus_single]; decide)

private theorem bl_pairwise :
    bl.Pairwise (fun a b => QuadraticMap.polar Qplus a b = 0) := by
  rw [bl, List.pairwise_cons]
  refine ⟨?_, ?_⟩
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> decide
  · rw [List.pairwise_cons]
    refine ⟨?_, ?_⟩
    · intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl <;> decide
    · rw [List.pairwise_cons]
      refine ⟨?_, ?_⟩
      · intro b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl <;> decide
      · rw [List.pairwise_cons]
        refine ⟨?_, ?_⟩
        · intro b hb
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl <;> decide
        · rw [List.pairwise_cons]
          exact ⟨by intro b hb; simp at hb, List.Pairwise.nil⟩

private theorem bl_span : Submodule.span (ZMod 5) {v | v ∈ bl} = ⊤ := by
  refine CFSG.ClassicalInvolution.span_eq_top_of_pairwise_polar (K := ZMod 5)
    (V := Fin 5 → ZMod 5) (Q := Qplus) (by decide) bl_ne_zero bl_pairwise ?_
  rw [bl, Module.finrank_fintype_fun_eq_card]
  simp

private theorem bl_prod_reflect :
    (bl.map (fun v => reflect Qplus v)).prod =
      (LinearEquiv.neg (ZMod 5) :
        (Fin 5 → ZMod 5) ≃ₗ[ZMod 5] (Fin 5 → ZMod 5)) :=
  CFSG.ClassicalInvolution.prod_map_reflect_eq_neg (Q := Qplus) bl_ne_zero bl_pairwise
    bl_span

private theorem bl_prod_reflectO :
    QuadraticMap.negOrthogonal Qplus = (bl.map reflO).prod := by
  apply Subtype.ext
  rw [QuadraticMap.coe_negOrthogonal, Subgroup.val_list_prod, List.map_map]
  exact bl_prod_reflect.symm

private theorem detSpinorNorm_reflO (hQ : Qplus.Nondegenerate) {v : Fin 5 → ZMod 5}
    [Invertible (Qplus v)] : detSpinorNorm hQ (reflO v) =
      ((-1 : (ZMod 5)ˣ), TauCeti.squareClassHom (unitOfInvertible (Qplus v))) := by
  have hrefl : reflO v = TauCeti.QuadraticMap.reflectionOrthogonal Qplus v := by
    apply Subtype.ext
    rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal]
    exact reflect_eq_reflection
  rw [hrefl, detSpinorNorm_reflectionOrthogonal]

private def two5 : (ZMod 5)ˣ := Units.mk0 (2 : ZMod 5) (by decide)

private theorem squareClassHom_eq_one_of_isSquare_val {u : (ZMod 5)ˣ}
    (hu : IsSquare (u : ZMod 5)) : TauCeti.squareClassHom u = 1 := by
  rw [← MonoidHom.mem_ker, TauCeti.ker_squareClassHom, Subgroup.mem_square]
  exact TauCeti.isSquare_units_val_iff.mp hu

private theorem squareClassHom_unitOfInvertible_eq_one {x : ZMod 5} [Invertible x]
    (hx : IsSquare x) : TauCeti.squareClassHom (unitOfInvertible x) = 1 :=
  squareClassHom_eq_one_of_isSquare_val (by simpa [val_unitOfInvertible] using hx)

private noncomputable def f (v : Fin 5 → ZMod 5) : (ZMod 5)ˣ :=
  if h : Qplus v = 0 then 1 else Units.mk0 (Qplus v) h

private lemma list_prod_pair (l : List (Fin 5 → ZMod 5))
    (g : (Fin 5 → ZMod 5) → (ZMod 5)ˣ) :
    (l.map (fun v => ((-1 : (ZMod 5)ˣ), TauCeti.squareClassHom (g v)))).prod =
      (((-1 : (ZMod 5)ˣ) ^ l.length, TauCeti.squareClassHom ((l.map g).prod))) := by
  induction l with
  | nil => refine Prod.ext rfl ?_
           exact (map_one (TauCeti.squareClassHom (K := ZMod 5))).symm
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, ih, pow_succ, map_mul]
    exact Prod.ext (mul_comm _ _) rfl

private theorem bl_prod_Qplus : (bl.map Qplus).prod = -1 := by
  simp only [bl, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Qplus_single]
  decide

private theorem isSquare_map_f : IsSquare ((bl.map f).prod) := by
  have hval : (((bl.map f).prod : (ZMod 5)ˣ) : ZMod 5) = -1 := by
    change (Units.coeHom (ZMod 5)) ((bl.map f).prod) = -1
    rw [map_list_prod (Units.coeHom (ZMod 5)) (bl.map f), List.map_map]
    refine (congrArg List.prod ?_).trans bl_prod_Qplus
    apply List.map_congr_left
    intro v hv
    simp [Function.comp_apply, f, bl_ne_zero v hv]
  rw [← TauCeti.isSquare_units_val_iff, hval]
  exact ⟨2, by decide⟩

private theorem detSpinorNorm_negOrthogonal (hQ : Qplus.Nondegenerate) :
    detSpinorNorm hQ (QuadraticMap.negOrthogonal Qplus) = (-1, 1) := by
  have hdet : detSpinorNorm hQ (QuadraticMap.negOrthogonal Qplus) =
      (bl.map (fun v => detSpinorNorm hQ (reflO v))).prod := by
    rw [bl_prod_reflectO, map_list_prod, List.map_map]
    rfl
  rw [hdet]
  have hper : ∀ v ∈ bl, detSpinorNorm hQ (reflO v) =
      ((-1 : (ZMod 5)ˣ), TauCeti.squareClassHom (f v)) := by
    intro v hv
    letI : Invertible (Qplus v) := invertibleOfNonzero (bl_ne_zero v hv)
    rw [detSpinorNorm_reflO hQ]
    congr 1
    apply congrArg TauCeti.squareClassHom
    apply Units.ext
    rw [val_unitOfInvertible]
    simp [f, bl_ne_zero v hv]
  rw [show (bl.map (fun v => detSpinorNorm hQ (reflO v))).prod =
      (bl.map (fun v => ((-1 : (ZMod 5)ˣ), TauCeti.squareClassHom (f v)))).prod by
    apply congrArg List.prod
    exact List.map_congr_left hper]
  rw [list_prod_pair]
  refine Prod.ext ?_ ?_
  · rw [show bl.length = 5 from rfl]
    decide
  · rw [← MonoidHom.mem_ker, TauCeti.ker_squareClassHom, Subgroup.mem_square]
    exact isSquare_map_f

private def aH : (ZMod 5)ˣ × Multiplicative (TauCeti.SquareClassGroup (ZMod 5)) :=
  (-1, TauCeti.squareClassHom two5)

private theorem aH_mul_self : aH * aH = 1 := by
  rw [aH]
  refine Prod.ext ?_ ?_
  · apply Units.ext
    simp
  · change TauCeti.squareClassHom two5 * TauCeti.squareClassHom two5 = 1
    rw [← map_mul]
    exact squareClassHom_eq_one_of_isSquare_val (by
      rw [Units.val_mul, two5, Units.val_mk0]
      decide)

private noncomputable def H : Subgroup
    ((ZMod 5)ˣ × Multiplicative (TauCeti.SquareClassGroup (ZMod 5))) where
  carrier := {x | x = 1 ∨ x = aH}
  mul_mem' := by
    rintro x y (rfl | rfl) (rfl | rfl)
    · exact Or.inl (one_mul 1)
    · exact Or.inr (one_mul aH)
    · exact Or.inr (mul_one aH)
    · exact Or.inl aH_mul_self
  one_mem' := Or.inl rfl
  inv_mem' := by
    rintro x (rfl | rfl)
    · exact Or.inl (inv_one)
    · exact Or.inr (inv_eq_of_mul_eq_one_left aH_mul_self)

private theorem negOnePair_notMem_H :
    ((-1 : (ZMod 5)ˣ),
      (1 : Multiplicative (TauCeti.SquareClassGroup (ZMod 5)))) ∉ H := by
  intro h
  rcases h with h | h
  · exact absurd (congrArg Prod.fst h) (by decide)
  · have h2 : (1 : Multiplicative (TauCeti.SquareClassGroup (ZMod 5))) =
        TauCeti.squareClassHom two5 := congrArg Prod.snd h
    have hsc : TauCeti.squareClassHom two5 = 1 := h2.symm
    rw [← MonoidHom.mem_ker, TauCeti.ker_squareClassHom, Subgroup.mem_square,
      ← TauCeti.isSquare_units_val_iff, two5, Units.val_mk0] at hsc
    exact absurd hsc (by decide)

private theorem squareClassHom_unitOfInvertible_of_nonsquare {x : ZMod 5} [Invertible x]
    (hx : ¬ IsSquare x) :
    TauCeti.squareClassHom (unitOfInvertible x) = TauCeti.squareClassHom two5 := by
  rw [TauCeti.squareClassHom_apply, TauCeti.squareClassHom_apply,
    Multiplicative.ofAdd.injective.eq_iff]
  rw [TauCeti.squareClass_eq_iff_isSquare_mul, ← TauCeti.isSquare_units_val_iff,
    Units.val_mul, val_unitOfInvertible, two5, Units.val_mk0]
  fin_cases x
  · exact absurd (⟨0, by decide⟩ : IsSquare (0 : ZMod 5)) hx
  · exact absurd (⟨1, by decide⟩ : IsSquare (1 : ZMod 5)) hx
  · decide
  · decide
  · exact absurd (⟨2, by decide⟩ : IsSquare (4 : ZMod 5)) hx

private theorem detSpinorNorm_iota_mem_H (hQ : Qplus.Nondegenerate)
    (g : GL (Fin 5) (ZMod 5)) (hg : g ∈ fiveReflectionGroup 4 true false) :
    detSpinorNorm hQ ⟨iota g, iota_mem_O hg⟩ ∈ H := by
  refine Subgroup.closure_induction (k := fiveReflections 4 true false)
    (p := fun g hg => detSpinorNorm hQ ⟨iota g, iota_mem_O hg⟩ ∈ H)
    ?_ ?_ ?_ ?_ hg
  · intro r hr
    obtain ⟨v, hv, hnsq, rfl⟩ := exists_eq_fiveReflOf hr
    have hv' : Qplus v ≠ 0 := by rwa [Qplus_apply]
    have hnsq' : ¬ IsSquare (Qplus v) := by
      intro h
      exact Bool.false_ne_true (hnsq.mp (by rwa [Qplus_apply] at h))
    letI : Invertible (Qplus v) := invertibleOfNonzero hv'
    have hsub : (⟨iota (fiveReflOf 4 true v),
        iota_mem_O (Subgroup.subset_closure hr)⟩ :
        TauCeti.QuadraticMap.orthogonalGroup Qplus) =
        TauCeti.QuadraticMap.reflectionOrthogonal Qplus v :=
      Subtype.ext (iota_fiveReflOf v)
    rw [hsub, detSpinorNorm_reflectionOrthogonal,
      squareClassHom_unitOfInvertible_of_nonsquare hnsq']
    exact Or.inr rfl
  · have hone : (⟨iota 1, iota_mem_O (Subgroup.one_mem _)⟩ :
        TauCeti.QuadraticMap.orthogonalGroup Qplus) = 1 :=
      Subtype.ext (map_one iota)
    rw [hone, map_one]
    exact H.one_mem
  · intro x y hx hy ihx ihy
    have hxy : (⟨iota (x * y), iota_mem_O (Subgroup.mul_mem _ hx hy)⟩ :
        TauCeti.QuadraticMap.orthogonalGroup Qplus) =
        ⟨iota x, iota_mem_O hx⟩ * ⟨iota y, iota_mem_O hy⟩ :=
      Subtype.ext (map_mul iota x y)
    rw [hxy, map_mul]
    exact H.mul_mem ihx ihy
  · intro x hx ihx
    have hxy : (⟨iota x⁻¹, iota_mem_O (Subgroup.inv_mem _ hx)⟩ :
        TauCeti.QuadraticMap.orthogonalGroup Qplus) =
        ⟨iota x, iota_mem_O hx⟩⁻¹ :=
      Subtype.ext (map_inv iota x)
    rw [hxy, map_inv]
    exact H.inv_mem ihx

theorem det_fiveReflOf {n : ℕ} {ε : Bool} {x : Fin (n + 1) → ZMod 5}
    (hx : fiveForm n ε x x ≠ 0) :
    Matrix.GeneralLinearGroup.det (fiveReflOf n ε x) = -1 := by
  apply Units.ext
  change Matrix.det (fiveReflMatrix n ε x) = (-1 : ZMod 5)
  have hmat : fiveReflMatrix n ε x =
      1 - vecMulVec ((2 * (fiveForm n ε x x)⁻¹) • x) (fiveFormVec n ε x) := by
    rw [fiveReflMatrix, smul_vecMulVec]
  rw [hmat, TauCeti.det_one_sub_vecMulVec, dotProduct_smul,
    fiveFormVec_dotProduct, smul_eq_mul]
  rw [show (2 * (fiveForm n ε x x)⁻¹) * fiveForm n ε x x = 2 by
    rw [mul_assoc, inv_mul_cancel₀ hx, mul_one]]
  rfl

theorem neg_one_notMem_fiveReflectionGroup_four_true_false :
    (-1 : GL (Fin 5) (ZMod 5)) ∉ fiveReflectionGroup 4 true false := by
  intro hmem
  have hH := detSpinorNorm_iota_mem_H Qplus_nondegenerate (-1) hmem
  have hsub : (⟨iota (-1 : GL (Fin 5) (ZMod 5)), iota_mem_O hmem⟩ :
      TauCeti.QuadraticMap.orthogonalGroup Qplus) =
      QuadraticMap.negOrthogonal Qplus :=
    Subtype.ext iota_neg_one
  rw [hsub, detSpinorNorm_negOrthogonal Qplus_nondegenerate] at hH
  exact negOnePair_notMem_H hH

theorem notMem_fiveReflectionGroup_four_true_false_of_mem_fiveReflections_true
    {r : GL (Fin 5) (ZMod 5)} (hr : r ∈ fiveReflections 4 true true) :
    r ∉ fiveReflectionGroup 4 true false := by
  intro hmem
  obtain ⟨v, hv, hsq, rfl⟩ := exists_eq_fiveReflOf hr
  have hv' : Qplus v ≠ 0 := by rwa [Qplus_apply]
  have hsq' : IsSquare (Qplus v) := by
    rw [Qplus_apply]
    exact hsq.mpr rfl
  letI : Invertible (Qplus v) := invertibleOfNonzero hv'
  have hH := detSpinorNorm_iota_mem_H Qplus_nondegenerate (fiveReflOf 4 true v) hmem
  have hsub : (⟨iota (fiveReflOf 4 true v), iota_mem_O hmem⟩ :
      TauCeti.QuadraticMap.orthogonalGroup Qplus) =
      TauCeti.QuadraticMap.reflectionOrthogonal Qplus v :=
    Subtype.ext (iota_fiveReflOf v)
  rw [hsub, detSpinorNorm_reflectionOrthogonal,
    squareClassHom_unitOfInvertible_eq_one hsq'] at hH
  exact negOnePair_notMem_H hH

end CFSG.OddTranspositions.PartThree
