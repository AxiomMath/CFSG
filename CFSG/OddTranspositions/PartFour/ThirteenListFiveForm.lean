module

public import CFSG.OddTranspositions.PartFour.Fourteen.TableE1Five
public import CFSG.OddTranspositions.PartThree.FiveReflectionFischer
public import CFSG.LocalAnalysis.WeakClosure81.SevenNineDefs
import CFSG.OddTranspositions.PartThree.Eleven.Five.Refl
import CFSG.ClassicalInvolution.Orders.OrthogonalIndex
import CFSG.ClassicalInvolution.Orders.OrthogonalNeg
import CFSG.ClassicalGroups.Orthogonal.Matrix
import CFSG.LieType.Universal.Spin.Forms
import TauCeti.Algebra.Group.Units.Basic
import TauCeti.FieldTheory.SquareClassGroup.Basic
public import CFSG.LocalAnalysis.WeakClosure81.SevenFour
public import CFSG.LocalAnalysis.WeakClosure81.SevenKGen
public import CFSG.RankThree.GF2n.Tim79aSec2

public section

namespace CFSG.OddTranspositions.PartFour.ListFive

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.OddTranspositions.PartThree CFSG.LocalAnalysis.WeakClosure81
open CFSG.OddTranspositions.PartFour.TableE1Five

@[expose] def minusBilin : LinearMap.BilinForm (ZMod 5) (Fin 4 → ZMod 5) :=
  fiveBilin 3 false true

theorem minusBilin_apply (x y : Fin 4 → ZMod 5) :
    minusBilin x y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 - 2 * (x 3 * y 3) := by
  rw [minusBilin, fiveBilin_apply, fiveForm, Fin.sum_univ_three]
  simp only [fiveSignRep, if_true, inv_one, one_mul, Bool.false_eq_true, if_false]
  rfl

theorem minusBilin_comm (x y : Fin 4 → ZMod 5) : minusBilin x y = minusBilin y x :=
  fiveBilin_comm 3 false true x y

theorem minusBilin_nondegenerate (x : Fin 4 → ZMod 5) (hx : ∀ y, minusBilin x y = 0) : x = 0 :=
  fiveBilin_nondegenerate 3 false true x hx

theorem reflSet_minusBilin : reflSet minusBilin = fiveReflections 3 false true :=
  fischerTransvections_fiveBilin 3 false true

theorem reflGroup_minusBilin : reflGroup minusBilin = fiveReflectionGroup 3 false true := by
  rw [reflGroup, reflSet_minusBilin, fiveReflectionGroup]

theorem minusBilin_single_zero : minusBilin (Pi.single 0 1) (Pi.single 0 1) = 1 := by
  rw [minusBilin_apply]
  decide

private theorem aniso_two (u v : ZMod 5) (h : u * u - 2 * (v * v) = 0) : u = 0 ∧ v = 0 := by
  revert u v
  decide

private theorem five_eq_zero : (5 : ZMod 5) = 0 := by
  decide

private theorem minors_aux (x y z w x' y' z' w' : ZMod 5)
    (ha : x * x + y * y + z * z - 2 * (w * w) = 0)
    (hac : x * x' + y * y' + z * z' - 2 * (w * w') = 0)
    (hc : x' * x' + y' * y' + z' * z' - 2 * (w' * w') = 0) :
    x * z' = z * x' ∧ y * z' = z * y' ∧ x * w' = w * x' ∧ y * w' = w * y' := by
  obtain ⟨E1, E3⟩ := aniso_two ((x' - 2 * y') * z - (x - 2 * y) * z')
    ((x' - 2 * y') * w - (x - 2 * y) * w') (by
      linear_combination (x' - 2 * y') ^ 2 * ha - 2 * (x' - 2 * y') * (x - 2 * y) * hac +
        (x - 2 * y) ^ 2 * hc - ((x' - 2 * y') * y - (x - 2 * y) * y') ^ 2 * five_eq_zero)
  obtain ⟨E2, E4⟩ := aniso_two ((x' + 2 * y') * z - (x + 2 * y) * z')
    ((x' + 2 * y') * w - (x + 2 * y) * w') (by
      linear_combination (x' + 2 * y') ^ 2 * ha - 2 * (x' + 2 * y') * (x + 2 * y) * hac +
        (x + 2 * y) ^ 2 * hc - ((x' + 2 * y') * y - (x + 2 * y) * y') ^ 2 * five_eq_zero)
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (-3) * E1 + (-3) * E2 - (x * z' - z * x') * five_eq_zero
  · linear_combination (-4) * E2 + 4 * E1 - 3 * (y * z' - z * y') * five_eq_zero
  · linear_combination (-3) * E3 + (-3) * E4 - (x * w' - w * x') * five_eq_zero
  · linear_combination (-4) * E4 + 4 * E3 - 3 * (y * w' - w * y') * five_eq_zero

theorem minusBilin_witt (a c : Fin 4 → ZMod 5) (ha : minusBilin a a = 0)
    (hac : minusBilin a c = 0) (hc : minusBilin c c = 0) :
    ∃ l m : ZMod 5, (l ≠ 0 ∨ m ≠ 0) ∧ l • a + m • c = 0 := by
  rw [minusBilin_apply] at ha hac hc
  obtain ⟨h02, h12, h03, h13⟩ := minors_aux (a 0) (a 1) (a 2) (a 3) (c 0) (c 1) (c 2) (c 3)
    ha hac hc
  obtain ⟨h01, h21, -, h23⟩ := minors_aux (a 0) (a 2) (a 1) (a 3) (c 0) (c 2) (c 1) (c 3)
    (by linear_combination ha) (by linear_combination hac) (by linear_combination hc)
  have key : ∀ i : Fin 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
  have hm : ∀ i j : Fin 4, a i * c j = a j * c i := by
    intro i j
    rcases key i with rfl | rfl | rfl | rfl <;> rcases key j with rfl | rfl | rfl | rfl <;>
      first
        | rfl
        | linear_combination h01 | linear_combination -h01
        | linear_combination h02 | linear_combination -h02
        | linear_combination h03 | linear_combination -h03
        | linear_combination h12 | linear_combination -h12
        | linear_combination h13 | linear_combination -h13
        | linear_combination h21 | linear_combination -h21
        | linear_combination h23 | linear_combination -h23
  by_cases h0 : a = 0
  · exact ⟨1, 0, Or.inl one_ne_zero, by rw [h0, smul_zero, zero_smul, add_zero]⟩
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra! h
    exact h0 (funext h)
  refine ⟨c i, -a i, Or.inr (neg_ne_zero.mpr hi), funext fun j => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  linear_combination hm j i

section Spinor

open QuadraticMap CFSG.ClassicalInvolution
open CFSG.ClassicalGroups.Orthogonal (reflect reflect_mem_orthogonalGroup reflect_eq_reflection
  toLinEquiv toLinEquiv_apply)

private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private instance : Invertible (2 : ZMod 5) := invertibleOfNonzero (by decide)

private noncomputable def Qm : QuadraticForm (ZMod 5) (Fin 4 → ZMod 5) :=
  LinearMap.BilinMap.toQuadraticMap minusBilin

private theorem Qm_apply (x : Fin 4 → ZMod 5) : Qm x = minusBilin x x :=
  LinearMap.BilinMap.toQuadraticMap_apply _ _

private theorem Qm_polar (x y : Fin 4 → ZMod 5) : polar Qm x y = 2 * minusBilin x y := by
  rw [Qm, LinearMap.BilinMap.polar_toQuadraticMap, minusBilin_comm y x, two_mul]

private theorem Qm_nondegenerate : Qm.Nondegenerate :=
  QuadraticMap.nondegenerate_polar_iff.mp
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun v hv =>
      minusBilin_nondegenerate v fun w => by
        have := hv w
        rw [Qm_polar] at this
        exact (mul_eq_zero.mp this).resolve_left (by decide))

private theorem mem_orthogonalGroup_of_mem {g : GL (Fin 4) (ZMod 5)}
    (hg : g ∈ reflGroup minusBilin) :
    toLinEquiv (Fin 4) (ZMod 5) g ∈ TauCeti.QuadraticMap.orthogonalGroup Qm := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
  rw [toLinEquiv_apply, Qm_apply, Qm_apply]
  exact reflGroup_le_isomGroup minusBilin_comm hg x x

private theorem toLinEquiv_refl {v : Fin 4 → ZMod 5} (hv : minusBilin v v = 1)
    [Invertible (Qm v)] :
    toLinEquiv (Fin 4) (ZMod 5) (refl minusBilin v) =
      (TauCeti.QuadraticMap.reflectionOrthogonal Qm v :
        (Fin 4 → ZMod 5) ≃ₗ[ZMod 5] (Fin 4 → ZMod 5)) := by
  rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal]
  ext y
  rw [toLinEquiv_apply, ← act, act_refl hv, TauCeti.QuadraticMap.reflection_apply, Qm_polar,
    minusBilin_comm v y]
  have hinv : ⅟(Qm v) = 1 := by
    rw [invOf_eq_inv, Qm_apply, hv, inv_one]
  rw [hinv, one_mul, sub_eq_add_neg, ← neg_smul, neg_mul]

private theorem squareClassHom_eq_one_of_isSquare {u : (ZMod 5)ˣ}
    (hu : IsSquare (u : ZMod 5)) : TauCeti.squareClassHom u = 1 := by
  rw [← MonoidHom.mem_ker, TauCeti.ker_squareClassHom, Subgroup.mem_square]
  exact TauCeti.isSquare_units_val_iff.mp hu

private theorem spinorNorm_eq_one {g : GL (Fin 4) (ZMod 5)} (hg : g ∈ reflGroup minusBilin) :
    (detSpinorNorm Qm_nondegenerate ⟨toLinEquiv (Fin 4) (ZMod 5) g,
      mem_orthogonalGroup_of_mem hg⟩).2 = 1 := by
  refine Subgroup.closure_induction (k := reflSet minusBilin)
    (p := fun g hg => (detSpinorNorm Qm_nondegenerate ⟨toLinEquiv (Fin 4) (ZMod 5) g,
      mem_orthogonalGroup_of_mem hg⟩).2 = 1) ?_ ?_ ?_ ?_ hg
  · intro r hr
    obtain ⟨v, hv, rfl⟩ := mem_reflSet_iff.mp hr
    have hQv : Qm v = 1 := by rw [Qm_apply, hv]
    letI : Invertible (Qm v) := invertibleOfNonzero (by rw [hQv]; decide)
    have hsub : (⟨toLinEquiv (Fin 4) (ZMod 5) (refl minusBilin v),
        mem_orthogonalGroup_of_mem (Subgroup.subset_closure hr)⟩ :
        TauCeti.QuadraticMap.orthogonalGroup Qm) =
        TauCeti.QuadraticMap.reflectionOrthogonal Qm v :=
      Subtype.ext (toLinEquiv_refl hv)
    rw [hsub, detSpinorNorm_reflectionOrthogonal]
    exact squareClassHom_eq_one_of_isSquare (by
      rw [val_unitOfInvertible, hQv]
      exact ⟨1, (mul_one 1).symm⟩)
  · have hone : (⟨toLinEquiv (Fin 4) (ZMod 5) 1, mem_orthogonalGroup_of_mem (Subgroup.one_mem _)⟩ :
        TauCeti.QuadraticMap.orthogonalGroup Qm) = 1 :=
      Subtype.ext (map_one _)
    rw [hone, map_one]
    rfl
  · intro x y hx hy ihx ihy
    have hxy : (⟨toLinEquiv (Fin 4) (ZMod 5) (x * y),
        mem_orthogonalGroup_of_mem (Subgroup.mul_mem _ hx hy)⟩ :
        TauCeti.QuadraticMap.orthogonalGroup Qm) =
        ⟨toLinEquiv (Fin 4) (ZMod 5) x, mem_orthogonalGroup_of_mem hx⟩ *
          ⟨toLinEquiv (Fin 4) (ZMod 5) y, mem_orthogonalGroup_of_mem hy⟩ :=
      Subtype.ext (map_mul _ x y)
    rw [hxy, map_mul, Prod.snd_mul, ihx, ihy, mul_one]
  · intro x hx ihx
    have hxi : (⟨toLinEquiv (Fin 4) (ZMod 5) x⁻¹,
        mem_orthogonalGroup_of_mem (Subgroup.inv_mem _ hx)⟩ :
        TauCeti.QuadraticMap.orthogonalGroup Qm) =
        ⟨toLinEquiv (Fin 4) (ZMod 5) x, mem_orthogonalGroup_of_mem hx⟩⁻¹ :=
      Subtype.ext (map_inv _ x)
    rw [hxi, map_inv, Prod.snd_inv, ihx, inv_one]

private noncomputable def reflO (v : Fin 4 → ZMod 5) :
    TauCeti.QuadraticMap.orthogonalGroup Qm :=
  ⟨reflect Qm v, reflect_mem_orthogonalGroup Qm v⟩

private def bl : List (Fin 4 → ZMod 5) :=
  [Pi.single 0 1, Pi.single 1 1, Pi.single 2 1, Pi.single 3 1]

private theorem bl_ne_zero : ∀ a ∈ bl, Qm a ≠ 0 := by
  intro a ha
  simp only [bl, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> (rw [Qm_apply, minusBilin_apply]; decide)

private theorem bl_pairwise : bl.Pairwise (fun a b => polar Qm a b = 0) := by
  refine List.Pairwise.imp (R := fun a b => minusBilin a b = 0) (fun {a b} h => ?_) ?_
  · rw [Qm_polar, h, mul_zero]
  · simp only [bl, minusBilin_apply]
    decide

private theorem bl_span : Submodule.span (ZMod 5) {v | v ∈ bl} = ⊤ := by
  refine span_eq_top_of_pairwise_polar (K := ZMod 5) (V := Fin 4 → ZMod 5) (Q := Qm)
    (by decide) bl_ne_zero bl_pairwise ?_
  rw [bl, Module.finrank_fintype_fun_eq_card]
  simp

private theorem bl_prod_reflectO : QuadraticMap.negOrthogonal Qm = (bl.map reflO).prod := by
  apply Subtype.ext
  rw [QuadraticMap.coe_negOrthogonal, Subgroup.val_list_prod, List.map_map]
  exact (prod_map_reflect_eq_neg (Q := Qm) bl_ne_zero bl_pairwise bl_span).symm

private noncomputable def unitQ (v : Fin 4 → ZMod 5) : (ZMod 5)ˣ :=
  if h : Qm v = 0 then 1 else Units.mk0 (Qm v) h

private theorem detSpinorNorm_reflO {v : Fin 4 → ZMod 5} (hv : Qm v ≠ 0) :
    detSpinorNorm Qm_nondegenerate (reflO v) =
      ((-1 : (ZMod 5)ˣ), TauCeti.squareClassHom (unitQ v)) := by
  letI : Invertible (Qm v) := invertibleOfNonzero hv
  have hrefl : reflO v = TauCeti.QuadraticMap.reflectionOrthogonal Qm v := by
    apply Subtype.ext
    rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal]
    exact reflect_eq_reflection
  rw [hrefl, detSpinorNorm_reflectionOrthogonal]
  congr 2
  apply Units.ext
  rw [val_unitOfInvertible]
  simp [unitQ, hv]

private theorem spinorNorm_negOrthogonal :
    (detSpinorNorm Qm_nondegenerate (QuadraticMap.negOrthogonal Qm)).2 ≠ 1 := by
  rw [bl_prod_reflectO, map_list_prod, List.map_map]
  have hper : ∀ v ∈ bl, (detSpinorNorm Qm_nondegenerate ∘ reflO) v =
      ((-1 : (ZMod 5)ˣ), TauCeti.squareClassHom (unitQ v)) := fun v hv =>
    detSpinorNorm_reflO (bl_ne_zero v hv)
  rw [List.map_congr_left hper]
  have hsnd : ∀ l : List (Fin 4 → ZMod 5),
      ((l.map fun v => ((-1 : (ZMod 5)ˣ), TauCeti.squareClassHom (unitQ v))).prod).2 =
        TauCeti.squareClassHom ((l.map unitQ).prod) := by
    intro l
    induction l with
    | nil => exact (map_one TauCeti.squareClassHom).symm
    | cons a l ih => simp only [List.map_cons, List.prod_cons, Prod.snd_mul, ih, map_mul]
  rw [hsnd]
  have hval : (((bl.map unitQ).prod : (ZMod 5)ˣ) : ZMod 5) = 3 := by
    change (Units.coeHom (ZMod 5)) ((bl.map unitQ).prod) = 3
    rw [map_list_prod (Units.coeHom (ZMod 5)) (bl.map unitQ), List.map_map]
    have : ∀ v ∈ bl, ((Units.coeHom (ZMod 5)) ∘ unitQ) v = Qm v := fun v hv => by
      simp [unitQ, bl_ne_zero v hv]
    rw [List.map_congr_left this]
    simp only [bl, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Qm_apply,
      minusBilin_apply]
    decide
  intro h
  rw [← MonoidHom.mem_ker, TauCeti.ker_squareClassHom, Subgroup.mem_square,
    ← TauCeti.isSquare_units_val_iff, hval] at h
  exact absurd h (by decide)

theorem neg_one_notMem_reflGroup_minusBilin :
    (-1 : GL (Fin 4) (ZMod 5)) ∉ reflGroup minusBilin := by
  intro hmem
  have h := spinorNorm_eq_one hmem
  have hsub : (⟨toLinEquiv (Fin 4) (ZMod 5) (-1), mem_orthogonalGroup_of_mem hmem⟩ :
      TauCeti.QuadraticMap.orthogonalGroup Qm) = QuadraticMap.negOrthogonal Qm := by
    apply Subtype.ext
    rw [QuadraticMap.coe_negOrthogonal]
    ext x
    rw [toLinEquiv_apply, show (-1 : GL (Fin 4) (ZMod 5)) = -(1 : GL (Fin 4) (ZMod 5)) from rfl,
      Units.val_neg, Units.val_one, Matrix.neg_mulVec, Matrix.one_mulVec]
    rfl
  rw [hsub] at h
  exact spinorNorm_negOrthogonal h

end Spinor

theorem center_reflGroup_minusBilin : Subgroup.center (reflGroup minusBilin) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rcases coe_eq_of_mem_center minusBilin_comm minusBilin_nondegenerate le_rfl
      minusBilin_single_zero hg with h | h
  · exact (Subgroup.mem_bot).mpr (Subtype.ext h)
  · exact absurd (h ▸ g.2) neg_one_notMem_reflGroup_minusBilin

@[expose] def minusSevenNineForm : LinearMap.BilinForm (ZMod 5) (Fin 4 → ZMod 5) :=
  (-2 : ZMod 5) • minusBilin

private theorem minusSevenNineForm_apply (x y : Fin 4 → ZMod 5) :
    minusSevenNineForm x y = -2 * minusBilin x y :=
  rfl

theorem orthReflSet_minusSevenNineForm :
    orthReflSet 5 4 minusSevenNineForm = reflSet minusBilin := by
  ext g
  simp only [orthReflSet, CFSG.Open.fischerTransvections, Set.mem_setOf_eq,
    minusSevenNineForm_apply]
  constructor
  · rintro ⟨v, hv, hg⟩
    refine ⟨v, ?_, hg⟩
    have h2 : (-2 : ZMod 5) * (minusBilin v v - 1) = 0 := by linear_combination hv
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left (by decide))
  · rintro ⟨v, hv, hg⟩
    exact ⟨v, by rw [hv, mul_one], hg⟩

theorem isSevenNineGroup_of_mulEquiv {L : Type} [Group L] {D : Set L}
    (e : L ≃* reflGroup minusBilin)
    (he : ∀ d ∈ D, (e d : GL (Fin 4) (ZMod 5)) ∈ reflSet minusBilin) :
    IsSevenNineGroup L D := by
  have hcl : reflGroup minusBilin = Subgroup.closure (orthReflSet 5 4 minusSevenNineForm) := by
    rw [orthReflSet_minusSevenNineForm]
  refine Or.inl ⟨minusSevenNineForm, fun x y => by
    rw [minusSevenNineForm_apply, minusSevenNineForm_apply, minusBilin_comm], fun x hx =>
    minusBilin_nondegenerate x fun y => by
      have h2 := hx y
      rw [minusSevenNineForm_apply] at h2
      exact (mul_eq_zero.mp h2).resolve_left (by decide), fun a c ha hac hc => ?_,
    e.trans (MulEquiv.subgroupCongr hcl), fun d hd => ?_⟩
  · have h0 : ∀ x y : Fin 4 → ZMod 5, minusSevenNineForm x y = 0 → minusBilin x y = 0 := by
      intro x y h
      rw [minusSevenNineForm_apply] at h
      exact (mul_eq_zero.mp h).resolve_left (by decide)
    exact minusBilin_witt a c (h0 a a ha) (h0 a c hac) (h0 c c hc)
  · rw [← orthReflSet_minusSevenNineForm] at he
    exact he d hd

end CFSG.OddTranspositions.PartFour.ListFive
