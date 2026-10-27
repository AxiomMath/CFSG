module

public import CFSG.Certificates.CosetTablePresented
public import CFSG.LinearAlgebra.LinearGroups.Generation
public import Certificates.Data.H13.U42AutP10Rel
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open Matrix CFSG.CosetTable CFSG.LinearGroups
open scoped MatrixGroups

abbrev P10M4 : Type := Matrix (Fin 4) (Fin 4) (ZMod 3)

@[expose] def p10gm : Fin 7 → P10M4 :=
  ![!![1, 1, 0, 0; 1, 2, 0, 0; 2, 0, 2, 1; 0, 1, 1, 1],
    !![0, 2, 0, 0; 1, 0, 0, 0; 0, 0, 0, 2; 0, 0, 1, 0],
    !![0, 0, 1, 0; 0, 0, 0, 2; 2, 0, 0, 0; 0, 1, 0, 0],
    !![0, 2, 0, 0; 1, 0, 0, 0; 1, 0, 0, 2; 0, 2, 1, 0],
    !![2, 0, 1, 0; 0, 1, 0, 2; 1, 0, 1, 0; 0, 2, 0, 2],
    !![2, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 1; 0, 0, 1, 2],
    !![1, 1, 0, 0; 2, 1, 0, 0; 0, 0, 1, 1; 0, 0, 2, 1]]

theorem p10gm_det (i : Fin 7) : (p10gm i).det = 1 := by
  revert i
  decide +kernel

@[expose] def p10gSL (i : Fin 7) : SL(4, ZMod 3) := ⟨p10gm i, p10gm_det i⟩

@[expose] def p10evalM (w : List (Fin 7)) : P10M4 := (w.map p10gm).prod

theorem p10_pos : ∀ r ∈ p10Ws, ∀ l ∈ r, l.2 = true := by decide

theorem p10_rel_check :
    ∀ r ∈ p10Ws, p10evalM (r.map Prod.fst) = 1 ∨ p10evalM (r.map Prod.fst) = -1 := by
  decide +kernel

@[expose] def p10Elem : List (Fin 4 × Fin 4 × List (Fin 7)) :=
  [(0, 1, [0, 1, 2, 3, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 3, 2, 6,
      3, 1, 4, 5]),
   (0, 2, [3, 1, 4, 3, 2, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 3, 6, 2]),
   (0, 3, [0, 1, 2, 0, 3, 1, 2, 4, 3, 2, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3]),
   (1, 0, [1, 3, 1, 2, 0, 3, 2, 4, 3, 1, 2, 3, 4, 5, 4, 3, 2, 0, 6, 3, 6, 2, 3, 4, 5]),
   (1, 2, [1, 3, 1, 2, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 1, 2, 0, 3, 2, 4, 5]),
   (1, 3, [1, 3, 1, 4, 3, 2, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 3, 2, 6]),
   (2, 0, [0, 1, 2, 3, 1, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 1, 2, 3, 4, 5, 6, 3, 1, 6]),
   (2, 1, [0, 1, 2, 3, 1, 2, 4, 3, 2, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2]),
   (2, 3, [3, 1, 2, 0, 3, 2, 4, 3, 1, 2, 3, 4, 5, 4, 3, 1, 2, 0, 6, 3, 2, 6, 3, 1, 4, 5]),
   (3, 0, [1, 2, 3, 1, 2, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 1, 2, 0, 3, 4, 5]),
   (3, 1, [0, 2, 3, 1, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 1, 2, 3, 4, 5, 6, 3, 6]),
   (3, 2, [0, 2, 3, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 3, 6, 2, 3, 4,
      5])]

theorem p10_elem_check : ∀ e ∈ p10Elem,
    p10evalM e.2.2 = 1 + Matrix.single e.1 e.2.1 1 ∨
      p10evalM e.2.2 = -(1 + Matrix.single e.1 e.2.1 1) := by
  decide +kernel

theorem p10_elem_cover : ∀ i j : Fin 4, i ≠ j → ∃ e ∈ p10Elem, e.1 = i ∧ e.2.1 = j := by
  decide

abbrev p10pr : SL(4, ZMod 3) →* PSL(4, ZMod 3) := QuotientGroup.mk' _

theorem p10_coe_list_prod (w : List (Fin 7)) :
    (((w.map p10gSL).prod : SL(4, ZMod 3)) : P10M4) = p10evalM w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [List.map_cons, List.prod_cons, Matrix.SpecialLinearGroup.coe_mul, ih]
    rfl

theorem p10pr_eq_one {g : SL(4, ZMod 3)} (h : (g : P10M4) = 1 ∨ (g : P10M4) = -1) :
    p10pr g = 1 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Matrix.SpecialLinearGroup.mem_center_iff]
  rcases h with h | h
  · exact ⟨1, by decide, by rw [h]; decide +kernel⟩
  · refine ⟨-1, by decide, ?_⟩
    rw [h]
    decide +kernel

theorem p10_lift_pos (w : List (Fin 7)) :
    FreeGroup.lift (fun i => p10pr (p10gSL i)) (FreeGroup.mk (w.map fun i => (i, true))) =
      p10pr ((w.map p10gSL).prod) := by
  rw [FreeGroup.lift_mk, map_list_prod]
  simp [List.map_map, Function.comp_def]

theorem p10_eq_map_fst {r : List (Fin 7 × Bool)} (h : ∀ l ∈ r, l.2 = true) :
    r = (r.map Prod.fst).map fun i => (i, true) := by
  induction r with
  | nil => rfl
  | cons l r ih =>
    have hl : l.2 = true := h l List.mem_cons_self
    have hr := ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    obtain ⟨a, b⟩ := l
    simp only at hl
    subst hl
    simp only [List.map_cons]
    exact congrArg (List.cons (a, true)) hr

noncomputable def p10ModelHom : PG 7 p10Ws →* PSL(4, ZMod 3) :=
  PresentedGroup.toGroup (f := fun i => p10pr (p10gSL i)) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [p10_eq_map_fst (p10_pos w hw), p10_lift_pos]
    refine p10pr_eq_one ?_
    rw [p10_coe_list_prod]
    exact p10_rel_check w hw)

theorem p10ModelHom_mk (w : List (Fin 7)) :
    p10ModelHom (PresentedGroup.mk _ (FreeGroup.mk (w.map fun i => (i, true)))) =
      p10pr ((w.map p10gSL).prod) := by
  exact p10_lift_pos w

@[expose] def p10negI : SL(4, ZMod 3) := ⟨-1, by decide +kernel⟩

theorem p10pr_negI : p10pr p10negI = 1 :=
  p10pr_eq_one (Or.inr rfl)

theorem p10pr_eq_of_neg {a b : SL(4, ZMod 3)} (h : (b : P10M4) = a ∨ (b : P10M4) = -a) :
    p10pr b = p10pr a := by
  rcases h with h | h
  · rw [Subtype.ext h]
  · have : b = p10negI * a := by
      refine Subtype.ext ?_
      rw [Matrix.SpecialLinearGroup.coe_mul, h]
      exact (neg_one_mul (a : P10M4)).symm
    rw [this, map_mul, p10pr_negI, one_mul]

theorem p10_transvection_pow :
    ∀ (i j : Fin 4) (h : i ≠ j) (c : ZMod 3), SpecialLinearGroup.transvection h c =
      (SpecialLinearGroup.transvection h (1 : ZMod 3)) ^ c.val := by
  decide +kernel

theorem p10_transvection_mem (i j : Fin 4) (h : i ≠ j) :
    p10pr (SpecialLinearGroup.transvection h (1 : ZMod 3)) ∈ p10ModelHom.range := by
  obtain ⟨⟨a, b, w⟩, he, rfl, rfl⟩ := p10_elem_cover i j h
  refine ⟨PresentedGroup.mk _ (FreeGroup.mk (w.map fun i => (i, true))), ?_⟩
  rw [p10ModelHom_mk]
  refine p10pr_eq_of_neg ?_
  rw [p10_coe_list_prod]
  exact p10_elem_check _ he

theorem p10ModelHom_surjective : Function.Surjective p10ModelHom := by
  set H : Subgroup SL(4, ZMod 3) := p10ModelHom.range.comap p10pr with hH
  have htop : H = ⊤ := by
    rw [eq_top_iff, ← special_linear_elementary_generation (n := 4) (K := ZMod 3),
      Subgroup.closure_le]
    rintro A ⟨i, j, hij, c, rfl⟩
    rw [p10_transvection_pow]
    exact pow_mem (p10_transvection_mem i j hij) _
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have : g ∈ H := htop ▸ Subgroup.mem_top g
  exact this

end CFSG.Quasithin.H13.F431.U42Aut
