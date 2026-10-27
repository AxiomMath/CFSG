module

public import CFSG.Timmesfeld.ARS.CaseHCount
public import CFSG.GroupTheory.InvolutionHexagonIncidence
public import Mathlib.Algebra.Order.Group.End

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.GroupTheory.InvolutionHexagon

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

abbrev Pt (R : Set (Subgroup G)) : Type _ := {A : Subgroup G // A ∈ R}

abbrev Ln (R : Set (Subgroup G)) : Type _ := {V : Subgroup G // IsLine R V}

@[expose] def inc (R : Set (Subgroup G)) (A : Pt R) (V : Ln R) : Prop := A.1 ≤ V.1

theorem collinear_iff (h : Hyp G R) {p q : Pt R} (hpq : p ≠ q) :
    Collinear (inc R) p q ↔ q.1 ∈ lambdaSet R p.1 := by
  have := h.finite
  constructor
  · rintro ⟨⟨V, A, hA, D, hD, rfl⟩, hp, hq⟩
    exact (mem_lambdaSet_of_le_sup h.root h.noIsolated hA hD p.2 hp q.2 hq
      (fun e => hpq (Subtype.ext e))).1
  · intro hl
    exact ⟨⟨p.1 ⊔ q.1, p.1, p.2, q.1, hl, rfl⟩, le_sup_left, le_sup_right⟩

theorem image_setOf_inc (V : Ln R) :
    Subtype.val '' {p : Pt R | inc R p V} = pointsOn R V.1 := by
  ext B
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2, hp⟩
  · rintro ⟨hB, hBV⟩
    exact ⟨⟨B, hB⟩, hBV, rfl⟩

theorem image_setOf_inc_lines (p : Pt R) :
    Subtype.val '' {V : Ln R | inc R p V} = linesThrough R p.1 := by
  ext V
  constructor
  · rintro ⟨V, hV, rfl⟩
    exact ⟨V.2, hV⟩
  · rintro ⟨hV, hpV⟩
    exact ⟨⟨V, hV⟩, hpV, rfl⟩

theorem hexagonData (h : Hyp G R) (hH : SigmaEqLambda R) {A₀ : Subgroup G} (hA₀ : A₀ ∈ R)
    (hq : Nat.card A₀ = 2) (hL : (linesThrough R A₀).ncard = 3) : HexagonData (inc R) := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hcard : ∀ A ∈ R, Nat.card A = 2 := fun A hA => (hR.card_eq hA hA₀).trans hq
  have hcol : ∀ {p q : Pt R}, Collinear (inc R) p q → p ≠ q → q.1 ∈ lambdaSet R p.1 :=
    fun hpq hne => (collinear_iff h hne).1 hpq
  have hncol : ∀ {p q : Pt R}, ¬ Collinear (inc R) p q → p ≠ q → q.1 ∉ lambdaSet R p.1 :=
    fun hpq hne hl => hpq ((collinear_iff h hne).2 hl)
  have hne : ∀ {p q : Pt R}, p ≠ q → p.1 ≠ q.1 := fun hpq e => hpq (Subtype.ext e)
  refine ⟨inferInstance, inferInstance, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_coe_set_eq, ncard_eq h hH hA₀ hq hL]
    norm_num
  · rintro ⟨V, A, hA, D, hD, rfl⟩
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective, image_setOf_inc,
      ncard_pointsOn h hA hD, hcard A hA]
  · intro p
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective, image_setOf_inc_lines,
      ncard_linesThrough_eq h hA₀ p.2, hL]
  · rintro p q ⟨_, A, hA, D, hD, rfl⟩ ⟨_, A', hA', D', hD', rfl⟩ hpq hp hq hp' hq'
    exact Subtype.ext (eq_of_le_of_le h hA hD hA' hD' p.2 q.2 (hne hpq) hp hq hp' hq')
  · intro a b c hab hbc hac h1 h2 h3
    have hb := hcol h1 hab
    have hc := hcol h3 hac
    have hc' := hcol h2 hbc
    refine ⟨⟨a.1 ⊔ b.1, a.1, a.2, b.1, hb, rfl⟩, le_sup_left, le_sup_right, ?_⟩
    exact le_line h hH a.2 hb a.2 le_sup_left b.2 le_sup_right (hne hab) c.2 hc.1.2.2.symm
      hc'.1.2.2.symm
  · rintro ⟨a, b, c, d, hnd, h1, h2, h3, h4, h5, h6⟩
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
    obtain ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd, -⟩ := hnd
    exact false_of_quadrangle h hH a.2 (hcol h1 hab) (hcol h2 hbc) (hcol h3 hcd)
      (hcol h4 (Ne.symm had)) (hncol h5 hac) (hne (Ne.symm hac)) (hne (Ne.symm hbd))
  · rintro ⟨a, b, c, d, e, hnd, h1, h2, h3, h4, h5, h6, h7, -, -, -⟩
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
    obtain ⟨⟨hab, hac, had, hae⟩, ⟨hbc, hbd, hbe⟩, ⟨hcd, hce⟩, hde, -⟩ := hnd
    exact false_of_pentagon h hH a.2 (hcol h1 hab) (hcol h2 hbc) (hcol h3 hcd) (hcol h4 hde)
      (hcol h5 (Ne.symm hae)) (hncol h6 hac) (hne (Ne.symm hac)) (hncol h7 had)
      (hne (Ne.symm had)) (hne hbe)

@[expose] def conjPt (hR : IsRootClass R) (g : G) (A : Pt R) : Pt R :=
  ⟨conjSub A.1 g, hR.conjSub_mem A.2 g⟩

@[expose] def conjLn (hR : IsRootClass R) (g : G) (V : Ln R) : Ln R :=
  ⟨conjSub V.1 g, IsLine.conjSub hR V.2 g⟩

section Action

variable (hR : IsRootClass R)

theorem conjPt_one (A : Pt R) : conjPt hR 1 A = A := Subtype.ext (conjSub_one A.1)

theorem conjPt_mul (g g' : G) (A : Pt R) : conjPt hR (g * g') A = conjPt hR g (conjPt hR g' A) :=
  Subtype.ext (conjSub_mul A.1 g g')

theorem conjLn_one (V : Ln R) : conjLn hR 1 V = V := Subtype.ext (conjSub_one V.1)

theorem conjLn_mul (g g' : G) (V : Ln R) : conjLn hR (g * g') V = conjLn hR g (conjLn hR g' V) :=
  Subtype.ext (conjSub_mul V.1 g g')

theorem inc_conj (g : G) (A : Pt R) (V : Ln R) :
    inc R (conjPt hR g A) (conjLn hR g V) ↔ inc R A V :=
  Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective

@[expose] def conjAut (g : G) : incidenceGraph (inc R) ≃g incidenceGraph (inc R) where
  toFun := Sum.map (conjPt hR g) (conjLn hR g)
  invFun := Sum.map (conjPt hR g⁻¹) (conjLn hR g⁻¹)
  left_inv := by
    rintro (p | T)
    · rw [Sum.map_inl, Sum.map_inl, ← conjPt_mul, inv_mul_cancel, conjPt_one]
    · rw [Sum.map_inr, Sum.map_inr, ← conjLn_mul, inv_mul_cancel, conjLn_one]
  right_inv := by
    rintro (p | T)
    · rw [Sum.map_inl, Sum.map_inl, ← conjPt_mul, mul_inv_cancel, conjPt_one]
    · rw [Sum.map_inr, Sum.map_inr, ← conjLn_mul, mul_inv_cancel, conjLn_one]
  map_rel_iff' := by
    rintro (p | T) (q | T')
    · simp only [Equiv.coe_fn_mk, Sum.map_inl, not_incidenceGraph_adj_inl_inl]
    · simp only [Equiv.coe_fn_mk, Sum.map_inl, Sum.map_inr, incidenceGraph_adj_inl_inr]
      exact inc_conj hR g p T'
    · simp only [Equiv.coe_fn_mk, Sum.map_inl, Sum.map_inr, incidenceGraph_adj_inr_inl]
      exact inc_conj hR g q T
    · simp only [Equiv.coe_fn_mk, Sum.map_inr, not_incidenceGraph_adj_inr_inr]

theorem conjAut_inl (g : G) (p : Pt R) : conjAut hR g (Sum.inl p) = Sum.inl (conjPt hR g p) :=
  rfl

theorem conjAut_inr (g : G) (T : Ln R) : conjAut hR g (Sum.inr T) = Sum.inr (conjLn hR g T) :=
  rfl

@[expose] def conjAction : G →* (incidenceGraph (inc R) ≃g incidenceGraph (inc R)) where
  toFun := conjAut hR
  map_one' := RelIso.ext fun v => by
    rcases v with p | T
    · rw [conjAut_inl, conjPt_one]
      rfl
    · rw [conjAut_inr, conjLn_one]
      rfl
  map_mul' g g' := RelIso.ext fun v => by
    rcases v with p | T
    · rw [conjAut_inl, conjPt_mul, RelIso.mul_apply, conjAut_inl, conjAut_inl]
    · rw [conjAut_inr, conjLn_mul, RelIso.mul_apply, conjAut_inr, conjAut_inr]

theorem incidenceColoring_conjAction (g : G) (v : Pt R ⊕ Ln R) :
    incidenceColoring (inc R) (conjAction hR g v) = incidenceColoring (inc R) v := by
  rcases v with p | T <;> rfl

end Action

theorem conjAction_injective (h : Hyp G R) (hq : ∀ A ∈ R, Nat.card A = 2) :
    Function.Injective (conjAction h.root) := by
  have := h.finite
  have hR := h.root
  rw [injective_iff_map_eq_one]
  intro g hg
  have hfix : ∀ A ∈ R, conjSub A g = A := fun A hA => by
    have := DFunLike.congr_fun hg (Sum.inl ⟨A, hA⟩)
    rw [conjAction, MonoidHom.coe_mk, OneHom.coe_mk, conjAut_inl, RelIso.one_apply,
      Sum.inl.injEq] at this
    exact congrArg Subtype.val this
  have hcen : ∀ A ∈ R, ∀ a ∈ A, g * a * g⁻¹ = a := by
    intro A hA a ha
    by_cases ha1 : a = 1
    · rw [ha1, mul_one, mul_inv_cancel]
    have hmem : g * a * g⁻¹ ∈ A := by
      rw [← hfix A hA]
      exact conj_mem_conjSub g ha
    refine eq_of_mem_of_card_eq_two (hq A hA) ha ha1 hmem ?_
    intro h1
    apply ha1
    have : a = g⁻¹ * (g * a * g⁻¹) * g := by group
    rw [this, h1]
    group
  have hle : (⊤ : Subgroup G) ≤ Subgroup.centralizer {g} := by
    rw [← hR.gen]
    refine iSup₂_le fun A hA a ha => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hcen A hA a ha
    calc a * g = (g * a * g⁻¹) * g := by rw [this]
      _ = g * a := by group
  have hgc : g ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro x
    have := hle (Subgroup.mem_top x)
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  rw [h.center, Subgroup.mem_bot] at hgc
  exact hgc

theorem isPerfect (h : Hyp G R) : Group.IsPerfect G := by
  have hR := h.root
  rw [Group.isPerfect_def]
  obtain ⟨E, hE, F, hF, hEF⟩ := h.nondeg
  have hC : ⁅E, F⁆ ≤ commutator G := Subgroup.commutator_mono le_top le_top
  have hN : (commutator G).Normal := inferInstance
  refine eq_top_iff.2 ?_
  rw [← hR.gen]
  refine iSup₂_le fun A hA => ?_
  obtain ⟨g, rfl⟩ := hR.exists_conjSub_eq hEF.1 hA
  rintro _ ⟨y, hy, rfl⟩
  exact hN.conj_mem y (hC hy) g

end CaseH

end CFSG.Timmesfeld.ARS
