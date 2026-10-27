module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08FullCoords
public import CFSG.LocalAnalysis.StandardType.GGQ2S08Cartan
public import CFSG.LocalAnalysis.StandardType.GGQ2LDatumDims
public import CFSG.LocalAnalysis.StandardType.GGQTwoLDatumWeyl
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrDatumInner
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

inductive GGQ2ShapeTag
  | full | a | b | c | d
  deriving DecidableEq

@[expose] def GGQ2LDatum.HasShape {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Bs L : Subgroup G} {x : G} (M : GGQ2LDatum p Bs L x) : GGQ2ShapeTag → Prop
  | .full => M.ShapeFull
  | .a => M.ShapeA
  | .b => M.ShapeB
  | .c => M.ShapeC
  | .d => M.ShapeD

@[expose] def GGQ2S08Cell (t : LargeEvenLieTag) (r : ℕ) (s : GGQ2ShapeTag) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting 3 B Bs x L D J → ¬ GGQTwoI1 Bs D J → 4 ∣ Nat.card ↥(ggAutomizer J Bs) →
    ∀ (M : GGQ2LDatum 3 Bs L x), M.HasShape s → ∀ {labL : LargeEvenLabel},
      LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL) →
      labL.tag = t → labL.rank = r → GGLabQTwo 3 labL → GGQ2LabelWeyl labL M.coxeter →
      ∀ (g : G) (φ : MulAut ↥Bs), GGQ2Ind Bs g φ → GGIsReflection 3 φ →
        g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G)

@[expose] def GGQ2ReflEKSmallInput : Prop :=
  (∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → ¬ GGQTwoI1 Bs D J →
    4 ∣ Nat.card (ggAutomizer J Bs) → Nat.card ↥Bs ≤ 3 ^ 9 →
    ∀ (g : G) (φ : MulAut ↥Bs), GGQ2Ind Bs g φ → GGIsReflection p φ → GGQ2MovesX Bs x φ →
      GGQ2CentreNotIn Bs D φ → GGQ2EForm Bs J φ →
        g ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G)) ∧
  (∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → ¬ GGQTwoI1 Bs D J →
    4 ∣ Nat.card (ggAutomizer J Bs) → Nat.card ↥Bs ≤ 3 ^ 9 →
    ∀ (g : G) (φ : MulAut ↥Bs), GGQ2Ind Bs g φ → GGIsReflection p φ → GGQ2MovesX Bs x φ →
      GGQ2CentreNotIn Bs D φ → ¬ GGQ2EForm Bs J φ →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → (∀ c : ↥Bs, (c : G) = y → φ c = c) →
        (¬ ∃ k ∈ K, GGQ2Ind Bs k φ) →
        (¬ ∃ k ∈ K, k ∈ Subgroup.normalizer (Bs : Set G) ∧ k * x * k⁻¹ = g * x * g⁻¹) →
          g ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G))

@[expose] def ggQ2S08CellList : List (LargeEvenLieTag × ℕ × GGQ2ShapeTag) :=
  [(.twA, 4, .full), (.twA, 5, .a), (.twA, 5, .b), (.twA, 5, .c), (.twA, 5, .d),
   (.twA, 6, .full), (.twA, 7, .full), (.twA, 8, .a), (.twA, 8, .b), (.twA, 8, .c),
   (.twA, 8, .d),
   (.B, 4, .full), (.B, 5, .full), (.B, 6, .full), (.B, 7, .full), (.B, 8, .full),
   (.C, 4, .full), (.C, 5, .full), (.C, 6, .full), (.C, 7, .full), (.C, 8, .full),
   (.D, 4, .full), (.D, 6, .full), (.D, 8, .full),
   (.twD, 5, .full), (.twD, 7, .full),
   (.F4, 0, .full),
   (.twE6, 0, .a), (.twE6, 0, .b), (.twE6, 0, .c), (.twE6, 0, .d),
   (.E7, 0, .full), (.E8, 0, .full)]

@[expose] def GGQ2S08SmallCells : Prop :=
  ∀ (t : LargeEvenLieTag) (r : ℕ) (s : GGQ2ShapeTag),
    (t, r, s) ∈ ggQ2S08CellList → GGQ2S08Cell t r s

private lemma ggQ2S08_cardV {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) :
    Nat.card ↥Bs = 3 ^ Module.finrank (ZMod 3) M.V := by
  have : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := rfl
    _ = Nat.card M.V := Nat.card_congr M.model.toEquiv
    _ = 3 ^ Module.finrank (ZMod 3) M.V :=
      (FiniteField.pow_finrank_eq_natCard 3 M.V).symm

private lemma ggQ2S08_finrank_le_nine {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hcard : Nat.card ↥Bs ≤ 3 ^ 9) :
    Module.finrank (ZMod 3) M.V ≤ 9 := by
  rw [ggQ2S08_cardV M] at hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hcard

private lemma ggQ2S08_fixed_iff {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (v : M.V) :
    (∀ g ∈ M.toWDatum.weyl, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {M.xV} := by
  have hfixed : v ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) ↔
      ∀ g ∈ M.toWDatum.weyl, g v = v := by
    rw [M.weyl_eq_map, mem_ggFixedSubmodule_iff]
    constructor
    · rintro h g hg
      obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hg
      exact h φ hφ
    · intro h φ hφ
      exact h (ggLin (p := 3) M.model φ) (Subgroup.mem_map_of_mem _ hφ)
  rw [← hfixed, M.fixed_x]
  rfl

private lemma ggQ2S08_mem_span_of_simple_fixed {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (v : M.V)
    (h : ∀ i, ggLin (p := 3) M.model (M.simple i) v = v) :
    v ∈ Submodule.span (ZMod 3) {M.xV} := by
  let H : Subgroup (MulAut ↥Bs) :=
    { carrier := {φ | ggLin (p := 3) M.model φ v = v}
      one_mem' := by simp
      mul_mem' := by
        rintro a b ha hb
        show ggLin (p := 3) M.model (a * b) v = v
        rw [map_mul]
        show (ggLin (p := 3) M.model a) ((ggLin (p := 3) M.model b) v) = v
        rw [hb, ha]
      inv_mem' := by
        rintro a ha
        show ggLin (p := 3) M.model a⁻¹ v = v
        rw [map_inv]
        apply (ggLin (p := 3) M.model a).injective
        change (ggLin (p := 3) M.model a) ((ggLin (p := 3) M.model a).symm v) =
          (ggLin (p := 3) M.model a) v
        rw [LinearEquiv.apply_symm_apply]
        exact ha.symm }
  have hle : Subgroup.closure (Set.range M.simple) ≤ H := by
    rw [Subgroup.closure_le H]
    rintro φ ⟨i, rfl⟩
    show ggLin (p := 3) M.model (M.simple i) v = v
    exact h i
  have hmem : v ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
    rw [mem_ggFixedSubmodule_iff]
    intro φ hφ
    rw [M.automizer_L] at hφ
    exact hle hφ
  rw [M.fixed_x] at hmem
  exact hmem

private lemma ggQ2S08_kernel_eq_bot {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hdet : ((M.cartan.det : ℤ) : ZMod 3) ≠ 0) :
    ∀ v ∈ M.coSpan, (∀ i, M.root i v = 0) → v = 0 := by
  intro v hv hroot
  rw [GGQ2LDatum.coSpan, Submodule.mem_span_range_iff_exists_fun] at hv
  obtain ⟨c, hc⟩ := hv
  have hmat : ((Int.castRingHom (ZMod 3)).mapMatrix M.cartan).det ≠ 0 := by
    rw [← RingHom.map_det]
    exact hdet
  have h0 : ((Int.castRingHom (ZMod 3)).mapMatrix M.cartan).mulVec c = 0 := by
    funext j
    have h := hroot j
    rw [← hc] at h
    simp only [map_sum, map_smul, smul_eq_mul, M.pairing] at h
    simpa [Matrix.mulVec, dotProduct, mul_comm] using h
  have hc0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero hmat h0
  rw [hc0] at hc
  simpa using hc.symm

private lemma ggQ2S08_shapeFull_of_det {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hxV0 : M.xV ≠ 0)
    (hdet : ((M.cartan.det : ℤ) : ZMod 3) ≠ 0)
    (hind : LinearIndependent (ZMod 3) M.coroot) (hshape : M.Shape) : M.ShapeFull := by
  have hfin : Module.finrank (ZMod 3) M.coSpan = Fintype.card M.Λ := by
    rw [GGQ2LDatum.coSpan]
    exact finrank_span_eq_card hind
  have hxH : M.xV ∉ M.coSpan := by
    intro hxspan
    have hroot0 : ∀ i : M.Λ, M.root i M.xV = 0 := by
      intro i
      have hfixi := (ggQ2S08_fixed_iff M M.xV).mpr (Submodule.mem_span_singleton_self M.xV)
        (M.toWDatum.simpleRefl i) (M.toWDatum.simpleRefl_mem_weyl i)
      have h2 := GGQ2WDatum.simpleRefl_apply M.toWDatum i M.xV
      rw [h2] at hfixi
      have h0 : M.root i M.xV • M.coroot i = 0 := sub_eq_self.mp hfixi
      have h1 := congrArg (M.root i) h0
      rw [map_smul, smul_eq_mul, show M.root i (M.coroot i) = 2 from
        M.toWDatum.root_coroot_self i, map_zero] at h1
      exact (mul_eq_zero.mp h1).resolve_right (by decide : (2 : ZMod 3) ≠ 0)
    exact hxV0 (ggQ2S08_kernel_eq_bot M hdet M.xV hxspan hroot0)
  rcases hshape with hF | hA | hB | hC | hD
  · exact hF
  · exact absurd hA.2.2.1 hxH
  · exact absurd (hfin ▸ hB.2.1) (by omega)
  · exact absurd (hfin ▸ hC.2.1) (by omega)
  · exact absurd (hD.2.2 ▸ Submodule.mem_top) hxH

theorem ggQ2S08_not_shapeFull_of_det_zero {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x)
    (hdet : ¬ IsUnit (M.cartan.map (Int.castRingHom (ZMod 3))).det) :
    ¬ M.ShapeFull := by
  intro hFull
  let Cm : Matrix M.Λ M.Λ (ZMod 3) := M.cartan.map (Int.castRingHom (ZMod 3))
  have hnotinj : ¬ Function.Injective Cm.mulVec := by
    intro hinj
    exact hdet ((Matrix.isUnit_iff_isUnit_det Cm).mp
      ((Matrix.mulVec_injective_iff_isUnit).mp hinj))
  obtain ⟨u, v, huv, huvne⟩ := Function.not_injective_iff.mp hnotinj
  let c : M.Λ → ZMod 3 := u - v
  have hc : Cm.mulVec c = 0 := by
    rw [show c = u - v from rfl, Matrix.mulVec_sub, huv, sub_self]
  have hcne : c ≠ 0 := sub_ne_zero.mpr huvne
  have hind := hFull.2.1
  have hsum0 : (∑ j, c j • M.coroot j) = 0 → c = 0 := by
    intro h0
    funext i
    exact (Fintype.linearIndependent_iff.mp hind) c h0 i
  have hv0 : (∑ j, c j • M.coroot j) ≠ 0 := fun h0 => hcne (hsum0 h0)
  have hroot : ∀ i, M.root i (∑ j, c j • M.coroot j) = 0 := by
    intro i
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, M.pairing]
    have h := congrFun hc i
    simpa [Cm, Matrix.mulVec, dotProduct, mul_comm] using h
  have hfix : ∀ i, ggLin (p := 3) M.model (M.simple i) (∑ j, c j • M.coroot j) =
      ∑ j, c j • M.coroot j := by
    intro i
    rw [M.simple_apply, hroot i, zero_smul, sub_zero]
  have hspan := ggQ2S08_mem_span_of_simple_fixed M (∑ j, c j • M.coroot j) hfix
  have hv : (∑ j, c j • M.coroot j) ∈ M.coSpan := by
    rw [GGQ2LDatum.coSpan]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hspan
  have ha0 : a ≠ 0 := by
    intro h0
    exact hv0 (by rw [← ha, h0, zero_smul])
  have hx : M.xV ∈ M.coSpan := by
    have h1 : M.xV = a⁻¹ • (∑ j, c j • M.coroot j) := by
      rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
    rw [h1]
    exact M.coSpan.smul_mem _ hv
  exact hFull.2.2.1 hx

private lemma ggQ2S08_det_eq_of_cartan {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    {ℓ : ℕ} (M : GGQ2LDatum 3 Bs L x) (e : Fin ℓ ≃ M.Λ)
    (C₀ : Matrix (Fin ℓ) (Fin ℓ) ℤ) (hC : ∀ i j, M.cartan (e i) (e j) = C₀ i j) :
    (M.cartan.map (Int.castRingHom (ZMod 3))).det =
      (C₀.map (Int.castRingHom (ZMod 3))).det := by
  have hcart : M.cartan = Matrix.reindex e e C₀ := by
    ext i j
    have := hC (e.symm i) (e.symm j)
    simpa [Matrix.reindex, Matrix.submatrix_apply] using this
  rw [hcart]
  rw [show (Matrix.reindex e e C₀).map (Int.castRingHom (ZMod 3)) =
      Matrix.reindex e e (C₀.map (Int.castRingHom (ZMod 3))) from rfl]
  change ((C₀.map (Int.castRingHom (ZMod 3))).submatrix e.symm e.symm).det =
    (C₀.map (Int.castRingHom (ZMod 3))).det
  rw [Matrix.det_submatrix_equiv_self e.symm (C₀.map (Int.castRingHom (ZMod 3)))]

private lemma ggQ2S08_det_A (r : ℕ) :
    ((CartanMatrix.A r).map (Int.castRingHom (ZMod 3))).det = ((r + 1 : ℤ) : ZMod 3) := by
  rw [show (CartanMatrix.A r).map (Int.castRingHom (ZMod 3)) =
      (Int.castRingHom (ZMod 3)).mapMatrix (CartanMatrix.A r) from rfl,
    ← RingHom.map_det (Int.castRingHom (ZMod 3)) (CartanMatrix.A r), CartanMatrix.A_det]
  norm_num

private lemma ggQ2S08_det_B (r : ℕ) (hr : 0 < r) :
    ((CartanMatrix.B r).map (Int.castRingHom (ZMod 3))).det = (2 : ZMod 3) := by
  rw [show (CartanMatrix.B r).map (Int.castRingHom (ZMod 3)) =
      (Int.castRingHom (ZMod 3)).mapMatrix (CartanMatrix.B r) from rfl,
    ← RingHom.map_det (Int.castRingHom (ZMod 3)) (CartanMatrix.B r), CartanMatrix.B_det hr]
  norm_num

private lemma ggQ2S08_det_C (r : ℕ) (hr : 0 < r) :
    ((CartanMatrix.C r).map (Int.castRingHom (ZMod 3))).det = (2 : ZMod 3) := by
  rw [show (CartanMatrix.C r).map (Int.castRingHom (ZMod 3)) =
      (Int.castRingHom (ZMod 3)).mapMatrix (CartanMatrix.C r) from rfl,
    ← RingHom.map_det (Int.castRingHom (ZMod 3)) (CartanMatrix.C r), CartanMatrix.C_det hr]
  norm_num

private lemma ggQ2S08_det_D (r : ℕ) (hr : 2 ≤ r) :
    ((CartanMatrix.D r).map (Int.castRingHom (ZMod 3))).det = (4 : ZMod 3) := by
  rw [show (CartanMatrix.D r).map (Int.castRingHom (ZMod 3)) =
      (Int.castRingHom (ZMod 3)).mapMatrix (CartanMatrix.D r) from rfl,
    ← RingHom.map_det (Int.castRingHom (ZMod 3)) (CartanMatrix.D r), CartanMatrix.D_det hr]
  norm_num

private lemma ggQ2S08_det_E6 :
    ((CartanMatrix.E 6).map (Int.castRingHom (ZMod 3))).det = (3 : ZMod 3) := by
  rw [show (CartanMatrix.E 6).map (Int.castRingHom (ZMod 3)) =
      (Int.castRingHom (ZMod 3)).mapMatrix (CartanMatrix.E 6) from rfl,
    ← RingHom.map_det (Int.castRingHom (ZMod 3)) (CartanMatrix.E 6),
    CartanMatrix.E_det (by norm_num : 3 ≤ 6)]
  norm_num

private lemma ggQ2S08_det_E7 :
    ((CartanMatrix.E 7).map (Int.castRingHom (ZMod 3))).det = (2 : ZMod 3) := by
  rw [show (CartanMatrix.E 7).map (Int.castRingHom (ZMod 3)) =
      (Int.castRingHom (ZMod 3)).mapMatrix (CartanMatrix.E 7) from rfl,
    ← RingHom.map_det (Int.castRingHom (ZMod 3)) (CartanMatrix.E 7),
    CartanMatrix.E_det (by norm_num : 3 ≤ 7)]
  norm_num

private lemma ggQ2S08_det_E8 :
    ((CartanMatrix.E 8).map (Int.castRingHom (ZMod 3))).det = (1 : ZMod 3) := by
  rw [show (CartanMatrix.E 8).map (Int.castRingHom (ZMod 3)) =
      (Int.castRingHom (ZMod 3)).mapMatrix (CartanMatrix.E 8) from rfl,
    ← RingHom.map_det (Int.castRingHom (ZMod 3)) (CartanMatrix.E 8),
    CartanMatrix.E_det (by norm_num : 3 ≤ 8)]
  norm_num

private lemma ggQ2S08_det_F4 :
    (CartanMatrix.F₄.map (Int.castRingHom (ZMod 3))).det = (1 : ZMod 3) := by
  rw [show CartanMatrix.F₄.map (Int.castRingHom (ZMod 3)) =
      (Int.castRingHom (ZMod 3)).mapMatrix CartanMatrix.F₄ from rfl,
    ← RingHom.map_det (Int.castRingHom (ZMod 3)) CartanMatrix.F₄, CartanMatrix.F₄_det]
  norm_num

private lemma ggQ2S08_isUnit_det_A (r : ℕ) (h : ¬ 3 ∣ r + 1) :
    IsUnit ((CartanMatrix.A r).map (Int.castRingHom (ZMod 3))).det := by
  rw [ggQ2S08_det_A r, isUnit_iff_ne_zero]
  intro hz
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
  exact h (by exact_mod_cast hz)

private lemma ggQ2S08_isUnit_det_B (r : ℕ) (hr : 0 < r) :
    IsUnit ((CartanMatrix.B r).map (Int.castRingHom (ZMod 3))).det := by
  rw [ggQ2S08_det_B r hr]; decide

private lemma ggQ2S08_isUnit_det_C (r : ℕ) (hr : 0 < r) :
    IsUnit ((CartanMatrix.C r).map (Int.castRingHom (ZMod 3))).det := by
  rw [ggQ2S08_det_C r hr]; decide

private lemma ggQ2S08_isUnit_det_D (r : ℕ) (hr : 2 ≤ r) :
    IsUnit ((CartanMatrix.D r).map (Int.castRingHom (ZMod 3))).det := by
  rw [ggQ2S08_det_D r hr]; decide

private lemma ggQ2S08_isUnit_det_E7 :
    IsUnit ((CartanMatrix.E 7).map (Int.castRingHom (ZMod 3))).det := by
  rw [ggQ2S08_det_E7]; decide

private lemma ggQ2S08_isUnit_det_E8 :
    IsUnit ((CartanMatrix.E 8).map (Int.castRingHom (ZMod 3))).det := by
  rw [ggQ2S08_det_E8]; decide

private lemma ggQ2S08_isUnit_det_F4 :
    IsUnit (CartanMatrix.F₄.map (Int.castRingHom (ZMod 3))).det := by
  rw [ggQ2S08_det_F4]; decide

private lemma ggQ2S08_isUnit_det_F4t :
    IsUnit ((CartanMatrix.F₄.transpose).map (Int.castRingHom (ZMod 3))).det := by
  rw [show (CartanMatrix.F₄.transpose).map (Int.castRingHom (ZMod 3)) =
      (CartanMatrix.F₄.map (Int.castRingHom (ZMod 3))).transpose from rfl,
    Matrix.det_transpose, ggQ2S08_det_F4]
  decide

private lemma ggQ2S08_not_isUnit_det_E6 :
    ¬ IsUnit ((CartanMatrix.E 6).map (Int.castRingHom (ZMod 3))).det := by
  rw [ggQ2S08_det_E6]; decide

private theorem ggQ2S08_exists_cell {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) (hcard : Nat.card ↥Bs ≤ 3 ^ 9)
    {labL : LargeEvenLabel} (hlab : GGQ2TBLabel labL)
    (hmark : LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL))
    (M : GGQ2LDatum 3 Bs L x) (hLW : GGQ2LabelWeyl labL M.coxeter) (hshape : M.Shape)
    (hheart : Module.finrank (ZMod 3) M.V ≤ Fintype.card M.Λ →
      (labL.tag = .twA ∧ 3 ∣ labL.rank + 1) ∨ labL.tag = .twE6) :
    ∃ s : GGQ2ShapeTag, M.HasShape s ∧ (labL.tag, labL.rank, s) ∈ ggQ2S08CellList := by
  classical
  have hfin9 := ggQ2S08_finrank_le_nine M hcard
  have hΛ := ggQ2LD_card_lie hLW hlab
  have hx1 : x ≠ 1 := hS.1.1.1.2.2.2.2.2.2.1.2.2.1
  obtain ⟨lab, hlab2, -, R, hRgrp, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hmark
  have hlabL2 : LargeEvenInLambda2 labL := hP ▸ hlab2
  have cell {s : GGQ2ShapeTag} (hs : M.HasShape s)
      (hmem : (labL.tag, labL.rank, s) ∈ ggQ2S08CellList) :
      ∃ s : GGQ2ShapeTag, M.HasShape s ∧ (labL.tag, labL.rank, s) ∈ ggQ2S08CellList :=
    ⟨s, hs, hmem⟩
  have shapeFull_of_unit (hunit : IsUnit (M.cartan.map (Int.castRingHom (ZMod 3))).det) :
      M.ShapeFull := by
    have hdet : ((M.cartan.det : ℤ) : ZMod 3) ≠ 0 := by
      have h := isUnit_iff_ne_zero.mp hunit
      rwa [show M.cartan.map (Int.castRingHom (ZMod 3)) =
          (Int.castRingHom (ZMod 3)).mapMatrix M.cartan from rfl,
        ← RingHom.map_det (Int.castRingHom (ZMod 3)) M.cartan] at h
    have hind := GGQ2WDatum.coroot_linearIndependent_of_det M.toWDatum hdet
    have hxV0 : M.xV ≠ 0 := by
      intro h0
      have h1 : Additive.ofMul (⟨x, M.hx⟩ : ↥Bs) = 0 :=
        M.model.injective (by rw [map_zero]; exact h0)
      have h2 : (⟨x, M.hx⟩ : ↥Bs) = 1 := Additive.ofMul.injective (by simpa using h1)
      exact hx1 (Subtype.ext_iff.mp h2)
    exact ggQ2S08_shapeFull_of_det M hxV0 hdet hind hshape
  unfold GGQ2TBLabel at hlab
  rcases hlab with ⟨htag, h4⟩ | ⟨htag, h4⟩ | ⟨htag, heven, h4⟩ | ⟨htag, hodd, h4⟩ |
    htag | htag | htag | htag
  ·
    have hLW' : ∃ e : Fin labL.rank ≃ M.Λ,
        M.coxeter = (CoxeterMatrix.A labL.rank).reindex e := by
      simpa only [GGQ2LabelWeyl, htag] using hLW
    obtain ⟨e, he⟩ := hLW'
    have hcardΛ : Fintype.card M.Λ = labL.rank := by rw [hΛ, GGQ2LieRank, htag]
    have hC : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.A labL.rank i j :=
      ggQ2_cartan_A e he M.isCartan
    by_cases h3 : 3 ∣ labL.rank + 1
    · have hnotunit : ¬ IsUnit (M.cartan.map (Int.castRingHom (ZMod 3))).det := by
        rw [ggQ2S08_det_eq_of_cartan M e (CartanMatrix.A labL.rank) hC, ggQ2S08_det_A]
        intro hunit
        have hz : ((labL.rank + 1 : ℤ) : ZMod 3) = 0 := by
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
          exact_mod_cast h3
        exact (isUnit_iff_ne_zero.mp hunit) hz
      have hnotfull : ¬ M.ShapeFull := ggQ2S08_not_shapeFull_of_det_zero M hnotunit
      rcases hshape with hF | hA | hB | hC | hD
      · exact absurd hF hnotfull
      · have hdim : Module.finrank (ZMod 3) M.V = Fintype.card M.Λ + 1 :=
          ggQ2LD_dim_nonheart M (Or.inr (Or.inl hA))
        have hr8 : labL.rank ≤ 8 := by rw [hdim, hcardΛ] at hfin9; omega
        have hmem : (labL.tag, labL.rank, .a) ∈ ggQ2S08CellList := by
          interval_cases labL.rank <;> simp [ggQ2S08CellList, htag] at h3 ⊢
        exact cell (s := .a) (by simpa only [GGQ2LDatum.HasShape] using hA) hmem
      · have hdim : Module.finrank (ZMod 3) M.V = Fintype.card M.Λ :=
          ggQ2LD_dim_heart M (Or.inl hB)
        have hr9 : labL.rank ≤ 9 := by rw [hdim, hcardΛ] at hfin9; omega
        have hmem : (labL.tag, labL.rank, .b) ∈ ggQ2S08CellList := by
          interval_cases labL.rank <;> simp [ggQ2S08CellList, htag] at h3 ⊢
        exact cell (s := .b) (by simpa only [GGQ2LDatum.HasShape] using hB) hmem
      · have hdim : Module.finrank (ZMod 3) M.V = Fintype.card M.Λ + 1 :=
          ggQ2LD_dim_nonheart M (Or.inr (Or.inr hC))
        have hr8 : labL.rank ≤ 8 := by rw [hdim, hcardΛ] at hfin9; omega
        have hmem : (labL.tag, labL.rank, .c) ∈ ggQ2S08CellList := by
          interval_cases labL.rank <;> simp [ggQ2S08CellList, htag] at h3 ⊢
        exact cell (s := .c) (by simpa only [GGQ2LDatum.HasShape] using hC) hmem
      · have hdim : Module.finrank (ZMod 3) M.V = Fintype.card M.Λ :=
          ggQ2LD_dim_heart M (Or.inr hD)
        have hr9 : labL.rank ≤ 9 := by rw [hdim, hcardΛ] at hfin9; omega
        have hmem : (labL.tag, labL.rank, .d) ∈ ggQ2S08CellList := by
          interval_cases labL.rank <;> simp [ggQ2S08CellList, htag] at h3 ⊢
        exact cell (s := .d) (by simpa only [GGQ2LDatum.HasShape] using hD) hmem
    · have hunitM : IsUnit (M.cartan.map (Int.castRingHom (ZMod 3))).det :=
        isUnit_cartan_det_of_reindex M e (CartanMatrix.A labL.rank) hC
          (ggQ2S08_isUnit_det_A labL.rank h3)
      have hFull : M.ShapeFull := shapeFull_of_unit hunitM
      have hdim : Module.finrank (ZMod 3) M.V = Fintype.card M.Λ + 1 :=
        ggQ2LD_dim_nonheart M (Or.inl hFull)
      have hr8 : labL.rank ≤ 8 := by rw [hdim, hcardΛ] at hfin9; omega
      have hmem : (labL.tag, labL.rank, .full) ∈ ggQ2S08CellList := by
        interval_cases labL.rank <;> simp [ggQ2S08CellList, htag] at h3 ⊢
      exact cell (s := .full) (by simpa only [GGQ2LDatum.HasShape] using hFull) hmem
  ·
    rcases htag with htag | htag
    · have hLW' : ∃ e : Fin labL.rank ≃ M.Λ,
          M.coxeter = (CoxeterMatrix.B labL.rank).reindex e := by
        simpa only [GGQ2LabelWeyl, htag] using hLW
      obtain ⟨e, he⟩ := hLW'
      have hcardΛ : Fintype.card M.Λ = labL.rank := by rw [hΛ, GGQ2LieRank, htag]
      have hunitM : IsUnit (M.cartan.map (Int.castRingHom (ZMod 3))).det := by
        rcases ggQ2_cartan_B e he M.isCartan with hC | hC
        · exact isUnit_cartan_det_of_reindex M e (CartanMatrix.B labL.rank) hC
            (ggQ2S08_isUnit_det_B labL.rank (by omega))
        · exact isUnit_cartan_det_of_reindex M e (CartanMatrix.C labL.rank) hC
            (ggQ2S08_isUnit_det_C labL.rank (by omega))
      have hFull : M.ShapeFull := shapeFull_of_unit hunitM
      have hdim : Module.finrank (ZMod 3) M.V = Fintype.card M.Λ + 1 :=
        ggQ2LD_dim_nonheart M (Or.inl hFull)
      have hr8 : labL.rank ≤ 8 := by rw [hdim, hcardΛ] at hfin9; omega
      have hmem : (labL.tag, labL.rank, .full) ∈ ggQ2S08CellList := by
        interval_cases labL.rank <;> simp [ggQ2S08CellList, htag]
      exact cell (s := .full) (by simpa only [GGQ2LDatum.HasShape] using hFull) hmem
    · have hLW' : ∃ e : Fin labL.rank ≃ M.Λ,
          M.coxeter = (CoxeterMatrix.B labL.rank).reindex e := by
        simpa only [GGQ2LabelWeyl, htag] using hLW
      obtain ⟨e, he⟩ := hLW'
      have hcardΛ : Fintype.card M.Λ = labL.rank := by rw [hΛ, GGQ2LieRank, htag]
      have hunitM : IsUnit (M.cartan.map (Int.castRingHom (ZMod 3))).det := by
        rcases ggQ2_cartan_B e he M.isCartan with hC | hC
        · exact isUnit_cartan_det_of_reindex M e (CartanMatrix.B labL.rank) hC
            (ggQ2S08_isUnit_det_B labL.rank (by omega))
        · exact isUnit_cartan_det_of_reindex M e (CartanMatrix.C labL.rank) hC
            (ggQ2S08_isUnit_det_C labL.rank (by omega))
      have hFull : M.ShapeFull := shapeFull_of_unit hunitM
      have hdim : Module.finrank (ZMod 3) M.V = Fintype.card M.Λ + 1 :=
        ggQ2LD_dim_nonheart M (Or.inl hFull)
      have hr8 : labL.rank ≤ 8 := by rw [hdim, hcardΛ] at hfin9; omega
      have hmem : (labL.tag, labL.rank, .full) ∈ ggQ2S08CellList := by
        interval_cases labL.rank <;> simp [ggQ2S08CellList, htag]
      exact cell (s := .full) (by simpa only [GGQ2LDatum.HasShape] using hFull) hmem
  ·
    have hLW' : ∃ e : Fin labL.rank ≃ M.Λ,
        M.coxeter = (ggCoxeterMatrixD labL.rank).reindex e := by
      simpa only [GGQ2LabelWeyl, htag] using hLW
    obtain ⟨e, he⟩ := hLW'
    have hcardΛ : Fintype.card M.Λ = labL.rank := by rw [hΛ, GGQ2LieRank, htag]
    have hC : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.D labL.rank i j :=
      ggQ2_cartan_D e he M.isCartan
    have hunitM : IsUnit (M.cartan.map (Int.castRingHom (ZMod 3))).det :=
      isUnit_cartan_det_of_reindex M e (CartanMatrix.D labL.rank) hC
        (ggQ2S08_isUnit_det_D labL.rank (by omega))
    have hFull : M.ShapeFull := shapeFull_of_unit hunitM
    have hdim : Module.finrank (ZMod 3) M.V = Fintype.card M.Λ + 1 :=
      ggQ2LD_dim_nonheart M (Or.inl hFull)
    have hr8 : labL.rank ≤ 8 := by rw [hdim, hcardΛ] at hfin9; omega
    have hmem : (labL.tag, labL.rank, .full) ∈ ggQ2S08CellList := by
      interval_cases labL.rank <;> simp [ggQ2S08CellList, Even, htag] at heven ⊢ <;> omega
    exact cell (s := .full) (by simpa only [GGQ2LDatum.HasShape] using hFull) hmem
  ·
    have hLW' : ∃ e : Fin labL.rank ≃ M.Λ,
        M.coxeter = (ggCoxeterMatrixD labL.rank).reindex e := by
      simpa only [GGQ2LabelWeyl, htag] using hLW
    obtain ⟨e, he⟩ := hLW'
    have hcardΛ : Fintype.card M.Λ = labL.rank := by rw [hΛ, GGQ2LieRank, htag]
    have hC : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.D labL.rank i j :=
      ggQ2_cartan_D e he M.isCartan
    have hunitM : IsUnit (M.cartan.map (Int.castRingHom (ZMod 3))).det :=
      isUnit_cartan_det_of_reindex M e (CartanMatrix.D labL.rank) hC
        (ggQ2S08_isUnit_det_D labL.rank (by omega))
    have hFull : M.ShapeFull := shapeFull_of_unit hunitM
    have hdim : Module.finrank (ZMod 3) M.V = Fintype.card M.Λ + 1 :=
      ggQ2LD_dim_nonheart M (Or.inl hFull)
    have hr8 : labL.rank ≤ 8 := by rw [hdim, hcardΛ] at hfin9; omega
    have hmem : (labL.tag, labL.rank, .full) ∈ ggQ2S08CellList := by
      interval_cases labL.rank <;> simp [ggQ2S08CellList, Odd, htag] at hodd ⊢ <;> omega
    exact cell (s := .full) (by simpa only [GGQ2LDatum.HasShape] using hFull) hmem
  ·
    have hLW' : ∃ e : Fin 4 ≃ M.Λ, M.coxeter = CoxeterMatrix.F₄.reindex e := by
      simpa only [GGQ2LabelWeyl, htag] using hLW
    obtain ⟨e, he⟩ := hLW'
    have hcardΛ : Fintype.card M.Λ = 4 := by rw [hΛ, GGQ2LieRank, htag]
    have hunitM : IsUnit (M.cartan.map (Int.castRingHom (ZMod 3))).det := by
      rcases ggQ2_cartan_F₄ e he M.isCartan with hC | hC
      · exact isUnit_cartan_det_of_reindex M e CartanMatrix.F₄ hC ggQ2S08_isUnit_det_F4
      · exact isUnit_cartan_det_of_reindex M e (CartanMatrix.F₄.transpose) hC
          ggQ2S08_isUnit_det_F4t
    have hFull : M.ShapeFull := shapeFull_of_unit hunitM
    have hrank0 : labL.rank = 0 := by
      have h := hlabL2
      simp only [LargeEvenInLambda2, htag] at h
      exact h.2
    have hmem : (labL.tag, labL.rank, .full) ∈ ggQ2S08CellList := by
      rw [hrank0, htag]; decide
    exact cell (s := .full) (by simpa only [GGQ2LDatum.HasShape] using hFull) hmem
  ·
    have hLW' : ∃ e : Fin 6 ≃ M.Λ, M.coxeter = CoxeterMatrix.E₆.reindex e := by
      simpa only [GGQ2LabelWeyl, htag] using hLW
    obtain ⟨e, he⟩ := hLW'
    have hcardΛ : Fintype.card M.Λ = 6 := by rw [hΛ, GGQ2LieRank, htag]
    have hC : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.E₆ i j :=
      ggQ2_cartan_E₆ e he M.isCartan
    have hnotunit : ¬ IsUnit (M.cartan.map (Int.castRingHom (ZMod 3))).det := by
      rw [ggQ2S08_det_eq_of_cartan M e CartanMatrix.E₆ hC, ggQ2S08_det_E6]
      decide
    have hnotfull : ¬ M.ShapeFull := ggQ2S08_not_shapeFull_of_det_zero M hnotunit
    have hrank0 : labL.rank = 0 := by
      have h := hlabL2
      simp only [LargeEvenInLambda2, htag] at h
      exact h.2
    rcases hshape with hF | hA | hB | hC | hD
    · exact absurd hF hnotfull
    · have hmem : (labL.tag, labL.rank, .a) ∈ ggQ2S08CellList := by
        rw [hrank0, htag]; decide
      exact cell (s := .a) (by simpa only [GGQ2LDatum.HasShape] using hA) hmem
    · have hmem : (labL.tag, labL.rank, .b) ∈ ggQ2S08CellList := by
        rw [hrank0, htag]; decide
      exact cell (s := .b) (by simpa only [GGQ2LDatum.HasShape] using hB) hmem
    · have hmem : (labL.tag, labL.rank, .c) ∈ ggQ2S08CellList := by
        rw [hrank0, htag]; decide
      exact cell (s := .c) (by simpa only [GGQ2LDatum.HasShape] using hC) hmem
    · have hmem : (labL.tag, labL.rank, .d) ∈ ggQ2S08CellList := by
        rw [hrank0, htag]; decide
      exact cell (s := .d) (by simpa only [GGQ2LDatum.HasShape] using hD) hmem
  ·
    have hLW' : ∃ e : Fin 7 ≃ M.Λ, M.coxeter = CoxeterMatrix.E₇.reindex e := by
      simpa only [GGQ2LabelWeyl, htag] using hLW
    obtain ⟨e, he⟩ := hLW'
    have hcardΛ : Fintype.card M.Λ = 7 := by rw [hΛ, GGQ2LieRank, htag]
    have hC : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.E₇ i j :=
      ggQ2_cartan_E₇ e he M.isCartan
    have hunitM : IsUnit (M.cartan.map (Int.castRingHom (ZMod 3))).det :=
      isUnit_cartan_det_of_reindex M e CartanMatrix.E₇ hC ggQ2S08_isUnit_det_E7
    have hFull : M.ShapeFull := shapeFull_of_unit hunitM
    have hrank0 : labL.rank = 0 := by
      have h := hlabL2
      simp only [LargeEvenInLambda2, htag] at h
      exact h.2
    have hmem : (labL.tag, labL.rank, .full) ∈ ggQ2S08CellList := by
      rw [hrank0, htag]; decide
    exact cell (s := .full) (by simpa only [GGQ2LDatum.HasShape] using hFull) hmem
  ·
    have hLW' : ∃ e : Fin 8 ≃ M.Λ, M.coxeter = CoxeterMatrix.E₈.reindex e := by
      simpa only [GGQ2LabelWeyl, htag] using hLW
    obtain ⟨e, he⟩ := hLW'
    have hcardΛ : Fintype.card M.Λ = 8 := by rw [hΛ, GGQ2LieRank, htag]
    have hC : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.E₈ i j :=
      ggQ2_cartan_E₈ e he M.isCartan
    have hunitM : IsUnit (M.cartan.map (Int.castRingHom (ZMod 3))).det :=
      isUnit_cartan_det_of_reindex M e CartanMatrix.E₈ hC ggQ2S08_isUnit_det_E8
    have hFull : M.ShapeFull := shapeFull_of_unit hunitM
    have hrank0 : labL.rank = 0 := by
      have h := hlabL2
      simp only [LargeEvenInLambda2, htag] at h
      exact h.2
    have hmem : (labL.tag, labL.rank, .full) ∈ ggQ2S08CellList := by
      rw [hrank0, htag]; decide
    exact cell (s := .full) (by simpa only [GGQ2LDatum.HasShape] using hFull) hmem

@[expose] def GGQ2S08CellEK (t : LargeEvenLieTag) (r : ℕ) (s : GGQ2ShapeTag) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting 3 B Bs x L D J → ¬ GGQTwoI1 Bs D J → 4 ∣ Nat.card ↥(ggAutomizer J Bs) →
    ∀ (M : GGQ2LDatum 3 Bs L x), M.HasShape s → ∀ {labL : LargeEvenLabel},
      LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL) →
      labL.tag = t → labL.rank = r → GGLabQTwo 3 labL → GGQ2LabelWeyl labL M.coxeter →
      ∀ (g : G) (φ : MulAut ↥Bs), GGQ2Ind Bs g φ → GGIsReflection 3 φ → GGQ2MovesX Bs x φ →
        GGQ2CentreNotIn Bs D φ →
        (GGQ2EForm Bs J φ → g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G)) ∧
        (¬ GGQ2EForm Bs J φ → ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
          (∀ c : ↥Bs, (c : G) = y → φ c = c) → (¬ ∃ k ∈ K, GGQ2Ind Bs k φ) →
          (¬ ∃ k ∈ K, k ∈ Subgroup.normalizer (Bs : Set G) ∧ k * x * k⁻¹ = g * x * g⁻¹) →
            g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G))

theorem GGQ2S08Cell.toEK {t : LargeEvenLieTag} {r : ℕ} {s : GGQ2ShapeTag}
    (h : GGQ2S08Cell t r s) : GGQ2S08CellEK t r s := by
  intro G _ _ B Bs x L D J hS hI1 hCav M hs labL hmark ht hr hq hW g φ hInd hR _ _
  exact ⟨fun _ => h hS hI1 hCav M hs hmark ht hr hq hW g φ hInd hR,
    fun _ _ _ _ _ _ _ => h hS hI1 hCav M hs hmark ht hr hq hW g φ hInd hR⟩

@[expose] def GGQ2S08SmallCellsEK : Prop :=
  ∀ (t : LargeEvenLieTag) (r : ℕ) (s : GGQ2ShapeTag),
    (t, r, s) ∈ ggQ2S08CellList → GGQ2S08CellEK t r s

theorem ggQ2s08_reflEKSmall_of_cellsEK (hTB : GGQ2TableBI1Fail) (hcells : GGQ2S08SmallCellsEK) :
    GGQ2ReflEKSmallInput := by
  constructor
  · intro G _ _ p B Bs x L D J hS hp hI1 hCav hcard g φ hInd hR hM hCen hE
    subst hp
    obtain ⟨labL, hglab, hlab, hmark, M, hLW, hshape, hheart⟩ := hTB hS rfl hI1
    obtain ⟨s, hs, hmem⟩ := ggQ2S08_exists_cell hS hcard hlab hmark M hLW hshape hheart
    exact (hcells _ _ s hmem hS hI1 hCav M hs hmark rfl rfl hglab hLW g φ hInd hR hM hCen).1 hE
  · intro G _ _ p B Bs x L D J hS hp hI1 hCav hcard g φ hInd hR hM hCen hne y K hNbr hy hnotK
      hnotAK
    subst hp
    obtain ⟨labL, hglab, hlab, hmark, M, hLW, hshape, hheart⟩ := hTB hS rfl hI1
    obtain ⟨s, hs, hmem⟩ := ggQ2S08_exists_cell hS hcard hlab hmark M hLW hshape hheart
    exact (hcells _ _ s hmem hS hI1 hCav M hs hmark rfl rfl hglab hLW g φ hInd hR hM hCen).2 hne
      y K hNbr hy hnotK hnotAK

theorem ggQ2s08_reflEKSmall_of_cells (hTB : GGQ2TableBI1Fail) (hcells : GGQ2S08SmallCells) :
    GGQ2ReflEKSmallInput :=
  ggQ2s08_reflEKSmall_of_cellsEK hTB fun t r s hmem => GGQ2S08Cell.toEK (hcells t r s hmem)

end CFSG.StandardType

end
