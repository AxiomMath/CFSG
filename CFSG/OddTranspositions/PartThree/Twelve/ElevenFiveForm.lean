module

public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveModel
public import CFSG.OddTranspositions.PartThree.FiveReflectionFischer
public import CFSG.OddTranspositions.PartThree.Eleven.Five.FiveFormAux
import CFSG.Mathlib.LinearAlgebra.BilinForm.Finrank
public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveRefl
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveMultReflPair
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveChartModel
import CFSG.Mathlib.Algebra.IsSquareMul

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix
open CFSG.OddTranspositions.PartFour.TableE1Five

@[expose] def fiveReflectionsIn (k : ℕ) (ε π : Bool)
    (W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)) : Set (GL (Fin (k + 1)) (ZMod 5)) :=
  {g | ∃ v ∈ W, fiveForm k ε v v ≠ 0 ∧ (IsSquare (fiveForm k ε v v) ↔ π = true) ∧
    ∀ x, (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x =
      x - (2 * fiveForm k ε x v * (fiveForm k ε v v)⁻¹) • v}

@[expose] def fiveReflectionGroupIn (k : ℕ) (ε π : Bool)
    (W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)) : Subgroup (GL (Fin (k + 1)) (ZMod 5)) :=
  Subgroup.closure (fiveReflectionsIn k ε π W)

@[expose] def IsFiveNondeg (k : ℕ) (ε : Bool) (W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)) :
    Prop :=
  ((fiveBilin k ε true).restrict W).Nondegenerate

theorem isFiveNondeg_iff {k : ℕ} {ε : Bool}
    {W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} :
    IsFiveNondeg k ε W ↔ ∀ x ∈ W, (∀ y ∈ W, fiveForm k ε x y = 0) → x = 0 := by
  constructor
  · intro hW x hx h
    exact Subtype.ext_iff.mp (hW.1 ⟨x, hx⟩ fun y => by
      rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply, fiveBilin_apply,
        h y y.2, mul_zero])
  · intro hW
    refine ⟨?_, ?_⟩
    · intro x hx
      exact Subtype.ext (hW x x.2 fun y hy => by
        have h' := hx ⟨y, hy⟩
        rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
          fiveBilin_apply] at h'
        exact (mul_eq_zero.mp h').resolve_left (inv_ne_zero (fiveSignRep_ne_zero true)))
    · intro y hy
      exact Subtype.ext (hW y y.2 fun x hx => by
        have h' := hy ⟨x, hx⟩
        rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
          fiveBilin_apply] at h'
        have := (mul_eq_zero.mp h').resolve_left (inv_ne_zero (fiveSignRep_ne_zero true))
        rwa [fiveForm_comm] at this)

@[expose] def fiveOrth (k : ℕ) (ε : Bool) (U : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)) :
    Submodule (ZMod 5) (Fin (k + 1) → ZMod 5) :=
  (fiveBilin k ε true).orthogonal U

theorem mem_fiveOrth {k : ℕ} {ε : Bool} {U : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)}
    {x : Fin (k + 1) → ZMod 5} : x ∈ fiveOrth k ε U ↔ ∀ u ∈ U, fiveForm k ε x u = 0 := by
  rw [fiveOrth, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h u hu
    have h' := h u hu
    rw [fiveBilin_apply] at h'
    have := (mul_eq_zero.mp h').resolve_left (inv_ne_zero (fiveSignRep_ne_zero true))
    rwa [fiveForm_comm] at this
  · intro h u hu
    rw [fiveBilin_apply, fiveForm_comm, h u hu, mul_zero]

theorem fiveForm_self_add_smul_smul (k : ℕ) (ε : Bool)
    (x y : Fin (k + 1) → ZMod 5) (a b : ZMod 5) :
    fiveForm k ε (a • x + b • y) (a • x + b • y) =
      a ^ 2 * fiveForm k ε x x + 2 * a * b * fiveForm k ε x y +
        b ^ 2 * fiveForm k ε y y := by
  rw [fiveForm_self_add, fiveForm_smul_smul, fiveForm_smul_smul, fiveForm_smul_smul]
  ring

theorem fiveForm_self_add_smul_smul_singular (k : ℕ) (ε : Bool)
    (x y : Fin (k + 1) → ZMod 5) (a b : ZMod 5)
    (hx : fiveForm k ε x x = 0) (hy : fiveForm k ε y y = 0) :
    fiveForm k ε (a • x + b • y) (a • x + b • y) = 2 * a * b * fiveForm k ε x y := by
  rw [fiveForm_self_add_smul_smul, hx, hy]
  ring

theorem five_sq_sum_covers (a b : ZMod 5) (ha : a ≠ 0) (hb : b ≠ 0) (c : ZMod 5) :
    ∃ α β : ZMod 5, α ^ 2 * a + β ^ 2 * b = c := by
  revert c
  have ha' : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by revert a; decide
  have hb' : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by revert b; decide
  rcases ha' with rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl <;>
    decide +kernel

private theorem five_diag_plane_det (a b c : ZMod 5) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ∃ α β α' β' : ZMod 5,
      α ^ 2 * a + β ^ 2 * b = c ∧ α' ^ 2 * a + β' ^ 2 * b = c ∧
        α * β' - α' * β ≠ 0 := by
  revert a b c
  decide +kernel

theorem five_diag_plane_coeffs (a b c : ZMod 5) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ∃ x y α β α' β' : ZMod 5,
      α ^ 2 * a + β ^ 2 * b = c ∧ α' ^ 2 * a + β' ^ 2 * b = c ∧
        x * α + y * α' = 1 ∧ x * β + y * β' = 0 := by
  obtain ⟨α, β, α', β', h1, h2, hdet⟩ := five_diag_plane_det a b c ha hb hc
  refine ⟨β' / (α * β' - α' * β), -(β / (α * β' - α' * β)), α, β, α', β', h1, h2, ?_, ?_⟩
  · have hdet' : β' * α - α' * β ≠ 0 := by rwa [mul_comm α β'] at hdet
    field_simp [hdet']
    ring
  · have hdet' : β' * α - α' * β ≠ 0 := by rwa [mul_comm α β'] at hdet
    field_simp [hdet']
    ring

theorem five_hyp_plane_coeffs (e : ZMod 5) :
    ∃ x y α β α' β' : ZMod 5,
      α * β = e ∧ α' * β' = e ∧ x * α + y * α' = 1 ∧ x * β + y * β' = 0 := by
  refine ⟨3, 4, 1, e, 2, 3 * e, ?_, ?_, ?_, ?_⟩
  · ring
  · have h : (2 : ZMod 5) * 3 = 1 := by decide
    calc 2 * (3 * e) = ((2 : ZMod 5) * 3) * e := by ring
      _ = 1 * e := by rw [h]
      _ = e := one_mul e
  · decide
  · have h : (15 : ZMod 5) = 0 := by decide
    calc 3 * e + 4 * (3 * e) = (15 : ZMod 5) * e := by ring
      _ = 0 * e := by rw [h]
      _ = 0 := zero_mul e

theorem exists_fiveForm_ne_zero_of_finrank_pos {k : ℕ} {ε : Bool}
    {N : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} (hN : IsFiveNondeg k ε N)
    (h : 0 < Module.finrank (ZMod 5) N) : ∃ v ∈ N, fiveForm k ε v v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hNbot : N ≠ ⊥ := by
    intro hbot
    rw [hbot] at h
    simp at h
  obtain ⟨x, hxN, hx0⟩ := (Submodule.ne_bot_iff N).mp hNbot
  refine hx0 (isFiveNondeg_iff.1 hN x hxN fun y hy => ?_)
  have h2 : (2 : ZMod 5) * fiveForm k ε x y = 0 := by
    have hsum := fiveForm_self_add k ε x y
    rw [hcon x hxN, hcon y hy, hcon (x + y) (N.add_mem hxN hy)] at hsum
    simpa using hsum.symm
  exact (mul_eq_zero.mp h2).resolve_left (by decide)

theorem isFiveNondeg_top (k : ℕ) (ε : Bool) : IsFiveNondeg k ε ⊤ := by
  rw [isFiveNondeg_iff]
  intro x _ hx
  exact fiveBilin_nondegenerate k ε true x fun y => by
    rw [fiveBilin_apply, hx y (Submodule.mem_top), mul_zero]

theorem isFiveNondeg_span_singleton {k : ℕ} {ε : Bool} {v : Fin (k + 1) → ZMod 5}
    (hv : fiveForm k ε v v ≠ 0) : IsFiveNondeg k ε (Submodule.span (ZMod 5) {v}) := by
  rw [isFiveNondeg_iff]
  intro x hx hxorth
  obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hx
  have h := hxorth v (Submodule.mem_span_singleton_self v)
  rw [fiveForm_smul_left] at h
  rw [(mul_eq_zero.mp h).resolve_right hv, zero_smul]

theorem finrank_inf_fiveOrth_add {k : ℕ} {ε : Bool}
    {W U : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} (hW : IsFiveNondeg k ε W) (hUW : U ≤ W) :
    Module.finrank (ZMod 5) ↥(W ⊓ fiveOrth k ε U) + Module.finrank (ZMod 5) U =
      Module.finrank (ZMod 5) W := by
  have hkey : Module.finrank (ZMod 5) ↥(W ⊓ fiveOrth k ε U) =
      Module.finrank (ZMod 5) ↥W - Module.finrank (ZMod 5) ↥U :=
    LinearMap.BilinForm.finrank_inf_orthogonal_of_restrict_nondegenerate
      (K := ZMod 5) (V := Fin (k + 1) → ZMod 5) (fiveBilin k ε true) hUW hW
  have hle : Module.finrank (ZMod 5) U ≤ Module.finrank (ZMod 5) W :=
    Submodule.finrank_mono hUW
  omega

theorem isFiveNondeg_inf_fiveOrth {k : ℕ} {ε : Bool}
    {W U : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} (hW : IsFiveNondeg k ε W)
    (hU : IsFiveNondeg k ε U) (hUW : U ≤ W) : IsFiveNondeg k ε (W ⊓ fiveOrth k ε U) := by
  rw [isFiveNondeg_iff]
  intro x hx hxorth
  have hxW : x ∈ W := hx.1
  have hxU : x ∈ fiveOrth k ε U := hx.2
  have hdisj : U ⊓ (W ⊓ fiveOrth k ε U) = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    exact isFiveNondeg_iff.1 hU u hu.1 fun y hy => (mem_fiveOrth.mp hu.2.2) y hy
  have hdim : Module.finrank (ZMod 5) ↥(U ⊔ (W ⊓ fiveOrth k ε U)) =
      Module.finrank (ZMod 5) W := by
    have h1 : Module.finrank (ZMod 5) ↥(U ⊔ (W ⊓ fiveOrth k ε U)) +
        Module.finrank (ZMod 5) ↥(U ⊓ (W ⊓ fiveOrth k ε U)) =
        Module.finrank (ZMod 5) ↥U + Module.finrank (ZMod 5) ↥(W ⊓ fiveOrth k ε U) := by
      exact Submodule.finrank_sup_add_finrank_inf_eq
        (K := ZMod 5) (V := Fin (k + 1) → ZMod 5) U (W ⊓ fiveOrth k ε U)
    have hbot : Module.finrank (ZMod 5) ↥(U ⊓ (W ⊓ fiveOrth k ε U)) = 0 := by
      have := congrArg (fun p : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5) =>
        Module.finrank (ZMod 5) ↥p) hdisj
      simpa using this
    have h2 : Module.finrank (ZMod 5) ↥(W ⊓ fiveOrth k ε U) + Module.finrank (ZMod 5) ↥U =
        Module.finrank (ZMod 5) ↥W := finrank_inf_fiveOrth_add hW hUW
    omega
  have hsup : U ⊔ (W ⊓ fiveOrth k ε U) = W :=
    Submodule.eq_of_le_of_finrank_eq
      (sup_le hUW (inf_le_left : W ⊓ fiveOrth k ε U ≤ W)) hdim
  apply isFiveNondeg_iff.1 hW x hxW
  intro w hw
  rw [← hsup] at hw
  rcases Submodule.mem_sup.mp hw with ⟨u, hu, v, hv, rfl⟩
  rw [fiveForm_add_right, (mem_fiveOrth.mp hxU) u hu, hxorth v hv, add_zero]

theorem exists_fiveForm_eq_of_nondeg {k : ℕ} {ε : Bool}
    {N : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} (hN : IsFiveNondeg k ε N)
    (h2 : 2 ≤ Module.finrank (ZMod 5) N) {c : ZMod 5} :
    ∃ x ∈ N, fiveForm k ε x x = c := by
  have h2' : 2 ≤ Module.finrank (ZMod 5) N := h2
  obtain ⟨v, hvN, hv⟩ := exists_fiveForm_ne_zero_of_finrank_pos hN (by omega)
  have hv0 : v ≠ 0 := by rintro rfl; exact hv (by simp [fiveForm])
  have hspan_le : Submodule.span (ZMod 5) {v} ≤ N :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvN)
  have hMnd : IsFiveNondeg k ε (N ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {v})) :=
    isFiveNondeg_inf_fiveOrth hN (isFiveNondeg_span_singleton hv) hspan_le
  have hMdim : 1 ≤ Module.finrank (ZMod 5)
      ↥(N ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {v})) := by
    have h := finrank_inf_fiveOrth_add hN hspan_le
    have h1 : Module.finrank (ZMod 5) (Submodule.span (ZMod 5) {v}) = 1 :=
      finrank_span_singleton hv0
    rw [h1] at h
    omega
  obtain ⟨w, hwM, hw⟩ := exists_fiveForm_ne_zero_of_finrank_pos hMnd hMdim
  have hwN : w ∈ N := hwM.1
  have hvw : fiveForm k ε v w = 0 := by
    have hwv : fiveForm k ε w v = 0 :=
      (mem_fiveOrth.mp hwM.2) v (Submodule.mem_span_singleton_self v)
    rwa [fiveForm_comm] at hwv
  obtain ⟨a, b, hab⟩ := five_sq_sum_covers (fiveForm k ε v v) (fiveForm k ε w w) hv hw c
  exact ⟨a • v + b • w, N.add_mem (N.smul_mem a hvN) (N.smul_mem b hwN), by
    rw [fiveForm_self_add_smul_smul, hvw, mul_zero, add_zero, hab]⟩

theorem exists_fiveForm_eq_zero_of_nondeg {k : ℕ} {ε : Bool}
    {N : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} (hN : IsFiveNondeg k ε N)
    (h3 : 3 ≤ Module.finrank (ZMod 5) N) : ∃ x ∈ N, x ≠ 0 ∧ fiveForm k ε x x = 0 := by
  have h3' : 3 ≤ Module.finrank (ZMod 5) N := h3
  obtain ⟨v, hvN, hv⟩ := exists_fiveForm_ne_zero_of_finrank_pos hN (by omega)
  have hv0 : v ≠ 0 := by rintro rfl; exact hv (by simp [fiveForm])
  have hspan_le : Submodule.span (ZMod 5) {v} ≤ N :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvN)
  have hMnd : IsFiveNondeg k ε (N ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {v})) :=
    isFiveNondeg_inf_fiveOrth hN (isFiveNondeg_span_singleton hv) hspan_le
  have hMdim : 2 ≤ Module.finrank (ZMod 5)
      ↥(N ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {v})) := by
    have h := finrank_inf_fiveOrth_add hN hspan_le
    have h1 : Module.finrank (ZMod 5) (Submodule.span (ZMod 5) {v}) = 1 :=
      finrank_span_singleton hv0
    rw [h1] at h
    omega
  obtain ⟨w, hwM, hw⟩ := exists_fiveForm_eq_of_nondeg hMnd hMdim
    (c := -fiveForm k ε v v)
  have hwN : w ∈ N := hwM.1
  have hvw : fiveForm k ε v w = 0 := by
    have hwv : fiveForm k ε w v = 0 :=
      (mem_fiveOrth.mp hwM.2) v (Submodule.mem_span_singleton_self v)
    rwa [fiveForm_comm] at hwv
  refine ⟨v + w, N.add_mem hvN hwN, ?_, ?_⟩
  · intro h0
    have hw_eq : w = -v := by
      funext i
      have hi : v i + w i = 0 := by simpa using congrFun h0 i
      exact eq_neg_of_add_eq_zero_right hi
    have hvw' : fiveForm k ε v (-v) = 0 := by rw [hw_eq] at hvw; exact hvw
    have hneg := fiveForm_neg_right k ε v v
    have h2 : -fiveForm k ε v v = 0 := hneg ▸ hvw'
    exact hv (neg_eq_zero.mp h2)
  · rw [fiveForm_self_add, hvw, hw, mul_zero, add_zero]
    exact add_neg_cancel _

theorem commute_fiveReflOf_iff (n : ℕ) (ε : Bool) {v w : Fin (n + 1) → ZMod 5}
    (hv : fiveForm n ε v v ≠ 0) (hw : fiveForm n ε w w ≠ 0) :
    Commute (fiveReflOf n ε v) (fiveReflOf n ε w) ↔
      fiveForm n ε v w = 0 ∨ ∃ μ : ZMod 5, w = μ • v := by
  constructor
  · intro hcomm
    by_cases h_eq : fiveReflOf n ε v = fiveReflOf n ε w
    · right
      exact exists_smul_eq_of_fiveReflOf_eq hv h_eq
    · left
      exact fiveForm_eq_zero_of_commute_fiveReflOf hv hw hcomm.eq h_eq
  · rintro (h | ⟨μ, rfl⟩)
    · exact fiveReflOf_commute_of_orthogonal (π := decide (IsSquare (fiveForm n ε v v))) hv
        (by simp [decide_eq_true_eq]) h
    · by_cases hμ : μ = 0
      · exfalso
        exact hw (by simp [hμ, fiveForm])
      · rw [fiveReflOf_smul n ε v hμ]

theorem neg_notMem_fiveReflections {n : ℕ} (hn : 2 ≤ n) (ε π : Bool)
    {r : GL (Fin (n + 1)) (ZMod 5)} (hr : r ∈ fiveReflections n ε π) :
    -r ∉ fiveReflections n ε π := by
  intro hnr
  obtain ⟨v, hv, -, rfl⟩ := exists_eq_fiveReflOf hr
  obtain ⟨w, hw, -, h_eq⟩ := exists_eq_fiveReflOf hnr
  have h2 : ∀ x, (2 : ZMod 5) • x =
      (2 * fiveForm n ε x v * (fiveForm n ε v v)⁻¹) • v +
        (2 * fiveForm n ε x w * (fiveForm n ε w w)⁻¹) • w := by
    intro x
    have h := congrArg (fun g : GL (Fin (n + 1)) (ZMod 5) =>
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ x) h_eq
    simp only [Units.val_neg, Matrix.neg_mulVec, fiveReflOf_mulVec] at h
    linear_combination (norm := module) -h
  have htop : (⊤ : Submodule (ZMod 5) (Fin (n + 1) → ZMod 5)) ≤
      Submodule.span (ZMod 5) ({v, w} : Set (Fin (n + 1) → ZMod 5)) := by
    intro x _
    rw [Submodule.mem_span_pair]
    refine ⟨(2 : ZMod 5)⁻¹ * (2 * fiveForm n ε x v * (fiveForm n ε v v)⁻¹),
      (2 : ZMod 5)⁻¹ * (2 * fiveForm n ε x w * (fiveForm n ε w w)⁻¹), ?_⟩
    calc ((2 : ZMod 5)⁻¹ * (2 * fiveForm n ε x v * (fiveForm n ε v v)⁻¹)) • v +
          ((2 : ZMod 5)⁻¹ * (2 * fiveForm n ε x w * (fiveForm n ε w w)⁻¹)) • w
        = (2 : ZMod 5)⁻¹ • ((2 * fiveForm n ε x v * (fiveForm n ε v v)⁻¹) • v +
            (2 * fiveForm n ε x w * (fiveForm n ε w w)⁻¹) • w) := by module
      _ = (2 : ZMod 5)⁻¹ • ((2 : ZMod 5) • x) := by rw [← h2 x]
      _ = x := by rw [smul_smul, inv_mul_cancel₀ (by decide : (2 : ZMod 5) ≠ 0), one_smul]
  have hspan : Submodule.span (ZMod 5) ({v, w} : Set (Fin (n + 1) → ZMod 5)) = ⊤ :=
    le_antisymm le_top htop
  have hfin : Module.finrank (ZMod 5) (⊤ : Submodule (ZMod 5) (Fin (n + 1) → ZMod 5)) ≤ 2 := by
    rw [← hspan]
    calc Module.finrank (ZMod 5) (Submodule.span (ZMod 5) ({v, w} : Set (Fin (n + 1) → ZMod 5)))
        ≤ ({v, w} : Set (Fin (n + 1) → ZMod 5)).toFinset.card := finrank_span_le_card _
      _ ≤ 2 := by
        rw [Set.toFinset_insert, Set.toFinset_singleton]
        exact Finset.card_insert_le _ _
  rw [finrank_top, Module.finrank_fin_fun] at hfin
  omega

theorem commute_mk_iff_commute {n : ℕ} (hn : 4 ≤ n) (ε π : Bool)
    {r s : fiveReflectionGroup n ε π}
    (hs : (s : GL (Fin (n + 1)) (ZMod 5)) ∈ fiveReflections n ε π) :
    Commute (QuotientGroup.mk r : fiveProjective n ε π) (QuotientGroup.mk s) ↔ Commute r s := by
  constructor
  · intro hcomm
    have hmem : r * s * r⁻¹ * s⁻¹ ∈ Subgroup.center (fiveReflectionGroup n ε π) := by
      rw [← QuotientGroup.eq_one_iff]
      have h := hcomm.eq
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv, h]
      group
    rcases (mem_center_fiveReflectionGroup_iff hn ε π _).mp hmem with h1 | hneg
    · rw [commute_iff_eq]
      apply Subtype.ext
      have h1' : (r : GL (Fin (n + 1)) (ZMod 5)) * (s : GL (Fin (n + 1)) (ZMod 5)) *
          (r : GL (Fin (n + 1)) (ZMod 5))⁻¹ * (s : GL (Fin (n + 1)) (ZMod 5))⁻¹ = 1 := by
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] using h1
      have h2 : (r : GL (Fin (n + 1)) (ZMod 5)) * (s : GL (Fin (n + 1)) (ZMod 5)) =
          (s : GL (Fin (n + 1)) (ZMod 5)) * (r : GL (Fin (n + 1)) (ZMod 5)) := by
        have h := congrArg (fun x => x * (s : GL (Fin (n + 1)) (ZMod 5))) h1'
        have h' : (r : GL (Fin (n + 1)) (ZMod 5)) * (s : GL (Fin (n + 1)) (ZMod 5)) *
            (r : GL (Fin (n + 1)) (ZMod 5))⁻¹ = (s : GL (Fin (n + 1)) (ZMod 5)) := by
          simpa [mul_assoc] using h
        have h'' := congrArg (fun x => x * (r : GL (Fin (n + 1)) (ZMod 5))) h'
        simpa [mul_assoc] using h''
      simpa only [Subgroup.coe_mul] using h2
    · exfalso
      have hconj : (r : GL (Fin (n + 1)) (ZMod 5)) * (s : GL (Fin (n + 1)) (ZMod 5)) *
          (r : GL (Fin (n + 1)) (ZMod 5))⁻¹ ∈ fiveReflections n ε π :=
        conj_mem_fiveReflections (fiveForm_mulVec_of_mem r.2) hs
      have hneg_eq : (r : GL (Fin (n + 1)) (ZMod 5)) * (s : GL (Fin (n + 1)) (ZMod 5)) *
          (r : GL (Fin (n + 1)) (ZMod 5))⁻¹ = -(s : GL (Fin (n + 1)) (ZMod 5)) := by
        have h := congrArg (fun x => x * (s : GL (Fin (n + 1)) (ZMod 5))) hneg
        simpa [mul_assoc] using h
      exact neg_notMem_fiveReflections (by omega : 2 ≤ n) ε π hs (hneg_eq ▸ hconj)
  · intro hcomm
    rw [commute_iff_eq]
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm.eq]

theorem orderOf_fiveReflOf_mul (n : ℕ) (ε π : Bool) {v w : Fin (n + 1) → ZMod 5}
    (hv : fiveForm n ε v v ≠ 0) (hvπ : IsSquare (fiveForm n ε v v) ↔ π = true)
    (hw : fiveForm n ε w w ≠ 0) (hwπ : IsSquare (fiveForm n ε w w) ↔ π = true)
    (hvw : ∀ μ : ZMod 5, w ≠ μ • v) :
    orderOf (fiveReflOf n ε v * fiveReflOf n ε w) =
      if fiveForm n ε v w = 0 then 2
      else if fiveForm n ε v w ^ 2 = fiveForm n ε v v * fiveForm n ε w w then 5 else 3 := by
  have hsal : fiveSignRep π ≠ 0 := fiveSignRep_ne_zero π
  obtain ⟨μ, hμ⟩ := exists_sq_mul_eq_fiveSignRep hv hvπ
  obtain ⟨ν, hν⟩ := exists_sq_mul_eq_fiveSignRep hw hwπ
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    simp only [pow_two, zero_mul] at hμ
    exact hsal hμ.symm
  have hν0 : ν ≠ 0 := by
    rintro rfl
    simp only [pow_two, zero_mul] at hν
    exact hsal hν.symm
  have hbμ : fiveBilin n ε π (μ • v) (μ • v) = 1 := by
    rw [fiveBilin_apply, fiveForm_smul_left, fiveForm_smul_right]
    have h : μ * (μ * fiveForm n ε v v) = fiveSignRep π := by
      calc μ * (μ * fiveForm n ε v v) = μ ^ 2 * fiveForm n ε v v := by ring
        _ = fiveSignRep π := hμ
    rw [h, inv_mul_cancel₀ hsal]
  have hbν : fiveBilin n ε π (ν • w) (ν • w) = 1 := by
    rw [fiveBilin_apply, fiveForm_smul_left, fiveForm_smul_right]
    have h : ν * (ν * fiveForm n ε w w) = fiveSignRep π := by
      calc ν * (ν * fiveForm n ε w w) = ν ^ 2 * fiveForm n ε w w := by ring
        _ = fiveSignRep π := hν
    rw [h, inv_mul_cancel₀ hsal]
  have hrv : fiveReflOf n ε v = refl (fiveBilin n ε π) (μ • v) := by
    rw [refl_fiveBilin_eq_fiveReflOf n ε π hbμ, fiveReflOf_smul n ε v hμ0]
  have hrw : fiveReflOf n ε w = refl (fiveBilin n ε π) (ν • w) := by
    rw [refl_fiveBilin_eq_fiveReflOf n ε π hbν, fiveReflOf_smul n ε w hν0]
  have hne_smul : ∀ c d : ZMod 5, c ≠ 0 → c • w ≠ d • v := by
    intro c d hc h
    apply hvw (c⁻¹ * d)
    calc w = c⁻¹ • (c • w) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ = c⁻¹ • (d • v) := by rw [h]
      _ = (c⁻¹ * d) • v := smul_smul _ _ _
  have hne1 : ν • w ≠ μ • v := hne_smul ν μ hν0
  have hne2 : ν • w ≠ -(μ • v) := by
    simpa only [neg_smul] using hne_smul ν (-μ) hν0
  have hrne : refl (fiveBilin n ε π) (μ • v) ≠ refl (fiveBilin n ε π) (ν • w) := by
    intro h
    rcases (refl_eq_refl_iff hbμ hbν).mp h with h' | h'
    · exact hne1 h'
    · exact hne2 h'
  by_cases hB0 : fiveForm n ε v w = 0
  · rw [if_pos hB0]
    have hb0 : fiveBilin n ε π (μ • v) (ν • w) = 0 := by
      rw [fiveBilin_apply, fiveForm_smul_left, fiveForm_smul_right]
      simp [hB0]
    have hcomm : Commute (refl (fiveBilin n ε π) (μ • v))
        (refl (fiveBilin n ε π) (ν • w)) :=
      (FiveChartModel.refl_commute_iff_of_ne (fiveBilin_comm n ε π) hbμ hbν hne1 hne2).mpr hb0
    have hne : refl (fiveBilin n ε π) (μ • v) * refl (fiveBilin n ε π) (ν • w) ≠ 1 := by
      intro h
      apply hrne
      have h2 := congrArg (fun z => z * refl (fiveBilin n ε π) (ν • w)) h
      simpa [mul_assoc] using h2
    have hsq : (refl (fiveBilin n ε π) (μ • v) *
        refl (fiveBilin n ε π) (ν • w)) ^ 2 = 1 := by
      rw [pow_two]
      calc (refl (fiveBilin n ε π) (μ • v) * refl (fiveBilin n ε π) (ν • w)) *
            (refl (fiveBilin n ε π) (μ • v) * refl (fiveBilin n ε π) (ν • w))
          = refl (fiveBilin n ε π) (μ • v) * (refl (fiveBilin n ε π) (ν • w) *
              refl (fiveBilin n ε π) (μ • v)) * refl (fiveBilin n ε π) (ν • w) := by group
        _ = refl (fiveBilin n ε π) (μ • v) * (refl (fiveBilin n ε π) (μ • v) *
              refl (fiveBilin n ε π) (ν • w)) * refl (fiveBilin n ε π) (ν • w) := by
              rw [hcomm.eq]
        _ = (refl (fiveBilin n ε π) (μ • v) * refl (fiveBilin n ε π) (μ • v)) *
              (refl (fiveBilin n ε π) (ν • w) * refl (fiveBilin n ε π) (ν • w)) := by group
        _ = 1 := by rw [refl_mul_self, refl_mul_self, one_mul]
    rw [hrv, hrw]
    exact orderOf_eq_prime hsq hne
  · rw [if_neg hB0]
    have hb0 : fiveBilin n ε π (μ • v) (ν • w) ≠ 0 := by
      rw [fiveBilin_apply, fiveForm_smul_left, fiveForm_smul_right]
      exact mul_ne_zero (inv_ne_zero hsal) (mul_ne_zero hμ0 (mul_ne_zero hν0 hB0))
    have hord := FiveChartModel.refl_mul_refl_order (fiveBilin_comm n ε π) hbμ hbν
      hne1 hne2 hb0
    have hiff : (fiveBilin n ε π (μ • v) (ν • w)) ^ 2 = 1 ↔
        fiveForm n ε v w ^ 2 = fiveForm n ε v v * fiveForm n ε w w := by
      have hsq := fiveBilin_smul_smul_sq n ε π hμ hν
      constructor
      · intro h
        rw [← hsq, h, one_mul]
      · intro h
        rw [← hsq] at h
        exact mul_right_cancel₀ (mul_ne_zero hv hw) (by simpa using h)
    rw [hrv, hrw, hord]
    by_cases hB2 : fiveForm n ε v w ^ 2 = fiveForm n ε v v * fiveForm n ε w w
    · rw [if_pos hB2, if_pos (hiff.mpr hB2)]
    · rw [if_neg hB2, if_neg (fun h => hB2 (hiff.mp h))]

theorem span_fiveForm_eq_of_nondeg {k : ℕ} {ε : Bool}
    {N : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} (hN : IsFiveNondeg k ε N)
    (h2 : 2 ≤ Module.finrank (ZMod 5) N) {c : ZMod 5} (hc : c ≠ 0) :
    Submodule.span (ZMod 5) {x | x ∈ N ∧ fiveForm k ε x x = c} = N := by
  have h2' : 2 ≤ Module.finrank (ZMod 5) N := h2
  refine le_antisymm (Submodule.span_le.mpr (fun x hx => hx.1)) ?_
  intro m hm
  by_cases hm0 : m = 0
  · rw [hm0]; exact Submodule.zero_mem _
  by_cases hQm : fiveForm k ε m m = 0
  · obtain ⟨z, hzN, hzm⟩ : ∃ z ∈ N, fiveForm k ε m z ≠ 0 := by
      by_contra h
      push Not at h
      exact hm0 (isFiveNondeg_iff.1 hN m hm h)
    set t : ZMod 5 := -(fiveForm k ε z z) / (2 * fiveForm k ε m z) with ht
    set z' : Fin (k + 1) → ZMod 5 := z + t • m with hz'
    have hz'N : z' ∈ N := N.add_mem hzN (N.smul_mem t hm)
    have hQmz : fiveForm k ε m z' = fiveForm k ε m z := by
      rw [hz', fiveForm_add_right, fiveForm_smul_right, hQm, mul_zero, add_zero]
    have hQz' : fiveForm k ε z' z' = 0 := by
      rw [hz', fiveForm_self_add, fiveForm_smul_smul, hQm, mul_zero, fiveForm_smul_right, ht,
        fiveForm_comm k ε z m]
      have h2B : (2 : ZMod 5) * fiveForm k ε m z ≠ 0 := mul_ne_zero (by decide) hzm
      have h2ne : (2 : ZMod 5) ≠ 0 := by decide
      field_simp [h2B, h2ne]
      ring
    have hzm' : fiveForm k ε m z' ≠ 0 := by rw [hQmz]; exact hzm
    obtain ⟨r, s, a, b, a', b', hab, hab', hr1, hr2⟩ :=
      five_hyp_plane_coeffs (c * (2 * fiveForm k ε m z')⁻¹)
    set v1 : Fin (k + 1) → ZMod 5 := a • m + b • z' with hv1
    set v2 : Fin (k + 1) → ZMod 5 := a' • m + b' • z' with hv2
    have hv1S : v1 ∈ Submodule.span (ZMod 5) {u | u ∈ N ∧ fiveForm k ε u u = c} := by
      refine Submodule.subset_span ⟨N.add_mem (N.smul_mem a hm) (N.smul_mem b hz'N), ?_⟩
      rw [hv1]
      calc fiveForm k ε (a • m + b • z') (a • m + b • z')
          = 2 * a * b * fiveForm k ε m z' :=
            fiveForm_self_add_smul_smul_singular k ε m z' a b hQm hQz'
        _ = c := by
            calc 2 * a * b * fiveForm k ε m z'
                = 2 * (a * b) * fiveForm k ε m z' := by ring
              _ = 2 * (c * (2 * fiveForm k ε m z')⁻¹) * fiveForm k ε m z' := by rw [hab]
              _ = c := by
                have h2B' : (2 : ZMod 5) * fiveForm k ε m z' ≠ 0 :=
                  mul_ne_zero (by decide) hzm'
                rw [show 2 * (c * (2 * fiveForm k ε m z')⁻¹) * fiveForm k ε m z' =
                    c * ((2 * fiveForm k ε m z')⁻¹ * (2 * fiveForm k ε m z')) by ring]
                rw [inv_mul_cancel₀ h2B', mul_one]
    have hv2S : v2 ∈ Submodule.span (ZMod 5) {u | u ∈ N ∧ fiveForm k ε u u = c} := by
      refine Submodule.subset_span ⟨N.add_mem (N.smul_mem a' hm) (N.smul_mem b' hz'N), ?_⟩
      rw [hv2]
      calc fiveForm k ε (a' • m + b' • z') (a' • m + b' • z')
          = 2 * a' * b' * fiveForm k ε m z' :=
            fiveForm_self_add_smul_smul_singular k ε m z' a' b' hQm hQz'
        _ = c := by
            calc 2 * a' * b' * fiveForm k ε m z'
                = 2 * (a' * b') * fiveForm k ε m z' := by ring
              _ = 2 * (c * (2 * fiveForm k ε m z')⁻¹) * fiveForm k ε m z' := by rw [hab']
              _ = c := by
                have h2B' : (2 : ZMod 5) * fiveForm k ε m z' ≠ 0 :=
                  mul_ne_zero (by decide) hzm'
                rw [show 2 * (c * (2 * fiveForm k ε m z')⁻¹) * fiveForm k ε m z' =
                    c * ((2 * fiveForm k ε m z')⁻¹ * (2 * fiveForm k ε m z')) by ring]
                rw [inv_mul_cancel₀ h2B', mul_one]
    have hmv : m = r • v1 + s • v2 := by
      calc m = (1 : ZMod 5) • m + (0 : ZMod 5) • z' := by simp
        _ = (r * a + s * a') • m + (r * b + s * b') • z' := by rw [hr1, hr2]
        _ = r • v1 + s • v2 := by rw [hv1, hv2]; module
    rw [hmv]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hv1S) (Submodule.smul_mem _ _ hv2S)
  · have hm_ne : m ≠ 0 := by
      intro h0; rw [h0] at hQm; exact hQm (by simp [fiveForm])
    have hspan_le : Submodule.span (ZMod 5) {m} ≤ N :=
      Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hm)
    have hMnd : IsFiveNondeg k ε (N ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {m})) :=
      isFiveNondeg_inf_fiveOrth hN (isFiveNondeg_span_singleton hQm) hspan_le
    have hMdim : 1 ≤ Module.finrank (ZMod 5)
        ↥(N ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {m})) := by
      have h := finrank_inf_fiveOrth_add hN hspan_le
      have h1 : Module.finrank (ZMod 5) (Submodule.span (ZMod 5) {m}) = 1 :=
        finrank_span_singleton hm_ne
      rw [h1] at h
      omega
    obtain ⟨w, hwM, hw⟩ := exists_fiveForm_ne_zero_of_finrank_pos hMnd hMdim
    have hwN : w ∈ N := hwM.1
    have hmw : fiveForm k ε m w = 0 := by
      have hwm : fiveForm k ε w m = 0 :=
        (mem_fiveOrth.mp hwM.2) m (Submodule.mem_span_singleton_self m)
      rwa [fiveForm_comm] at hwm
    obtain ⟨r, s, a, b, a', b', hab, hab', hr1, hr2⟩ :=
      five_diag_plane_coeffs (fiveForm k ε m m) (fiveForm k ε w w) c hQm hw hc
    set v1 : Fin (k + 1) → ZMod 5 := a • m + b • w with hv1
    set v2 : Fin (k + 1) → ZMod 5 := a' • m + b' • w with hv2
    have hv1S : v1 ∈ Submodule.span (ZMod 5) {u | u ∈ N ∧ fiveForm k ε u u = c} := by
      refine Submodule.subset_span ⟨N.add_mem (N.smul_mem a hm) (N.smul_mem b hwN), ?_⟩
      rw [hv1]
      calc fiveForm k ε (a • m + b • w) (a • m + b • w)
          = a ^ 2 * fiveForm k ε m m + b ^ 2 * fiveForm k ε w w := by
            rw [fiveForm_self_add_smul_smul, hmw]; ring
        _ = c := hab
    have hv2S : v2 ∈ Submodule.span (ZMod 5) {u | u ∈ N ∧ fiveForm k ε u u = c} := by
      refine Submodule.subset_span ⟨N.add_mem (N.smul_mem a' hm) (N.smul_mem b' hwN), ?_⟩
      rw [hv2]
      calc fiveForm k ε (a' • m + b' • w) (a' • m + b' • w)
          = a' ^ 2 * fiveForm k ε m m + b' ^ 2 * fiveForm k ε w w := by
            rw [fiveForm_self_add_smul_smul, hmw]; ring
        _ = c := hab'
    have hmv : m = r • v1 + s • v2 := by
      calc m = (1 : ZMod 5) • m + (0 : ZMod 5) • w := by simp
        _ = (r * a + s * a') • m + (r * b + s * b') • w := by rw [hr1, hr2]
        _ = r • v1 + s • v2 := by rw [hv1, hv2]; module
    rw [hmv]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hv1S) (Submodule.smul_mem _ _ hv2S)

theorem fiveReflOf_sub_apply_of_form_eq {k : ℕ} {ε : Bool} {x y : Fin (k + 1) → ZMod 5}
    (hxy : fiveForm k ε x x = fiveForm k ε y y)
    (hne : fiveForm k ε (x - y) (x - y) ≠ 0) :
    (fiveReflOf k ε (x - y) : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x = y := by
  rw [fiveReflOf_mulVec]
  have hQ : fiveForm k ε (x - y) (x - y) =
      2 * (fiveForm k ε x x - fiveForm k ε x y) := by
    rw [fiveForm_sub_sub, hxy]; ring
  have hB : fiveForm k ε x (x - y) = fiveForm k ε x x - fiveForm k ε x y :=
    fiveForm_sub_right k ε x x y
  have hD : fiveForm k ε x x - fiveForm k ε x y ≠ 0 := by
    intro h
    exact hne (by rw [hQ, h, mul_zero])
  have hcoef : 2 * fiveForm k ε x (x - y) * (fiveForm k ε (x - y) (x - y))⁻¹ = 1 := by
    rw [hB, hQ]
    exact mul_inv_cancel₀ (mul_ne_zero (by decide : (2 : ZMod 5) ≠ 0) hD)
  rw [hcoef, one_smul]
  abel

theorem fiveReflOf_add_apply_of_form_eq {k : ℕ} {ε : Bool} {x y : Fin (k + 1) → ZMod 5}
    (hxy : fiveForm k ε x x = fiveForm k ε y y)
    (hne : fiveForm k ε (x + y) (x + y) ≠ 0) :
    (fiveReflOf k ε (x + y) : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x = -y := by
  rw [fiveReflOf_mulVec]
  have hQ : fiveForm k ε (x + y) (x + y) =
      2 * (fiveForm k ε x x + fiveForm k ε x y) := by
    rw [fiveForm_add_add, hxy]; ring
  have hB : fiveForm k ε x (x + y) = fiveForm k ε x x + fiveForm k ε x y :=
    fiveForm_add_right k ε x x y
  have hD : fiveForm k ε x x + fiveForm k ε x y ≠ 0 := by
    intro h
    exact hne (by rw [hQ, h, mul_zero])
  have hcoef : 2 * fiveForm k ε x (x + y) * (fiveForm k ε (x + y) (x + y))⁻¹ = 1 := by
    rw [hB, hQ]
    exact mul_inv_cancel₀ (mul_ne_zero (by decide : (2 : ZMod 5) ≠ 0) hD)
  rw [hcoef, one_smul]
  abel

theorem fiveReflOf_mem_fiveReflectionsIn {k : ℕ} {ε π : Bool}
    {W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} {v : Fin (k + 1) → ZMod 5}
    (hvW : v ∈ W) (hv : fiveForm k ε v v ≠ 0) (hπ : IsSquare (fiveForm k ε v v) ↔ π = true) :
    fiveReflOf k ε v ∈ fiveReflectionsIn k ε π W :=
  ⟨v, hvW, hv, hπ, fun x => fiveReflOf_mulVec k ε v x⟩

private theorem five_exists_orth_pair_sign (c b : ZMod 5) (hc : c ≠ 0) (h1 : b ≠ c) (h2 : b ≠ -c)
    (π : Bool) (hπ : IsSquare c ↔ (!π) = true) :
    (2 * c - 2 * b ≠ 0 ∧ (IsSquare (2 * c - 2 * b) ↔ π = true)) ∨
      (2 * c + 2 * b ≠ 0 ∧ (IsSquare (2 * c + 2 * b) ↔ π = true)) := by
  revert c b π
  decide

theorem fiveReflOf_mul_mem_fiveReflectionGroupIn_of_conj {k : ℕ} {ε π : Bool}
    {W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)}
    {x u z : Fin (k + 1) → ZMod 5} (hxW : x ∈ W) (huW : u ∈ W)
    (hx : fiveForm k ε x x ≠ 0) (hxπ : IsSquare (fiveForm k ε x x) ↔ (!π) = true)
    (hu : fiveForm k ε u u ≠ 0) (huπ : IsSquare (fiveForm k ε u u) ↔ π = true)
    (hux : (fiveReflOf k ε u : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x = z ∨
      (fiveReflOf k ε u : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x = -z) :
    fiveReflOf k ε x * fiveReflOf k ε z ∈ fiveReflectionGroupIn k ε π W := by
  have hgx : ∀ a b, fiveForm k ε ((fiveReflOf k ε x : Matrix (Fin (k + 1)) (Fin (k + 1))
      (ZMod 5)) *ᵥ a) ((fiveReflOf k ε x : Matrix _ _ _) *ᵥ b) = fiveForm k ε a b :=
    fun a b => fiveForm_mulVec_of_mem
      (Subgroup.subset_closure (fiveReflOf_mem hx hxπ)) a b
  have hgu : ∀ a b, fiveForm k ε ((fiveReflOf k ε u : Matrix (Fin (k + 1)) (Fin (k + 1))
      (ZMod 5)) *ᵥ a) ((fiveReflOf k ε u : Matrix _ _ _) *ᵥ b) = fiveForm k ε a b :=
    fun a b => fiveForm_mulVec_of_mem
      (Subgroup.subset_closure (fiveReflOf_mem hu huπ)) a b
  have hmem_u : fiveReflOf k ε u ∈ fiveReflectionGroupIn k ε π W :=
    Subgroup.subset_closure (fiveReflOf_mem_fiveReflectionsIn huW hu huπ)
  have hrxuW : (fiveReflOf k ε x : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ u ∈ W := by
    rw [fiveReflOf_mulVec]
    exact W.sub_mem huW (W.smul_mem _ hxW)
  have hrxuQ : fiveForm k ε ((fiveReflOf k ε x : Matrix _ _ _) *ᵥ u)
      ((fiveReflOf k ε x : Matrix _ _ _) *ᵥ u) = fiveForm k ε u u := hgx u u
  have hmem_rxu : fiveReflOf k ε ((fiveReflOf k ε x : Matrix _ _ _) *ᵥ u) ∈
      fiveReflectionGroupIn k ε π W :=
    Subgroup.subset_closure (fiveReflOf_mem_fiveReflectionsIn hrxuW
      (by rw [hrxuQ]; exact hu) (by rw [hrxuQ]; exact huπ))
  have hz_eq : fiveReflOf k ε z =
      fiveReflOf k ε u * fiveReflOf k ε x * (fiveReflOf k ε u)⁻¹ := by
    rcases hux with h | h
    · rw [← h]
      exact (conj_fiveReflOf hgu x).symm
    · have hz : z = -((fiveReflOf k ε u : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x) := by
        rw [h]
        exact (neg_neg z).symm
      have hneg : -((fiveReflOf k ε u : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x) =
          (-1 : ZMod 5) • ((fiveReflOf k ε u : Matrix (Fin (k + 1)) (Fin (k + 1))
            (ZMod 5)) *ᵥ x) := by
        funext j
        simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
        exact (neg_one_mul _).symm
      rw [hz, hneg, fiveReflOf_smul k ε _ (by decide : (-1 : ZMod 5) ≠ 0)]
      exact (conj_fiveReflOf hgu x).symm
  have hrxu_eq : fiveReflOf k ε ((fiveReflOf k ε x : Matrix _ _ _) *ᵥ u) =
      fiveReflOf k ε x * fiveReflOf k ε u * (fiveReflOf k ε x)⁻¹ :=
    (conj_fiveReflOf hgx u).symm
  have hprod : fiveReflOf k ε x * fiveReflOf k ε z =
      fiveReflOf k ε ((fiveReflOf k ε x : Matrix _ _ _) *ᵥ u) * fiveReflOf k ε u := by
    rw [hz_eq, hrxu_eq,
      show (fiveReflOf k ε x)⁻¹ = fiveReflOf k ε x from Units.ext rfl,
      show (fiveReflOf k ε u)⁻¹ = fiveReflOf k ε u from Units.ext rfl]
    group
  rw [hprod]
  exact mul_mem hmem_rxu hmem_u

theorem fiveReflOf_mul_mem_fiveReflectionGroupIn_of_b_ne {k : ℕ} {ε π : Bool}
    {W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)}
    {x z : Fin (k + 1) → ZMod 5} (hxW : x ∈ W) (hzW : z ∈ W)
    (hx : fiveForm k ε x x ≠ 0) (hxπ : IsSquare (fiveForm k ε x x) ↔ (!π) = true)
    (hz : fiveForm k ε z z = fiveForm k ε x x)
    (h1 : fiveForm k ε x z ≠ fiveForm k ε x x)
    (h2 : fiveForm k ε x z ≠ -fiveForm k ε x x) :
    fiveReflOf k ε x * fiveReflOf k ε z ∈ fiveReflectionGroupIn k ε π W := by
  rcases five_exists_orth_pair_sign (fiveForm k ε x x) (fiveForm k ε x z) hx h1 h2 π hxπ with
    ⟨hne, hsign⟩ | ⟨hne, hsign⟩
  ·
    have hQ : fiveForm k ε (x - z) (x - z) = 2 * fiveForm k ε x x - 2 * fiveForm k ε x z := by
      rw [fiveForm_sub_sub, hz]; ring
    have hne' : fiveForm k ε (x - z) (x - z) ≠ 0 := by rw [hQ]; exact hne
    have hsign' : IsSquare (fiveForm k ε (x - z) (x - z)) ↔ π = true := by
      rw [hQ]; exact hsign
    have hru : (fiveReflOf k ε (x - z) : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x = z :=
      fiveReflOf_sub_apply_of_form_eq hz.symm hne'
    exact fiveReflOf_mul_mem_fiveReflectionGroupIn_of_conj hxW (W.sub_mem hxW hzW)
      hx hxπ hne' hsign' (Or.inl hru)
  ·
    have hQ : fiveForm k ε (x + z) (x + z) = 2 * fiveForm k ε x x + 2 * fiveForm k ε x z := by
      rw [fiveForm_add_add, hz]; ring
    have hne' : fiveForm k ε (x + z) (x + z) ≠ 0 := by rw [hQ]; exact hne
    have hsign' : IsSquare (fiveForm k ε (x + z) (x + z)) ↔ π = true := by
      rw [hQ]; exact hsign
    have hru : (fiveReflOf k ε (x + z) : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x = -z :=
      fiveReflOf_add_apply_of_form_eq hz.symm hne'
    exact fiveReflOf_mul_mem_fiveReflectionGroupIn_of_conj hxW (W.add_mem hxW hzW)
      hx hxπ hne' hsign' (Or.inr hru)

theorem exists_fiveForm_hyperbolic_partner {k : ℕ} {ε : Bool}
    {N : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} (hN : IsFiveNondeg k ε N)
    {s : Fin (k + 1) → ZMod 5} (hsN : s ∈ N) (hs : fiveForm k ε s s = 0) (hs0 : s ≠ 0) :
    ∃ s' ∈ N, fiveForm k ε s s' = 1 ∧ fiveForm k ε s' s' = 0 := by
  have hw : ∃ w ∈ N, fiveForm k ε s w ≠ 0 := by
    by_contra h
    push Not at h
    exact hs0 (isFiveNondeg_iff.1 hN s hsN fun y hy => h y hy)
  obtain ⟨w, hwN, hsw⟩ := hw
  let u : Fin (k + 1) → ZMod 5 := (fiveForm k ε s w)⁻¹ • w
  let a : ZMod 5 := fiveForm k ε u u / 2
  have huN : u ∈ N := N.smul_mem _ hwN
  have hBu : fiveForm k ε u s = 1 := by
    dsimp only [u]
    rw [fiveForm_smul_left, fiveForm_comm k ε w s]
    field_simp
  have hBus : fiveForm k ε u s = 1 := hBu
  refine ⟨u - a • s, N.sub_mem huN (N.smul_mem _ hsN), ?_, ?_⟩
  · rw [fiveForm_sub_right, fiveForm_smul_right, fiveForm_smul_right, hs, mul_zero,
      inv_mul_cancel₀ hsw]
    ring
  · have h1 : fiveForm k ε (a • s) (a • s) = 0 := by
      rw [fiveForm_smul_left, fiveForm_smul_right, hs, mul_zero, mul_zero]
    have h2 : fiveForm k ε u (a • s) = a := by
      rw [fiveForm_smul_right, hBus, mul_one]
    have h2a : 2 * a = fiveForm k ε u u := by
      dsimp only [a]
      rw [div_eq_mul_inv, ← mul_assoc, mul_comm (2 : ZMod 5) (fiveForm k ε u u), mul_assoc,
        mul_inv_cancel₀ (by decide : (2 : ZMod 5) ≠ 0), mul_one]
    rw [fiveForm_sub_sub, h1, h2, h2a]
    ring

private theorem exists_five_ne_zero_ne {c : ZMod 5} (hc : c ≠ 0) :
    ∃ b : ZMod 5, b ≠ 0 ∧ b ≠ c ∧ b ≠ -c := by
  revert c
  decide

theorem fiveReflOf_mul_mem_fiveReflectionGroupIn_of_b_eq {k : ℕ} {ε π : Bool}
    {W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} (hW : IsFiveNondeg k ε W)
    {x y : Fin (k + 1) → ZMod 5} (hxW : x ∈ W) (hyW : y ∈ W)
    (hx : fiveForm k ε x x ≠ 0) (hxπ : IsSquare (fiveForm k ε x x) ↔ (!π) = true)
    (hy : fiveForm k ε y y = fiveForm k ε x x)
    (hb : fiveForm k ε x y = fiveForm k ε x x) :
    fiveReflOf k ε x * fiveReflOf k ε y ∈ fiveReflectionGroupIn k ε π W := by
  by_cases hs0 : y - x = 0
  · have hyx : y = x := sub_eq_zero.mp hs0
    rw [hyx]
    have hxx : fiveReflOf k ε x * fiveReflOf k ε x = 1 := by
      rw [← show (fiveReflOf k ε x)⁻¹ = fiveReflOf k ε x from Units.ext rfl]
      exact mul_inv_cancel _
    rw [hxx]
    exact one_mem _
  · have hsW : y - x ∈ W := W.sub_mem hyW hxW
    have hs : fiveForm k ε (y - x) (y - x) = 0 := by
      rw [fiveForm_sub_sub, hy, fiveForm_comm k ε y x, hb]; ring
    have hsx : fiveForm k ε (y - x) x = 0 := by
      rw [fiveForm_sub_left, fiveForm_comm k ε y x, hb, sub_self]
    have hUW : Submodule.span (ZMod 5) {x} ≤ W :=
      Submodule.span_le.mpr (by
        intro v hv
        rw [Set.mem_singleton_iff] at hv
        rw [hv]
        exact hxW)
    have hN : IsFiveNondeg k ε (W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {x})) :=
      isFiveNondeg_inf_fiveOrth hW (isFiveNondeg_span_singleton hx) hUW
    have hsN : y - x ∈ W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {x}) := by
      refine ⟨hsW, mem_fiveOrth.2 fun u hu => ?_⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
      rw [fiveForm_smul_right, hsx, mul_zero]
    obtain ⟨s', hs'N, hss', hs'⟩ := exists_fiveForm_hyperbolic_partner hN hsN hs hs0
    obtain ⟨b', hb'0, hb'c, hb'nc⟩ := exists_five_ne_zero_ne hx
    let a : ZMod 5 := fiveForm k ε x x / (2 * b')
    let z : Fin (k + 1) → ZMod 5 := a • (y - x) + b' • s'
    have hs'orth : s' ∈ fiveOrth k ε (Submodule.span (ZMod 5) {x}) := hs'N.2
    have hzW : z ∈ W := W.add_mem (W.smul_mem _ hsW) (W.smul_mem _ hs'N.1)
    have hQz : fiveForm k ε z z = fiveForm k ε x x := by
      have hQas : fiveForm k ε (a • (y - x)) (a • (y - x)) = 0 := by
        rw [fiveForm_smul_left, fiveForm_smul_right, hs, mul_zero, mul_zero]
      have hQbs : fiveForm k ε (b' • s') (b' • s') = 0 := by
        rw [fiveForm_smul_left, fiveForm_smul_right, hs', mul_zero, mul_zero]
      have hBas : fiveForm k ε (a • (y - x)) (b' • s') = a * b' := by
        rw [fiveForm_smul_left, fiveForm_smul_right, hss', mul_one]
      dsimp only [z]
      rw [fiveForm_add_add, hQas, hQbs, hBas, zero_add, add_zero]
      dsimp only [a]
      field_simp
    have hBxz : fiveForm k ε x z = 0 := by
      have h1 : fiveForm k ε x (a • (y - x)) = 0 := by
        rw [fiveForm_smul_right, fiveForm_comm k ε x (y - x), fiveForm_sub_left,
          fiveForm_comm k ε y x, hb, sub_self, mul_zero]
      have h2 : fiveForm k ε x (b' • s') = 0 := by
        rw [fiveForm_smul_right]
        have : fiveForm k ε x s' = 0 := by
          rw [fiveForm_comm]
          exact (mem_fiveOrth.mp hs'orth) x (Submodule.subset_span (Set.mem_singleton x))
        rw [this, mul_zero]
      dsimp only [z]
      rw [fiveForm_add_right, h1, h2, add_zero]
    have hBzy : fiveForm k ε z y = b' := by
      have hy_eq : y = x + (y - x) := by abel
      have hz_x : fiveForm k ε z x = 0 := by rw [fiveForm_comm]; exact hBxz
      have hzs : fiveForm k ε z (y - x) = b' := by
        have h1 : fiveForm k ε (a • (y - x)) (y - x) = 0 := by
          rw [fiveForm_smul_left, hs, mul_zero]
        have h2 : fiveForm k ε (b' • s') (y - x) = b' := by
          rw [fiveForm_smul_left, fiveForm_comm k ε s' (y - x), hss', mul_one]
        dsimp only [z]
        rw [fiveForm_add_left, h1, h2, zero_add]
      rw [hy_eq, fiveForm_add_right, hz_x, hzs, zero_add]
    have hz : fiveForm k ε z z ≠ 0 := by rw [hQz]; exact hx
    have hzπ : IsSquare (fiveForm k ε z z) ↔ (!π) = true := by rw [hQz]; exact hxπ
    have h1 : fiveForm k ε x z ≠ fiveForm k ε x x := by
      rw [hBxz]; exact fun h => hx h.symm
    have h2 : fiveForm k ε x z ≠ -fiveForm k ε x x := by
      rw [hBxz]; exact fun h => hx (neg_eq_zero.mp h.symm)
    have h1' : fiveForm k ε z y ≠ fiveForm k ε z z := by
      rw [hBzy, hQz]; exact hb'c
    have h2' : fiveForm k ε z y ≠ -fiveForm k ε z z := by
      rw [hBzy, hQz]; exact hb'nc
    have hxz := fiveReflOf_mul_mem_fiveReflectionGroupIn_of_b_ne hxW hzW hx hxπ
      hQz h1 h2
    have hzy := fiveReflOf_mul_mem_fiveReflectionGroupIn_of_b_ne hzW hyW hz hzπ
      (by rw [hy, hQz]) h1' h2'
    have hzz : fiveReflOf k ε z * fiveReflOf k ε z = 1 := by
      rw [← show (fiveReflOf k ε z)⁻¹ = fiveReflOf k ε z from Units.ext rfl]
      exact mul_inv_cancel _
    have hprod : fiveReflOf k ε x * fiveReflOf k ε y =
        (fiveReflOf k ε x * fiveReflOf k ε z) * (fiveReflOf k ε z * fiveReflOf k ε y) := by
      rw [mul_assoc]
      congr 1
      rw [← mul_assoc, hzz, one_mul]
    rw [hprod]
    exact mul_mem hxz hzy

theorem fiveReflOf_mul_mem_fiveReflectionGroupIn_of_not_eq {k : ℕ} {ε π : Bool}
    {W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} (hW : IsFiveNondeg k ε W)
    {x y : Fin (k + 1) → ZMod 5} (hxW : x ∈ W) (hyW : y ∈ W)
    (hx : fiveForm k ε x x ≠ 0) (hxπ : IsSquare (fiveForm k ε x x) ↔ (!π) = true)
    (hy : fiveForm k ε y y = fiveForm k ε x x) :
    fiveReflOf k ε x * fiveReflOf k ε y ∈ fiveReflectionGroupIn k ε π W := by
  by_cases hb : fiveForm k ε x y = fiveForm k ε x x
  · exact fiveReflOf_mul_mem_fiveReflectionGroupIn_of_b_eq hW hxW hyW hx hxπ hy hb
  · by_cases hb' : fiveForm k ε x y = -fiveForm k ε x x
    ·
      have hnyW : -y ∈ W := W.neg_mem hyW
      have hny : fiveForm k ε (-y) (-y) = fiveForm k ε x x := by
        calc fiveForm k ε (-y) (-y) = - fiveForm k ε y (-y) := fiveForm_neg_left k ε y (-y)
          _ = - (- fiveForm k ε y y) := congrArg Neg.neg (fiveForm_neg_right k ε y y)
          _ = fiveForm k ε y y := neg_neg _
          _ = fiveForm k ε x x := hy
      have hbn : fiveForm k ε x (-y) = fiveForm k ε x x := by
        calc fiveForm k ε x (-y) = - fiveForm k ε x y := fiveForm_neg_right k ε x y
          _ = - (- fiveForm k ε x x) := congrArg Neg.neg hb'
          _ = fiveForm k ε x x := neg_neg _
      have hres := fiveReflOf_mul_mem_fiveReflectionGroupIn_of_b_eq hW hxW hnyW hx hxπ hny hbn
      have hrny : fiveReflOf k ε (-y) = fiveReflOf k ε y := by
        rw [show -y = (-1 : ZMod 5) • y from by
          funext j; simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
          exact (neg_one_mul (y j)).symm, fiveReflOf_smul k ε y (by decide)]
      rwa [hrny] at hres
    · exact fiveReflOf_mul_mem_fiveReflectionGroupIn_of_b_ne hxW hyW hx hxπ hy hb hb'

theorem fiveReflOf_mul_mem_fiveReflectionGroupIn_of_not {k : ℕ} {ε π : Bool}
    {W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} (hW : IsFiveNondeg k ε W)
    {x y : Fin (k + 1) → ZMod 5} (hxW : x ∈ W) (hyW : y ∈ W)
    (hx : fiveForm k ε x x ≠ 0) (hxπ : IsSquare (fiveForm k ε x x) ↔ (!π) = true)
    (hy : fiveForm k ε y y ≠ 0) (hyπ : IsSquare (fiveForm k ε y y) ↔ (!π) = true) :
    fiveReflOf k ε x * fiveReflOf k ε y ∈ fiveReflectionGroupIn k ε π W := by
  obtain ⟨l, hl⟩ := exists_sq_mul_eq_of_isSquare_iff hy hx (hyπ.trans hxπ.symm)
  have hl0 : l ≠ 0 := by
    rintro rfl
    simp at hl
    exact hx hl.symm
  have hy'W : l • y ∈ W := W.smul_mem l hyW
  have hy' : fiveForm k ε (l • y) (l • y) = fiveForm k ε x x := by
    rw [fiveForm_smul_left, fiveForm_smul_right]
    rw [show l * (l * fiveForm k ε y y) = l ^ 2 * fiveForm k ε y y by ring, hl]
  have hres := fiveReflOf_mul_mem_fiveReflectionGroupIn_of_not_eq hW hxW hy'W hx hxπ hy'
  rwa [fiveReflOf_smul k ε y hl0] at hres

theorem exists_fiveReflOf_not_fixing {k : ℕ} {ε π : Bool}
    {W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} (hW : IsFiveNondeg k ε W)
    (h4 : 4 ≤ Module.finrank (ZMod 5) W)
    {x : Fin (k + 1) → ZMod 5} (hxW : x ∈ W) (hx : x ≠ 0) :
    ∃ v ∈ W, fiveForm k ε v v ≠ 0 ∧ (IsSquare (fiveForm k ε v v) ↔ (!π) = true) ∧
      (fiveReflOf k ε v : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x = x := by
  have hUW : Submodule.span (ZMod 5) {x} ≤ W :=
    Submodule.span_le.mpr (by
      intro v hv
      rw [Set.mem_singleton_iff] at hv
      rw [hv]
      exact hxW)
  by_cases hxQ : fiveForm k ε x x = 0
  · obtain ⟨xs, hxsW, hxxs, hxs0⟩ := exists_fiveForm_hyperbolic_partner hW hxW hxQ hx
    let H : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5) :=
      Submodule.span (ZMod 5) ({x, xs} : Set (Fin (k + 1) → ZMod 5))
    have hH : IsFiveNondeg k ε H := by
      rw [isFiveNondeg_iff]
      intro u hu horth
      obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hu
      have hmemx : x ∈ ({x, xs} : Set (Fin (k + 1) → ZMod 5)) := by simp
      have hmemxs : xs ∈ ({x, xs} : Set (Fin (k + 1) → ZMod 5)) := by simp
      have hbx : fiveForm k ε u x = 0 := horth x (Submodule.subset_span hmemx)
      have hbxs : fiveForm k ε u xs = 0 := horth xs (Submodule.subset_span hmemxs)
      have hb : b = 0 := by
        rw [← hab, fiveForm_add_left, fiveForm_smul_left, fiveForm_smul_left, hxQ, mul_zero,
          fiveForm_comm k ε xs x, hxxs, mul_one, zero_add] at hbx
        exact hbx
      have ha : a = 0 := by
        rw [← hab, fiveForm_add_left, fiveForm_smul_left, fiveForm_smul_left, hxxs, mul_one,
          hxs0, mul_zero, add_zero] at hbxs
        exact hbxs
      rw [← hab, hb, ha, zero_smul, zero_smul, add_zero]
    have hHW : H ≤ W := Submodule.span_le.mpr (by
      intro v hv
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl
      · exact hxW
      · exact hxsW)
    have hHle : Module.finrank (ZMod 5) H ≤ 2 := by
      have hcard := finrank_span_le_card (R := ZMod 5) ({x, xs} : Set (Fin (k + 1) → ZMod 5))
      have hc : ({x, xs} : Set (Fin (k + 1) → ZMod 5)).toFinset.card ≤ 2 := by
        rw [Set.toFinset_insert, Set.toFinset_singleton]
        exact Finset.card_insert_le _ _
      have : Module.finrank (ZMod 5) H ≤ 2 := by
        rw [show H = Submodule.span (ZMod 5) ({x, xs} : Set _) from rfl]
        exact le_trans hcard hc
      exact this
    have hN : IsFiveNondeg k ε (W ⊓ fiveOrth k ε H) :=
      isFiveNondeg_inf_fiveOrth hW hH hHW
    have hdim : 2 ≤ Module.finrank (ZMod 5) ↥(W ⊓ fiveOrth k ε H) := by
      have h := finrank_inf_fiveOrth_add hW hHW
      omega
    obtain ⟨v, hvN, hvQ⟩ := exists_fiveForm_eq_of_nondeg hN hdim (c := fiveSignRep (!π))
    refine ⟨v, hvN.1, ?_, ?_, ?_⟩
    · rw [hvQ]; exact fiveSignRep_ne_zero (!π)
    · rw [hvQ]; exact isSquare_fiveSignRep_iff (!π)
    · rw [fiveReflOf_mulVec]
      have hvx : fiveForm k ε v x = 0 :=
        (mem_fiveOrth.mp hvN.2) x (Submodule.subset_span (by simp))
      rw [fiveForm_comm k ε x v, hvx, mul_zero, zero_mul, zero_smul]
      abel
  · have hN : IsFiveNondeg k ε (W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {x})) :=
      isFiveNondeg_inf_fiveOrth hW (isFiveNondeg_span_singleton hxQ) hUW
    have hdim : 2 ≤ Module.finrank (ZMod 5)
        ↥(W ⊓ fiveOrth k ε (Submodule.span (ZMod 5) {x})) := by
      have h := finrank_inf_fiveOrth_add hW hUW
      have h1 : Module.finrank (ZMod 5) (Submodule.span (ZMod 5) {x}) ≤ 1 := by
        have := finrank_span_le_card (R := ZMod 5) ({x} : Set (Fin (k + 1) → ZMod 5))
        simpa using this
      omega
    obtain ⟨v, hvN, hvQ⟩ := exists_fiveForm_eq_of_nondeg hN hdim (c := fiveSignRep (!π))
    refine ⟨v, hvN.1, ?_, ?_, ?_⟩
    · rw [hvQ]; exact fiveSignRep_ne_zero (!π)
    · rw [hvQ]; exact isSquare_fiveSignRep_iff (!π)
    · rw [fiveReflOf_mulVec]
      have hvx : fiveForm k ε v x = 0 :=
        (mem_fiveOrth.mp hvN.2) x (Submodule.subset_span (by simp))
      rw [fiveForm_comm k ε x v, hvx, mul_zero, zero_mul, zero_smul]
      abel

theorem exists_mem_fiveReflectionGroupIn_apply_eq {k : ℕ} {ε π : Bool}
    {W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} (hW : IsFiveNondeg k ε W)
    (h4 : 4 ≤ Module.finrank (ZMod 5) W) {x y : Fin (k + 1) → ZMod 5} (hx : x ∈ W) (hy : y ∈ W)
    (hxy : fiveForm k ε x x = fiveForm k ε y y) (hne : fiveForm k ε x x ≠ 0) :
    ∃ g ∈ fiveReflectionGroupIn k ε π W,
      (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x = y := by
  have hx0 : x ≠ 0 := by
    intro h
    exact hne (by rw [h]; simp [fiveForm])
  have hyne : fiveForm k ε y y ≠ 0 := by rwa [← hxy]
  by_cases hq : fiveForm k ε (x - y) (x - y) = 0
  ·
    have hB : fiveForm k ε x y = fiveForm k ε x x := by
      have h := fiveForm_sub_sub k ε x y
      rw [hq] at h
      have h3 : 2 * fiveForm k ε x y = fiveForm k ε x x + fiveForm k ε y y :=
        (sub_eq_zero.mp h.symm).symm
      have h2 : 2 * fiveForm k ε x y = 2 * fiveForm k ε x x := by
        rw [h3, ← hxy, ← two_mul]
      exact mul_left_cancel₀ (by decide : (2 : ZMod 5) ≠ 0) h2
    have hQxy : fiveForm k ε (x + y) (x + y) = 4 * fiveForm k ε x x := by
      rw [fiveForm_add_add, ← hxy, hB]; ring
    have hQxy_ne : fiveForm k ε (x + y) (x + y) ≠ 0 := by
      rw [hQxy]; exact mul_ne_zero (by decide : (4 : ZMod 5) ≠ 0) hne
    have hQxyW : x + y ∈ W := W.add_mem hx hy
    have hradd : (fiveReflOf k ε (x + y) : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x =
        -y := fiveReflOf_add_apply_of_form_eq hxy hQxy_ne
    have hry : (fiveReflOf k ε y : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y = -y := by
      rw [fiveReflOf_mulVec]
      have hc : 2 * fiveForm k ε y y * (fiveForm k ε y y)⁻¹ = 2 := by
        rw [mul_assoc, mul_inv_cancel₀ hyne, mul_one]
      rw [hc]
      rw [show (2 : ZMod 5) • y = y + y by
        simp only [show (2 : ZMod 5) = 1 + 1 by norm_num, add_smul, one_smul]]
      abel
    have hfinal : (fiveReflOf k ε y * fiveReflOf k ε (x + y) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x = y := by
      rw [← Matrix.mulVec_mulVec, hradd,
        show (fiveReflOf k ε y : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ (-y) =
          -((fiveReflOf k ε y : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y) from
          Matrix.mulVec_neg y _,
        hry]
      exact neg_neg y
    by_cases hcπ : IsSquare (fiveForm k ε x x) ↔ π = true
    · have hyπ : IsSquare (fiveForm k ε y y) ↔ π = true := by rw [← hxy]; exact hcπ
      have hxyπ : IsSquare (fiveForm k ε (x + y) (x + y)) ↔ π = true := by
        rw [hQxy, show (4 : ZMod 5) * fiveForm k ε x x = 2 * 2 * fiveForm k ε x x by norm_num,
          isSquare_mul_self_mul_iff (by decide : (2 : ZMod 5) ≠ 0)]
        exact hcπ
      refine ⟨fiveReflOf k ε y * fiveReflOf k ε (x + y), ?_, hfinal⟩
      exact mul_mem (Subgroup.subset_closure (fiveReflOf_mem_fiveReflectionsIn hy hyne hyπ))
        (Subgroup.subset_closure (fiveReflOf_mem_fiveReflectionsIn hQxyW hQxy_ne hxyπ))
    · have hcπ' : IsSquare (fiveForm k ε x x) ↔ (!π) = true := by cases π <;> simp_all
      have hyπ' : IsSquare (fiveForm k ε y y) ↔ (!π) = true := by rw [← hxy]; exact hcπ'
      have hxyπ' : IsSquare (fiveForm k ε (x + y) (x + y)) ↔ (!π) = true := by
        rw [hQxy, show (4 : ZMod 5) * fiveForm k ε x x = 2 * 2 * fiveForm k ε x x by norm_num,
          isSquare_mul_self_mul_iff (by decide : (2 : ZMod 5) ≠ 0)]
        exact hcπ'
      refine ⟨fiveReflOf k ε y * fiveReflOf k ε (x + y), ?_, hfinal⟩
      exact fiveReflOf_mul_mem_fiveReflectionGroupIn_of_not hW hy hQxyW hyne hyπ' hQxy_ne hxyπ'
  ·
    by_cases hcπ : IsSquare (fiveForm k ε (x - y) (x - y)) ↔ π = true
    · refine ⟨fiveReflOf k ε (x - y), ?_, fiveReflOf_sub_apply_of_form_eq hxy hq⟩
      exact Subgroup.subset_closure
        (fiveReflOf_mem_fiveReflectionsIn (W.sub_mem hx hy) hq hcπ)
    · have hcπ' : IsSquare (fiveForm k ε (x - y) (x - y)) ↔ (!π) = true := by
        cases π <;> simp_all
      obtain ⟨t, htW, ht, htπ, htx⟩ := exists_fiveReflOf_not_fixing hW h4 hx hx0
      refine ⟨fiveReflOf k ε (x - y) * fiveReflOf k ε t, ?_, ?_⟩
      · exact fiveReflOf_mul_mem_fiveReflectionGroupIn_of_not hW (W.sub_mem hx hy) htW hq hcπ'
          ht htπ
      · rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, htx,
          fiveReflOf_sub_apply_of_form_eq hxy hq]

theorem exists_fiveForm_polar_ne_zero_pair {k : ℕ} {ε : Bool}
    {W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} (hW : IsFiveNondeg k ε W)
    {x y : Fin (k + 1) → ZMod 5} (hxW : x ∈ W) (hyW : y ∈ W) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    ∃ u ∈ W, fiveForm k ε x u ≠ 0 ∧ fiveForm k ε y u ≠ 0 := by
  have hxw : ∃ w ∈ W, fiveForm k ε x w ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (isFiveNondeg_iff.1 hW x hxW fun z hz => h z hz)
  obtain ⟨w, hwW, hxw⟩ := hxw
  by_cases hyw : fiveForm k ε y w = 0
  · have hyw' : ∃ w' ∈ W, fiveForm k ε y w' ≠ 0 := by
      by_contra h
      push Not at h
      exact hy0 (isFiveNondeg_iff.1 hW y hyW fun z hz => h z hz)
    obtain ⟨w', hw'W, hyw'⟩ := hyw'
    by_cases hsum : fiveForm k ε x w + fiveForm k ε x w' = 0
    · have hxw' : fiveForm k ε x w' ≠ 0 := by
        intro h0
        exact hxw (by rw [h0, add_zero] at hsum; exact hsum)
      refine ⟨w + 2 • w', W.add_mem hwW (W.smul_mem _ hw'W), ?_, ?_⟩
      · rw [fiveForm_add_right, fiveForm_smul_right]
        have h1 : fiveForm k ε x w + 2 * fiveForm k ε x w' = fiveForm k ε x w' := by
          linear_combination hsum
        rw [h1]; exact hxw'
      · rw [fiveForm_add_right, fiveForm_smul_right, hyw, zero_add]
        exact mul_ne_zero (by decide : (2 : ZMod 5) ≠ 0) hyw'
    · refine ⟨w + w', W.add_mem hwW hw'W, ?_, ?_⟩
      · rw [fiveForm_add_right]; exact hsum
      · rw [fiveForm_add_right, hyw, zero_add]; exact hyw'
  · exact ⟨w, hwW, hxw, hyw⟩

theorem exists_fiveForm_singular_polar_ne_zero_pair {k : ℕ} {ε : Bool}
    {W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} (hW : IsFiveNondeg k ε W)
    {x y : Fin (k + 1) → ZMod 5} (hxW : x ∈ W) (hyW : y ∈ W) (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hxs : fiveForm k ε x x = 0) (hxy0 : fiveForm k ε x y = 0) :
    ∃ z ∈ W, fiveForm k ε z z = 0 ∧ fiveForm k ε x z ≠ 0 ∧ fiveForm k ε z y ≠ 0 := by
  obtain ⟨u, huW, hxu, hyu⟩ := exists_fiveForm_polar_ne_zero_pair hW hxW hyW hx0 hy0
  let t : ZMod 5 := -(fiveForm k ε u u) / (2 * fiveForm k ε x u)
  refine ⟨u + t • x, W.add_mem huW (W.smul_mem _ hxW), ?_, ?_, ?_⟩
  · have h1 : fiveForm k ε (t • x) (t • x) = 0 := by
      rw [fiveForm_smul_left, fiveForm_smul_right, hxs, mul_zero, mul_zero]
    have h2 : fiveForm k ε u (t • x) = t * fiveForm k ε x u := by
      rw [fiveForm_smul_right, fiveForm_comm k ε u x]
    rw [fiveForm_add_add, h1, h2, add_zero]
    have hden : (2 * fiveForm k ε x u : ZMod 5) ≠ 0 :=
      mul_ne_zero (by decide : (2 : ZMod 5) ≠ 0) hxu
    have ht : 2 * (t * fiveForm k ε x u) = - fiveForm k ε u u := by
      dsimp only [t]
      rw [div_eq_mul_inv,
        show 2 * (-(fiveForm k ε u u) * (2 * fiveForm k ε x u)⁻¹ * fiveForm k ε x u) =
          -fiveForm k ε u u * ((2 * fiveForm k ε x u) * (2 * fiveForm k ε x u)⁻¹) by ring,
        mul_inv_cancel₀ hden, mul_one]
    rw [ht]
    abel
  · rw [fiveForm_add_right, fiveForm_smul_right, hxs, mul_zero, add_zero]
    exact hxu
  · rw [fiveForm_add_left, fiveForm_smul_left, hxy0, mul_zero, add_zero,
      fiveForm_comm k ε u y]
    exact hyu

theorem exists_mem_fiveReflectionGroupIn_apply_eq_of_singular {k : ℕ} {ε π : Bool}
    {W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)} (hW : IsFiveNondeg k ε W)
    (h4 : 4 ≤ Module.finrank (ZMod 5) W) {x y : Fin (k + 1) → ZMod 5} (hx : x ∈ W) (hy : y ∈ W)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hxs : fiveForm k ε x x = 0) (hys : fiveForm k ε y y = 0) :
    ∃ g ∈ fiveReflectionGroupIn k ε π W,
      (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x = y := by
  have hxy0 : fiveForm k ε x x = fiveForm k ε y y := by rw [hxs, hys]
  by_cases hBxy : fiveForm k ε x y = 0
  ·
    obtain ⟨z, hzW, hzs, hxz, hzy⟩ :=
      exists_fiveForm_singular_polar_ne_zero_pair hW hx hy hx0 hy0 hxs hBxy
    have hq1 : fiveForm k ε (x - z) (x - z) ≠ 0 := by
      have h2 : 2 * fiveForm k ε x z ≠ 0 := mul_ne_zero (by decide : (2 : ZMod 5) ≠ 0) hxz
      rw [fiveForm_sub_sub, hxs, hzs, zero_add, zero_sub]
      exact neg_ne_zero.mpr h2
    have hq2 : fiveForm k ε (z - y) (z - y) ≠ 0 := by
      have h2 : 2 * fiveForm k ε z y ≠ 0 := mul_ne_zero (by decide : (2 : ZMod 5) ≠ 0) hzy
      rw [fiveForm_sub_sub, hzs, hys, zero_add, zero_sub]
      exact neg_ne_zero.mpr h2
    have hsw1 : (fiveReflOf k ε (x - z) : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x =
        z := fiveReflOf_sub_apply_of_form_eq (by rw [hxs, hzs]) hq1
    have hsw2 : (fiveReflOf k ε (z - y) : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ z =
        y := fiveReflOf_sub_apply_of_form_eq (by rw [hzs, hys]) hq2
    have hxzW : x - z ∈ W := W.sub_mem hx hzW
    have hzyW : z - y ∈ W := W.sub_mem hzW hy
    by_cases hs1 : IsSquare (fiveForm k ε (x - z) (x - z)) ↔ π = true
    · by_cases hs2 : IsSquare (fiveForm k ε (z - y) (z - y)) ↔ π = true
      ·
        refine ⟨fiveReflOf k ε (z - y) * fiveReflOf k ε (x - z), ?_, ?_⟩
        · exact mul_mem
            (Subgroup.subset_closure (fiveReflOf_mem_fiveReflectionsIn hzyW hq2 hs2))
            (Subgroup.subset_closure (fiveReflOf_mem_fiveReflectionsIn hxzW hq1 hs1))
        · rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hsw1, hsw2]
      ·
        have hs2' : IsSquare (fiveForm k ε (z - y) (z - y)) ↔ (!π) = true := by
          cases π <;> simp_all
        obtain ⟨t, htW, ht, htπ, hty⟩ := exists_fiveReflOf_not_fixing hW h4 hy hy0
        refine ⟨(fiveReflOf k ε t * fiveReflOf k ε (z - y)) * fiveReflOf k ε (x - z), ?_, ?_⟩
        · exact mul_mem
            (fiveReflOf_mul_mem_fiveReflectionGroupIn_of_not hW htW hzyW ht htπ hq2 hs2')
            (Subgroup.subset_closure (fiveReflOf_mem_fiveReflectionsIn hxzW hq1 hs1))
        · rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
            ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hsw1, hsw2, hty]
    · have hs1' : IsSquare (fiveForm k ε (x - z) (x - z)) ↔ (!π) = true := by
        cases π <;> simp_all
      by_cases hs2 : IsSquare (fiveForm k ε (z - y) (z - y)) ↔ π = true
      ·
        obtain ⟨t, htW, ht, htπ, htx⟩ := exists_fiveReflOf_not_fixing hW h4 hx hx0
        refine ⟨fiveReflOf k ε (z - y) * (fiveReflOf k ε (x - z) * fiveReflOf k ε t), ?_, ?_⟩
        · exact mul_mem
            (Subgroup.subset_closure (fiveReflOf_mem_fiveReflectionsIn hzyW hq2 hs2))
            (fiveReflOf_mul_mem_fiveReflectionGroupIn_of_not hW hxzW htW hq1 hs1' ht htπ)
        · rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
            ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, htx, hsw1, hsw2]
      ·
        have hs2' : IsSquare (fiveForm k ε (z - y) (z - y)) ↔ (!π) = true := by
          cases π <;> simp_all
        refine ⟨fiveReflOf k ε (z - y) * fiveReflOf k ε (x - z), ?_, ?_⟩
        · exact fiveReflOf_mul_mem_fiveReflectionGroupIn_of_not hW hzyW hxzW hq2 hs2' hq1 hs1'
        · rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hsw1, hsw2]
  ·
    have hq : fiveForm k ε (x - y) (x - y) ≠ 0 := by
      have h2 : 2 * fiveForm k ε x y ≠ 0 := mul_ne_zero (by decide : (2 : ZMod 5) ≠ 0) hBxy
      rw [fiveForm_sub_sub, hxs, hys, zero_add, zero_sub]
      exact neg_ne_zero.mpr h2
    have hsw : (fiveReflOf k ε (x - y) : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x =
        y := fiveReflOf_sub_apply_of_form_eq hxy0 hq
    have hxyW : x - y ∈ W := W.sub_mem hx hy
    by_cases hs : IsSquare (fiveForm k ε (x - y) (x - y)) ↔ π = true
    · exact ⟨fiveReflOf k ε (x - y),
        Subgroup.subset_closure (fiveReflOf_mem_fiveReflectionsIn hxyW hq hs), hsw⟩
    · have hs' : IsSquare (fiveForm k ε (x - y) (x - y)) ↔ (!π) = true := by
        cases π <;> simp_all
      obtain ⟨t, htW, ht, htπ, htx⟩ := exists_fiveReflOf_not_fixing hW h4 hx hx0
      refine ⟨fiveReflOf k ε (x - y) * fiveReflOf k ε t, ?_, ?_⟩
      · exact fiveReflOf_mul_mem_fiveReflectionGroupIn_of_not hW hxyW htW hq hs' ht htπ
      · rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, htx, hsw]

end CFSG.OddTranspositions.PartThree

end
