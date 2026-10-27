module

public import CFSG.RankThree.Classical.TransvectionReciprocalPair

public section

namespace CFSG.RankThree.PartOne.LIT

open CFSG.RankThree.Classical (IsTransvectionWith)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

@[expose] def TrIn (H : Subgroup (V ≃ₗ[ZMod p] V)) (c : V) (f : Module.Dual (ZMod p) V) : Prop :=
  f c = 0 ∧ ∃ t ∈ H, ∀ x, t x = x + f x • c

namespace TrIn

variable {H : Subgroup (V ≃ₗ[ZMod p] V)} {c d c' : V} {f g f' : Module.Dual (ZMod p) V}

theorem zero_center (f : Module.Dual (ZMod p) V) : TrIn H 0 f :=
  ⟨map_zero f, 1, H.one_mem, fun x => by simp⟩

theorem zero_axis (c : V) : TrIn H c 0 :=
  ⟨by simp, 1, H.one_mem, fun x => by simp⟩

theorem of_isTransvectionWith {t : V ≃ₗ[ZMod p] V} (ht : t ∈ H) (h : IsTransvectionWith t c f) :
    TrIn H c f :=
  ⟨h.2.2.1, t, ht, h.2.2.2⟩

theorem inv_apply {t : V ≃ₗ[ZMod p] V} (hfc : f c = 0) (htx : ∀ x, t x = x + f x • c) (x : V) :
    t⁻¹ x = x - f x • c := by
  show t.symm x = _
  rw [LinearEquiv.symm_apply_eq, htx, map_sub, map_smul, hfc]
  simp

theorem smul (h : TrIn H c f) (s : ZMod p) : TrIn H c (s • f) := by
  obtain ⟨hfc, t, ht, htx⟩ := h
  refine ⟨by simp [hfc], t ^ s.val, H.pow_mem ht _, fun x => ?_⟩
  have key : ∀ n : ℕ, ((t ^ n) x) = x + ((n : ZMod p) * f x) • c := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', LinearEquiv.mul_apply, ih, htx (x + ((n : ZMod p) * f x) • c)]
      simp only [map_add, map_smul, hfc, smul_eq_mul]
      push_cast
      module
  rw [key, ZMod.natCast_zmod_val]
  simp

theorem add (h : TrIn H c f) (h' : TrIn H c f') : TrIn H c (f + f') := by
  obtain ⟨hfc, t, ht, htx⟩ := h
  obtain ⟨hfc', t', ht', htx'⟩ := h'
  refine ⟨by simp [hfc, hfc'], t * t', H.mul_mem ht ht', fun x => ?_⟩
  rw [LinearEquiv.mul_apply, htx', htx (x + f' x • c)]
  simp only [map_add, map_smul, hfc, smul_zero, LinearMap.add_apply, add_smul, add_zero]
  abel

theorem neg (h : TrIn H c f) : TrIn H c (-f) := by
  obtain ⟨hfc, t, ht, htx⟩ := h
  refine ⟨by simp [hfc], t⁻¹, H.inv_mem ht, fun x => ?_⟩
  rw [inv_apply hfc htx]
  simp [sub_eq_add_neg]

theorem sub (h : TrIn H c f) (h' : TrIn H c f') : TrIn H c (f - f') := by
  have := h.add h'.neg
  simpa [sub_eq_add_neg] using this

theorem conj (h : TrIn H c f) {g : V ≃ₗ[ZMod p] V} (hg : g ∈ H) :
    TrIn H (g c) (f ∘ₗ g.symm.toLinearMap) := by
  obtain ⟨hfc, t, ht, htx⟩ := h
  refine ⟨by simpa using hfc, g * t * g⁻¹, H.mul_mem (H.mul_mem hg ht) (H.inv_mem hg), fun x => ?_⟩
  show g (t (g.symm x)) = x + f (g.symm x) • g c
  rw [htx, map_add, map_smul]
  simp

theorem smul_center_iff {s : ZMod p} : TrIn H (s • c) f ↔ TrIn H c (s • f) := by
  constructor
  · rintro ⟨hfc, t, ht, htx⟩
    refine ⟨by simpa [map_smul] using hfc, t, ht, fun x => ?_⟩
    rw [htx, LinearMap.smul_apply, smul_eq_mul, mul_comm, mul_smul]
  · rintro ⟨hfc, t, ht, htx⟩
    refine ⟨by simpa [map_smul] using hfc, t, ht, fun x => ?_⟩
    rw [htx, LinearMap.smul_apply, smul_eq_mul, mul_comm, mul_smul]

theorem add_center (h : TrIn H c f) (h' : TrIn H c' f) : TrIn H (c + c') f := by
  obtain ⟨hfc, t, ht, htx⟩ := h
  obtain ⟨hfc', t', ht', htx'⟩ := h'
  refine ⟨by simp [hfc, hfc'], t * t', H.mul_mem ht ht', fun x => ?_⟩
  rw [LinearEquiv.mul_apply, htx', htx (x + f x • c')]
  simp only [map_add, map_smul, hfc', smul_eq_mul, mul_zero, add_zero, smul_add]
  abel

theorem rule_R (h₁ : TrIn H c f) (h₂ : TrIn H d g) (hgc : g c = 0) : TrIn H c (f d • g) := by
  obtain ⟨hfc, t₁, ht₁, htx₁⟩ := h₁
  obtain ⟨hgd, t₂, ht₂, htx₂⟩ := h₂
  refine ⟨by simp [LinearMap.smul_apply, hgc],
    t₁ * t₂ * t₁⁻¹ * t₂⁻¹,
    H.mul_mem (H.mul_mem (H.mul_mem ht₁ ht₂) (H.inv_mem ht₁)) (H.inv_mem ht₂), fun x => ?_⟩
  simp only [LinearEquiv.mul_apply]
  rw [inv_apply hgd htx₂, inv_apply hfc htx₁, htx₂, htx₁]
  simp only [map_sub, map_add, map_smul, hgc, hfc, hgd, smul_eq_mul, mul_zero, sub_zero,
    LinearMap.smul_apply]
  module

end TrIn

variable (H : Subgroup (V ≃ₗ[ZMod p] V))

@[expose] def FullCenter (c : V) : Prop :=
  c ≠ 0 ∧ ∀ f : Module.Dual (ZMod p) V, f c = 0 → TrIn H c f

@[expose] def IsFrame (U L : Submodule (ZMod p) V) : Prop :=
  IsCompl U L ∧ Module.finrank (ZMod p) U = 2 ∧ Module.finrank (ZMod p) L = 2 ∧
    ∀ c ∈ U, ∀ f : Module.Dual (ZMod p) V, (∀ l ∈ L, f l = 0) → f c = 0 → TrIn H c f

@[expose] def HasUniqueAxes : Prop :=
  ∀ (a : V) (f f' : Module.Dual (ZMod p) V), a ≠ 0 → TrIn H a f → TrIn H a f' → f ≠ 0 →
    ∃ t : ZMod p, f' = t • f

end CFSG.RankThree.PartOne.LIT
