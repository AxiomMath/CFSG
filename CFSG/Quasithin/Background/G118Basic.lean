module

public import CFSG.Quasithin.Background.G11Stmts
public import CFSG.Quasithin.Background.G10SixteenB

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

namespace G116Props

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {X L : Subgroup (GLV V)} {I : Submodule (ZMod 2) V} (h : G116Props B Γ v₁ X L I)

include h

theorem irrPlus : IrrPlus (normalClosure Γ L) I := h.1

theorem invariant_X : Invariant X I := h.2.2.1

theorem homogeneous : Homogeneous (normalClosure Γ L) := h.2.2.2.2.1

theorem selfDual : SelfDual (normalClosure Γ L) I := h.2.2.2.2.2.2.1

theorem faithful : FaithfulOn (normalClosure Γ L) I := h.2.2.2.2.2.2.2.1

end G116Props

namespace G118

section Setup

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

theorem irrPlus_isIrr (h108 : G108Hyp B Γ v₁ W X X₀ L) {J : Submodule (ZMod 2) V}
    (hJ : IrrPlus (normalClosure Γ L) J) : IsIrr (normalClosure Γ L) J :=
  hJ.isIrr h108.fixedSpace_H

theorem isIrr_I (h108 : G108Hyp B Γ v₁ W X X₀ L) (hI : G116Props B Γ v₁ X L I) :
    IsIrr (normalClosure Γ L) I := irrPlus_isIrr h108 hI.irrPlus

theorem faithful_all (h108 : G108Hyp B Γ v₁ W X X₀ L) (hI : G116Props B Γ v₁ X L I)
    {J : Submodule (ZMod 2) V} (hJ : IsIrr (normalClosure Γ L) J) :
    FaithfulOn (normalClosure Γ L) J := h108.faithful_of_irr hI.irrPlus hI.faithful hJ

theorem centralizerIn_iff (h108 : G108Hyp B Γ v₁ W X X₀ L) (hI : G116Props B Γ v₁ X L I)
    {y : GLV V} (hy : y ∈ X) :
    (∀ h ∈ normalClosure Γ L, y * h = h * y) ↔ ∀ i ∈ I, y i = i := by
  have hyI : conjSub y I = I := hI.invariant_X.conjSub_eq hy
  constructor
  · intro hc
    refine fixes_of_commute_sq_eq_one (isIrr_I h108 hI) (h108.X_sq y hy) hyI ?_
    intro k hk i _
    have := congrArg (fun g : GLV V => g i) (hc k hk)
    exact this
  · intro hy1 h hh
    have hyΓ : y ∈ Γ := h108.X_le hy
    have hk : y * h * y⁻¹ * h⁻¹ ∈ normalClosure Γ L :=
      (normalClosure Γ L).mul_mem ((normalClosure_normal Γ L) y hyΓ h hh)
        ((normalClosure Γ L).inv_mem hh)
    have hyinv : ∀ j ∈ I, (y⁻¹ : GLV V) j = j := fun j hj => by
      have := hy1 j hj
      calc (y⁻¹ : GLV V) j = (y⁻¹ : GLV V) (y j) := by rw [this]
        _ = j := LinearEquiv.symm_apply_apply y j
    have h1 : y * h * y⁻¹ * h⁻¹ = 1 := by
      refine faithfulOn_iff.1 hI.faithful _ hk fun i hi => ?_
      have hhi : (h⁻¹ : GLV V) i ∈ I :=
        (isIrr_I h108 hI).1 h⁻¹ ((normalClosure Γ L).inv_mem hh) i hi
      show y (h ((y⁻¹ : GLV V) ((h⁻¹ : GLV V) i))) = i
      rw [hyinv _ hhi]
      have : h ((h⁻¹ : GLV V) i) = i := LinearEquiv.apply_symm_apply h i
      rw [this]
      exact hy1 i hi
    have h2 : y * h * y⁻¹ = h := mul_inv_eq_one.1 h1
    calc y * h = (y * h * y⁻¹) * y := by group
      _ = h * y := by rw [h2]

omit [Finite V] in
theorem mem_centralizerIn_iff {y : GLV V} :
    y ∈ centralizerIn X (normalClosure Γ L) ↔
      y ∈ X ∧ ∀ h ∈ normalClosure Γ L, y * h = h * y := by
  unfold centralizerIn
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hy, hc⟩
    exact ⟨hy, fun h hh => (hc h hh).symm⟩
  · rintro ⟨hy, hc⟩
    exact ⟨hy, fun h hh => (hc h hh).symm⟩

theorem fixes_of_mem_centralizerIn (h108 : G108Hyp B Γ v₁ W X X₀ L)
    (hI : G116Props B Γ v₁ X L I) {y : GLV V}
    (hy : y ∈ centralizerIn X (normalClosure Γ L)) : ∀ i ∈ I, y i = i := by
  obtain ⟨hyX, hyc⟩ := mem_centralizerIn_iff.1 hy
  exact (centralizerIn_iff h108 hI hyX).1 hyc

theorem mem_centralizerIn_of_fixes (h108 : G108Hyp B Γ v₁ W X X₀ L)
    (hI : G116Props B Γ v₁ X L I) {y : GLV V} (hyX : y ∈ X) (hy : ∀ i ∈ I, y i = i) :
    y ∈ centralizerIn X (normalClosure Γ L) :=
  mem_centralizerIn_iff.2 ⟨hyX, (centralizerIn_iff h108 hI hyX).2 hy⟩

theorem exists_mem_centralizerIn_ne_one (h108 : G108Hyp B Γ v₁ W X X₀ L)
    (hI : G116Props B Γ v₁ X L I) (hnf : ¬ FaithfulOn X I) :
    ∃ y ∈ centralizerIn X (normalClosure Γ L), y ≠ 1 := by
  rw [faithfulOn_iff] at hnf
  push Not at hnf
  obtain ⟨y, hyX, hyI, hy1⟩ := hnf
  exact ⟨y, mem_centralizerIn_of_fixes h108 hI hyX hyI, hy1⟩

theorem dim_le_of_card_X (h108 : G108Hyp B Γ v₁ W X X₀ L) {k : ℕ} (hk : Nat.card X = 2 ^ k) :
    Module.finrank (ZMod 2) V ≤ 2 * (k + 1) := by
  have h1 := h108.toG101Hyp.dim_le_two_mul
  have hdvd : X₀.relIndex X ∣ 2 ^ k := by
    rw [← hk]
    exact Subgroup.relIndex_dvd_card X₀ X
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hjeq, Nat.log_pow Nat.one_lt_two] at h1
  omega

end Setup

end G118

end G11

end CFSG.Quasithin
