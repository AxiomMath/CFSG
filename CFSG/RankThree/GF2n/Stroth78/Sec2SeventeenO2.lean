module

public import CFSG.RankThree.GF2n.Stroth78.ConjAction

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

noncomputable abbrev diffSpan (S : Setting z E F) (Y : Subgroup (Hbar z)) :
    Submodule (ZMod 2) (Additive (QbarOf S)) :=
  Submodule.span (ZMod 2) {u | ∃ y ∈ Y, ∃ v : Additive (QbarOf S),
    u = ((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v}

theorem diffSpan_invariant_Y (S : Setting z E F) (Y : Subgroup (Hbar z)) :
    ∀ y ∈ Y, ∀ w ∈ diffSpan S Y,
      ((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w ∈
        diffSpan S Y := by
  classical
  intro y hy w hw
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · rintro u ⟨y₀, hy₀, v, rfl⟩
    have hmul : ((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
          (((rhoBar S y₀ : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v) =
        ((rhoBar S (y * y₀) : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v := by
      rw [map_mul]
      rfl
    have hval : ((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
          (((rhoBar S y₀ : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v) =
        (((rhoBar S (y * y₀) : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v) -
          (((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v) := by
      rw [map_sub, hmul]
      abel
    rw [hval]
    exact (diffSpan S Y).sub_mem
      (Submodule.subset_span ⟨y * y₀, Y.mul_mem hy hy₀, v, rfl⟩)
      (Submodule.subset_span ⟨y, hy, v, rfl⟩)
  · simpa using (diffSpan S Y).zero_mem
  · intro x z _ _ hx hz
    simpa only [map_add] using (diffSpan S Y).add_mem hx hz
  · intro c x _ hx
    simpa only [map_smul] using (diffSpan S Y).smul_mem c hx

theorem diffSpan_fixed_of_comm (S : Setting z E F) {a : G} (Y : Subgroup (Hbar z))
    (hcomm : ∀ l ∈ Lbar S a, ∀ y ∈ Y, ∀ v : Additive (QbarOf S),
      ((rhoBar S l : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
        (((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v) =
      ((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v) :
    ∀ l ∈ Lbar S a, ∀ w ∈ diffSpan S Y,
      ((rhoBar S l : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w = w := by
  classical
  intro l hl w hw
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · rintro u ⟨y, hy, v, rfl⟩
    exact hcomm l hl y hy v
  · simp
  · intro x z _ _ hx hz
    rw [map_add, hx, hz]
  · intro c x _ hx
    rw [map_smul, hx]

theorem diffSpan_invariant_closure (S : Setting z E F) {a : G} (Y : Subgroup (Hbar z))
    (hcomm : ∀ l ∈ Lbar S a, ∀ y ∈ Y, ∀ v : Additive (QbarOf S),
      ((rhoBar S l : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
        (((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v) =
      ((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v) :
    ∀ g ∈ Subgroup.closure ((Lbar S a : Set (Hbar z)) ∪ (Y : Set (Hbar z))),
      ∀ w ∈ diffSpan S Y,
        ((rhoBar S g : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w ∈
          diffSpan S Y := by
  classical
  let k : Set (Hbar z) := (Lbar S a : Set (Hbar z)) ∪ (Y : Set (Hbar z))
  let M : Subgroup (Hbar z) := Subgroup.closure k
  have hP : ∀ g ∈ M,
      (∀ w ∈ diffSpan S Y,
        ((rhoBar S g : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w ∈
          diffSpan S Y) ∧
      (∀ w ∈ diffSpan S Y,
        ((rhoBar S g⁻¹ : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w ∈
          diffSpan S Y) := by
    intro g hg
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hg
    · intro x hx
      have hx' : x ∈ (Lbar S a : Set (Hbar z)) ∪ (Y : Set (Hbar z)) := hx
      rcases hx' with hxL | hxY
      · refine ⟨fun w hw => ?_, fun w hw => ?_⟩
        · rw [diffSpan_fixed_of_comm S Y hcomm x hxL w hw]
          exact hw
        · rw [diffSpan_fixed_of_comm S Y hcomm x⁻¹ ((Lbar S a).inv_mem hxL) w hw]
          exact hw
      · exact ⟨diffSpan_invariant_Y S Y x hxY,
          diffSpan_invariant_Y S Y x⁻¹ (Y.inv_mem hxY)⟩
    · refine ⟨fun w hw => ?_, fun w hw => ?_⟩
      · simpa using hw
      · simpa using hw
    · intro x y hx hy hpx hpy
      refine ⟨fun w hw => ?_, fun w hw => ?_⟩
      · have h1 : ((rhoBar S (x * y) : Additive (QbarOf S) ≃ₗ[ZMod 2]
            Additive (QbarOf S))) w =
            ((rhoBar S x : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
              (((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w) := by
          rw [map_mul]
          rfl
        rw [h1]
        exact hpx.1 _ (hpy.1 w hw)
      · have h1 : ((rhoBar S (x * y)⁻¹ : Additive (QbarOf S) ≃ₗ[ZMod 2]
            Additive (QbarOf S))) w =
            ((rhoBar S y⁻¹ : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
              (((rhoBar S x⁻¹ : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w) := by
          rw [mul_inv_rev, map_mul]
          rfl
        rw [h1]
        exact hpy.2 _ (hpx.2 w hw)
    · intro x hx hpx
      refine ⟨hpx.2, ?_⟩
      simpa [inv_inv] using hpx.1
  intro g hg w hw
  exact (hP g hg).1 w hw

theorem diffSpan_stabilizer_normal (S : Setting z E F) {a : G} (Y : Subgroup (Hbar z))
    (hcomm : ∀ l ∈ Lbar S a, ∀ y ∈ Y, ∀ v : Additive (QbarOf S),
      ((rhoBar S l : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
        (((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v) =
      ((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v) :
    ∀ g ∈ Subgroup.closure ((Lbar S a : Set (Hbar z)) ∪ (Y : Set (Hbar z))),
      ∀ k ∈ Subgroup.closure ((Lbar S a : Set (Hbar z)) ∪ (Y : Set (Hbar z))),
        (∀ w ∈ diffSpan S Y,
          ((rhoBar S k : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w = w) →
        ∀ w ∈ diffSpan S Y,
          ((rhoBar S (g * k * g⁻¹) : Additive (QbarOf S) ≃ₗ[ZMod 2]
            Additive (QbarOf S))) w = w := by
  classical
  let M : Subgroup (Hbar z) :=
    Subgroup.closure ((Lbar S a : Set (Hbar z)) ∪ (Y : Set (Hbar z)))
  intro g hg k hk hkfix w hw
  have hginv : ((rhoBar S g⁻¹ : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w ∈
      diffSpan S Y := diffSpan_invariant_closure S Y hcomm g⁻¹ (M.inv_mem hg) w hw
  have hkw : ((rhoBar S k : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
      (((rhoBar S g⁻¹ : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w) =
      ((rhoBar S g⁻¹ : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w :=
    hkfix _ hginv
  have h1 : ((rhoBar S (g * k * g⁻¹) : Additive (QbarOf S) ≃ₗ[ZMod 2]
        Additive (QbarOf S))) w =
      ((rhoBar S g : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
        (((rhoBar S k : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
          (((rhoBar S g⁻¹ : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w)) := by
    rw [map_mul, map_mul]
    rfl
  rw [h1, hkw]
  have hgg : ((rhoBar S g : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
      (((rhoBar S g⁻¹ : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w) = w := by
    have h1 : ((rhoBar S (g * g⁻¹) : Additive (QbarOf S) ≃ₗ[ZMod 2]
        Additive (QbarOf S))) w = w := by simp
    have h2 : ((rhoBar S (g * g⁻¹) : Additive (QbarOf S) ≃ₗ[ZMod 2]
        Additive (QbarOf S))) w =
        ((rhoBar S g : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
          (((rhoBar S g⁻¹ : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w) := by
      rw [map_mul]
      rfl
    rw [h2] at h1
    exact h1
  exact hgg

theorem commutator_diffSpan_fixed (S : Setting z E F) {a : G} (Y : Subgroup (Hbar z))
    (hcomm : ∀ l ∈ Lbar S a, ∀ y ∈ Y, ∀ v : Additive (QbarOf S),
      ((rhoBar S l : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
        (((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v) =
      ((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v) :
    ∀ l ∈ Lbar S a, ∀ y ∈ Y, ∀ w ∈ diffSpan S Y,
      ((rhoBar S ⁅l, y⁆ : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w = w := by
  classical
  let M : Subgroup (Hbar z) :=
    Subgroup.closure ((Lbar S a : Set (Hbar z)) ∪ (Y : Set (Hbar z)))
  intro l hl y hy w hw
  have hyM : y ∈ M := Subgroup.subset_closure (Or.inr hy)
  have hlinvM : l⁻¹ ∈ M := Subgroup.subset_closure (Or.inl ((Lbar S a).inv_mem hl))
  have hkinv : ∀ w ∈ diffSpan S Y,
      ((rhoBar S l⁻¹ : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w = w :=
    diffSpan_fixed_of_comm S Y hcomm l⁻¹ ((Lbar S a).inv_mem hl)
  have hfix : ((rhoBar S (y * l⁻¹ * y⁻¹) : Additive (QbarOf S) ≃ₗ[ZMod 2]
        Additive (QbarOf S))) w = w :=
    diffSpan_stabilizer_normal S Y hcomm y hyM l⁻¹ hlinvM hkinv w hw
  have hcommut : ⁅l, y⁆ = l * (y * l⁻¹ * y⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [hcommut]
  have h1 : ((rhoBar S (l * (y * l⁻¹ * y⁻¹)) : Additive (QbarOf S) ≃ₗ[ZMod 2]
        Additive (QbarOf S))) w =
      ((rhoBar S l : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
        (((rhoBar S (y * l⁻¹ * y⁻¹) : Additive (QbarOf S) ≃ₗ[ZMod 2]
          Additive (QbarOf S))) w) := by
    rw [map_mul]
    rfl
  rw [h1, hfix, diffSpan_fixed_of_comm S Y hcomm l hl w hw]

theorem sq_eq_one_of_mem_Y_of_fixes_diffSpan (S : Setting z E F) (Y : Subgroup (Hbar z)) :
    ∀ x ∈ Y,
      (∀ w ∈ diffSpan S Y,
        ((rhoBar S x : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w = w) →
      x ^ 2 = 1 := by
  intro x hxY hxW
  refine rhoBar_injective S ?_
  rw [map_pow, map_one]
  apply Subtype.ext
  have hφ2 : ((rhoBar S x : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) *
      (rhoBar S x : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) = 1 := by
    refine LinearEquiv.ext fun v => ?_
    change ((rhoBar S x : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
      (((rhoBar S x : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v) = v
    set d : Additive (QbarOf S) :=
      ((rhoBar S x : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v
      with hd
    have hgen : d ∈ diffSpan S Y := by
      rw [hd]
      exact Submodule.subset_span ⟨x, hxY, v, rfl⟩
    have hfix : ((rhoBar S x : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) d = d :=
      hxW d hgen
    have hφv : ((rhoBar S x : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v =
        v + d := by
      rw [hd]
      abel
    have hdd : d + d = 0 := by
      have h11 : (1 : ZMod 2) + 1 = 0 := by decide
      have h := add_smul (1 : ZMod 2) 1 d
      rw [h11] at h
      simpa using h.symm
    calc
      ((rhoBar S x : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
          (((rhoBar S x : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v)
          = ((rhoBar S x : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
              (v + d) := congrArg _ hφv
      _ = ((rhoBar S x : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v +
            ((rhoBar S x : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) d :=
          map_add _ v d
      _ = (v + d) + d := by rw [hφv, hfix]
      _ = v := by rw [add_assoc, hdd, add_zero]
  simpa [pow_two] using hφ2

theorem isPGroup_two_of_le_Y_of_fixes_diffSpan (S : Setting z E F) (Y : Subgroup (Hbar z))
    (P : Subgroup (Hbar z)) (hPY : P ≤ Y)
    (hfix : ∀ p ∈ P, ∀ w ∈ diffSpan S Y,
      ((rhoBar S p : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w = w) :
    IsPGroup 2 P := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro p
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simpa using sq_eq_one_of_mem_Y_of_fixes_diffSpan S Y (p : Hbar z) (hPY p.2) (hfix p p.2)

theorem eq_one_of_mem_Y_of_fixes_diffSpan (S : Setting z E F) (Y : Subgroup (Hbar z))
    (hO2 : ∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
      Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) :
    ∀ y ∈ Y,
      (∀ w ∈ diffSpan S Y,
        ((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w = w) →
      y = 1 := by
  classical
  intro y hy hyW
  let P : Subgroup (Hbar z) :=
    { carrier := {g | g ∈ Y ∧ ∀ w ∈ diffSpan S Y,
        ((rhoBar S g : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w = w}
      one_mem' := by
        refine ⟨Y.one_mem, ?_⟩
        intro w hw
        simp
      mul_mem' := by
        rintro a b ⟨haY, haW⟩ ⟨hbY, hbW⟩
        refine ⟨Y.mul_mem haY hbY, ?_⟩
        intro w hw
        have h1 : ((rhoBar S (a * b) : Additive (QbarOf S) ≃ₗ[ZMod 2]
              Additive (QbarOf S))) w =
            ((rhoBar S a : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
              (((rhoBar S b : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w) := by
          rw [map_mul]
          rfl
        rw [h1, hbW w hw, haW w hw]
      inv_mem' := by
        rintro a ⟨haY, haW⟩
        refine ⟨Y.inv_mem haY, ?_⟩
        intro w hw
        have h1 : ((rhoBar S a : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
            (((rhoBar S a⁻¹ : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w) = w := by
          have h0 : ((rhoBar S (a * a⁻¹) : Additive (QbarOf S) ≃ₗ[ZMod 2]
              Additive (QbarOf S))) w = w := by simp
          have h1 : ((rhoBar S (a * a⁻¹) : Additive (QbarOf S) ≃ₗ[ZMod 2]
              Additive (QbarOf S))) w =
              ((rhoBar S a : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
                (((rhoBar S a⁻¹ : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w) := by
            rw [map_mul]
            rfl
          rw [h1] at h0
          exact h0
        have h2 : ((rhoBar S a : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w = w :=
          haW w hw
        refine (rhoBar S a : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)).injective ?_
        rw [h1, h2] }
  have hPY : P ≤ Y := fun g hg => hg.1
  have h2P : IsPGroup 2 P :=
    isPGroup_two_of_le_Y_of_fixes_diffSpan S Y P hPY (fun p hp w hw => hp.2 w hw)
  have hnP : Y ≤ Subgroup.normalizer (P : Set (Hbar z)) := by
    rw [Subgroup.le_normalizer_iff]
    intro g hg p hp
    refine ⟨Y.mul_mem (Y.mul_mem hg hp.1) (Y.inv_mem hg), ?_⟩
    intro w hw
    have h1 : ((rhoBar S (g * p * g⁻¹) : Additive (QbarOf S) ≃ₗ[ZMod 2]
          Additive (QbarOf S))) w =
        ((rhoBar S g : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
          (((rhoBar S p : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
            (((rhoBar S g⁻¹ : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w)) := by
      rw [map_mul, map_mul]
      rfl
    rw [h1]
    have hginv : ((rhoBar S g⁻¹ : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w ∈
        diffSpan S Y := diffSpan_invariant_Y S Y g⁻¹ (Y.inv_mem hg) w hw
    rw [hp.2 _ hginv]
    have hgg : ((rhoBar S g : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
        (((rhoBar S g⁻¹ : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w) = w := by
      have h0 : ((rhoBar S (g * g⁻¹) : Additive (QbarOf S) ≃ₗ[ZMod 2]
          Additive (QbarOf S))) w = w := by simp
      have h1 : ((rhoBar S (g * g⁻¹) : Additive (QbarOf S) ≃ₗ[ZMod 2]
          Additive (QbarOf S))) w =
          ((rhoBar S g : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
            (((rhoBar S g⁻¹ : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w) := by
        rw [map_mul]
        rfl
      rw [h1] at h0
      exact h0
    exact hgg
  have hbot : P = ⊥ := hO2 P hPY h2P hnP
  have hyP : y ∈ P := ⟨hy, hyW⟩
  rw [hbot] at hyP
  simpa using hyP

theorem commutator_Lbar_Y_eq_one_of_O2_of_le_normalizer
    (S : Setting z E F) {a : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a) (hza : z ∈ QaOf a)
    (Y : Subgroup (Hbar z))
    (hO2 : ∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
      Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥)
    (hcomm : ∀ l ∈ Lbar S a, ∀ y ∈ Y, ∀ v : Additive (QbarOf S),
      ((rhoBar S l : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
        (((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v) =
      ((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v)
    (hL : Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z))) :
    ∀ l ∈ Lbar S a, ∀ y ∈ Y, Commute l y := by
  intro l hl y hy
  have hfix : ∀ w ∈ diffSpan S Y,
      ((rhoBar S ⁅l, y⁆ : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w = w :=
    commutator_diffSpan_fixed S Y hcomm l hl y hy
  have hmemY : ⁅l, y⁆ ∈ Y := by
    have h1 : l * y * l⁻¹ ∈ Y :=
      (Subgroup.le_normalizer_iff.mp hL) l hl y hy
    have h2 : ⁅l, y⁆ = (l * y * l⁻¹) * y⁻¹ := by
      rw [commutatorElement_def]
    rw [h2]
    exact Y.mul_mem h1 (Y.inv_mem hy)
  exact commutatorElement_eq_one_iff_commute.mp
    (eq_one_of_mem_Y_of_fixes_diffSpan S Y hO2 ⁅l, y⁆ hmemY hfix)

end CFSG.RankThree.GF2n.Stroth78
