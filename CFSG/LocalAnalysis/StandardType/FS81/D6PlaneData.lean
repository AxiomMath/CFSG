module

public import CFSG.LocalAnalysis.StandardType.FS81.D6PlaneAux

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81.D6M

open CFSG.SeitzReduction.OmegaPilot
open scoped MatrixGroups

@[expose] def d6PlaneV4 (a b c d : ZMod 2) : Fin 4 → ZMod 2 := ![a, b, c, d]

@[expose] def d6PlaneU : Fin 18 → (Fin 4 → ZMod 2) :=
  ![d6PlaneV4 0 0 1 0,
   d6PlaneV4 0 1 0 0,
   d6PlaneV4 0 0 0 1,
   d6PlaneV4 1 0 0 1,
   d6PlaneV4 0 0 1 1,
   d6PlaneV4 0 0 1 0,
   d6PlaneV4 0 1 0 0,
   d6PlaneV4 1 0 0 0,
   d6PlaneV4 0 0 0 1,
   d6PlaneV4 0 1 1 0,
   d6PlaneV4 0 0 1 1,
   d6PlaneV4 0 0 1 1,
   d6PlaneV4 0 1 1 0,
   d6PlaneV4 0 0 1 0,
   d6PlaneV4 0 0 1 0,
   d6PlaneV4 0 0 1 1,
   d6PlaneV4 0 0 0 1,
   d6PlaneV4 0 0 0 1]

@[expose] def d6PlaneV : Fin 18 → (Fin 4 → ZMod 2) :=
  ![d6PlaneV4 1 0 0 1,
   d6PlaneV4 1 1 1 1,
   d6PlaneV4 1 1 1 1,
   d6PlaneV4 1 1 0 0,
   d6PlaneV4 1 0 0 0,
   d6PlaneV4 1 1 1 1,
   d6PlaneV4 1 0 0 1,
   d6PlaneV4 1 1 1 1,
   d6PlaneV4 0 1 0 0,
   d6PlaneV4 1 1 0 0,
   d6PlaneV4 0 1 0 0,
   d6PlaneV4 1 0 0 1,
   d6PlaneV4 1 0 0 0,
   d6PlaneV4 1 1 0 0,
   d6PlaneV4 1 0 0 0,
   d6PlaneV4 0 1 1 0,
   d6PlaneV4 0 1 1 0,
   d6PlaneV4 1 1 0 0]

@[expose] def d6PlanePU : Fin 18 → (Fin 4 → ZMod 2) :=
  ![d6PlaneV4 0 0 0 1,
   d6PlaneV4 0 1 1 0,
   d6PlaneV4 0 0 1 1,
   d6PlaneV4 1 0 0 0,
   d6PlaneV4 0 0 0 1,
   d6PlaneV4 0 0 1 1,
   d6PlaneV4 0 1 1 0,
   d6PlaneV4 1 0 0 1,
   d6PlaneV4 0 0 1 0,
   d6PlaneV4 0 1 0 0,
   d6PlaneV4 0 0 1 0,
   d6PlaneV4 0 0 0 1,
   d6PlaneV4 0 1 0 0,
   d6PlaneV4 0 0 1 1,
   d6PlaneV4 0 0 0 1,
   d6PlaneV4 0 0 1 0,
   d6PlaneV4 0 0 1 0,
   d6PlaneV4 0 0 1 1]

@[expose] def d6PlanePV : Fin 18 → (Fin 4 → ZMod 2) :=
  ![d6PlaneV4 0 1 1 0,
   d6PlaneV4 1 1 0 0,
   d6PlaneV4 1 0 0 1,
   d6PlaneV4 1 1 1 1,
   d6PlaneV4 1 1 0 0,
   d6PlaneV4 0 1 1 0,
   d6PlaneV4 1 0 0 0,
   d6PlaneV4 1 1 0 0,
   d6PlaneV4 1 0 0 0,
   d6PlaneV4 1 1 1 1,
   d6PlaneV4 1 1 0 0,
   d6PlaneV4 1 1 1 1,
   d6PlaneV4 1 0 0 1,
   d6PlaneV4 0 1 0 0,
   d6PlaneV4 0 1 0 0,
   d6PlaneV4 1 1 1 1,
   d6PlaneV4 1 0 0 1,
   d6PlaneV4 1 0 0 0]

theorem d6PlaneEmb_v4_inl_zero (a b c d : ZMod 2) :
    d6PlaneEmb (d6PlaneV4 a b c d) (Sum.inl 0) = 0 := by
  rw [d6PlaneEmb_inl_zero]

theorem d6PlaneEmb_v4_inl_one (a b c d : ZMod 2) :
    d6PlaneEmb (d6PlaneV4 a b c d) (Sum.inl 1) = 0 := by
  rw [d6PlaneEmb_inl_one]

theorem d6PlaneEmb_v4_inl_two (a b c d : ZMod 2) :
    d6PlaneEmb (d6PlaneV4 a b c d) (Sum.inl 2) = a := by
  rw [d6PlaneEmb_inl_two]; rfl

theorem d6PlaneEmb_v4_inl_three (a b c d : ZMod 2) :
    d6PlaneEmb (d6PlaneV4 a b c d) (Sum.inl 3) = b := by
  rw [d6PlaneEmb_inl_three]; rfl

theorem d6PlaneEmb_v4_inl_four (a b c d : ZMod 2) :
    d6PlaneEmb (d6PlaneV4 a b c d) (Sum.inl 4) = 0 := by
  rw [d6PlaneEmb_inl_four]

theorem d6PlaneEmb_v4_inl_five (a b c d : ZMod 2) :
    d6PlaneEmb (d6PlaneV4 a b c d) (Sum.inl 5) = 0 := by
  rw [d6PlaneEmb_inl_five]

theorem d6PlaneEmb_v4_inr_zero (a b c d : ZMod 2) :
    d6PlaneEmb (d6PlaneV4 a b c d) (Sum.inr 0) = 0 := by
  rw [d6PlaneEmb_inr_zero]

theorem d6PlaneEmb_v4_inr_one (a b c d : ZMod 2) :
    d6PlaneEmb (d6PlaneV4 a b c d) (Sum.inr 1) = 0 := by
  rw [d6PlaneEmb_inr_one]

theorem d6PlaneEmb_v4_inr_two (a b c d : ZMod 2) :
    d6PlaneEmb (d6PlaneV4 a b c d) (Sum.inr 2) = c := by
  rw [d6PlaneEmb_inr_two]; rfl

theorem d6PlaneEmb_v4_inr_three (a b c d : ZMod 2) :
    d6PlaneEmb (d6PlaneV4 a b c d) (Sum.inr 3) = d := by
  rw [d6PlaneEmb_inr_three]; rfl

theorem d6PlaneEmb_v4_inr_four (a b c d : ZMod 2) :
    d6PlaneEmb (d6PlaneV4 a b c d) (Sum.inr 4) = 0 := by
  rw [d6PlaneEmb_inr_four]

theorem d6PlaneEmb_v4_inr_five (a b c d : ZMod 2) :
    d6PlaneEmb (d6PlaneV4 a b c d) (Sum.inr 5) = 0 := by
  rw [d6PlaneEmb_inr_five]

abbrev d6InPair {M : Type*} [Zero M] [Add M] (u v x : M) : Prop :=
  x = 0 ∨ x = u ∨ x = v ∨ x = u + v

instance d6InPair_decidable {M : Type*} [Zero M] [Add M] [DecidableEq M]
    (u v x : M) : Decidable (d6InPair u v x) :=
  inferInstanceAs (Decidable (x = 0 ∨ x = u ∨ x = v ∨ x = u + v))

abbrev d6Pres (u v : Fin 4 → ZMod 2)
    (g : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) : Prop :=
  d6InPair u v (g u) ∧ d6InPair u v (g v)

instance d6Pres_decidable (u v : Fin 4 → ZMod 2)
    (g : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) : Decidable (d6Pres u v g) :=
  inferInstanceAs (Decidable (d6InPair u v (g u) ∧ d6InPair u v (g v)))

theorem d6mem_span_pair {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {u v x : M} :
    x ∈ Submodule.span (ZMod 2) ({u, v} : Set M) ↔ d6InPair u v x := by
  have h2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    rcases h2 a with rfl | rfl <;> rcases h2 b with rfl | rfl <;> simp [d6InPair]
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, 0, by simp⟩
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
    · exact ⟨1, 1, by simp⟩

theorem d6InPair_map {M N : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    [AddCommGroup N] [Module (ZMod 2) N] {u v x : M} (f : M →ₗ[ZMod 2] N)
    (h : d6InPair u v x) : d6InPair (f u) (f v) (f x) := by
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl (map_zero f)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (by rw [map_add])))

theorem d6InPair_emb_iff {u v z : Fin 4 → ZMod 2} :
    d6InPair (d6PlaneEmb u) (d6PlaneEmb v) (d6PlaneEmb z) ↔ d6InPair u v z := by
  constructor
  · rintro (h | h | h | h)
    · exact Or.inl (d6PlaneEmb_injective (by rw [h, map_zero]))
    · exact Or.inr (Or.inl (d6PlaneEmb_injective h))
    · exact Or.inr (Or.inr (Or.inl (d6PlaneEmb_injective h)))
    · exact Or.inr (Or.inr (Or.inr (d6PlaneEmb_injective (by rw [h, map_add]))))
  · intro h
    exact d6InPair_map d6PlaneEmb h

theorem d6span_pair_eq_of {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    {u v u' v' : M} (h1 : d6InPair u' v' u) (h2 : d6InPair u' v' v)
    (h3 : d6InPair u v u') (h4 : d6InPair u v v') :
    Submodule.span (ZMod 2) ({u, v} : Set M) = Submodule.span (ZMod 2) ({u', v'} : Set M) := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact d6mem_span_pair.mpr h1
    · exact d6mem_span_pair.mpr h2
  · rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact d6mem_span_pair.mpr h3
    · exact d6mem_span_pair.mpr h4

theorem d6maps_span_pair {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    {u v : M} {f : M →ₗ[ZMod 2] M} (h1 : d6InPair u v (f u)) (h2 : d6InPair u v (f v)) :
    ∀ x ∈ Submodule.span (ZMod 2) ({u, v} : Set M),
      f x ∈ Submodule.span (ZMod 2) ({u, v} : Set M) := by
  have hle : Submodule.span (ZMod 2) ({u, v} : Set M) ≤
      Submodule.comap f (Submodule.span (ZMod 2) ({u, v} : Set M)) := by
    rw [Submodule.span_le]
    intro x hx
    rcases hx with rfl | rfl
    · simpa [d6mem_span_pair] using h1
    · simpa [d6mem_span_pair] using h2
  intro x hx
  exact hle hx

theorem d6span_map_eq_of_preimage {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    {u v u' v' w w' : M} {f : M →ₗ[ZMod 2] M}
    (h1 : f u ∈ Submodule.span (ZMod 2) ({u', v'} : Set M))
    (h2 : f v ∈ Submodule.span (ZMod 2) ({u', v'} : Set M))
    (hw : w ∈ Submodule.span (ZMod 2) ({u, v} : Set M))
    (hw' : w' ∈ Submodule.span (ZMod 2) ({u, v} : Set M))
    (hu' : f w = u') (hv' : f w' = v') :
    (Submodule.span (ZMod 2) ({u, v} : Set M)).map f =
      Submodule.span (ZMod 2) ({u', v'} : Set M) := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.map_span_le]
    intro m hm
    rcases hm with rfl | rfl
    · exact h1
    · exact h2
  · rw [Submodule.span_le]
    intro x hx
    rcases hx with rfl | rfl
    · rw [← hu']
      exact Submodule.mem_map_of_mem hw
    · rw [← hv']
      exact Submodule.mem_map_of_mem hw'

theorem d6maps_span_emb {u v : Fin 4 → ZMod 2}
    {g : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)} {f : V12 ≃ₗ[ZMod 2] V12}
    (hf : ∀ x, f (d6PlaneEmb x) = d6PlaneEmb (g x)) (h : d6Pres u v g) :
    ∀ x ∈ Submodule.span (ZMod 2) ({d6PlaneEmb u, d6PlaneEmb v} : Set V12),
      f x ∈ Submodule.span (ZMod 2) ({d6PlaneEmb u, d6PlaneEmb v} : Set V12) := by
  refine d6maps_span_pair (u := d6PlaneEmb u) (v := d6PlaneEmb v)
    (f := (f : V12 →ₗ[ZMod 2] V12)) ?_ ?_
  · have hfu : (f : V12 →ₗ[ZMod 2] V12) (d6PlaneEmb u) = d6PlaneEmb (g u) := hf u
    rw [hfu]
    exact d6InPair_emb_iff.mpr h.1
  · have hfv : (f : V12 →ₗ[ZMod 2] V12) (d6PlaneEmb v) = d6PlaneEmb (g v) := hf v
    rw [hfv]
    exact d6InPair_emb_iff.mpr h.2

@[expose] noncomputable def d6PlaneB4 : LinearMap.BilinForm (ZMod 2) (Fin 4 → ZMod 2) :=
  LinearMap.BilinForm.comp (QuadraticMap.polarBilin Q12) d6PlaneEmb d6PlaneEmb

theorem d6PlaneB4_apply (x y : Fin 4 → ZMod 2) :
    d6PlaneB4 x y = d6PlaneB x y := by
  rw [d6PlaneB4, LinearMap.BilinForm.comp_apply, QuadraticMap.polarBilin_apply_apply,
    d6PlaneB_emb]

@[expose] noncomputable def d6Perp4 (P : Submodule (ZMod 2) (Fin 4 → ZMod 2)) :
    Submodule (ZMod 2) (Fin 4 → ZMod 2) :=
  d6PlaneB4.orthogonal P

theorem d6mem_perp4_iff {P : Submodule (ZMod 2) (Fin 4 → ZMod 2)} {y : Fin 4 → ZMod 2} :
    y ∈ d6Perp4 P ↔ ∀ x ∈ P, d6PlaneB x y = 0 := by
  rw [d6Perp4, LinearMap.BilinForm.mem_orthogonal_iff]
  simp only [d6PlaneB4_apply]

theorem d6mem_perp4_span_pair {u v y : Fin 4 → ZMod 2} :
    y ∈ d6Perp4 (Submodule.span (ZMod 2) ({u, v} : Set (Fin 4 → ZMod 2))) ↔
      d6PlaneB u y = 0 ∧ d6PlaneB v y = 0 := by
  rw [d6mem_perp4_iff]
  constructor
  · intro h
    exact ⟨h u (Submodule.subset_span (by simp)), h v (Submodule.subset_span (by simp))⟩
  · rintro ⟨hu, hv⟩ x hx
    have hu' : d6PlaneB4 u y = 0 := by rwa [d6PlaneB4_apply]
    have hv' : d6PlaneB4 v y = 0 := by rwa [d6PlaneB4_apply]
    have h : d6PlaneB4 x y = 0 := by
      refine Submodule.span_induction (p := fun x _ => d6PlaneB4 x y = 0) ?_ ?_ ?_ ?_ hx
      · intro x hx
        rcases hx with rfl | rfl
        · exact hu'
        · exact hv'
      · simp
      · intro a b _ _ ha hb
        simp only [map_add, LinearMap.add_apply, ha, hb, add_zero]
      · intro c a _ ha
        simp only [map_smul, LinearMap.smul_apply, ha, smul_zero]
    rwa [d6PlaneB4_apply] at h

theorem d6span_pair_map_emb (u v : Fin 4 → ZMod 2) :
    (Submodule.span (ZMod 2) ({u, v} : Set (Fin 4 → ZMod 2))).map d6PlaneEmb =
      Submodule.span (ZMod 2) ({d6PlaneEmb u, d6PlaneEmb v} : Set V12) := by
  rw [Submodule.map_span]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, (rfl | rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨u, Or.inl rfl, rfl⟩
    · exact ⟨v, Or.inr rfl, rfl⟩

theorem d6perpY2_map (P : Submodule (ZMod 2) (Fin 4 → ZMod 2)) :
    perpY2 (P.map d6PlaneEmb) = (d6Perp4 P).map d6PlaneEmb := by
  ext y
  constructor
  · intro hy
    rw [perpY2, Submodule.mem_inf] at hy
    obtain ⟨hyY, hyo⟩ := hy
    obtain ⟨z, rfl⟩ := (d6mem_Y2_iff y).mp hyY
    refine Submodule.mem_map.mpr ⟨z, ?_, rfl⟩
    rw [d6mem_perp4_iff]
    intro w hw
    have hmem : d6PlaneEmb w ∈ P.map d6PlaneEmb := Submodule.mem_map_of_mem hw
    have hzero := (LinearMap.BilinForm.mem_orthogonal_iff.mp hyo) (d6PlaneEmb w) hmem
    rwa [QuadraticMap.polarBilin_apply_apply, d6PlaneB_emb] at hzero
  · rintro ⟨z, hz, rfl⟩
    rw [perpY2, Submodule.mem_inf]
    refine ⟨(d6mem_Y2_iff _).mpr ⟨z, rfl⟩, ?_⟩
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    rw [Submodule.mem_map] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    rw [QuadraticMap.polarBilin_apply_apply, d6PlaneB_emb]
    exact (d6mem_perp4_iff.mp hz) w hw

theorem d6perpY2_span_pair_emb (u v : Fin 4 → ZMod 2) :
    perpY2 (Submodule.span (ZMod 2) ({d6PlaneEmb u, d6PlaneEmb v} : Set V12)) =
      (d6Perp4 (Submodule.span (ZMod 2) ({u, v} : Set (Fin 4 → ZMod 2)))).map d6PlaneEmb := by
  rw [← d6span_pair_map_emb, d6perpY2_map]

theorem d6Plane_hyp_data (i : Fin 18) :
    d6PlaneQ (d6PlaneU i) = 0 ∧ d6PlaneQ (d6PlaneV i) = 0 ∧
      d6PlaneB (d6PlaneU i) (d6PlaneV i) = 1 := by
  revert i; decide +kernel

theorem d6Plane_exists_index (x y : Fin 4 → ZMod 2) (hx : d6PlaneQ x = 0)
    (hy : d6PlaneQ y = 0) (hb : d6PlaneB x y = 1) :
    ∃ i : Fin 18, d6InPair (d6PlaneU i) (d6PlaneV i) x ∧
      d6InPair (d6PlaneU i) (d6PlaneV i) y ∧
      d6InPair x y (d6PlaneU i) ∧ d6InPair x y (d6PlaneV i) := by
  revert x y
  set_option synthInstance.maxSize 512 in
  decide +kernel

theorem d6Plane_perp_data (i : Fin 18) (y : Fin 4 → ZMod 2) :
    (d6PlaneB (d6PlaneU i) y = 0 ∧ d6PlaneB (d6PlaneV i) y = 0) ↔
      d6InPair (d6PlanePU i) (d6PlanePV i) y := by
  revert i y; decide +kernel

theorem d6Perp4_span_pair_data (i : Fin 18) :
    d6Perp4 (Submodule.span (ZMod 2) ({d6PlaneU i, d6PlaneV i} : Set (Fin 4 → ZMod 2))) =
      Submodule.span (ZMod 2) ({d6PlanePU i, d6PlanePV i} : Set (Fin 4 → ZMod 2)) := by
  ext y
  rw [d6mem_perp4_span_pair, d6mem_span_pair, d6Plane_perp_data]

theorem d6perp_index_data (i : Fin 18) :
    ∃ j : Fin 18, d6InPair (d6PlaneU j) (d6PlaneV j) (d6PlanePU i) ∧
      d6InPair (d6PlaneU j) (d6PlaneV j) (d6PlanePV i) ∧
      d6InPair (d6PlanePU i) (d6PlanePV i) (d6PlaneU j) ∧
      d6InPair (d6PlanePU i) (d6PlanePV i) (d6PlaneV j) := by
  revert i; decide +kernel

theorem d6sigOf_unique_data (i : Fin 18) (A A' B B' : d6PlaneSL) (hA : A ≠ 1) (hA' : A' ≠ 1)
    (h : d6Pres (d6PlaneU i) (d6PlaneV i) (d6PlaneNle B * d6PlaneFle A))
    (h' : d6Pres (d6PlaneU i) (d6PlaneV i) (d6PlaneNle B' * d6PlaneFle A')) :
    A = A' := by
  revert i A A' B B'; decide +kernel

theorem d6sigOf_perp_data (i : Fin 18) (A : d6PlaneSL) (hA : A ≠ 1)
    (h : ∃ B : d6PlaneSL, d6Pres (d6PlaneU i) (d6PlaneV i) (d6PlaneNle B * d6PlaneFle A)) :
    ∃ B' : d6PlaneSL,
      d6Pres (d6PlanePU i) (d6PlanePV i) (d6PlaneNle B' * d6PlaneFle A) := by
  revert i A; decide +kernel

theorem d6node_perp_data (i j : Fin 18) (A : d6PlaneSL) (hA : A ≠ 1)
    (hi : ∃ B : d6PlaneSL, d6Pres (d6PlaneU i) (d6PlaneV i) (d6PlaneNle B * d6PlaneFle A))
    (hj : ∃ B' : d6PlaneSL, d6Pres (d6PlaneU j) (d6PlaneV j) (d6PlaneNle B' * d6PlaneFle A)) :
    ∃ D : d6PlaneSL,
      d6InPair (d6PlanePU j) (d6PlanePV j) (d6PlaneNle D (d6PlaneU i)) ∧
      d6InPair (d6PlanePU j) (d6PlanePV j) (d6PlaneNle D (d6PlaneV i)) ∧
      d6InPair (d6PlaneU i) (d6PlaneV i) (d6PlaneNle D⁻¹ (d6PlanePU j)) ∧
      d6InPair (d6PlaneU i) (d6PlaneV i) (d6PlaneNle D⁻¹ (d6PlanePV j)) := by
  revert i j A; decide +kernel

theorem d6transitive_data (i j : Fin 18) :
    ∃ A B : d6PlaneSL,
      d6InPair (d6PlaneU j) (d6PlaneV j) ((d6PlaneNle B * d6PlaneFle A) (d6PlaneU i)) ∧
      d6InPair (d6PlaneU j) (d6PlaneV j) ((d6PlaneNle B * d6PlaneFle A) (d6PlaneV i)) ∧
      d6InPair (d6PlaneU i) (d6PlaneV i) ((d6PlaneFle A⁻¹ * d6PlaneNle B⁻¹) (d6PlaneU j)) ∧
      d6InPair (d6PlaneU i) (d6PlaneV i) ((d6PlaneFle A⁻¹ * d6PlaneNle B⁻¹) (d6PlaneV j)) := by
  revert i j; decide +kernel

theorem d6IsHypPlane_iff (P : Submodule (ZMod 2) V12) :
    IsHypPlane P ↔ ∃ i : Fin 18, P = Submodule.span (ZMod 2)
      ({d6PlaneEmb (d6PlaneU i), d6PlaneEmb (d6PlaneV i)} : Set V12) := by
  constructor
  · rintro ⟨hPY, u, u', hP, hu, hu', hb⟩
    have huY : u ∈ Y2 := hPY (hP ▸ Submodule.subset_span (by simp))
    have hu'Y : u' ∈ Y2 := hPY (hP ▸ Submodule.subset_span (by simp))
    obtain ⟨x, rfl⟩ := (d6mem_Y2_iff u).mp huY
    obtain ⟨y, rfl⟩ := (d6mem_Y2_iff u').mp hu'Y
    rw [d6PlaneQ_emb] at hu hu'
    rw [d6PlaneB_emb] at hb
    obtain ⟨i, h1, h2, h3, h4⟩ := d6Plane_exists_index x y hu hu' hb
    refine ⟨i, ?_⟩
    rw [hP]
    exact d6span_pair_eq_of (d6InPair_emb_iff.mpr h1) (d6InPair_emb_iff.mpr h2)
      (d6InPair_emb_iff.mpr h3) (d6InPair_emb_iff.mpr h4)
  · rintro ⟨i, rfl⟩
    have h := d6Plane_hyp_data i
    refine ⟨?_, d6PlaneEmb (d6PlaneU i), d6PlaneEmb (d6PlaneV i), rfl,
      (d6PlaneQ_emb _).trans h.1, (d6PlaneQ_emb _).trans h.2.1,
      (d6PlaneB_emb _ _).trans h.2.2⟩
    rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact d6PlaneEmb_mem_Y2 _
    · exact d6PlaneEmb_mem_Y2 _

end CFSG.StandardType.FrameRoute.FS81.D6M
