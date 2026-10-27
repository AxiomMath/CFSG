module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaRootsOrbitAux

public section

namespace CFSG.StandardType.E6QTwo

open Module CFSG.Assembly

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V} {B : LinearMap.BilinForm (ZMod 3) V}

@[expose] def rootReflOrth (y : V) : Set (V ≃ₗ[ZMod 3] V) :=
  {r | ∃ u : V, ∃ hu : B u u = 2, B u y = 0 ∧ r = rootRefl (B := B) u hu}

section Frame

variable {f : Fin 5 → V}

noncomputable def stdFrameRefl (hV : Nat.card V = 3 ^ 5)
    (hf : ∀ i j, B (f i) (f j) = if i = j then 1 else 0) (r : Fin 5 → ZMod 3) :
    V ≃ₗ[ZMod 3] V :=
  if h : r ⬝ᵥ r = 2 then
    rootRefl (B := B) ((frameCoord hV hf).symm r) (by
      rw [frameCoord_form hV hf ((frameCoord hV hf).symm r) ((frameCoord hV hf).symm r),
        LinearEquiv.apply_symm_apply]
      exact h)
  else 1

noncomputable def stdFrameWord (hV : Nat.card V = 3 ^ 5)
    (hf : ∀ i j, B (f i) (f j) = if i = j then 1 else 0) :
    List (Fin 5 → ZMod 3) → V ≃ₗ[ZMod 3] V
  | [] => 1
  | r :: l => stdFrameWord hV hf l * stdFrameRefl hV hf r

theorem stdFrameRefl_apply (hV : Nat.card V = 3 ^ 5)
    (hf : ∀ i j, B (f i) (f j) = if i = j then 1 else 0) {r : Fin 5 → ZMod 3}
    (hr : r ⬝ᵥ r = 2) (u : V) :
    frameCoord hV hf (stdFrameRefl hV hf r u) = stdRefl r (frameCoord hV hf u) := by
  unfold stdFrameRefl
  rw [dif_pos hr, rootRefl_apply, map_sub, map_smul]
  rw [frameCoord_form hV hf ((frameCoord hV hf).symm r) u, LinearEquiv.apply_symm_apply]
  rfl

theorem stdFrameWord_apply (hV : Nat.card V = 3 ^ 5)
    (hf : ∀ i j, B (f i) (f j) = if i = j then 1 else 0) (l : List (Fin 5 → ZMod 3))
    (u : V) (hl : ∀ r ∈ l, r ⬝ᵥ r = 2) :
    frameCoord hV hf (stdFrameWord hV hf l u) = stdWord l (frameCoord hV hf u) := by
  induction l generalizing u with
  | nil => rfl
  | cons r l ih =>
      have hr : r ⬝ᵥ r = 2 := hl r List.mem_cons_self
      have hl' : ∀ r' ∈ l, r' ⬝ᵥ r' = 2 := fun r' hr' =>
        hl r' (List.mem_cons_of_mem r hr')
      change frameCoord hV hf ((stdFrameWord hV hf l * stdFrameRefl hV hf r) u) =
        stdWord (r :: l) (frameCoord hV hf u)
      rw [LinearEquiv.mul_apply, ih (u := stdFrameRefl hV hf r u) hl',
        stdFrameRefl_apply hV hf hr]
      rfl

theorem stdFrameRefl_mem (hV : Nat.card V = 3 ^ 5)
    (hf : ∀ i j, B (f i) (f j) = if i = j then 1 else 0) {y : V}
    (hFy : frameCoord hV hf y = stdY0) {r : Fin 5 → ZMod 3} (hr : r ⬝ᵥ r = 2)
    (hry : r ⬝ᵥ stdY0 = 0) :
    stdFrameRefl hV hf r ∈ Subgroup.closure (rootReflOrth (B := B) y) := by
  refine Subgroup.subset_closure ⟨(frameCoord hV hf).symm r, ?_, ?_, ?_⟩
  · rw [frameCoord_form hV hf ((frameCoord hV hf).symm r) ((frameCoord hV hf).symm r),
      LinearEquiv.apply_symm_apply]
    exact hr
  · rw [frameCoord_form hV hf ((frameCoord hV hf).symm r) y, LinearEquiv.apply_symm_apply,
      hFy]
    exact hry
  · unfold stdFrameRefl
    rw [dif_pos hr]

theorem stdFrameWord_mem (hV : Nat.card V = 3 ^ 5)
    (hf : ∀ i j, B (f i) (f j) = if i = j then 1 else 0) {y : V}
    (hFy : frameCoord hV hf y = stdY0) (l : List (Fin 5 → ZMod 3))
    (hl : ∀ r ∈ l, r ⬝ᵥ r = 2 ∧ r ⬝ᵥ stdY0 = 0) :
    stdFrameWord hV hf l ∈ Subgroup.closure (rootReflOrth (B := B) y) := by
  induction l with
  | nil => exact Subgroup.one_mem _
  | cons r l ih =>
      have hr : r ⬝ᵥ r = 2 ∧ r ⬝ᵥ stdY0 = 0 := hl r List.mem_cons_self
      have hl' : ∀ r' ∈ l, r' ⬝ᵥ r' = 2 ∧ r' ⬝ᵥ stdY0 = 0 := fun r' hr' =>
        hl r' (List.mem_cons_of_mem r hr')
      change stdFrameWord hV hf l * stdFrameRefl hV hf r ∈ _
      exact Subgroup.mul_mem _ (ih hl') (stdFrameRefl_mem hV hf hFy hr.1 hr.2)

theorem exists_stdFrameWord_T30 (hV : Nat.card V = 3 ^ 5)
    (hf : ∀ i j, B (f i) (f j) = if i = j then 1 else 0) {y : V}
    (hFy : frameCoord hV hf y = stdY0) {v : V} (hv : B v v = 2) (hvy : B v y = 0) :
    ∃ g ∈ Subgroup.closure (rootReflOrth (B := B) y),
      g ((frameCoord hV hf).symm stdB30) = v := by
  have hvT : frameCoord hV hf v ∈ stdT30 := by
    refine stdT30_spec (frameCoord hV hf v) ?_ ?_
    · exact (frameCoord_form hV hf v v).symm.trans hv
    · rw [← hFy, ← frameCoord_form hV hf v y]
      exact hvy
  obtain ⟨l, hlW, hl⟩ := stdW30_apply (frameCoord hV hf v) hvT
  let g := stdFrameWord hV hf l
  have hgmem : g ∈ Subgroup.closure (rootReflOrth (B := B) y) :=
    stdFrameWord_mem hV hf hFy l fun r hr =>
      stdT30_norm r (stdW30_roots l hlW r hr)
  have hcoord : frameCoord hV hf (g ((frameCoord hV hf).symm stdB30)) =
      frameCoord hV hf v := by
    rw [stdFrameWord_apply hV hf l ((frameCoord hV hf).symm stdB30) fun r hr =>
      (stdT30_norm r (stdW30_roots l hlW r hr)).1,
      LinearEquiv.apply_symm_apply, hl]
  exact ⟨g, hgmem, (frameCoord hV hf).injective hcoord⟩

theorem exists_stdFrameWord_T20 (hV : Nat.card V = 3 ^ 5)
    (hf : ∀ i j, B (f i) (f j) = if i = j then 1 else 0) {y : V}
    (hFy : frameCoord hV hf y = stdY0) {v : V} (hv : B v v = 2) (hvy : B v y = 1)
    (hvne : v ≠ -y) :
    ∃ g ∈ Subgroup.closure (rootReflOrth (B := B) y),
      g ((frameCoord hV hf).symm stdB20) = v := by
  have hvT : frameCoord hV hf v ∈ stdT20 := by
    refine stdT20_mem ?_ ?_ ?_
    · exact (frameCoord_form hV hf v v).symm.trans hv
    · rw [← hFy, ← frameCoord_form hV hf v y]
      exact hvy
    · intro h
      apply hvne
      apply (frameCoord hV hf).injective
      rw [map_neg, hFy]
      exact h
  obtain ⟨l, hlW, hl⟩ := stdW20_apply (frameCoord hV hf v) hvT
  let g := stdFrameWord hV hf l
  have hgmem : g ∈ Subgroup.closure (rootReflOrth (B := B) y) :=
    stdFrameWord_mem hV hf hFy l fun r hr =>
      stdT30_norm r (stdW20_roots l hlW r hr)
  have hcoord : frameCoord hV hf (g ((frameCoord hV hf).symm stdB20)) =
      frameCoord hV hf v := by
    rw [stdFrameWord_apply hV hf l ((frameCoord hV hf).symm stdB20) fun r hr =>
      (stdT30_norm r (stdW20_roots l hlW r hr)).1,
      LinearEquiv.apply_symm_apply, hl]
  exact ⟨g, hgmem, (frameCoord hV hf).injective hcoord⟩

end Frame

theorem exists_mem_closure_rootRefl_apply_eq_of_dot_one
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    {y v w : V} (hy : B y y = 2) (hw : B w w = 2) (hwy : B w y = 1) (hwne : w ≠ -y)
    (hv : B v v = 2) (hvy : B v y = 1) (hvne : v ≠ -y) :
    ∃ g ∈ Subgroup.closure (rootReflOrth (B := B) y), g w = v := by
  obtain ⟨f, hf, hf01⟩ := exists_frame_add_eq_of_root hP hV hB hα hy
  have hFy : frameCoord hV hf y = stdY0 := by
    rw [← hf01, map_add, frameCoord_frame hV hf 0, frameCoord_frame hV hf 1]
    exact stdY0_eq.symm
  obtain ⟨a, haW, haw⟩ := exists_stdFrameWord_T20 hV hf hFy (v := w) hw hwy hwne
  obtain ⟨b, hbW, hbv⟩ := exists_stdFrameWord_T20 hV hf hFy (v := v) hv hvy hvne
  refine ⟨b * a⁻¹, Subgroup.mul_mem _ hbW (Subgroup.inv_mem _ haW), ?_⟩
  have hinv : a⁻¹ w = (frameCoord hV hf).symm stdB20 := by
    rw [LinearEquiv.coe_inv]
    apply a.injective
    rw [LinearEquiv.apply_symm_apply, haw]
  rw [LinearEquiv.mul_apply, hinv, hbv]

theorem e6Weyl_le_closure_insert_of_one
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    {y w : V} (hy : B y y = 2) (hw : B w w = 2) (hwy : B w y = 1) (hwne : w ≠ -y) :
    e6Weyl hα ≤ Subgroup.closure (insert (rootRefl (B := B) w hw)
      (rootReflOrth (B := B) y)) := by
  classical
  let W := Subgroup.closure (rootReflOrth (B := B) y)
  let H := Subgroup.closure (insert (rootRefl (B := B) w hw) (rootReflOrth (B := B) y))
  have hWH : W ≤ H := Subgroup.closure_mono (Set.subset_insert _ _)
  have hH_e6 : H ≤ e6Weyl hα := by
    change Subgroup.closure (insert (rootRefl (B := B) w hw) (rootReflOrth (B := B) y)) ≤
      e6Weyl hα
    rw [Subgroup.closure_le]
    intro g hg
    rcases Set.mem_insert_iff.mp hg with rfl | hgS
    · exact rootRefl_mem_e6Weyl hP hV hB hα hw
    · rcases hgS with ⟨u, hu, huy, rfl⟩
      exact rootRefl_mem_e6Weyl hP hV hB hα hu
  have isomH : ∀ g ∈ H, ∀ a b, B (g a) (g b) = B a b := fun g hg =>
    bilinForm_apply_e6Weyl hP hV hB hα (hH_e6 hg)
  have hwH : rootRefl (B := B) w hw ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
  have hstep : ∀ (z : V) (hz : B z z = 2), B z y = 1 → z ≠ -y →
      rootRefl (B := B) z hz ∈ H := by
    intro z hz hzy hzne
    obtain ⟨k, hkW, hkw⟩ := exists_mem_closure_rootRefl_apply_eq_of_dot_one hP hV hB hα
      hy hw hwy hwne hz hzy hzne
    have hkH : k ∈ H := hWH hkW
    have hconj := rootRefl_conj_iso (B := B) (g := k) (isomH k hkH) hw
    have hmem : k * rootRefl (B := B) w hw * k⁻¹ ∈ H :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hkH hwH) (Subgroup.inv_mem _ hkH)
    rw [hconj] at hmem
    simpa only [hkw] using hmem
  obtain ⟨f, hf, hf01⟩ := exists_frame_add_eq_of_root hP hV hB hα hy
  have hFy : frameCoord hV hf y = stdY0 := by
    rw [← hf01, map_add, frameCoord_frame hV hf 0, frameCoord_frame hV hf 1]
    exact stdY0_eq.symm
  have hwT20 : frameCoord hV hf w ∈ stdT20 := by
    refine stdT20_mem ?_ ?_ ?_
    · exact (frameCoord_form hV hf w w).symm.trans hw
    · rw [← hFy, ← frameCoord_form hV hf w y]
      exact hwy
    · intro h
      apply hwne
      apply (frameCoord hV hf).injective
      rw [map_neg, hFy]
      exact h
  obtain ⟨hzT, hzrefl⟩ := stdT20_step (frameCoord hV hf w) hwT20
  have hzcoord : frameCoord hV hf (y - w) = stdY0 - frameCoord hV hf w := by
    rw [map_sub, hFy]
    rfl
  have hzT' : frameCoord hV hf (y - w) ∈ stdT20 := by
    rw [hzcoord]
    exact hzT
  have hznorm : B (y - w) (y - w) = 2 :=
    (frameCoord_form hV hf (y - w) (y - w)).trans (stdT20_norm _ hzT').1
  have hzdot : B (y - w) y = 1 := by
    rw [frameCoord_form hV hf (y - w) y, hFy]
    exact (stdT20_norm _ hzT').2.1
  have hzne : y - w ≠ -y := by
    intro h
    have hc : frameCoord hV hf (y - w) = -stdY0 := by
      rw [h, map_neg, hFy]
    exact (stdT20_norm _ hzT').2.2 hc
  have hrootw_z : rootRefl (B := B) w hw (y - w) = y := by
    apply (frameCoord hV hf).injective
    have hcoord : frameCoord hV hf (rootRefl (B := B) w hw (y - w)) = stdY0 := by
      rw [frameCoord_rootRefl, hzcoord]
      change stdRefl (frameCoord hV hf w) (stdY0 - frameCoord hV hf w) = stdY0
      exact hzrefl
    rw [hcoord, hFy]
  have hzH : rootRefl (B := B) (y - w) hznorm ∈ H := hstep (y - w) hznorm hzdot hzne
  have hyH : rootRefl (B := B) y hy ∈ H := by
    have hconj := rootRefl_conj_iso (B := B) (g := rootRefl (B := B) w hw)
      (rootRefl_isometry hP hV hB hα hw) hznorm
    have hmem : rootRefl (B := B) w hw * rootRefl (B := B) (y - w) hznorm *
        (rootRefl (B := B) w hw)⁻¹ ∈ H :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hwH hzH) (Subgroup.inv_mem _ hwH)
    rw [hconj] at hmem
    simpa only [hrootw_z] using hmem
  have hroots : ∀ (r : V) (hr : B r r = 2), rootRefl (B := B) r hr ∈ H := by
    intro r hr
    rcases (by decide : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2) (B r y) with h0 | h1 | h2
    · exact Subgroup.subset_closure
        (Set.mem_insert_iff.mpr (Or.inr ⟨r, hr, h0, rfl⟩))
    · by_cases hry : r = -y
      · have : rootRefl (B := B) r hr = rootRefl (B := B) y hy := by
          simpa [hry] using rootRefl_neg (B := B) y hy
        rw [this]
        exact hyH
      · exact hstep r hr h1 hry
    · by_cases hry : r = y
      · have : rootRefl (B := B) r hr = rootRefl (B := B) y hy := by
          simpa [hry]
        rw [this]
        exact hyH
      · have hz : B (-r) (-r) = 2 := by
          rw [LinearMap.BilinForm.neg_left, LinearMap.BilinForm.neg_right, neg_neg]
          exact hr
        have hzy : B (-r) y = 1 := by
          rw [LinearMap.BilinForm.neg_left, h2]
          decide
        have hzne : -r ≠ -y := by
          intro h
          exact hry (neg_inj.mp h)
        have heq : rootRefl (B := B) r hr = rootRefl (B := B) (-r) hz := by
          simpa using (rootRefl_neg (B := B) r hr).symm
        rw [heq]
        exact hstep (-r) hz hzy hzne
  change Subgroup.closure (Set.range fun i => reflection (hα i)) ≤ H
  rw [Subgroup.closure_le]
  rintro g ⟨i, rfl⟩
  change reflection (hα i) ∈ H
  have hsimple : reflection (hα i) = rootRefl (B := B) (h i)
      (by rw [hB i (h i), hα i]) := by
    apply LinearEquiv.ext
    intro u
    rw [Module.reflection_apply, rootRefl_apply, hB i u]
  rw [hsimple]
  exact hroots (h i) (by rw [hB i (h i), hα i])

end CFSG.StandardType.E6QTwo

end
