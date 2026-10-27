module

public import CFSG.Quasithin.EmptyFaithful.SzN31SmD6HeisModel
public import CFSG.Quasithin.EmptyFaithful.SzN31CntLinB
public import CFSG.Quasithin.Background.G11Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN31

namespace SmD6Heis

open CFSG.Quasithin.G11 CntLin

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

structure PtRel (x y z : GLV V) : Prop where
  xy : ∀ w, x (y w) = z (y (x w))
  zx : ∀ w, z (x w) = x (z w)
  zy : ∀ w, z (y w) = y (z w)
  z2 : ∀ w, z (z w) = z w + w
  x3 : ∀ w, x (x (x w)) = w
  y3 : ∀ w, y (y (y w)) = w
  z3 : ∀ w, z (z (z w)) = w

theorem apply_cube {e : GLV V} (he3 : e ^ 3 = 1) (w : V) : e (e (e w)) = w := by
  have := congrArg (fun f : GLV V => f w) he3
  simpa [pow_succ] using this

theorem sq_add_add_eq_zero' {e : GLV V} (he3 : e ^ 3 = 1) (hfpf : ∀ v, e v = v → v = 0)
    (v : V) : e (e v) + e v + v = 0 := by
  apply hfpf
  rw [map_add, map_add, apply_cube he3]
  abel

theorem sq_eq_of_add_add_eq_zero' {e : GLV V} (h : ∀ v, e (e v) + e v + v = 0) (v : V) :
    e (e v) = e v + v := by
  have := h v
  calc e (e v) = -(e v + v) := eq_neg_of_add_eq_zero_left (by rwa [add_assoc] at this)
    _ = e v + v := zmod2_neg _

theorem ptRel_of_group {Pb : Subgroup (GLV V)}
    (hirr : ∀ U : Submodule (ZMod 2) V, Invariant Pb U → U = ⊥ ∨ U = ⊤)
    {x y z : GLV V} (hxP : x ∈ Pb) (hyP : y ∈ Pb) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) (hzc : ∀ g ∈ Pb, g * z = z * g)
    (hxy : x * y = z * y * x) : PtRel x y z := by
  have hfix : fixSp V z ⊤ = ⊥ := by
    have hinv : Invariant Pb (fixSp V z ⊤) := fun g hg u hu =>
      fixSp_invariant (hzc g hg) (fun _ _ => Submodule.mem_top) u hu
    rcases hirr _ hinv with h | h
    · exact h
    · exfalso
      apply hz1
      ext u
      have : u ∈ fixSp V z ⊤ := by rw [h]; exact Submodule.mem_top
      exact (mem_fixSp.1 this).2
  have hfpf : ∀ v, z v = v → v = 0 := fun v hv => by
    have : v ∈ fixSp V z ⊤ := mem_fixSp.2 ⟨Submodule.mem_top, hv⟩
    rw [hfix] at this
    exact (Submodule.mem_bot (ZMod 2)).1 this
  refine ⟨fun w => ?_, fun w => ?_, fun w => ?_, fun w => ?_, apply_cube hx3, apply_cube hy3,
    apply_cube hz3⟩
  · have := DFunLike.congr_fun hxy w
    simpa using this
  · exact (comm_apply (hzc x hxP) w).symm
  · exact (comm_apply (hzc y hyP) w).symm
  · exact sq_eq_of_add_add_eq_zero' (sq_add_add_eq_zero' hz3 hfpf) w

section Fixed

variable {x y z : GLV V} (h : PtRel x y z)

include h in
theorem PtRel.k1 (t : V) : y (y (x (y t))) = z (x t) := by
  simp only [h.xy, h.zy, h.zx, h.y3]

include h in
theorem PtRel.k2 (t : V) : y (y (x (x (y t)))) = z (z (x (x t))) := by
  simp only [h.xy, h.zy, h.zx, h.y3]

include h in
theorem PtRel.k3 (t : V) : y (x (y (y t))) = z (z (x t)) := by
  simp only [h.xy, h.zy, h.zx, h.y3]

include h in
theorem PtRel.k4 (t : V) : y (x (x (y (y t)))) = z (x (x t)) := by
  simp only [h.xy, h.zy, h.zx, h.y3, h.z3]

include h in
theorem PtRel.exists_fixed_vector [Nontrivial V] : ∃ v : V, v ≠ 0 ∧ x v = v := by
  by_contra hcon
  push Not at hcon
  have h0 : ∀ v, x v = v → v = 0 := fun v hv => by_contra fun hne => hcon v hne hv
  have E0 : ∀ t : V, t + x t + x (x t) = 0 := by
    intro t
    apply h0
    rw [map_add, map_add, h.x3]
    abel
  have E1 : ∀ t : V, t + z (x t) + z (z (x (x t))) = 0 := by
    intro t
    have := congrArg (fun s => y (y s)) (E0 (y t))
    simp only [map_add, map_zero, h.y3, h.k1, h.k2] at this
    exact this
  have E2 : ∀ t : V, t + z (z (x t)) + z (x (x t)) = 0 := by
    intro t
    have := congrArg (fun s => y s) (E0 (y (y t)))
    simp only [map_add, map_zero, h.y3, h.k3, h.k4] at this
    exact this
  have hall : ∀ t : V, t = 0 := by
    intro t
    have e : t = (t + x t + x (x t)) + (t + z (x t) + z (z (x (x t)))) +
        (t + z (z (x t)) + z (x (x t))) := by
      rw [h.z2 (x t), h.z2 (x (x t))]
      have e' : (t + x t + x (x t)) + (t + z (x t) + (z (x (x t)) + x (x t))) +
          (t + (z (x t) + x t) + z (x (x t))) = (t + t + t) + (x t + x t) + (x (x t) + x (x t)) +
          (z (x t) + z (x t)) + (z (x (x t)) + z (x (x t))) := by abel
      rw [e', zmod2_add_self (x t), zmod2_add_self (x (x t)), zmod2_add_self (z (x t)),
        zmod2_add_self (z (x (x t))), zmod2_add_self t]
      simp
    rw [e, E0 t, E1 t, E2 t]
    simp
  obtain ⟨w, hw⟩ := exists_ne (0 : V)
  exact hw (hall w)

end Fixed

section Columns

variable {x y z : GLV V} (h : PtRel x y z) {v : V}

@[expose] def vecs (y z : GLV V) (v : V) : Fin 6 → V :=
  ![v, z v, y v, z (y v), y (y v), z (y (y v))]

include h in
theorem PtRel.x_col1 (hv : x v = v) : x (z v) = z v := by
  rw [← h.zx, hv]

include h in
theorem PtRel.x_col2 (hv : x v = v) : x (y v) = z (y v) := by
  rw [h.xy, hv]

include h in
theorem PtRel.x_col3 (hv : x v = v) : x (z (y v)) = z (y v) + y v := by
  rw [← h.zx, h.xy, hv, h.z2]

include h in
theorem PtRel.x_col4' (hv : x v = v) : x (y (y v)) = z (z (y (y v))) := by
  rw [h.xy, h.xy, hv, ← h.zy]

include h in
theorem PtRel.x_col4 (hv : x v = v) : x (y (y v)) = z (y (y v)) + y (y v) := by
  rw [h.x_col4' hv, h.z2]

include h in
theorem PtRel.x_col5 (hv : x v = v) : x (z (y (y v))) = y (y v) := by
  rw [← h.zx, h.x_col4' hv, h.z3]

include h in
theorem PtRel.cols_x (hv : x v = v) (j : Fin 6) :
    x (vecs y z v j) = ∑ i, mX i j • vecs y z v i := by
  fin_cases j
  · simp [vecs, mX, Fin.sum_univ_succ, hv]
  · simp [vecs, mX, Fin.sum_univ_succ, h.x_col1 hv]
  · simp [vecs, mX, Fin.sum_univ_succ, h.x_col2 hv]
  · simp [vecs, mX, Fin.sum_univ_succ, h.x_col3 hv, add_comm]
  · simp [vecs, mX, Fin.sum_univ_succ, h.x_col4 hv, add_comm]
  · simp [vecs, mX, Fin.sum_univ_succ, h.x_col5 hv]

include h in
theorem PtRel.cols_y (j : Fin 6) : y (vecs y z v j) = ∑ i, mY i j • vecs y z v i := by
  fin_cases j
  · simp [vecs, mY, Fin.sum_univ_succ]
  · simp [vecs, mY, Fin.sum_univ_succ, ← h.zy]
  · simp [vecs, mY, Fin.sum_univ_succ]
  · simp [vecs, mY, Fin.sum_univ_succ, ← h.zy]
  · simp [vecs, mY, Fin.sum_univ_succ, h.y3]
  · simp [vecs, mY, Fin.sum_univ_succ, ← h.zy, h.y3]

include h in
theorem PtRel.cols_z (j : Fin 6) : z (vecs y z v j) = ∑ i, mZ i j • vecs y z v i := by
  fin_cases j
  · simp [vecs, mZ, Fin.sum_univ_succ]
  · simp [vecs, mZ, Fin.sum_univ_succ, h.z2, add_comm]
  · simp [vecs, mZ, Fin.sum_univ_succ]
  · simp [vecs, mZ, Fin.sum_univ_succ, h.z2, add_comm]
  · simp [vecs, mZ, Fin.sum_univ_succ]
  · simp [vecs, mZ, Fin.sum_univ_succ, h.z2, add_comm]

end Columns

section Span

theorem inv_apply_mem_of_finite [Finite V] {g : GLV V} {U : Submodule (ZMod 2) V}
    (hg : ∀ u ∈ U, g u ∈ U) (u : V) (hu : u ∈ U) : g⁻¹ u ∈ U := by
  have hinj : Function.Injective (fun w : U => (⟨g w, hg w w.2⟩ : U)) := fun a b hab => by
    apply Subtype.ext
    exact g.injective (congrArg Subtype.val hab)
  obtain ⟨w, hw⟩ := Finite.surjective_of_injective hinj ⟨u, hu⟩
  have hgw : g (w : V) = u := congrArg Subtype.val hw
  have h2 : g⁻¹ u = w := by
    rw [← hgw]
    exact g.symm_apply_apply _
  rw [h2]
  exact w.2

theorem apply_mem_of_mem_closure [Finite V] {S : Set (GLV V)} {U : Submodule (ZMod 2) V}
    (hS : ∀ g ∈ S, ∀ u ∈ U, g u ∈ U) {g : GLV V} (hg : g ∈ Subgroup.closure S) :
    ∀ u ∈ U, g u ∈ U := by
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact hS g hg
  | one => intro u hu; simpa using hu
  | mul g₁ g₂ _ _ h₁ h₂ => intro u hu; rw [LinearEquiv.mul_apply]; exact h₁ _ (h₂ u hu)
  | inv g _ hg => exact inv_apply_mem_of_finite hg

theorem apply_mem_span_of_cols {g : GLV V} {vs : Fin 6 → V} {M : M6}
    (hg : ∀ j, g (vs j) = ∑ i, M i j • vs i) :
    ∀ u ∈ Submodule.span (ZMod 2) (Set.range vs),
      g u ∈ Submodule.span (ZMod 2) (Set.range vs) := by
  intro u hu
  have hle : Submodule.map (g : V →ₗ[ZMod 2] V) (Submodule.span (ZMod 2) (Set.range vs)) ≤
      Submodule.span (ZMod 2) (Set.range vs) := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    show g (vs j) ∈ _
    rw [hg j]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact hle ⟨u, hu, rfl⟩

end Span

section BasisExists

variable {x y z : GLV V}

theorem exists_basis [Finite V] (hd : Module.finrank (ZMod 2) V = 6) {Pb : Subgroup (GLV V)}
    (hirr : ∀ U : Submodule (ZMod 2) V, Invariant Pb U → U = ⊥ ∨ U = ⊤)
    (h : PtRel x y z) (hgen : ∀ g ∈ Pb, g ∈ Subgroup.closure ({x, y} : Set (GLV V))) :
    ∃ B : Module.Basis (Fin 6) (ZMod 2) V, LinearMap.toMatrix B B (x : V →ₗ[ZMod 2] V) = mX ∧
      LinearMap.toMatrix B B (y : V →ₗ[ZMod 2] V) = mY ∧
      LinearMap.toMatrix B B (z : V →ₗ[ZMod 2] V) = mZ := by
  have hnt : Nontrivial V :=
    Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨v, hv0, hv⟩ := h.exists_fixed_vector
  have hxU := apply_mem_span_of_cols (g := x) (h.cols_x hv)
  have hyU := apply_mem_span_of_cols (g := y) (h.cols_y (v := v))
  have hinv : Invariant Pb (Submodule.span (ZMod 2) (Set.range (vecs y z v))) :=
    fun g hg u hu => apply_mem_of_mem_closure (S := {x, y}) (by
      rintro g (rfl | rfl)
      · exact hxU
      · exact hyU) (hgen g hg) u hu
  have htop : Submodule.span (ZMod 2) (Set.range (vecs y z v)) = ⊤ := by
    rcases hirr _ hinv with h0 | h1
    · exfalso
      have hvm : v ∈ Submodule.span (ZMod 2) (Set.range (vecs y z v)) :=
        Submodule.subset_span ⟨0, rfl⟩
      rw [h0] at hvm
      exact hv0 ((Submodule.mem_bot (ZMod 2)).1 hvm)
    · exact h1
  let B : Module.Basis (Fin 6) (ZMod 2) V := basisOfTopLeSpanOfCardEqFinrank (vecs y z v)
    (le_of_eq htop.symm) (by simp [hd])
  have hB : ∀ i, B i = vecs y z v i := fun i => by simp [B]
  have key : ∀ (g : GLV V) (M : M6), (∀ j, g (vecs y z v j) = ∑ i, M i j • vecs y z v i) →
      LinearMap.toMatrix B B (g : V →ₗ[ZMod 2] V) = M := by
    intro g M hg
    ext i j
    have h1 : ∑ i', M i' j • vecs y z v i' = ∑ i', M i' j • B i' := by simp [hB]
    rw [LinearMap.toMatrix_apply, hB, LinearEquiv.coe_coe, hg j, h1,
      Module.Basis.repr_sum_self]
  exact ⟨B, key x mX (h.cols_x hv), key y mY h.cols_y, key z mZ h.cols_z⟩

end BasisExists

end SmD6Heis

end CFSG.Quasithin.SzN31
