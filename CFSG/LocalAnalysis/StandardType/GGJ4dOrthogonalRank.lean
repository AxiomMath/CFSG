module

public import CFSG.HardMathSupport.Timmesfeld.RootAut.Main

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.RootAut Matrix

variable {τ : Tag}

private def formQ (x y : Fin τ.rank → ℚ) : ℚ :=
  ∑ i, ∑ j, x i * (τ.symmetrizedCartan i j : ℚ) * y j

private theorem formQ_toRat (x y : Fin τ.rank → ℤ) :
    formQ (toRat x) (toRat y) = (iform x y : ℚ) := by
  simp only [formQ, iform, toRat]
  push_cast
  ring

private theorem formQ_add_left (x x' y : Fin τ.rank → ℚ) :
    formQ (x + x') y = formQ x y + formQ x' y := by
  simp only [formQ, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem formQ_comm
    (x y : Fin τ.rank → ℚ) : formQ x y = formQ y x := by
  simp only [formQ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [symmetrizedCartan_symm τ j i]
  ring

private theorem formQ_add_right
    (x y y' : Fin τ.rank → ℚ) :
    formQ x (y + y') = formQ x y + formQ x y' := by
  rw [formQ_comm x (y + y'), formQ_add_left, formQ_comm y x, formQ_comm y' x]

private theorem formQ_smul_left (c : ℚ) (x y : Fin τ.rank → ℚ) :
    formQ (c • x) y = c * formQ x y := by
  simp only [formQ, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem formQ_smul_right
    (c : ℚ) (x y : Fin τ.rank → ℚ) :
    formQ x (c • y) = c * formQ x y := by
  rw [formQ_comm x (c • y), formQ_smul_left, formQ_comm y x]

private theorem formQ_self_pos
    {x : Fin τ.rank → ℚ} (hx : x ≠ 0) : 0 < formQ x x := by
  have hx' : (fun j => (x j : ℝ)) ≠ 0 := fun h =>
    hx (funext fun j => by simpa using congrFun h j)
  have h := (posDef_symmetrizedCartan τ).dotProduct_mulVec_pos hx'
  have heq : star (fun j => (x j : ℝ)) ⬝ᵥ
      ((τ.symmetrizedCartan.map (Int.cast : ℤ → ℝ)) *ᵥ fun j => (x j : ℝ)) =
      (formQ x x : ℝ) := by
    simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.map_apply, formQ, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [heq] at h
  exact_mod_cast h

private theorem formQ_span_span
    {S T : Set (Fin τ.rank → ℤ)}
    (hST : ∀ x ∈ S, ∀ y ∈ T, iform x y = 0) {u v : Fin τ.rank → ℚ}
    (hu : u ∈ Submodule.span ℚ (toRat '' S))
    (hv : v ∈ Submodule.span ℚ (toRat '' T)) : formQ u v = 0 := by
  refine Submodule.span_induction₂ (p := fun u v _ _ => formQ u v = 0) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hu hv
  · rintro x y ⟨x₀, hx₀, rfl⟩ ⟨y₀, hy₀, rfl⟩
    rw [formQ_toRat]
    exact_mod_cast hST x₀ hx₀ y₀ hy₀
  · intro y _
    simp [formQ]
  · intro x _
    simp [formQ]
  · intro x y z _ _ _ hxz hyz
    rw [formQ_add_left, hxz, hyz, add_zero]
  · intro x y z _ _ _ hxy hxz
    rw [formQ_add_right, hxy, hxz, add_zero]
  · intro c x y _ _ hxy
    rw [formQ_smul_left, hxy, mul_zero]
  · intro c x y _ _ hxy
    rw [formQ_smul_right, hxy, mul_zero]

private def spanQ (Ψ : Set (Fin τ.rank → ℤ)) : Submodule ℚ (Fin τ.rank → ℚ) :=
  Submodule.span ℚ (toRat '' Ψ)

private theorem compRank_eq_finrank_spanQ (Ψ : Set (Fin τ.rank → ℤ)) :
    compRank Ψ = Module.finrank ℚ (spanQ Ψ) := rfl

private theorem disjoint_spanQ
    {S T : Set (Fin τ.rank → ℤ)}
    (hST : ∀ x ∈ S, ∀ y ∈ T, iform x y = 0) : Disjoint (spanQ S) (spanQ T) := by
  rw [Submodule.disjoint_def]
  intro u hu hv
  by_contra hne
  have hpos : 0 < formQ u u := formQ_self_pos hne
  have hzero : formQ u u = 0 := formQ_span_span hST hu hv
  exact hpos.ne' hzero

private theorem finrank_sup_eq_add_of_disjoint {p q : Submodule ℚ (Fin τ.rank → ℚ)}
    (h : Disjoint p q) :
    Module.finrank ℚ ↥(p ⊔ q) = Module.finrank ℚ ↥p + Module.finrank ℚ ↥q := by
  have hd := Submodule.finrank_sup_add_finrank_inf_eq p q
  rw [h.eq_bot, finrank_bot, add_zero] at hd
  exact hd

theorem compRank_iUnion_finset_eq_sum
    {ι : Type} [DecidableEq ι] (s : Finset ι) (Ψ : ι → Set (Fin τ.rank → ℤ))
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x ∈ Ψ i, ∀ y ∈ Ψ j, iform x y = 0) :
    compRank (⋃ i ∈ s, Ψ i) = ∑ i ∈ s, compRank (Ψ i) := by
  classical
  have key : ∀ s : Finset ι, ∀ (Ψ : ι → Set (Fin τ.rank → ℤ)),
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x ∈ Ψ i, ∀ y ∈ Ψ j, iform x y = 0) →
      compRank (⋃ i ∈ s, Ψ i) = ∑ i ∈ s, compRank (Ψ i) := by
    intro s
    induction s using Finset.induction with
    | empty =>
        intro Ψ _
        simp [compRank]
    | insert a s ha ih =>
        intro Ψ horth
        have horth_s : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x ∈ Ψ i, ∀ y ∈ Ψ j, iform x y = 0 :=
          fun i hi j hj hij x hx y hy =>
            horth i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij x hx y hy
        have horth_a : ∀ x ∈ Ψ a, ∀ y ∈ (⋃ i ∈ s, Ψ i), iform x y = 0 := by
          intro x hx y hy
          simp only [Set.mem_iUnion, exists_prop] at hy
          obtain ⟨j, hj, hyj⟩ := hy
          have haj : a ≠ j := by rintro rfl; exact ha hj
          exact horth a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj) haj x hx y hyj
        have hspan_insert : spanQ (⋃ i ∈ insert a s, Ψ i) =
            spanQ (Ψ a) ⊔ spanQ (⋃ i ∈ s, Ψ i) := by
          rw [Finset.set_biUnion_insert]
          simp only [spanQ, Set.image_union, Submodule.span_union]
        have hdisj : Disjoint (spanQ (Ψ a)) (spanQ (⋃ i ∈ s, Ψ i)) :=
          disjoint_spanQ horth_a
        have hih := ih Ψ horth_s
        calc compRank (⋃ i ∈ insert a s, Ψ i)
            = Module.finrank ℚ ↥(spanQ (⋃ i ∈ insert a s, Ψ i)) :=
                compRank_eq_finrank_spanQ _
          _ = Module.finrank ℚ ↥(spanQ (Ψ a) ⊔ spanQ (⋃ i ∈ s, Ψ i)) := by rw [hspan_insert]
          _ = Module.finrank ℚ ↥(spanQ (Ψ a)) +
                Module.finrank ℚ ↥(spanQ (⋃ i ∈ s, Ψ i)) :=
                finrank_sup_eq_add_of_disjoint hdisj
          _ = compRank (Ψ a) + compRank (⋃ i ∈ s, Ψ i) := by
                rw [← compRank_eq_finrank_spanQ (Ψ a),
                  ← compRank_eq_finrank_spanQ (⋃ i ∈ s, Ψ i)]
          _ = compRank (Ψ a) + ∑ i ∈ s, compRank (Ψ i) := by rw [hih]
          _ = ∑ i ∈ insert a s, compRank (Ψ i) := by rw [Finset.sum_insert ha]
  exact key s Ψ horth

end CFSG.HardMathSupport.Timmesfeld.LangTorus
