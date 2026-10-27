module

public import CFSG.LocalAnalysis.StandardType.StarFour.BlockDatum
public import CFSG.LocalAnalysis.StandardType.StarFour.FrameNesting

public section

namespace CFSG.StandardType.StarFour

open CFSG.LinearAlgebra.RootGroupSL

variable {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
  [Module.Finite F V]

section Nesting

variable {P P' : Type} [CommGroup P] [CommGroup P']
  {ρ : P →* (V ≃ₗ[F] V)} {ρ' : P' →* (V ≃ₗ[F] V)}

private lemma nest_eq_single_of_coords {r : ℕ} {E : Fin r → Type} [∀ j, Zero (E j)]
    (i : Fin r) (x : ∀ j, E j) (h : ∀ j, j ≠ i → x j = 0) :
    x = Pi.single i (x i) := by
  funext j
  by_cases hj : j = i
  · subst hj
    rw [Pi.single_eq_same]
  · rw [h j hj, Pi.single_eq_of_ne hj]

private noncomputable def nestA (fr : SemiFrame F ρ) (fr' : SemiFrame F ρ') (i : Fin fr.r)
    (i' : Fin fr'.r) (u : Fin (fr.m i) → fr.E i) : Fin (fr'.m i') → fr'.E i' :=
  fr'.Φ (fr.Φ.symm (Pi.single i u)) i'

private noncomputable def nestB (fr : SemiFrame F ρ) (fr' : SemiFrame F ρ') (i : Fin fr.r)
    (i' : Fin fr'.r) (y : Fin (fr'.m i') → fr'.E i') : Fin (fr.m i) → fr.E i :=
  fr.Φ (fr'.Φ.symm (Pi.single i' y)) i

private lemma nestA_add (fr : SemiFrame F ρ) (fr' : SemiFrame F ρ') (i : Fin fr.r)
    (i' : Fin fr'.r) (u v : Fin (fr.m i) → fr.E i) :
    nestA fr fr' i i' (u + v) = nestA fr fr' i i' u + nestA fr fr' i i' v := by
  simp only [nestA, Pi.single_add, map_add, Pi.add_apply]

private lemma nestB_add (fr : SemiFrame F ρ) (fr' : SemiFrame F ρ') (i : Fin fr.r)
    (i' : Fin fr'.r) (y z : Fin (fr'.m i') → fr'.E i') :
    nestB fr fr' i i' (y + z) = nestB fr fr' i i' y + nestB fr fr' i i' z := by
  simp only [nestB, Pi.single_add, map_add, Pi.add_apply]

private lemma nestA_smul (fr : SemiFrame F ρ) (fr' : SemiFrame F ρ') (i : Fin fr.r)
    (i' : Fin fr'.r) (ε : fr'.E i' →ₐ[F] fr.E i)
    (h4 : ∀ (c : fr'.E i') (u : Fin (fr.m i) → fr.E i),
      fr'.Φ (fr.Φ.symm (Pi.single i (ε c • u))) i' =
        c • fr'.Φ (fr.Φ.symm (Pi.single i u)) i')
    (c : fr'.E i') (u : Fin (fr.m i) → fr.E i) :
    nestA fr fr' i i' (ε c • u) = c • nestA fr fr' i i' u :=
  h4 c u

private lemma nestB_smul (fr : SemiFrame F ρ) (fr' : SemiFrame F ρ') (i : Fin fr.r)
    (i' : Fin fr'.r) (ε : fr'.E i' →ₐ[F] fr.E i)
    (h2 : ∀ (c : fr'.E i') (y : Fin (fr'.m i') → fr'.E i'),
      fr.Φ (fr'.Φ.symm (Pi.single i' (c • y))) i =
        ε c • fr.Φ (fr'.Φ.symm (Pi.single i' y)) i)
    (c : fr'.E i') (y : Fin (fr'.m i') → fr'.E i') :
    nestB fr fr' i i' (c • y) = ε c • nestB fr fr' i i' y :=
  h2 c y

private lemma nestSingle (fr : SemiFrame F ρ) (fr' : SemiFrame F ρ') (i : Fin fr.r)
    (i' : Fin fr'.r)
    (h3 : ∀ (u : Fin (fr.m i) → fr.E i) (j : Fin fr'.r), j ≠ i' →
      fr'.Φ (fr.Φ.symm (Pi.single i u)) j = 0)
    (u : Fin (fr.m i) → fr.E i) :
    fr'.Φ (fr.Φ.symm (Pi.single i u)) = Pi.single i' (nestA fr fr' i i' u) :=
  nest_eq_single_of_coords i' _ (fun j hj => h3 u j hj)

private lemma nestB_nestA (fr : SemiFrame F ρ) (fr' : SemiFrame F ρ') (i : Fin fr.r)
    (i' : Fin fr'.r)
    (h3 : ∀ (u : Fin (fr.m i) → fr.E i) (j : Fin fr'.r), j ≠ i' →
      fr'.Φ (fr.Φ.symm (Pi.single i u)) j = 0)
    (u : Fin (fr.m i) → fr.E i) :
    nestB fr fr' i i' (nestA fr fr' i i' u) = u := by
  have h := nestSingle fr fr' i i' h3 u
  simp only [nestB]
  rw [← h, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply, Pi.single_eq_same]

private lemma nestB_coord (fr : SemiFrame F ρ) (fr' : SemiFrame F ρ') (i : Fin fr.r)
    (i' : Fin fr'.r)
    (h1 : ∀ j : Fin fr'.r, j ≠ i' → ∀ y : Fin (fr'.m j) → fr'.E j,
      fr.Φ (fr'.Φ.symm (Pi.single j y)) i = 0)
    (v : V) :
    nestB fr fr' i i' (fr'.Φ v i') = fr.Φ v i := by
  have hsum : v = ∑ j : Fin fr'.r, fr'.Φ.symm (Pi.single j (fr'.Φ v j)) := by
    apply fr'.Φ.injective
    rw [map_sum]
    simp only [LinearEquiv.apply_symm_apply]
    exact (LinearMap.sum_single_apply (fun j => Fin (fr'.m j) → fr'.E j) (fr'.Φ v)).symm
  have hone : fr.Φ v i =
      ∑ j : Fin fr'.r, fr.Φ (fr'.Φ.symm (Pi.single j (fr'.Φ v j))) i := by
    conv_lhs => rw [hsum]
    rw [map_sum, Finset.sum_apply]
  rw [hone, Finset.sum_eq_single i']
  · rfl
  · intro j _ hj
    exact h1 j hj (fr'.Φ v j)
  · intro hi
    exact absurd (Finset.mem_univ i') hi

private lemma nest_update_add_single {ι : Type*} [DecidableEq ι] {M : ι → Type*}
    [∀ j, AddCommMonoid (M j)] (f : ∀ j, M j) (i : ι) (y : M i) :
    Function.update f i (f i + y) = f + Pi.single i y := by
  funext j
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self, Pi.add_apply, Pi.single_eq_same]
  · rw [Function.update_of_ne hj, Pi.add_apply, Pi.single_eq_of_ne hj, add_zero]

end Nesting

theorem exists_blockDatum {P P' : Type} [CommGroup P] [CommGroup P']
    (η : P →* SpecialLinearGroup F V) (η' : P' →* SpecialLinearGroup F V) {g : P} {g' : P'}
    (hg' : ∀ x : P', x ∈ Subgroup.zpowers g') (hgg : η' g' = η g)
    (fr : SemiFrame F (groupRep η)) (fr' : SemiFrame F (groupRep η')) (i : Fin fr.r)
    (hm : 2 ≤ fr.m i) (i' : Fin fr'.r) (ε : fr'.E i' →ₐ[F] fr.E i)
    (h3 : ∀ (u : Fin (fr.m i) → fr.E i) (j : Fin fr'.r), j ≠ i' →
      fr'.Φ (fr.Φ.symm (Pi.single i u)) j = 0)
    (h1 : ∀ j : Fin fr'.r, j ≠ i' → ∀ y : Fin (fr'.m j) → fr'.E j,
      fr.Φ (fr'.Φ.symm (Pi.single j y)) i = 0)
    (h4 : ∀ (c : fr'.E i') (u : Fin (fr.m i) → fr.E i),
      fr'.Φ (fr.Φ.symm (Pi.single i (ε c • u))) i' = c • fr'.Φ (fr.Φ.symm (Pi.single i u)) i')
    (h2 : ∀ (c : fr'.E i') (y : Fin (fr'.m i') → fr'.E i'),
      fr.Φ (fr'.Φ.symm (Pi.single i' (c • y))) i =
        ε c • fr.Φ (fr'.Φ.symm (Pi.single i' y)) i) :
    letI : Algebra (fr'.E i') (fr.E i) := ε.toRingHom.toAlgebra
    ∃ (ι ι₁ : fr.E i →ₗ[fr'.E i'] (Fin (fr'.m i') → fr'.E i'))
      (π π₁ : (Fin (fr'.m i') → fr'.E i') →ₗ[fr'.E i'] fr.E i)
      (h1k : ∀ t, π (ι t) = 0) (_ : ∀ t, π (ι₁ t) = t) (_ : ∀ t, π₁ (ι t) = t)
      (h4k : ∀ t, π₁ (ι₁ t) = 0),
      (∀ t, fr'.blockSpecialLinear i' (datumElt ι π h1k t) =
        datumElt (fr.blockIota i (fr.idx0 i hm)) (fr.blockPi i (fr.idx1 i hm))
          (fun t => fr.blockPi_blockIota_ne i (fr.idx0_ne_idx1 i hm) t) t) ∧
      (∀ t, fr'.blockSpecialLinear i' (datumElt ι₁ π₁ h4k t) =
        datumElt (fr.blockIota i (fr.idx1 i hm)) (fr.blockPi i (fr.idx0 i hm))
          (fun t => fr.blockPi_blockIota_ne i (fr.idx0_ne_idx1 i hm).symm t) t) := by
  letI : Algebra (fr'.E i') (fr.E i) := ε.toRingHom.toAlgebra
  let A : (Fin (fr.m i) → fr.E i) →ₗ[fr'.E i'] (Fin (fr'.m i') → fr'.E i') :=
    { toFun := nestA fr fr' i i'
      map_add' := fun u v => nestA_add fr fr' i i' u v
      map_smul' := by
        intro c u
        show nestA fr fr' i i' (c • u) = c • nestA fr fr' i i' u
        rw [show (c • u : Fin (fr.m i) → fr.E i) = ε c • u from rfl]
        exact nestA_smul fr fr' i i' ε h4 c u }
  let B : (Fin (fr'.m i') → fr'.E i') →ₗ[fr'.E i'] (Fin (fr.m i) → fr.E i) :=
    { toFun := nestB fr fr' i i'
      map_add' := fun y z => nestB_add fr fr' i i' y z
      map_smul' := by
        intro c y
        show nestB fr fr' i i' (c • y) = c • nestB fr fr' i i' y
        rw [show (c • nestB fr fr' i i' y : Fin (fr.m i) → fr.E i) =
          ε c • nestB fr fr' i i' y from rfl]
        exact nestB_smul fr fr' i i' ε h2 c y }
  let single0 : fr.E i →ₗ[fr'.E i'] (Fin (fr.m i) → fr.E i) :=
    LinearMap.single (fr'.E i') (fun _ : Fin (fr.m i) => fr.E i) (fr.idx0 i hm)
  let single1 : fr.E i →ₗ[fr'.E i'] (Fin (fr.m i) → fr.E i) :=
    LinearMap.single (fr'.E i') (fun _ : Fin (fr.m i) => fr.E i) (fr.idx1 i hm)
  let proj0 : (Fin (fr.m i) → fr.E i) →ₗ[fr'.E i'] fr.E i :=
    LinearMap.proj (R := fr'.E i') (φ := fun _ : Fin (fr.m i) => fr.E i) (fr.idx0 i hm)
  let proj1 : (Fin (fr.m i) → fr.E i) →ₗ[fr'.E i'] fr.E i :=
    LinearMap.proj (R := fr'.E i') (φ := fun _ : Fin (fr.m i) => fr.E i) (fr.idx1 i hm)
  let ι : fr.E i →ₗ[fr'.E i'] (Fin (fr'.m i') → fr'.E i') := A.comp single0
  let ι₁ : fr.E i →ₗ[fr'.E i'] (Fin (fr'.m i') → fr'.E i') := A.comp single1
  let π : (Fin (fr'.m i') → fr'.E i') →ₗ[fr'.E i'] fr.E i := proj1.comp B
  let π₁ : (Fin (fr'.m i') → fr'.E i') →ₗ[fr'.E i'] fr.E i := proj0.comp B
  have h1k : ∀ t, π (ι t) = 0 := by
    intro t
    change nestB fr fr' i i' (nestA fr fr' i i' (Pi.single (fr.idx0 i hm) t))
      (fr.idx1 i hm) = 0
    rw [nestB_nestA fr fr' i i' h3 (Pi.single (fr.idx0 i hm) t)]
    exact Pi.single_eq_of_ne (fr.idx0_ne_idx1 i hm).symm t
  have h2k : ∀ t, π (ι₁ t) = t := by
    intro t
    change nestB fr fr' i i' (nestA fr fr' i i' (Pi.single (fr.idx1 i hm) t))
      (fr.idx1 i hm) = t
    rw [nestB_nestA fr fr' i i' h3 (Pi.single (fr.idx1 i hm) t), Pi.single_eq_same]
  have h3k : ∀ t, π₁ (ι t) = t := by
    intro t
    change nestB fr fr' i i' (nestA fr fr' i i' (Pi.single (fr.idx0 i hm) t))
      (fr.idx0 i hm) = t
    rw [nestB_nestA fr fr' i i' h3 (Pi.single (fr.idx0 i hm) t), Pi.single_eq_same]
  have h4k : ∀ t, π₁ (ι₁ t) = 0 := by
    intro t
    change nestB fr fr' i i' (nestA fr fr' i i' (Pi.single (fr.idx1 i hm) t))
      (fr.idx0 i hm) = 0
    rw [nestB_nestA fr fr' i i' h3 (Pi.single (fr.idx1 i hm) t)]
    exact Pi.single_eq_of_ne (fr.idx0_ne_idx1 i hm) t
  have eq1 : ∀ t, fr'.blockSpecialLinear i' (datumElt ι π h1k t) =
      datumElt (fr.blockIota i (fr.idx0 i hm)) (fr.blockPi i (fr.idx1 i hm))
        (fun t => fr.blockPi_blockIota_ne i (fr.idx0_ne_idx1 i hm) t) t := by
    intro t
    apply SpecialLinearGroup.ext
    intro v
    apply fr'.Φ.injective
    rw [fr'.blockSpecialLinear_apply]
    simp only [datumElt_apply]
    rw [map_add]
    rw [show fr'.Φ (fr.blockIota i (fr.idx0 i hm) (t * fr.blockPi i (fr.idx1 i hm) v)) =
        Pi.single i' (nestA fr fr' i i'
          (Pi.single (fr.idx0 i hm) (t * fr.blockPi i (fr.idx1 i hm) v))) from
      nestSingle fr fr' i i' h3
        (Pi.single (fr.idx0 i hm) (t * fr.blockPi i (fr.idx1 i hm) v))]
    rw [show π (fr'.Φ v i') = fr.blockPi i (fr.idx1 i hm) v from by
      change nestB fr fr' i i' (fr'.Φ v i') (fr.idx1 i hm) = fr.blockPi i (fr.idx1 i hm) v
      rw [nestB_coord fr fr' i i' h1 v]
      rfl]
    rw [nest_update_add_single]
    rfl
  have eq2 : ∀ t, fr'.blockSpecialLinear i' (datumElt ι₁ π₁ h4k t) =
      datumElt (fr.blockIota i (fr.idx1 i hm)) (fr.blockPi i (fr.idx0 i hm))
        (fun t => fr.blockPi_blockIota_ne i (fr.idx0_ne_idx1 i hm).symm t) t := by
    intro t
    apply SpecialLinearGroup.ext
    intro v
    apply fr'.Φ.injective
    rw [fr'.blockSpecialLinear_apply]
    simp only [datumElt_apply]
    rw [map_add]
    rw [show fr'.Φ (fr.blockIota i (fr.idx1 i hm) (t * fr.blockPi i (fr.idx0 i hm) v)) =
        Pi.single i' (nestA fr fr' i i'
          (Pi.single (fr.idx1 i hm) (t * fr.blockPi i (fr.idx0 i hm) v))) from
      nestSingle fr fr' i i' h3
        (Pi.single (fr.idx1 i hm) (t * fr.blockPi i (fr.idx0 i hm) v))]
    rw [show π₁ (fr'.Φ v i') = fr.blockPi i (fr.idx0 i hm) v from by
      change nestB fr fr' i i' (fr'.Φ v i') (fr.idx0 i hm) = fr.blockPi i (fr.idx0 i hm) v
      rw [nestB_coord fr fr' i i' h1 v]
      rfl]
    rw [nest_update_add_single]
    rfl
  exact ⟨ι, ι₁, π, π₁, h1k, h2k, h3k, h4k, eq1, eq2⟩

theorem blockDatum_numerics {P P' : Type} [CommGroup P] [CommGroup P']
    (η : P →* SpecialLinearGroup F V) (η' : P' →* SpecialLinearGroup F V)
    (fr : SemiFrame F (groupRep η)) (fr' : SemiFrame F (groupRep η')) (i : Fin fr.r)
    (i' : Fin fr'.r)
    (ε : fr'.E i' →ₐ[F] fr.E i)
    (h3 : ∀ (u : Fin (fr.m i) → fr.E i) (j : Fin fr'.r), j ≠ i' →
      fr'.Φ (fr.Φ.symm (Pi.single i u)) j = 0)
    (h4 : ∀ (c : fr'.E i') (u : Fin (fr.m i) → fr.E i),
      fr'.Φ (fr.Φ.symm (Pi.single i (ε c • u))) i' = c • fr'.Φ (fr.Φ.symm (Pi.single i u)) i') :
    letI : Algebra (fr'.E i') (fr.E i) := ε.toRingHom.toAlgebra
    Module.finrank (fr'.E i') (fr.E i) * fr.m i ≤ fr'.m i' := by
  letI : Algebra (fr'.E i') (fr.E i) := ε.toRingHom.toAlgebra
  let A : (Fin (fr.m i) → fr.E i) →ₗ[fr'.E i'] (Fin (fr'.m i') → fr'.E i') :=
    { toFun := nestA fr fr' i i'
      map_add' := fun u v => nestA_add fr fr' i i' u v
      map_smul' := by
        intro c u
        show nestA fr fr' i i' (c • u) = c • nestA fr fr' i i' u
        rw [show (c • u : Fin (fr.m i) → fr.E i) = ε c • u from rfl]
        exact nestA_smul fr fr' i i' ε h4 c u }
  have hinj : Function.Injective A := by
    intro u v huv
    have hu : nestB fr fr' i i' (nestA fr fr' i i' u) = u := nestB_nestA fr fr' i i' h3 u
    have hv : nestB fr fr' i i' (nestA fr fr' i i' v) = v := nestB_nestA fr fr' i i' h3 v
    have huv' : nestA fr fr' i i' u = nestA fr fr' i i' v := huv
    calc u = nestB fr fr' i i' (nestA fr fr' i i' u) := hu.symm
      _ = nestB fr fr' i i' (nestA fr fr' i i' v) := by rw [huv']
      _ = v := hv
  have hU : Module.finrank (fr'.E i') (Fin (fr.m i) → fr.E i) =
      fr.m i * Module.finrank (fr'.E i') (fr.E i) := by
    rw [Module.finrank_pi_fintype]
    simp [Finset.sum_const, Finset.card_univ]
  have hW : Module.finrank (fr'.E i') (Fin (fr'.m i') → fr'.E i') = fr'.m i' :=
    Module.finrank_fin_fun (R := fr'.E i')
  have hle := LinearMap.finrank_le_finrank_of_injective (f := A) hinj
  rw [hU, hW] at hle
  rw [mul_comm]
  exact hle

end CFSG.StandardType.StarFour
