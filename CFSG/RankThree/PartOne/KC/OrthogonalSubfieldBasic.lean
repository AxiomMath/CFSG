module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataQuotient

public section

open Matrix QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

namespace CFSG.RankThree.PartOne.KCOrthogonalSubfield

section Extension

variable {K : Type} [Field K] (k : Subfield K) {d : ℕ}

@[expose] def vecIncl (v : Fin d → k) : Fin d → K := fun i => (v i : K)

noncomputable abbrev glIncl : GL (Fin d) k →* GL (Fin d) K :=
  Matrix.GeneralLinearGroup.map k.subtype

@[expose] def IsExtension (Q₀ : QuadraticForm k (Fin d → k))
    (Q : QuadraticForm K (Fin d → K)) : Prop :=
  ∀ v : Fin d → k, Q (vecIncl k v) = ((Q₀ v : k) : K)

theorem vecIncl_add (v w : Fin d → k) : vecIncl k (v + w) = vecIncl k v + vecIncl k w := by
  funext i
  simp [vecIncl]

theorem vecIncl_single (i : Fin d) : vecIncl k (Pi.single i 1 : Fin d → k) = Pi.single i 1 := by
  funext j
  by_cases h : j = i
  · subst h; simp [vecIncl]
  · simp [vecIncl, h]

theorem glIncl_val (A : GL (Fin d) k) : (glIncl k A).val = A.val.map k.subtype := rfl

theorem mulVec_vecIncl (A : GL (Fin d) k) (v : Fin d → k) :
    (glIncl k A).val *ᵥ vecIncl k v = vecIncl k (A.val *ᵥ v) := by
  funext i
  exact (RingHom.map_mulVec k.subtype A.val v i).symm

theorem eq_of_agree (Q₁ Q₂ : QuadraticForm K (Fin d → K))
    (h : ∀ v : Fin d → k, Q₁ (vecIncl k v) = Q₂ (vecIncl k v)) : Q₁ = Q₂ := by
  have hv : ∀ i : Fin d, Q₁ (Pi.single i 1) = Q₂ (Pi.single i 1) := fun i => by
    have := h (Pi.single i 1)
    rwa [vecIncl_single] at this
  have hp : ∀ i j : Fin d, polar Q₁ (Pi.single i 1) (Pi.single j 1) =
      polar Q₂ (Pi.single i 1) (Pi.single j 1) := fun i j => by
    have := h (Pi.single i 1 + Pi.single j 1)
    rw [vecIncl_add, vecIncl_single, vecIncl_single] at this
    unfold QuadraticMap.polar
    rw [this, hv i, hv j]
  have hb : Q₁.toBilin (Pi.basisFun K (Fin d)) = Q₂.toBilin (Pi.basisFun K (Fin d)) := by
    refine (Pi.basisFun K (Fin d)).ext fun i => (Pi.basisFun K (Fin d)).ext fun j => ?_
    rw [QuadraticMap.toBilin_apply, QuadraticMap.toBilin_apply, Pi.basisFun_apply,
      Pi.basisFun_apply]
    split_ifs
    · exact hv i
    · exact hp i j
    · rfl
  rw [← Q₁.toQuadraticMap_toBilin (Pi.basisFun K (Fin d)), hb, Q₂.toQuadraticMap_toBilin]

variable {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)}

theorem glIncl_mem_isometries (hext : IsExtension k Q₀ Q) {A : GL (Fin d) k}
    (hA : A ∈ matrixIsometries Q₀) : glIncl k A ∈ matrixIsometries Q := by
  rw [mem_matrixIsometries_iff] at hA ⊢
  have h := eq_of_agree k (Q.comp (matrixLinearEquiv (glIncl k A)).toLinearMap) Q (fun v => by
    rw [QuadraticMap.comp_apply]
    change Q (matrixLinearEquiv (glIncl k A) (vecIncl k v)) = _
    rw [matrixLinearEquiv_apply, mulVec_vecIncl, hext, hext, ← matrixLinearEquiv_apply, hA])
  intro v
  exact congrArg (fun F => F v) h

theorem map_isometries_le (hext : IsExtension k Q₀ Q) :
    (matrixIsometries Q₀).map (glIncl k) ≤ matrixIsometries Q := by
  rintro _ ⟨A, hA, rfl⟩
  exact glIncl_mem_isometries k hext hA

theorem map_derived_le (hext : IsExtension k Q₀ Q) :
    (matrixDerived Q₀).map (glIncl k) ≤ matrixDerived Q := by
  rw [matrixDerived, Subgroup.map_commutator, matrixDerived]
  exact Subgroup.commutator_mono (map_isometries_le k hext) (map_isometries_le k hext)

end Extension


section Incl

variable {K : Type} [Field K] (k : Subfield K) {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)}

theorem scalar_entry {F : Type} [Field F] (c : Fˣ) (i j : Fin d) :
    ((GeneralLinearGroup.scalar (Fin d) c : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i j =
      if i = j then (c : F) else 0 := by
  simp [GeneralLinearGroup.scalar, Matrix.diagonal_apply]

theorem glIncl_scalar (c : kˣ) : glIncl k (GeneralLinearGroup.scalar (Fin d) c) =
    GeneralLinearGroup.scalar (Fin d) (Units.map k.subtype.toMonoidHom c) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glIncl_val, scalar_entry, Matrix.map_apply, scalar_entry]
  by_cases h : i = j <;> simp [h]

@[expose] noncomputable def inclHom (hext : IsExtension k Q₀ Q) :
    matrixDerived Q₀ →* matrixDerived Q :=
  ((glIncl k).comp (matrixDerived Q₀).subtype).codRestrict (matrixDerived Q) fun x =>
    map_derived_le k hext ⟨x.1, x.2, rfl⟩

theorem inclHom_val (hext : IsExtension k Q₀ Q) (x : matrixDerived Q₀) :
    ((inclHom k hext x : matrixDerived Q) : GL (Fin d) K) = glIncl k (x : GL (Fin d) k) := rfl

@[expose] noncomputable def incl (hext : IsExtension k Q₀ Q) :
    matrixProjectiveDerived Q₀ →* matrixProjectiveDerived Q :=
  QuotientGroup.lift (matrixDerivedScalars Q₀)
    ((matrixProjectiveProjection Q).comp (inclHom k hext)) (fun x hx => by
      obtain ⟨c, hc⟩ := (mem_matrixDerivedScalars_iff Q₀ x).mp hx
      change matrixProjectiveProjection Q (inclHom k hext x) = 1
      rw [matrixProjectiveProjection, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact (mem_matrixDerivedScalars_iff Q _).mpr ⟨Units.map k.subtype.toMonoidHom c, by
        rw [← glIncl_scalar, inclHom_val, hc]⟩)

theorem incl_mk (hext : IsExtension k Q₀ Q) (x : matrixDerived Q₀) :
    incl k hext (matrixProjectiveProjection Q₀ x) =
      matrixProjectiveProjection Q (inclHom k hext x) := rfl

theorem exists_scalar_of_glIncl (hd : 0 < d) {A : GL (Fin d) k} (c : Kˣ)
    (h : GeneralLinearGroup.scalar (Fin d) c = glIncl k A) :
    ∃ c₀ : kˣ, GeneralLinearGroup.scalar (Fin d) c₀ = A := by
  have hent : ∀ i j : Fin d, ((A.val i j : k) : K) = if i = j then (c : K) else 0 := fun i j => by
    have := congrArg (fun B : GL (Fin d) K => (B : Matrix (Fin d) (Fin d) K) i j) h
    simp only [scalar_entry, glIncl_val, Matrix.map_apply] at this
    exact this.symm
  set i₀ : Fin d := ⟨0, hd⟩
  have hc : (c : K) = ((A.val i₀ i₀ : k) : K) := by simpa using (hent i₀ i₀).symm
  have hc0 : A.val i₀ i₀ ≠ 0 := fun h0 => c.ne_zero (by rw [hc, h0]; rfl)
  have hAij : ∀ i j, A.val i j = if i = j then A.val i₀ i₀ else 0 := fun i j => by
    apply Subtype.ext
    have := hent i j
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte] at this ⊢
      rw [this, hc]
    · simp only [hij, ↓reduceIte] at this ⊢
      exact this
  refine ⟨Units.mk0 (A.val i₀ i₀) hc0, Units.ext (Matrix.ext fun i j => ?_)⟩
  rw [scalar_entry]
  exact (hAij i j).symm

theorem incl_injective (hext : IsExtension k Q₀ Q) (hd : 0 < d) :
    Function.Injective (incl k hext) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨y, rfl⟩ := matrixProjectiveProjection_surjective Q₀ x
  rw [incl_mk, matrixProjectiveProjection, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    mem_matrixDerivedScalars_iff] at hx
  obtain ⟨c, hc⟩ := hx
  obtain ⟨c₀, hc₀⟩ := exists_scalar_of_glIncl k hd c (by rw [hc]; rfl)
  rw [matrixProjectiveProjection, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact (mem_matrixDerivedScalars_iff Q₀ y).mpr ⟨c₀, hc₀⟩

end Incl

end CFSG.RankThree.PartOne.KCOrthogonalSubfield
