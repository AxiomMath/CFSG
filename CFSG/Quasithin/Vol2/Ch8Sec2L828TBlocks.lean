module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.Quasithin.H13.L828T

variable {E : Type*} [AddCommGroup E]

@[expose] def blockMat (Φ : AddMonoid.End (E × E)) : Matrix (Fin 2) (Fin 2) (AddMonoid.End E) :=
  !![(AddMonoidHom.fst E E).comp (Φ.comp (AddMonoidHom.inl E E)),
     (AddMonoidHom.fst E E).comp (Φ.comp (AddMonoidHom.inr E E));
     (AddMonoidHom.snd E E).comp (Φ.comp (AddMonoidHom.inl E E)),
     (AddMonoidHom.snd E E).comp (Φ.comp (AddMonoidHom.inr E E))]

@[expose] def diagEnd (γ : AddMonoid.End E) : AddMonoid.End (E × E) := AddMonoidHom.prodMap γ γ

theorem diagEnd_apply (γ : AddMonoid.End E) (z : E × E) : diagEnd γ z = (γ z.1, γ z.2) := rfl

private theorem map_mk_eq_add (Φ : AddMonoid.End (E × E)) (x y : E) :
    Φ (x, y) = Φ (x, 0) + Φ (0, y) := by
  rw [← map_add]
  simp

private theorem apply_eq_blockMat (Φ : AddMonoid.End (E × E)) (z : E × E) :
    Φ z = (blockMat Φ 0 0 z.1 + blockMat Φ 0 1 z.2, blockMat Φ 1 0 z.1 + blockMat Φ 1 1 z.2) := by
  obtain ⟨x, y⟩ := z
  rw [map_mk_eq_add Φ x y]
  rfl

theorem blockMat_mul (Φ Ψ : AddMonoid.End (E × E)) :
    blockMat (Φ * Ψ) = blockMat Φ * blockMat Ψ := by
  ext i j x
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j
  · exact congrArg Prod.fst (apply_eq_blockMat Φ (Ψ (x, 0)))
  · exact congrArg Prod.fst (apply_eq_blockMat Φ (Ψ (0, x)))
  · exact congrArg Prod.snd (apply_eq_blockMat Φ (Ψ (x, 0)))
  · exact congrArg Prod.snd (apply_eq_blockMat Φ (Ψ (0, x)))

theorem blockMat_one : blockMat (1 : AddMonoid.End (E × E)) = 1 := by
  ext i j x
  fin_cases i <;> fin_cases j <;> rfl

theorem blockMat_injective : Function.Injective (blockMat (E := E)) := by
  intro Φ Ψ h
  ext z : 1
  rw [apply_eq_blockMat Φ z, apply_eq_blockMat Ψ z, h]

theorem blockMat_mem_centralizer (Γ : Set (AddMonoid.End E)) (Φ : AddMonoid.End (E × E))
    (hΦ : ∀ γ ∈ Γ, Φ * diagEnd γ = diagEnd γ * Φ) (i j : Fin 2) :
    blockMat Φ i j ∈ Subring.centralizer Γ := by
  rw [Subring.mem_centralizer_iff]
  intro γ hγ
  have hc : ∀ z : E × E, Φ (diagEnd γ z) = diagEnd γ (Φ z) := fun z =>
    congrArg (fun F : AddMonoid.End (E × E) => F z) (hΦ γ hγ)
  have hfst : ∀ z : E × E, (Φ (diagEnd γ z)).1 = γ (Φ z).1 := fun z =>
    congrArg Prod.fst (hc z)
  have hsnd : ∀ z : E × E, (Φ (diagEnd γ z)).2 = γ (Φ z).2 := fun z =>
    congrArg Prod.snd (hc z)
  have hd : ∀ x : E, diagEnd γ (x, 0) = (γ x, 0) := fun x => Prod.ext rfl (map_zero γ)
  have hd' : ∀ y : E, diagEnd γ (0, y) = (0, γ y) := fun y => Prod.ext (map_zero γ) rfl
  have hA : ∀ x : E, (Φ (γ x, 0)).1 = γ (Φ (x, 0)).1 := fun x => by
    have h := hfst (x, 0)
    rw [hd x] at h
    exact h
  have hB : ∀ x : E, (Φ (γ x, 0)).2 = γ (Φ (x, 0)).2 := fun x => by
    have h := hsnd (x, 0)
    rw [hd x] at h
    exact h
  have hC : ∀ y : E, (Φ (0, γ y)).1 = γ (Φ (0, y)).1 := fun y => by
    have h := hfst (0, y)
    rw [hd' y] at h
    exact h
  have hD : ∀ y : E, (Φ (0, γ y)).2 = γ (Φ (0, y)).2 := fun y => by
    have h := hsnd (0, y)
    rw [hd' y] at h
    exact h
  ext x : 1
  fin_cases i <;> fin_cases j
  · exact (hA x).symm
  · exact (hC x).symm
  · exact (hB x).symm
  · exact (hD x).symm

private def centMat {X : Type*} [Group X] (Γ : Set (AddMonoid.End E))
    (ρ : X →* AddMonoid.End (E × E)) (hρ : ∀ x, ∀ γ ∈ Γ, ρ x * diagEnd γ = diagEnd γ * ρ x)
    (x : X) : Matrix (Fin 2) (Fin 2) (Subring.centralizer Γ) :=
  Matrix.of fun i j => ⟨blockMat (ρ x) i j, blockMat_mem_centralizer Γ (ρ x) (hρ x) i j⟩

private theorem centMat_map_val {X : Type*} [Group X] (Γ : Set (AddMonoid.End E))
    (ρ : X →* AddMonoid.End (E × E)) (hρ : ∀ x, ∀ γ ∈ Γ, ρ x * diagEnd γ = diagEnd γ * ρ x)
    (x : X) : (centMat Γ ρ hρ x).map Subtype.val = blockMat (ρ x) :=
  Matrix.ext fun _ _ => rfl

private theorem centMat_one {X : Type*} [Group X] (Γ : Set (AddMonoid.End E))
    (ρ : X →* AddMonoid.End (E × E)) (hρ : ∀ x, ∀ γ ∈ Γ, ρ x * diagEnd γ = diagEnd γ * ρ x) :
    centMat Γ ρ hρ 1 = 1 := by
  refine Matrix.ext fun i j => ?_
  apply Subtype.ext
  have h1 : blockMat (ρ 1) = 1 := by rw [map_one, blockMat_one]
  show blockMat (ρ 1) i j = ((1 : Matrix (Fin 2) (Fin 2) (Subring.centralizer Γ)) i j : AddMonoid.End E)
  rw [h1, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

private theorem centMat_mul {X : Type*} [Group X] (Γ : Set (AddMonoid.End E))
    (ρ : X →* AddMonoid.End (E × E)) (hρ : ∀ x, ∀ γ ∈ Γ, ρ x * diagEnd γ = diagEnd γ * ρ x)
    (x y : X) : centMat Γ ρ hρ (x * y) = centMat Γ ρ hρ x * centMat Γ ρ hρ y := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  apply Subtype.ext
  show blockMat (ρ (x * y)) i j =
    blockMat (ρ x) i 0 * blockMat (ρ y) 0 j + blockMat (ρ x) i 1 * blockMat (ρ y) 1 j
  rw [map_mul, blockMat_mul, Matrix.mul_apply, Fin.sum_univ_two]

private def centHom {X : Type*} [Group X] (Γ : Set (AddMonoid.End E))
    (ρ : X →* AddMonoid.End (E × E)) (hρ : ∀ x, ∀ γ ∈ Γ, ρ x * diagEnd γ = diagEnd γ * ρ x) :
    X →* Matrix (Fin 2) (Fin 2) (Subring.centralizer Γ) where
  toFun := centMat Γ ρ hρ
  map_one' := centMat_one Γ ρ hρ
  map_mul' := centMat_mul Γ ρ hρ

theorem exists_hom_gl2 (Γ : Set (AddMonoid.End E)) (K : Type*) [Field K]
    (κ : Subring.centralizer Γ ≃+* K) {X : Type*} [Group X] (ρ : X →* AddMonoid.End (E × E))
    (hρ : ∀ x, ∀ γ ∈ Γ, ρ x * diagEnd γ = diagEnd γ * ρ x) :
    ∃ f : X →* Matrix.GeneralLinearGroup (Fin 2) K, ∀ x, f x = 1 ↔ ρ x = 1 := by
  have hinj : Function.Injective (RingHom.mapMatrix κ.toRingHom :
      Matrix (Fin 2) (Fin 2) (Subring.centralizer Γ) →+* Matrix (Fin 2) (Fin 2) K) :=
    fun A B h => Matrix.map_injective κ.injective h
  have hone : (1 : Matrix (Fin 2) (Fin 2) (Subring.centralizer Γ)).map Subtype.val = 1 := by
    refine Matrix.ext fun i j => ?_
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have hC1 : ∀ x, centMat Γ ρ hρ x = 1 ↔ ρ x = 1 := by
    intro x
    constructor
    · intro h
      apply blockMat_injective
      rw [blockMat_one, ← centMat_map_val Γ ρ hρ x, h, hone]
    · intro h
      apply Matrix.map_injective Subtype.val_injective
      show (centMat Γ ρ hρ x).map Subtype.val =
        (1 : Matrix (Fin 2) (Fin 2) (Subring.centralizer Γ)).map Subtype.val
      rw [centMat_map_val Γ ρ hρ x, hone, h, blockMat_one]
  let F : X →* Matrix (Fin 2) (Fin 2) K :=
    (RingHom.mapMatrix κ.toRingHom).toMonoidHom.comp (centHom Γ ρ hρ)
  have hF : ∀ x, F x = 1 ↔ centMat Γ ρ hρ x = 1 := by
    intro x
    constructor
    · intro h
      apply hinj
      rw [map_one]
      exact h
    · intro h
      show (RingHom.mapMatrix κ.toRingHom) (centMat Γ ρ hρ x) = 1
      rw [h, map_one]
  have hU : ∀ x, F.toHomUnits x = 1 ↔ F x = 1 := by
    intro x
    rw [← Units.val_eq_one, MonoidHom.coe_toHomUnits]
  exact ⟨F.toHomUnits, fun x => (hU x).trans ((hF x).trans (hC1 x))⟩

@[expose] def diagRing : AddMonoid.End E →+* AddMonoid.End (E × E) where
  toFun := diagEnd
  map_one' := by
    ext z <;> rfl
  map_mul' := by
    intro a b
    ext z <;> rfl
  map_zero' := by
    ext z <;> rfl
  map_add' := by
    intro a b
    ext z <;> rfl

theorem diagRing_apply (γ : AddMonoid.End E) : diagRing γ = diagEnd γ := rfl

theorem diagRing_injective : Function.Injective (diagRing (E := E)) := by
  intro a b h
  ext x
  exact congrArg (fun F : AddMonoid.End (E × E) => (F (x, 0)).1) h

theorem blockMat_add (Φ Ψ : AddMonoid.End (E × E)) :
    blockMat (Φ + Ψ) = blockMat Φ + blockMat Ψ := by
  ext i j x
  fin_cases i <;> fin_cases j <;> rfl

theorem blockMat_diagEnd (γ : AddMonoid.End E) (i j : Fin 2) :
    blockMat (diagEnd γ) i j = if i = j then γ else 0 := by
  fin_cases i <;> fin_cases j
  · ext x
    rfl
  · ext x
    exact map_zero γ
  · ext x
    exact map_zero γ
  · ext x
    rfl

theorem exists_hom_gl2' (Γ : Set (AddMonoid.End E)) (K : Type*) [Field K]
    (κ : Subring.centralizer Γ ≃+* K) {X : Type*} [Group X] (ρ : X →* AddMonoid.End (E × E))
    (hρ : ∀ x, ∀ γ ∈ Γ, ρ x * diagEnd γ = diagEnd γ * ρ x) :
    ∃ f : X →* Matrix.GeneralLinearGroup (Fin 2) K, (∀ x, f x = 1 ↔ ρ x = 1) ∧
      ∀ (x : X) (i j : Fin 2), ∃ hmem : blockMat (ρ x) i j ∈ Subring.centralizer Γ,
        κ ⟨blockMat (ρ x) i j, hmem⟩ = ((f x : Matrix.GeneralLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) i j := by
  have hinj : Function.Injective (RingHom.mapMatrix κ.toRingHom :
      Matrix (Fin 2) (Fin 2) (Subring.centralizer Γ) →+* Matrix (Fin 2) (Fin 2) K) :=
    fun A B h => Matrix.map_injective κ.injective h
  have hone : (1 : Matrix (Fin 2) (Fin 2) (Subring.centralizer Γ)).map Subtype.val = 1 := by
    refine Matrix.ext fun i j => ?_
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have hC1 : ∀ x, centMat Γ ρ hρ x = 1 ↔ ρ x = 1 := by
    intro x
    constructor
    · intro h
      apply blockMat_injective
      rw [blockMat_one, ← centMat_map_val Γ ρ hρ x, h, hone]
    · intro h
      apply Matrix.map_injective Subtype.val_injective
      show (centMat Γ ρ hρ x).map Subtype.val =
        (1 : Matrix (Fin 2) (Fin 2) (Subring.centralizer Γ)).map Subtype.val
      rw [centMat_map_val Γ ρ hρ x, hone, h, blockMat_one]
  let F : X →* Matrix (Fin 2) (Fin 2) K :=
    (RingHom.mapMatrix κ.toRingHom).toMonoidHom.comp (centHom Γ ρ hρ)
  have hF : ∀ x, F x = 1 ↔ centMat Γ ρ hρ x = 1 := by
    intro x
    constructor
    · intro h
      apply hinj
      rw [map_one]
      exact h
    · intro h
      show (RingHom.mapMatrix κ.toRingHom) (centMat Γ ρ hρ x) = 1
      rw [h, map_one]
  have hU : ∀ x, F.toHomUnits x = 1 ↔ F x = 1 := by
    intro x
    rw [← Units.val_eq_one, MonoidHom.coe_toHomUnits]
  refine ⟨F.toHomUnits, fun x => (hU x).trans ((hF x).trans (hC1 x)), fun x i j => ?_⟩
  refine ⟨blockMat_mem_centralizer Γ (ρ x) (hρ x) i j, ?_⟩
  rw [MonoidHom.coe_toHomUnits]
  rfl

theorem eq_diag_of_matrix_scalar (Γ : Set (AddMonoid.End E)) (K : Type*) [Field K]
    (κ : Subring.centralizer Γ ≃+* K) {X : Type*} [Group X] (ρ : X →* AddMonoid.End (E × E))
    (hρ : ∀ x, ∀ γ ∈ Γ, ρ x * diagEnd γ = diagEnd γ * ρ x)
    (f : X →* Matrix.GeneralLinearGroup (Fin 2) K)
    (hf : ∀ (x : X) (i j : Fin 2), ∃ hmem : blockMat (ρ x) i j ∈ Subring.centralizer Γ,
        κ ⟨blockMat (ρ x) i j, hmem⟩ = ((f x : Matrix.GeneralLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) i j)
    {x x' : X} {τ : K}
    (h : ((f x : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) +
      ((f x' : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        τ • (1 : Matrix (Fin 2) (Fin 2) K)) :
    ρ x + ρ x' = diagEnd ((κ.symm τ : Subring.centralizer Γ) : AddMonoid.End E) := by
  apply blockMat_injective
  rw [blockMat_add]
  refine Matrix.ext fun i j => ?_
  rw [Matrix.add_apply, blockMat_diagEnd]
  obtain ⟨ha, ka⟩ := hf x i j
  obtain ⟨hb, kb⟩ := hf x' i j
  have hh : (f x : Matrix (Fin 2) (Fin 2) K) i j + (f x' : Matrix (Fin 2) (Fin 2) K) i j =
      if i = j then τ else 0 := by
    rw [← Matrix.add_apply, h]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hsum : κ ⟨blockMat (ρ x) i j + blockMat (ρ x') i j, Subring.add_mem _ ha hb⟩ =
      κ ⟨blockMat (ρ x) i j, ha⟩ + κ ⟨blockMat (ρ x') i j, hb⟩ :=
    map_add κ ⟨blockMat (ρ x) i j, ha⟩ ⟨blockMat (ρ x') i j, hb⟩
  rw [ka, kb] at hsum
  by_cases hij : i = j
  · rw [if_pos hij]
    rw [if_pos hij] at hh
    have hk : κ ⟨blockMat (ρ x) i j + blockMat (ρ x') i j, Subring.add_mem _ ha hb⟩ =
        κ (κ.symm τ) := by
      rw [hsum, hh, κ.apply_symm_apply]
    exact congrArg Subtype.val (κ.injective hk)
  · rw [if_neg hij]
    rw [if_neg hij] at hh
    have hk : κ ⟨blockMat (ρ x) i j + blockMat (ρ x') i j, Subring.add_mem _ ha hb⟩ = κ 0 := by
      rw [hsum, hh, map_zero]
    exact congrArg Subtype.val (κ.injective hk)

end CFSG.Quasithin.H13.L828T
