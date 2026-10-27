module

public import CFSG.Quasithin.Background.SmithB45J2Rep
public import CFSG.Quasithin.Background.SmithB45MatFrob
public import CFSG.CharacterTheory.SteinbergBYAlternatingSixModular
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.RepMap

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.J2Mod

open CFSG.CharacterTheory.SteinbergBY CFSG.Quasithin.B45Mat CFSG.Quasithin.J2Row
  CFSG.Quasithin.J2Model FieldFour Matrix Module

section Restrict

variable {G : Type*} [Group G] {n m : ℕ}

@[expose] noncomputable def restrictF4 (M : G →* Matrix (Fin n) (Fin n) FieldFour) :
    Representation (ZMod 2) G (Fin n → FieldFour) :=
  restrictScalarsRep (ZMod 2) (matrixBaseChange (RingHom.id FieldFour) M)

theorem restrictF4_apply (M : G →* Matrix (Fin n) (Fin n) FieldFour) (g : G)
    (x : Fin n → FieldFour) : restrictF4 M g x = M g *ᵥ x := by
  change (M g).map (RingHom.id FieldFour) *ᵥ x = _
  rw [RingHom.coe_id, Matrix.map_id]

@[expose] noncomputable def realPartInt (M : G →* Matrix (Fin n) (Fin n) FieldFour)
    (N : G →* Matrix (Fin m) (Fin m) (ZMod 2)) (T : Matrix (Fin m) (Fin n) FieldFour)
    (hT : ∀ g, T * M g = (N g).map ofPrime * T) :
    (restrictF4 M).IntertwiningMap (matrixBaseChange (RingHom.id (ZMod 2)) N) where
  toLinearMap := realPartMap T
  isIntertwining' g := by
    refine LinearMap.ext fun x => ?_
    funext a
    change reZ ((T *ᵥ restrictF4 M g x) a) = (((N g).map (RingHom.id (ZMod 2))) *ᵥ
      fun b => reZ ((T *ᵥ x) b)) a
    rw [restrictF4_apply, Matrix.mulVec_mulVec, hT g, ← Matrix.mulVec_mulVec, RingHom.coe_id,
      Matrix.map_id]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    rw [← reHom_apply, map_sum]
    exact Finset.sum_congr rfl fun b _ => by rw [reHom_apply, reZ_ofPrime_mul]

theorem exists_ne_zero_realPart {K : Type*} [Field K] (M : G →* Matrix (Fin n) (Fin n) FieldFour)
    (N : G →* Matrix (Fin m) (Fin m) (ZMod 2)) (φ : FieldFour →+* K) (ψ : ZMod 2 →+* K)
    (hψ : ∀ x, ψ x = φ (ofPrime x))
    (f : (matrixBaseChange φ M).IntertwiningMap (matrixBaseChange ψ N)) (hf : f ≠ 0) :
    ∃ f' : (restrictF4 M).IntertwiningMap (matrixBaseChange (RingHom.id (ZMod 2)) N), f' ≠ 0 := by
  have hT0 : LinearMap.toMatrix' f.toLinearMap ≠ 0 := by
    intro h
    apply hf
    apply Representation.IntertwiningMap.ext
    exact LinearMap.toMatrix'.injective (h.trans (map_zero _).symm)
  have hT : ∀ g, LinearMap.toMatrix' f.toLinearMap * (M g).map φ =
      ((N g).map ofPrime).map φ * LinearMap.toMatrix' f.toLinearMap := by
    intro g
    have h2 := congrArg LinearMap.toMatrix' (f.isIntertwining' g)
    change LinearMap.toMatrix' (f.toLinearMap ∘ₗ Matrix.toLin' ((M g).map φ)) =
      LinearMap.toMatrix' (Matrix.toLin' ((N g).map ψ) ∘ₗ f.toLinearMap) at h2
    simp only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] at h2
    rw [h2, Matrix.map_map]
    congr 2
    funext x
    exact hψ x
  obtain ⟨T, hT', hTM⟩ := exists_ne_zero_mul_eq_mul_of_map φ (fun g => M g)
    (fun g => (N g).map ofPrime) _ hT0 hT
  refine ⟨realPartInt M N T hTM, fun h => hT' (realPartMap_eq_zero T ?_)⟩
  exact congrArg Representation.IntertwiningMap.toLinearMap h

theorem finrank_fieldFour_fun : finrank (ZMod 2) (Fin n → FieldFour) = 2 * n := by
  rw [Module.finrank_pi_fintype, fieldFourCoord.finrank_eq, Module.finrank_fin_fun,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]

end Restrict

theorem frob_ofPrime (x : ZMod 2) : frob (ofPrime x) = ofPrime x := by
  revert x
  decide

section Binary

theorem nonempty_equiv_restrictF4 {K : Type*} [Field K] {d : ℕ}
    (N : G6 →* Matrix (Fin d) (Fin d) (ZMod 2))
    (hN : (matrixBaseChange (RingHom.id (ZMod 2)) N).IsIrreducible) (hd : 12 ≤ d)
    (φ : FieldFour →+* K) (ψ : ZMod 2 →+* K) (hψ : ∀ x, ψ x = φ (ofPrime x))
    (f : (matrixBaseChange φ rep6a).IntertwiningMap (matrixBaseChange ψ N)) (hf : f ≠ 0) :
    Nonempty ((matrixBaseChange (RingHom.id (ZMod 2)) N).Equiv (restrictF4 rep6a)) := by
  obtain ⟨f', hf'⟩ := exists_ne_zero_realPart rep6a N φ ψ hψ f hf
  have := hN
  have hsurj : Function.Surjective f' :=
    (Representation.IsIrreducible.surjective_or_eq_zero f').resolve_right hf'
  have hle : d ≤ 12 := by
    have h1 := LinearMap.finrank_range_le f'.toLinearMap
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_fin_fun,
      finrank_fieldFour_fun] at h1
    exact h1
  have hfr : finrank (ZMod 2) (Fin 6 → FieldFour) = finrank (ZMod 2) (Fin d → ZMod 2) := by
    rw [finrank_fieldFour_fun, Module.finrank_fin_fun]
    omega
  have hinj : Function.Injective f' :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr (f := f'.toLinearMap)).2 hsurj
  exact ⟨(f'.ofBijective ⟨hinj, hsurj⟩).symm⟩


theorem j2_binary_small (W : Type) [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (τ : Representation (ZMod 2) G6 W) (hτ : τ.IsIrreducible)
    (hW : finrank (ZMod 2) W < 24) :
    Nonempty (τ.Equiv (matrixBaseChange (RingHom.id (ZMod 2)) rep1)) ∨
      Nonempty (τ.Equiv (restrictF4 rep6a)) := by
  refine binary_coords_elim W τ hτ fun N hN hτN U hU0 hUirr => ?_
  obtain ⟨eτ⟩ := hτN
  let k := AlgebraicClosure (ZMod 2)
  obtain ⟨-, i, ⟨e⟩⟩ := j2ClosureRep_complete k U.toSubmodule U.toRepresentation hUirr
  have hdimU : finrank k U.toSubmodule = j2Dim i := by
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]
  have hUle : finrank k U.toSubmodule ≤ finrank (ZMod 2) W := by
    have h1 := Submodule.finrank_le U.toSubmodule
    rwa [Module.finrank_fin_fun] at h1
  fin_cases i
  ·
    obtain ⟨e'⟩ := nonempty_equiv_of_intertwining_binary rep1 N (isIrreducible_rep1 _) hN _ _
      (incl_comp_ne_zero U hU0 e)
    exact Or.inl ⟨eτ.trans e'⟩
  ·
    change U.toRepresentation.Equiv (matrixBaseChange (toField k) rep6a) at e
    have hd := two_mul_le_of_frob _ U hUirr (toField k) e
      (isEmpty_equiv_of_trace k rep6a rep6b w6 trace_ne_6)
    obtain ⟨e'⟩ := nonempty_equiv_restrictF4 N hN (by omega) (toField k) _ (fun _ => rfl) _
      (incl_comp_ne_zero U hU0 e)
    exact Or.inr ⟨eτ.trans e'⟩
  ·
    change U.toRepresentation.Equiv (matrixBaseChange (toField k) rep6b) at e
    have hd := two_mul_le_of_frob _ U hUirr (toField k) e
      (isEmpty_equiv_of_trace k rep6b (twist rep6b) w6 (by
        have h1 : Matrix.trace (rep6b w6) = ω₂ := by rw [trace_twist, trace_rep6a_w6, frob_ω]
        rw [trace_twist rep6b, h1, frob_ω₂]
        exact ω_ne_ω₂.symm))
    have e₁ : U.toRepresentation.Equiv (matrixBaseChange ((toField k).comp frob) rep6a) :=
      e.trans (Representation.Equiv.mk (LinearEquiv.refl _ _) fun g =>
        by rw [rep6b, matrixBaseChange_twist]; rfl)
    obtain ⟨e'⟩ := nonempty_equiv_restrictF4 N hN (by omega) ((toField k).comp frob) _
      (fun x => by rw [RingHom.comp_apply, RingHom.comp_apply, frob_ofPrime]) _
      (incl_comp_ne_zero U hU0 e₁)
    exact Or.inr ⟨eτ.trans e'⟩
  ·
    change U.toRepresentation.Equiv (matrixBaseChange (toField k) rep14a) at e
    have hd := two_mul_le_of_frob _ U hUirr (toField k) e
      (isEmpty_equiv_of_trace k rep14a rep14b w14 trace_ne_14)
    omega
  ·
    change U.toRepresentation.Equiv (matrixBaseChange (toField k) rep14b) at e
    have hd := two_mul_le_of_frob _ U hUirr (toField k) e
      (isEmpty_equiv_of_trace k rep14b (twist rep14b) w14 (by
        have h1 : Matrix.trace (rep14b w14) = ω := by
          rw [trace_twist, trace_rep14a_w14, frob_ω₂]
        rw [trace_twist rep14b, h1, frob_ω]
        exact ω_ne_ω₂))
    omega
  all_goals
    exfalso
    simp only [j2Dim] at hdimU
    norm_num [hdimU] at hUle
    omega

end Binary

end CFSG.Quasithin.J2Mod
