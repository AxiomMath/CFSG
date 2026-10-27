module

public import CFSG.CharacterTheory.SteinbergBYFieldFour
public import CFSG.CharacterTheory.SteinbergBYModularRealization
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.Quasithin.B45Mat

open CFSG.CharacterTheory.SteinbergBY FieldFour Module Matrix

section Frob

variable {k : Type*} [Field k] [CharP k 2] {n : ℕ}

@[expose] def sqVec (n : ℕ) : (Fin n → k) →+ (Fin n → k) where
  toFun x i := x i ^ 2
  map_zero' := by
    funext i
    simp
  map_add' x y := by
    funext i
    exact CharTwo.add_sq (x i) (y i)

theorem sqVec_apply (x : Fin n → k) (i : Fin n) : sqVec n x i = x i ^ 2 :=
  rfl

theorem eq_of_sq_eq {x y : k} (h : x ^ 2 = y ^ 2) : x = y := by
  have h2 : (x - y) ^ 2 = 0 := by
    rw [sub_eq_add_neg, CharTwo.add_sq, neg_sq, h, ← two_mul, CharTwo.two_eq_zero, zero_mul]
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h2)

theorem sqVec_injective : Function.Injective (sqVec n : (Fin n → k) →+ _) :=
  fun _ _ h => funext fun i => eq_of_sq_eq (congrFun h i)

theorem sqVec_smul (c : k) (x : Fin n → k) : sqVec n (c • x) = c ^ 2 • sqVec n x := by
  funext i
  simp [sqVec_apply, mul_pow]

theorem sqVec_mulVec_two {d : ℕ} (ψ : ZMod 2 →+* k) (A : Matrix (Fin d) (Fin d) (ZMod 2))
    (x : Fin d → k) : sqVec d (A.map ψ *ᵥ x) = A.map ψ *ᵥ sqVec d x := by
  funext i
  simp only [sqVec_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [CharTwo.sum_sq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_pow, ← map_pow]
  have : A i j ^ 2 = A i j := by
    generalize A i j = a
    revert a
    decide
  rw [this]

theorem sqVec_mulVec_four (φ : FieldFour →+* k) (A : Matrix (Fin n) (Fin n) FieldFour)
    (x : Fin n → k) : sqVec n (A.map φ *ᵥ x) = (A.map frob).map φ *ᵥ sqVec n x := by
  funext i
  simp only [sqVec_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [CharTwo.sum_sq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_pow, ← map_pow, frob_apply]

variable [IsAlgClosed k]

omit [CharP k 2] in
@[expose] noncomputable def sqrtK (y : k) : k :=
  (IsAlgClosed.exists_pow_nat_eq y (by norm_num : 0 < 2)).choose

omit [CharP k 2] in
theorem sqrtK_sq (y : k) : sqrtK y ^ 2 = y :=
  (IsAlgClosed.exists_pow_nat_eq y (by norm_num : 0 < 2)).choose_spec

@[expose] noncomputable def sqrtVec (x : Fin n → k) : Fin n → k := fun i => sqrtK (x i)

theorem sqVec_sqrtVec (x : Fin n → k) : sqVec n (sqrtVec x) = x :=
  funext fun i => sqrtK_sq (x i)

theorem sqrtVec_sqVec (x : Fin n → k) : sqrtVec (sqVec n x) = x :=
  sqVec_injective (sqVec_sqrtVec _)

theorem sqrtVec_add (x y : Fin n → k) : sqrtVec (x + y) = sqrtVec x + sqrtVec y :=
  sqVec_injective (by rw [map_add, sqVec_sqrtVec, sqVec_sqrtVec, sqVec_sqrtVec])

theorem sqrtVec_smul (c : k) (x : Fin n → k) : sqrtVec (c • x) = sqrtK c • sqrtVec x :=
  sqVec_injective (by rw [sqVec_smul, sqrtK_sq, sqVec_sqrtVec, sqVec_sqrtVec])

@[expose] noncomputable def sqSub (U : Submodule k (Fin n → k)) : Submodule k (Fin n → k) where
  carrier := sqVec n '' U
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, U.add_mem hx hy, map_add _ _ _⟩
  zero_mem' := ⟨0, U.zero_mem, map_zero _⟩
  smul_mem' := by
    rintro c _ ⟨x, hx, rfl⟩
    exact ⟨sqrtK c • x, U.smul_mem _ hx, by rw [sqVec_smul, sqrtK_sq]⟩

theorem mem_sqSub {U : Submodule k (Fin n → k)} {x : Fin n → k} :
    x ∈ sqSub U ↔ sqrtVec x ∈ U := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [sqrtVec_sqVec]
    exact hy
  · intro h
    exact ⟨_, h, sqVec_sqrtVec x⟩

theorem sqVec_mem_sqSub {U : Submodule k (Fin n → k)} {x : Fin n → k} (hx : x ∈ U) :
    sqVec n x ∈ sqSub U :=
  ⟨x, hx, rfl⟩

variable {G : Type*} [Group G] {d : ℕ}

@[expose] noncomputable def sqSubRep (ψ : ZMod 2 →+* k) {N : G →* Matrix (Fin d) (Fin d) (ZMod 2)}
    (U : Subrepresentation (matrixBaseChange ψ N)) : Subrepresentation (matrixBaseChange ψ N) where
  toSubmodule := sqSub U.toSubmodule
  apply_mem_toSubmodule g := by
    rintro _ ⟨x, hx, rfl⟩
    rw [matrixBaseChange_apply, ← sqVec_mulVec_two]
    exact sqVec_mem_sqSub (U.apply_mem_toSubmodule g hx)

@[expose] noncomputable def sqSubEquiv (ψ : ZMod 2 →+* k) {N : G →* Matrix (Fin d) (Fin d) (ZMod 2)}
    {U : Subrepresentation (matrixBaseChange ψ N)} (φ : FieldFour →+* k)
    {M : G →* Matrix (Fin n) (Fin n) FieldFour}
    (e : U.toRepresentation.Equiv (matrixBaseChange φ M)) :
    (sqSubRep ψ U).toRepresentation.Equiv (matrixBaseChange φ
      ((frob.mapMatrix : Matrix (Fin n) (Fin n) FieldFour →+* _).toMonoidHom.comp M)) :=
  Representation.Equiv.mk
    { toFun := fun x => sqVec n (e ⟨sqrtVec (x : Fin d → k), mem_sqSub.1 x.2⟩)
      invFun := fun y => ⟨sqVec d (e.symm (sqrtVec y) : Fin d → k),
        sqVec_mem_sqSub (e.symm (sqrtVec y)).2⟩
      map_add' := fun x y => by
        have : (⟨sqrtVec ((x + y : ↥(sqSubRep ψ U).toSubmodule) : Fin d → k),
            mem_sqSub.1 (x + y).2⟩ : ↥U.toSubmodule) =
            ⟨sqrtVec (x : Fin d → k), mem_sqSub.1 x.2⟩ + ⟨sqrtVec (y : Fin d → k),
              mem_sqSub.1 y.2⟩ := by
          apply Subtype.ext
          exact sqrtVec_add _ _
        simp only [this, map_add]
      map_smul' := fun c x => by
        have : (⟨sqrtVec ((c • x : ↥(sqSubRep ψ U).toSubmodule) : Fin d → k),
            mem_sqSub.1 (c • x).2⟩ : ↥U.toSubmodule) =
            sqrtK c • ⟨sqrtVec (x : Fin d → k), mem_sqSub.1 x.2⟩ := by
          apply Subtype.ext
          exact sqrtVec_smul _ _
        simp only [this, map_smul, sqVec_smul, sqrtK_sq, RingHom.id_apply]
      left_inv := fun x => by
        apply Subtype.ext
        change sqVec d (e.symm (sqrtVec (sqVec n (e ⟨sqrtVec (x : Fin d → k), _⟩))) :
          Fin d → k) = x
        rw [sqrtVec_sqVec, Representation.Equiv.symm_apply_apply]
        exact sqVec_sqrtVec _
      right_inv := fun y => by
        change sqVec n (e ⟨sqrtVec (sqVec d (e.symm (sqrtVec y) : Fin d → k)), _⟩) = y
        have : (⟨sqrtVec (sqVec d (e.symm (sqrtVec y) : Fin d → k)),
            mem_sqSub.1 (sqVec_mem_sqSub (e.symm (sqrtVec y)).2)⟩ : ↥U.toSubmodule) =
            e.symm (sqrtVec y) := by
          apply Subtype.ext
          exact sqrtVec_sqVec _
        rw [this, Representation.Equiv.apply_symm_apply]
        exact sqVec_sqrtVec y }
    fun g => by
      refine LinearMap.ext fun x => ?_
      change sqVec n (e ⟨sqrtVec (matrixBaseChange ψ N g (x : Fin d → k)), _⟩) =
        matrixBaseChange φ _ g (sqVec n (e ⟨sqrtVec (x : Fin d → k), _⟩))
      obtain ⟨_, ⟨y, hy, rfl⟩⟩ := x
      have h1 : (⟨sqrtVec (matrixBaseChange ψ N g (sqVec d y)),
          mem_sqSub.1 ((sqSubRep ψ U).apply_mem_toSubmodule g ⟨y, hy, rfl⟩)⟩ :
            ↥U.toSubmodule) = U.toRepresentation g ⟨y, hy⟩ := by
        apply Subtype.ext
        change sqrtVec (matrixBaseChange ψ N g (sqVec d y)) = matrixBaseChange ψ N g y
        rw [matrixBaseChange_apply, ← sqVec_mulVec_two, sqrtVec_sqVec]
        rfl
      have h2 : (⟨sqrtVec (sqVec d y), mem_sqSub.1 ⟨y, hy, rfl⟩⟩ : ↥U.toSubmodule) = ⟨y, hy⟩ :=
        Subtype.ext (sqrtVec_sqVec y)
      have h3 := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g ⟨y, hy⟩
      rw [Representation.Equiv.coe_toIntertwiningMap] at h3
      rw [h1, h2, h3, matrixBaseChange_apply, matrixBaseChange_apply, sqVec_mulVec_four]
      rfl

theorem two_mul_le_of_frob (ψ : ZMod 2 →+* k) {N : G →* Matrix (Fin d) (Fin d) (ZMod 2)}
    (U : Subrepresentation (matrixBaseChange ψ N)) (hU : U.toRepresentation.IsIrreducible)
    (φ : FieldFour →+* k) {M : G →* Matrix (Fin n) (Fin n) FieldFour}
    (e : U.toRepresentation.Equiv (matrixBaseChange φ M))
    (hne : IsEmpty ((matrixBaseChange φ M).Equiv (matrixBaseChange φ
      ((frob.mapMatrix : Matrix (Fin n) (Fin n) FieldFour →+* _).toMonoidHom.comp M)))) :
    2 * n ≤ d := by
  set U' := sqSubRep ψ U with hU'
  have e' := sqSubEquiv ψ φ e
  have hdU : finrank k U.toSubmodule = n := by
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]
  have hdU' : finrank k U'.toSubmodule = n := by
    rw [e'.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]
  have hcases : U.toSubmodule ⊓ U'.toSubmodule = ⊥ ∨ U.toSubmodule ≤ U'.toSubmodule := by
    let W : Subrepresentation U.toRepresentation :=
      { toSubmodule := (U.toSubmodule ⊓ U'.toSubmodule).comap U.toSubmodule.subtype
        apply_mem_toSubmodule := fun g x hx => by
          refine ⟨(U.toRepresentation g x).2, ?_⟩
          exact U'.apply_mem_toSubmodule g hx.2 }
    rcases hU.eq_bot_or_eq_top W with h | h
    · left
      refine eq_bot_iff.2 fun x hx => ?_
      have hxW : (⟨x, hx.1⟩ : ↥U.toSubmodule) ∈ W.toSubmodule := hx
      rw [h] at hxW
      have := (Submodule.mem_bot k).1 hxW
      exact (Submodule.mem_bot k).2 (congrArg Subtype.val this)
    · right
      intro x hx
      have hxW : (⟨x, hx⟩ : ↥U.toSubmodule) ∈ W.toSubmodule := by
        rw [h]
        exact Submodule.mem_top
      exact hxW.2
  rcases hcases with h | h
  · have h1 := Submodule.finrank_sup_add_finrank_inf_eq U.toSubmodule U'.toSubmodule
    rw [h, finrank_bot, add_zero, hdU, hdU'] at h1
    have h2 := Submodule.finrank_le (U.toSubmodule ⊔ U'.toSubmodule)
    rw [Module.finrank_fin_fun] at h2
    omega
  · exfalso
    have heq : U.toSubmodule = U'.toSubmodule :=
      Submodule.eq_of_le_of_finrank_eq h (by rw [hdU, hdU'])
    let f : U.toRepresentation.Equiv U'.toRepresentation :=
      Representation.Equiv.mk (LinearEquiv.ofEq _ _ heq) fun g => LinearMap.ext fun x => rfl
    exact hne.false ((e.symm.trans f).trans e')

end Frob

theorem binary_coords_elim {G : Type} [Group G] (W : Type) [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (τ : Representation (ZMod 2) G W) (hτ : τ.IsIrreducible)
    {P : Prop}
    (hP : ∀ (N : G →* Matrix (Fin (finrank (ZMod 2) W)) (Fin (finrank (ZMod 2) W)) (ZMod 2)),
      (matrixBaseChange (RingHom.id (ZMod 2)) N).IsIrreducible →
      Nonempty (τ.Equiv (matrixBaseChange (RingHom.id (ZMod 2)) N)) →
      ∀ U : Subrepresentation
        (matrixBaseChange ((toField (AlgebraicClosure (ZMod 2))).comp ofPrime) N),
        U ≠ ⊥ → U.toRepresentation.IsIrreducible → P) : P := by
  classical
  have hnt := nontrivial_of_isIrreducible τ
  let eW := (Module.finBasis (ZMod 2) W).equivFun
  let τ' := transportRep eW τ
  have hτ' : τ'.IsIrreducible := isIrreducible_of_equiv (transportRepEquiv eW τ) hτ
  let N := repMatrix τ'
  have hN : matrixBaseChange (RingHom.id (ZMod 2)) N = τ' := matrixBaseChange_repMatrix τ'
  have hNirr : (matrixBaseChange (RingHom.id (ZMod 2)) N).IsIrreducible := by
    rw [hN]
    exact hτ'
  have hτN : Nonempty (τ.Equiv (matrixBaseChange (RingHom.id (ZMod 2)) N)) := by
    rw [hN]
    exact ⟨transportRepEquiv eW τ⟩
  have hm : 0 < finrank (ZMod 2) W := Module.finrank_pos
  have : Nonempty (Fin (finrank (ZMod 2) W)) := ⟨⟨0, hm⟩⟩
  obtain ⟨U, hU0, hUirr⟩ := exists_isIrreducible_subrepresentation
    (matrixBaseChange ((toField (AlgebraicClosure (ZMod 2))).comp ofPrime) N)
  exact hP N hNirr hτN U hU0 hUirr

theorem incl_comp_ne_zero {G k V W : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] {ρ : Representation k G V} (U : Subrepresentation ρ)
    (hU0 : U ≠ ⊥) {σ : Representation k G W} (e : U.toRepresentation.Equiv σ) :
    (⟨U.toSubmodule.subtype, fun _ => LinearMap.ext fun _ => rfl⟩ :
      U.toRepresentation.IntertwiningMap ρ).comp e.symm.toIntertwiningMap ≠ 0 := by
  obtain ⟨u, huU, hu0⟩ : ∃ u ∈ U, u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hU0
    ext x
    exact ⟨fun hx => (Submodule.mem_bot k).mpr (hcon x hx),
      fun hx => (Submodule.mem_bot k).mp hx ▸ Submodule.zero_mem _⟩
  intro h0
  apply hu0
  have h1 := congrArg (fun f : σ.IntertwiningMap ρ => f (e ⟨u, huU⟩)) h0
  change U.toSubmodule.subtype (e.symm (e ⟨u, huU⟩)) = 0 at h1
  rw [Representation.Equiv.symm_apply_apply] at h1
  exact h1

end CFSG.Quasithin.B45Mat
