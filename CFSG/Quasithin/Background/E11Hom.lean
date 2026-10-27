module

public import Mathlib.RingTheory.SimpleModule.Isotypic
public import Mathlib.RingTheory.LittleWedderburn
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.FunLike.Fintype

public section

namespace CFSG.Quasithin.G11.E11

variable {R : Type*} [Ring R] {V I : Type*} [AddCommGroup V] [Module R V]
  [AddCommGroup I] [Module R I]

section Hom

variable [IsSimpleModule R I] [Finite I]

open Classical in
noncomputable scoped instance schurField : Field (Module.End R I) :=
  haveI : Finite (Module.End R I) := FunLike.finite (Module.End R I)
  littleWedderburn (Module.End R I)

scoped instance homModule : Module (Module.End R I) (I →ₗ[R] V) where
  smul f φ := φ ∘ₗ f
  one_smul φ := LinearMap.comp_id φ
  mul_smul f g φ := by
    show φ ∘ₗ (f * g) = (φ ∘ₗ g) ∘ₗ f
    rw [LinearMap.comp_assoc, mul_comm f g]
    rfl
  smul_zero _ := LinearMap.zero_comp _
  smul_add _ _ _ := LinearMap.add_comp _ _ _
  add_smul _ _ _ := LinearMap.comp_add _ _ _
  zero_smul _ := LinearMap.comp_zero _

@[simp] theorem smul_apply (f : Module.End R I) (φ : I →ₗ[R] V) (i : I) :
    (f • φ) i = φ (f i) := rfl

omit [Finite I] in
theorem isAtom_range {φ : I →ₗ[R] V} (hφ : φ ≠ 0) : IsAtom (LinearMap.range φ) := by
  have hinj : Function.Injective φ := LinearMap.injective_of_ne_zero hφ
  have : IsSimpleModule R (LinearMap.range φ) :=
    IsSimpleModule.congr (LinearEquiv.ofInjective φ hinj).symm
  exact isSimpleModule_iff_isAtom.1 this

theorem range_smul {f : Module.End R I} (hf : f ≠ 0) (φ : I →ₗ[R] V) :
    LinearMap.range (f • φ) = LinearMap.range φ :=
  LinearMap.range_comp_of_range_eq_top φ
    (LinearMap.range_eq_top.2 (LinearMap.surjective_of_ne_zero hf))

theorem exists_smul_eq_of_range_le {φ φ' : I →ₗ[R] V} (hφ' : φ' ≠ 0)
    (h : LinearMap.range φ ≤ LinearMap.range φ') : ∃ f : Module.End R I, f • φ' = φ := by
  have hinj := LinearMap.injective_of_ne_zero hφ'
  let e := LinearEquiv.ofInjective φ' hinj
  refine ⟨e.symm.toLinearMap ∘ₗ φ.codRestrict (LinearMap.range φ') (fun i => h ⟨i, rfl⟩), ?_⟩
  ext i
  have := e.apply_symm_apply ⟨φ i, h ⟨i, rfl⟩⟩
  exact congrArg Subtype.val this

theorem range_eq_iff {φ φ' : I →ₗ[R] V} (hφ : φ ≠ 0) (hφ' : φ' ≠ 0) :
    LinearMap.range φ = LinearMap.range φ' ↔ ∃ f : Module.End R I, f ≠ 0 ∧ f • φ' = φ := by
  constructor
  · intro h
    obtain ⟨f, hf⟩ := exists_smul_eq_of_range_le hφ' h.le
    refine ⟨f, ?_, hf⟩
    rintro rfl
    exact hφ (by rw [← hf, zero_smul])
  · rintro ⟨f, hf, rfl⟩
    exact range_smul hf φ'

open scoped LinearAlgebra.Projectivization

@[expose] noncomputable def pointRange (p : ℙ (Module.End R I) (I →ₗ[R] V)) : Submodule R V :=
  p.lift (fun φ => LinearMap.range φ.1) (by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ t h
    have ht : t ≠ 0 := by
      rintro rfl
      exact ha (by simpa using h)
    have h' : a = t • b := h
    show LinearMap.range a = LinearMap.range b
    rw [h', range_smul ht])

theorem pointRange_mk (φ : I →ₗ[R] V) (hφ : φ ≠ 0) :
    pointRange (Projectivization.mk (Module.End R I) φ hφ) = LinearMap.range φ := rfl

theorem isAtom_pointRange (p : ℙ (Module.End R I) (I →ₗ[R] V)) : IsAtom (pointRange p) := by
  induction p using Projectivization.ind with
  | h φ hφ => exact isAtom_range hφ

theorem pointRange_injective :
    Function.Injective (pointRange : ℙ (Module.End R I) (I →ₗ[R] V) → Submodule R V) := by
  intro p q h
  induction p using Projectivization.ind with
  | h φ hφ =>
    induction q using Projectivization.ind with
    | h φ' hφ' =>
      rw [pointRange_mk, pointRange_mk] at h
      obtain ⟨f, -, hf⟩ := (range_eq_iff hφ hφ').1 h
      exact (Projectivization.mk_eq_mk_iff' _ φ φ' hφ hφ').2 ⟨f, hf⟩

theorem exists_point_eq {m : Submodule R V} (hm : IsAtom m) (e : m ≃ₗ[R] I) :
    ∃ p : ℙ (Module.End R I) (I →ₗ[R] V), pointRange p = m := by
  have hφ : (m.subtype ∘ₗ e.symm.toLinearMap : I →ₗ[R] V) ≠ 0 := by
    intro h0
    have hbot : m = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have := LinearMap.congr_fun h0 (e ⟨x, hx⟩)
      simpa using this
    exact hm.1 hbot
  refine ⟨Projectivization.mk _ _ hφ, ?_⟩
  rw [pointRange_mk, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
    Submodule.range_subtype]

end Hom

section Coord

variable [IsSimpleModule R I] [Finite I] {n : ℕ} (e : V ≃ₗ[R] (Fin n → I))

@[expose] noncomputable def coordEquiv :
    (I →ₗ[R] V) ≃ₗ[Module.End R I] (Fin n → Module.End R I) where
  toFun φ j := (LinearMap.proj j : (Fin n → I) →ₗ[R] I) ∘ₗ (e : V →ₗ[R] (Fin n → I)) ∘ₗ φ
  map_add' φ φ' := by
    ext j i
    simp
  map_smul' f φ := by
    ext j i
    show (LinearMap.proj j : (Fin n → I) →ₗ[R] I) (e (φ (f i))) = (f * _) i
    rw [mul_comm]
    rfl
  invFun c := (e.symm : (Fin n → I) →ₗ[R] V) ∘ₗ LinearMap.pi c
  left_inv φ := by
    ext i
    simp
  right_inv c := by
    ext j i
    simp

include e in
theorem finrank_hom_eq : Module.finrank (Module.End R I) (I →ₗ[R] V) = n := by
  rw [(coordEquiv e).finrank_eq, Module.finrank_fin_fun]

omit [IsSimpleModule R I] in
theorem finite_hom [Finite V] : Finite (I →ₗ[R] V) := FunLike.finite (I →ₗ[R] V)

include e in
omit [IsSimpleModule R I] [Finite I] in
theorem natCard_eq_pow : Nat.card V = Nat.card I ^ n := by
  rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n),
    Fintype.card_fin]

end Coord

section Postcomp

variable [IsSimpleModule R I] [Finite I]

@[expose] noncomputable def postcomp :
    Module.End R V →+* Module.End (Module.End R I) (I →ₗ[R] V) where
  toFun g :=
    { toFun := fun φ => g ∘ₗ φ
      map_add' := fun φ φ' => LinearMap.comp_add _ _ _
      map_smul' := fun f φ => rfl }
  map_one' := by
    ext φ i
    rfl
  map_mul' g g' := by
    ext φ i
    rfl
  map_zero' := by
    ext φ i
    rfl
  map_add' g g' := by
    ext φ i
    rfl

theorem postcomp_apply (g : Module.End R V) (φ : I →ₗ[R] V) (i : I) :
    postcomp g φ i = g (φ i) := rfl

theorem postcomp_injective {n : ℕ} (e : V ≃ₗ[R] (Fin n → I)) :
    Function.Injective (postcomp (R := R) (I := I) (V := V)) := by
  refine (injective_iff_map_eq_zero _).2 fun g hg => ?_
  ext v
  have h1 : ∀ j : Fin n, ∀ i : I, g (e.symm (Pi.single j i)) = 0 := by
    intro j i
    have := LinearMap.congr_fun (LinearMap.congr_fun hg
      (e.symm.toLinearMap ∘ₗ LinearMap.single R (fun _ : Fin n => I) j)) i
    simpa [postcomp_apply] using this
  have h2 : v = e.symm (∑ j, Pi.single j ((e v) j)) := by
    rw [Finset.univ_sum_single, e.symm_apply_apply]
  rw [h2, map_sum, map_sum]
  simp [h1]

section Card

variable {n : ℕ} (e : V ≃ₗ[R] (Fin n → I))

include e in
omit [IsSimpleModule R I] [Finite I] in
theorem natCard_end : Nat.card (Module.End R V) = Nat.card (Module.End R I) ^ (n * n) := by
  have h : Module.End R V ≃ Matrix (Fin n) (Fin n) (Module.End R I) :=
    e.conjRingEquiv.toEquiv.trans (endVecRingEquivMatrixEnd (Fin n) R I).toEquiv
  rw [Nat.card_congr h]
  simp only [Matrix, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin,
    pow_mul]

include e in
theorem natCard_end_hom :
    Nat.card (Module.End (Module.End R I) (I →ₗ[R] V)) = Nat.card (Module.End R I) ^ (n * n) := by
  let b : Module.Basis (Fin n) (Module.End R I) (I →ₗ[R] V) :=
    Module.Basis.ofEquivFun (coordEquiv e)
  have h : Module.End (Module.End R I) (I →ₗ[R] V) ≃ Matrix (Fin n) (Fin n) (Module.End R I) :=
    (LinearMap.toMatrix b b).toEquiv
  rw [Nat.card_congr h]
  simp only [Matrix, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin,
    pow_mul]

include e in
theorem postcomp_bijective [Finite V] :
    Function.Bijective (postcomp (R := R) (I := I) (V := V)) := by
  have : Finite (I →ₗ[R] V) := finite_hom
  have : Finite (Module.End (Module.End R I) (I →ₗ[R] V)) := FunLike.finite _
  refine (postcomp_injective e).bijective_of_nat_card_le ?_
  rw [natCard_end_hom e, natCard_end e]

end Card

end Postcomp

section Sub

variable [IsSimpleModule R I] [Finite I]

@[expose] def homInto (M : Submodule R V) : Submodule (Module.End R I) (I →ₗ[R] V) where
  carrier := {φ | ∀ i, φ i ∈ M}
  add_mem' := fun {_ _} h h' i => M.add_mem (h i) (h' i)
  zero_mem' := fun _ => M.zero_mem
  smul_mem' := fun f _ h i => h (f i)

theorem mem_homInto {M : Submodule R V} {φ : I →ₗ[R] V} :
    φ ∈ homInto M ↔ ∀ i, φ i ∈ M := Iff.rfl

theorem mem_homInto_iff_range_le {M : Submodule R V} {φ : I →ₗ[R] V} :
    φ ∈ homInto M ↔ LinearMap.range φ ≤ M := by
  rw [mem_homInto]
  exact ⟨fun h _ ⟨i, hi⟩ => hi ▸ h i, fun h i => h ⟨i, rfl⟩⟩

@[expose] def subtypeComp (M : Submodule R V) : (I →ₗ[R] M) →ₗ[Module.End R I] (I →ₗ[R] V) where
  toFun φ' := M.subtype ∘ₗ φ'
  map_add' _ _ := LinearMap.comp_add _ _ _
  map_smul' _ _ := rfl

@[expose] noncomputable def homIntoEquiv (M : Submodule R V) :
    (I →ₗ[R] M) ≃ₗ[Module.End R I] homInto (I := I) M :=
  LinearEquiv.ofBijective ((subtypeComp M).codRestrict (homInto M) fun φ' i => (φ' i).2)
    ⟨fun φ₁ φ₂ h => by
      ext i
      exact LinearMap.congr_fun (congrArg Subtype.val h) i,
     fun φ => ⟨φ.1.codRestrict M φ.2, Subtype.ext (by ext i; rfl)⟩⟩

theorem natCard_eq_pow_finrank_homInto [Finite V] [IsSemisimpleModule R V]
    (hV : IsIsotypicOfType R V I) (M : Submodule R V) :
    Nat.card M = Nat.card I ^ Module.finrank (Module.End R I) (homInto (I := I) M) := by
  have hM : IsIsotypicOfType R M I := hV.of_injective M.subtype M.injective_subtype
  have : Module.Finite R M := Module.Finite.of_finite
  obtain ⟨m, ⟨eM⟩⟩ := hM.linearEquiv_fun
  rw [← (homIntoEquiv (I := I) M).finrank_eq, finrank_hom_eq eM, natCard_eq_pow eM]

end Sub

end CFSG.Quasithin.G11.E11
