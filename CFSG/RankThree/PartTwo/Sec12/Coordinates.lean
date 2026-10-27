module

public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.Classical.TransvectionReciprocalPair

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

variable {G : Type*} [Group G]

theorem exists_coords {A : Subgroup G} [Finite A] (hA : CFSG.Assembly.IsElemAbelian 3 A) {n : ℕ}
    (hcard : Nat.card A = 3 ^ n) : Nonempty (Multiplicative (Fin n → ZMod 3) ≃* A) := by
  classical
  let _ : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := fun x y => hA.1.is_comm.comm x y }
  let _ : Module (ZMod 3) (Additive A) := AddCommGroup.zmodModule (n := 3) fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, ofMul_eq_zero]
    exact Subtype.ext (hA.2 _ (Additive.toMul x).2)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfin : Module.finrank (ZMod 3) (Additive A) = n := by
    have h := FiniteField.pow_finrank_eq_natCard 3 (Additive A)
    have h' : Nat.card (Additive A) = 3 ^ n := hcard
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) (h.trans h')
  let b := Module.finBasisOfFinrankEq (ZMod 3) (Additive A) hfin
  exact ⟨MulEquiv.toAdditiveRight.symm b.equivFun.symm.toAddEquiv⟩

section Coords

variable {A : Subgroup G} {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
  (f : Multiplicative V ≃* A)

@[expose] def coordAdd (σ : MulAut A) : V ≃+ V :=
  MulEquiv.toAdditive ((f.trans σ).trans f.symm)

@[expose] def coordLin (σ : MulAut A) : V ≃ₗ[ZMod 3] V :=
  (coordAdd f σ).toLinearEquiv fun c v => ZMod.map_smul (coordAdd f σ).toAddMonoidHom c v

theorem coordLin_apply (σ : MulAut A) (v : V) :
    coordLin f σ v = Multiplicative.toAdd (f.symm (σ (f (Multiplicative.ofAdd v)))) :=
  rfl

@[expose] def coordHom : MulAut A →* (V ≃ₗ[ZMod 3] V) where
  toFun := coordLin f
  map_one' := by
    ext v
    simp [coordLin_apply]
  map_mul' σ τ := by
    ext v
    simp [coordLin_apply]

theorem coordHom_apply (σ : MulAut A) (v : V) :
    coordHom f σ v = Multiplicative.toAdd (f.symm (σ (f (Multiplicative.ofAdd v)))) :=
  rfl

theorem coordHom_injective : Function.Injective (coordHom f) := by
  intro σ τ h
  ext a
  have := congrArg (fun φ => f (Multiplicative.ofAdd (φ (Multiplicative.toAdd (f.symm a))))) h
  simpa [coordHom_apply] using congrArg Subtype.val this

@[expose] def wAction : Subgroup.normalizer (A : Set G) →* (V ≃ₗ[ZMod 3] V) :=
  (coordHom f).comp A.normalizerMonoidHom

theorem wAction_apply (g : Subgroup.normalizer (A : Set G)) (v : V) :
    ((f (Multiplicative.ofAdd (wAction f g v)) : A) : G) =
      (g : G) * (f (Multiplicative.ofAdd v) : G) * (g : G)⁻¹ := by
  simp [wAction, coordHom_apply]

@[expose] def coordVec (c : A) : V := Multiplicative.toAdd (f.symm c)

omit [Module (ZMod 3) V] in
theorem coordVec_ne_zero {c : A} (hc : c ≠ 1) : coordVec f c ≠ 0 := by
  intro h
  apply hc
  have h1 : f.symm c = 1 := by
    rw [coordVec] at h
    exact (MulEquiv.map_eq_one_iff f.symm).mp (by simpa using congrArg Multiplicative.ofAdd h)
      |> fun h2 => (MulEquiv.map_eq_one_iff f.symm).mpr h2
  simpa using congrArg f h1

theorem coordHom_apply_sub_mem {c : A} {σ : MulAut A} (hσ : σ ∈ transvectionGroup A c)
    (v : V) : coordHom f σ v - v ∈ Submodule.span (ZMod 3) {coordVec f c} := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hσ.2 (f (Multiplicative.ofAdd v)))
  rw [Submodule.mem_span_singleton]
  refine ⟨(k : ZMod 3), ?_⟩
  have h : Multiplicative.toAdd (f.symm (c ^ k)) =
      Multiplicative.toAdd (f.symm (σ (f (Multiplicative.ofAdd v)) *
        (f (Multiplicative.ofAdd v))⁻¹)) := by rw [hk]
  rw [map_mul, map_inv, map_zpow, toAdd_mul, toAdd_inv, toAdd_zpow, MulEquiv.symm_apply_apply,
    toAdd_ofAdd] at h
  rw [Int.cast_smul_eq_zsmul, coordHom_apply, coordVec, sub_eq_add_neg]
  exact h

theorem coordHom_apply_coordVec {c : A} {σ : MulAut A} (hσ : σ ∈ transvectionGroup A c) :
    coordHom f σ (coordVec f c) = coordVec f c := by
  simp [coordHom_apply, coordVec, hσ.1]

theorem coordHom_isTransvection {c : A} (hc : c ≠ 1) {σ : MulAut A}
    (hσ : σ ∈ transvectionGroup A c) (hσ1 : σ ≠ 1) :
    (∃ v φ, CFSG.RankThree.Classical.IsTransvectionWith (coordHom f σ) v φ) ∧
      LinearMap.range ((coordHom f σ : V →ₗ[ZMod 3] V) - 1) =
        Submodule.span (ZMod 3) {coordVec f c} := by
  set u := coordVec f c with hudef
  have hu : u ≠ 0 := coordVec_ne_zero f hc
  set r := coordHom f σ with hr
  set D : V →ₗ[ZMod 3] V := (r : V →ₗ[ZMod 3] V) - 1 with hDdef
  have hDapp : ∀ x, D x = r x - x := fun x => rfl
  have hD : ∀ x, D x ∈ Submodule.span (ZMod 3) {u} := fun x => by
    rw [hDapp]
    exact coordHom_apply_sub_mem f hσ x
  let φ : Module.Dual (ZMod 3) V :=
    (LinearEquiv.toSpanNonzeroSingleton (ZMod 3) V u hu).symm.toLinearMap ∘ₗ
      D.codRestrict (Submodule.span (ZMod 3) {u}) hD
  have hφ : ∀ x, D x = φ x • u := fun x => by
    have h := LinearEquiv.toSpanNonzeroSingleton_apply (ZMod 3) V u hu (φ x)
    simp only [φ, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.apply_symm_apply] at h
    exact congrArg Subtype.val h
  have hφ0 : φ ≠ 0 := by
    intro h0
    apply hσ1
    apply coordHom_injective f
    rw [map_one]
    ext x
    have h1 := hφ x
    rw [h0, LinearMap.zero_apply, zero_smul, hDapp, sub_eq_zero] at h1
    exact h1
  have hφu : φ u = 0 := by
    have h1 := hφ u
    rw [hDapp, show r u = u from coordHom_apply_coordVec f hσ, sub_self] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_right hu
  refine ⟨⟨u, φ, hu, hφ0, hφu, fun x => ?_⟩, ?_⟩
  · have h1 := hφ x
    rw [hDapp] at h1
    rw [← h1]
    abel
  · apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact hD x
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      obtain ⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hφ0 (LinearMap.ext hcon)
      refine ⟨(φ x)⁻¹ • x, ?_⟩
      rw [map_smul, hφ, smul_smul, inv_mul_cancel₀ hx, one_smul]

end Coords

end CFSG.RankThree.PartTwo.Sec12
