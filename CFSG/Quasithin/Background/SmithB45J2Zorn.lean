module

public import CFSG.CharacterTheory.SteinbergBYNortonCriterion
public import CFSG.CharacterTheory.SteinbergBYFieldFour
public import CFSG.Sporadic.Bridge.J2
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.Quasithin.J2Model

open CFSG.Open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.FieldFour
open CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.J2 TauCeti
open scoped Matrix

section Coordinates

variable {K : Type} [Field K]

@[expose] def zc (x : quasithinZorn K) : Fin 8 → K :=
  ![x.1, x.2.1 0, x.2.1 1, x.2.1 2, x.2.2.1 0, x.2.2.1 1, x.2.2.1 2, x.2.2.2]

@[expose] def zcInv (c : Fin 8 → K) : quasithinZorn K :=
  (c 0, ![c 1, c 2, c 3], ![c 4, c 5, c 6], c 7)

omit [Field K] in
theorem zcInv_zc (x : quasithinZorn K) : zcInv (zc x) = x := by
  obtain ⟨r, u, v, s⟩ := x
  simp only [zcInv, zc]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

omit [Field K] in
theorem zc_zcInv (c : Fin 8 → K) : zc (zcInv c) = c := by
  funext i
  fin_cases i <;> rfl

@[expose] def zcoord : quasithinZorn K ≃ₗ[K] (Fin 8 → K) where
  toFun := zc
  invFun := zcInv
  map_add' x y := by
    funext i
    fin_cases i <;> rfl
  map_smul' c x := by
    funext i
    fin_cases i <;> rfl
  left_inv := zcInv_zc
  right_inv := zc_zcInv

@[expose] def zornFun (M : Matrix (Fin 8) (Fin 8) K) (x : quasithinZorn K) : quasithinZorn K :=
  zcInv (M *ᵥ zc x)

@[expose] def zornHom :
    Matrix.GeneralLinearGroup (Fin 8) K →* (quasithinZorn K ≃ₗ[K] quasithinZorn K) where
  toFun g :=
    { toFun := zornFun (g : Matrix (Fin 8) (Fin 8) K)
      invFun := zornFun ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 8) K) : Matrix (Fin 8) (Fin 8) K)
      map_add' x y := by
        show zcInv (_ *ᵥ zcoord (x + y)) = zcInv (_ *ᵥ zcoord x) + zcInv (_ *ᵥ zcoord y)
        rw [map_add, Matrix.mulVec_add]
        exact zcoord.symm.map_add _ _
      map_smul' c x := by
        show zcInv (_ *ᵥ zcoord (c • x)) = c • zcInv (_ *ᵥ zcoord x)
        rw [map_smul, Matrix.mulVec_smul]
        exact zcoord.symm.map_smul _ _
      left_inv x := by
        show zcInv (_ *ᵥ zc (zcInv (_ *ᵥ zc x))) = x
        rw [zc_zcInv, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec, zcInv_zc]
      right_inv x := by
        show zcInv (_ *ᵥ zc (zcInv (_ *ᵥ zc x))) = x
        rw [zc_zcInv, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec, zcInv_zc] }
  map_one' := by
    refine LinearEquiv.ext fun x => ?_
    show zcInv ((1 : Matrix (Fin 8) (Fin 8) K) *ᵥ zc x) = x
    rw [Matrix.one_mulVec, zcInv_zc]
  map_mul' g h := by
    refine LinearEquiv.ext fun x => ?_
    show zcInv (((g * h : Matrix.GeneralLinearGroup (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) *ᵥ
      zc x) = zcInv ((g : Matrix (Fin 8) (Fin 8) K) *ᵥ zc (zcInv ((h : Matrix (Fin 8) (Fin 8) K) *ᵥ
        zc x)))
    rw [zc_zcInv, Units.val_mul, Matrix.mulVec_mulVec]

end Coordinates

section Bilinear

variable {K : Type} [Field K]

@[expose] def zornMulBil : quasithinZorn K →ₗ[K] quasithinZorn K →ₗ[K] quasithinZorn K :=
  LinearMap.mk₂ K quasithinZornMul
    (fun x x' y => by
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
      · simp [quasithinZornMul, Fin.sum_univ_three]
        ring
      · funext i
        fin_cases i <;> simp [quasithinZornMul, quasithinCross] <;> ring
      · funext i
        fin_cases i <;> simp [quasithinZornMul, quasithinCross] <;> ring
      · simp [quasithinZornMul, Fin.sum_univ_three]
        ring)
    (fun c x y => by
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
      · simp [quasithinZornMul, Fin.sum_univ_three]
        ring
      · funext i
        fin_cases i <;> simp [quasithinZornMul, quasithinCross] <;> ring
      · funext i
        fin_cases i <;> simp [quasithinZornMul, quasithinCross] <;> ring
      · simp [quasithinZornMul, Fin.sum_univ_three]
        ring)
    (fun x y y' => by
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
      · simp [quasithinZornMul, Fin.sum_univ_three]
        ring
      · funext i
        fin_cases i <;> simp [quasithinZornMul, quasithinCross] <;> ring
      · funext i
        fin_cases i <;> simp [quasithinZornMul, quasithinCross] <;> ring
      · simp [quasithinZornMul, Fin.sum_univ_three]
        ring)
    (fun c x y => by
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
      · simp [quasithinZornMul, Fin.sum_univ_three]
        ring
      · funext i
        fin_cases i <;> simp [quasithinZornMul, quasithinCross] <;> ring
      · funext i
        fin_cases i <;> simp [quasithinZornMul, quasithinCross] <;> ring
      · simp [quasithinZornMul, Fin.sum_univ_three]
        ring)

theorem zornMulBil_apply (x y : quasithinZorn K) : zornMulBil x y = quasithinZornMul x y := rfl

@[expose] noncomputable def zornBasis : Module.Basis (Fin 8) K (quasithinZorn K) :=
  (Pi.basisFun K (Fin 8)).map zcoord.symm

theorem map_mul_of_basis (f : quasithinZorn K →ₗ[K] quasithinZorn K)
    (h : ∀ i j : Fin 8, f (quasithinZornMul (zornBasis i) (zornBasis j)) =
      quasithinZornMul (f (zornBasis i)) (f (zornBasis j))) (x y : quasithinZorn K) :
    f (quasithinZornMul x y) = quasithinZornMul (f x) (f y) := by
  have key : (zornMulBil.compl₂ f).comp f = (LinearMap.compr₂ zornMulBil f) := by
    refine LinearMap.ext_basis zornBasis zornBasis fun i j => ?_
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearMap.compr₂_apply,
      zornMulBil_apply]
    exact (h i j).symm
  have := congrArg (fun F => F x y) key
  simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearMap.compr₂_apply,
    zornMulBil_apply] at this
  exact this.symm

end Bilinear

@[expose] def j2MatA : Matrix (Fin 8) (Fin 8) FieldFour :=
  untab #v[#v[ω₂, ω₂, ω₂, ω₂, 0, ω₂, 1, ω],
    #v[1, ω, ω₂, 1, ω, ω, ω₂, 1],
    #v[0, ω, 0, 0, 0, ω, ω, 0],
    #v[ω, ω₂, ω₂, ω₂, 0, ω, ω₂, ω],
    #v[0, 1, 0, 0, 0, ω, ω, 0],
    #v[0, 0, ω₂, ω, ω, ω₂, 1, 0],
    #v[ω₂, 0, ω₂, ω₂, 0, 0, ω₂, ω₂],
    #v[ω, ω₂, ω₂, ω₂, 0, ω₂, 1, ω₂]]

@[expose] def j2MatB : Matrix (Fin 8) (Fin 8) FieldFour :=
  untab #v[#v[ω₂, 1, 0, ω₂, 0, ω, ω, ω],
    #v[1, ω, 0, ω, 0, ω, ω₂, 1],
    #v[ω, ω, 1, ω, 1, 0, ω₂, ω],
    #v[1, ω₂, 0, ω, 0, ω₂, ω₂, 1],
    #v[0, 1, ω, ω, ω₂, ω₂, 1, 0],
    #v[0, ω, 0, 0, 0, ω₂, 0, 0],
    #v[1, 0, ω, ω₂, ω₂, ω₂, 0, 1],
    #v[ω, 1, 0, ω₂, 0, ω, ω, ω₂]]

theorem j2MatA_pow_seven : j2MatA ^ 7 = 1 := by decide +kernel

theorem j2MatB_pow_seven : j2MatB ^ 7 = 1 := by decide +kernel

@[expose] def j2GLA : Matrix.GeneralLinearGroup (Fin 8) FieldFour :=
  ⟨j2MatA, j2MatA ^ 6, by rw [← pow_succ', j2MatA_pow_seven],
    by rw [← pow_succ, j2MatA_pow_seven]⟩

@[expose] def j2GLB : Matrix.GeneralLinearGroup (Fin 8) FieldFour :=
  ⟨j2MatB, j2MatB ^ 6, by rw [← pow_succ', j2MatB_pow_seven],
    by rw [← pow_succ, j2MatB_pow_seven]⟩

theorem j2MatA_mul : ∀ i j : Fin 8,
    zornFun j2MatA (quasithinZornMul (zcInv (Pi.single i 1)) (zcInv (Pi.single j 1))) =
      quasithinZornMul (zornFun j2MatA (zcInv (Pi.single i 1)))
        (zornFun j2MatA (zcInv (Pi.single j 1))) := by
  decide +kernel

theorem j2MatB_mul : ∀ i j : Fin 8,
    zornFun j2MatB (quasithinZornMul (zcInv (Pi.single i 1)) (zcInv (Pi.single j 1))) =
      quasithinZornMul (zornFun j2MatB (zcInv (Pi.single i 1)))
        (zornFun j2MatB (zcInv (Pi.single j 1))) := by
  decide +kernel

theorem zornBasis_apply {K : Type} [Field K] (i : Fin 8) :
    (zornBasis i : quasithinZorn K) = zcInv (Pi.single i 1) := by
  simp [zornBasis, zcoord]

@[expose] def j2EquivA : quasithinZorn FieldFour ≃ₗ[FieldFour] quasithinZorn FieldFour :=
  zornHom j2GLA

@[expose] def j2EquivB : quasithinZorn FieldFour ≃ₗ[FieldFour] quasithinZorn FieldFour :=
  zornHom j2GLB

theorem j2EquivA_mul (x y : quasithinZorn FieldFour) :
    j2EquivA (quasithinZornMul x y) = quasithinZornMul (j2EquivA x) (j2EquivA y) :=
  map_mul_of_basis (j2EquivA : quasithinZorn FieldFour →ₗ[FieldFour] quasithinZorn FieldFour)
    (fun i j => by rw [zornBasis_apply, zornBasis_apply]; exact j2MatA_mul i j) x y

theorem j2EquivB_mul (x y : quasithinZorn FieldFour) :
    j2EquivB (quasithinZornMul x y) = quasithinZornMul (j2EquivB x) (j2EquivB y) :=
  map_mul_of_basis (j2EquivB : quasithinZorn FieldFour →ₗ[FieldFour] quasithinZorn FieldFour)
    (fun i j => by rw [zornBasis_apply, zornBasis_apply]; exact j2MatB_mul i j) x y

@[expose] def j2Img (i : ℕ) : Matrix.GeneralLinearGroup (Fin 8) FieldFour :=
  if i = 0 then j2GLA else j2GLB

theorem j2_relators_mat : ∀ v ∈ [r₁L, r₂L, r₃L],
    ((wordProd j2Img v : Matrix.GeneralLinearGroup (Fin 8) FieldFour) :
      Matrix (Fin 8) (Fin 8) FieldFour) = 1 := by
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl <;> decide +kernel

theorem j2_relators : ∀ v ∈ Sporadic.j2Presentation.relatorLetters, wordProd j2Img v = 1 := by
  rw [relatorLetters_eq]
  intro v hv
  exact Units.ext (j2_relators_mat v hv)

@[expose] noncomputable def j2PresHom : Sporadic.j2Presentation.Group →*
    Matrix.GeneralLinearGroup (Fin 8) FieldFour :=
  PresentedGroup.toGroup (lift_relator Sporadic.j2Presentation j2Img j2_relators)

theorem j2PresHom_of (i : Fin Sporadic.j2Presentation.generatorCount) :
    j2PresHom (PresentedGroup.of i) = j2Img i.val :=
  PresentedGroup.toGroup.of _

@[expose] noncomputable def j2Γ₀ :
    Subgroup (quasithinZorn FieldFour ≃ₗ[FieldFour] quasithinZorn FieldFour) :=
  (zornHom.comp j2PresHom).range

theorem zornHom_j2Img (i : ℕ) : zornHom (j2Img i) = if i = 0 then j2EquivA else j2EquivB := by
  unfold j2Img
  split <;> rfl

theorem j2Γ₀_eq : j2Γ₀ = Subgroup.closure {j2EquivA, j2EquivB} := by
  have h2 : Sporadic.j2Presentation.generatorCount = 2 := generatorCount_eq
  rw [j2Γ₀, MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [MonoidHom.comp_apply, j2PresHom_of, zornHom_j2Img]
    split
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ rfl
  · rintro (rfl | hg)
    · refine ⟨PresentedGroup.of ⟨0, by rw [h2]; norm_num⟩, ⟨_, rfl⟩, ?_⟩
      rw [MonoidHom.comp_apply, j2PresHom_of, zornHom_j2Img, ite_eq_left rfl]
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      refine ⟨PresentedGroup.of ⟨1, by rw [h2]; norm_num⟩, ⟨_, rfl⟩, ?_⟩
      rw [MonoidHom.comp_apply, j2PresHom_of, zornHom_j2Img, ite_eq_right one_ne_zero]

theorem j2Γ₀_le_quasithinG2 : j2Γ₀ ≤ quasithinG2 FieldFour := by
  rw [j2Γ₀_eq, Subgroup.closure_le]
  rintro g (rfl | hg)
  · exact Subgroup.subset_closure j2EquivA_mul
  · rw [Set.mem_singleton_iff] at hg
    subst hg
    exact Subgroup.subset_closure j2EquivB_mul

@[expose] noncomputable def j2PresOnto : Sporadic.j2Presentation.Group →* ↥j2Γ₀ :=
  (zornHom.comp j2PresHom).rangeRestrict

theorem j2PresOnto_surjective : Function.Surjective j2PresOnto :=
  MonoidHom.rangeRestrict_surjective _

instance : Finite j2Γ₀ := by
  obtain ⟨hfin, -⟩ := finite_card_le
  exact Finite.of_surjective _ j2PresOnto_surjective

end CFSG.Quasithin.J2Model
