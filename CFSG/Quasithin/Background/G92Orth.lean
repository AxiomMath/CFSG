module

public import CFSG.Quasithin.Background.G11Defs
public import CFSG.Quasithin.EmptyFaithful.SzN31CntLinA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.G92

open CFSG.Quasithin.G11
open scoped Matrix

@[expose] def IsOrth4ModuleG92 {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (G' : Subgroup (GLV V)) (U : Submodule (ZMod 2) V) : Prop :=
  ∃ (φ : ↥G' ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) ×
        Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    (ψ : ↥U ≃ₗ[ZMod 2] Matrix (Fin 2) (Fin 2) (ZMod 2)),
    ∀ (g : ↥G') (u u' : ↥U), (u' : V) = (g : GLV V) (u : V) →
      ψ u' = ((φ g).1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) * ψ u *
        ((φ g).2 : Matrix (Fin 2) (Fin 2) (ZMod 2)).transpose

private abbrev Mat2 : Type := Matrix (Fin 2) (Fin 2) (ZMod 2)

private abbrev SL2 : Type := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)

private def XM : Mat2 := !![0, 1; 1, 1]

private def SM : Mat2 := !![1, 1; 0, 1]

private def XG : SL2 := ⟨XM, by rw [XM, Matrix.det_fin_two_of]; decide⟩

private def SG : SL2 := ⟨SM, by rw [SM, Matrix.det_fin_two_of]; decide⟩

private theorem all_sl2 (A : SL2) : A = 1 ∨ A = XG ∨ A = XG * XG ∨ A = SG ∨ A = SG * XG ∨
    A = SG * XG * XG := by
  revert A
  decide

private theorem sl2_faithful (A B : SL2) (h : ∀ Y : Mat2, (A : Mat2) * Y * (B : Mat2)ᵀ = Y) :
    A = 1 ∧ B = 1 := by
  revert A B
  decide

private theorem mem_closure_XS (A : SL2) : A ∈ Subgroup.closure ({XG, SG} : Set SL2) := by
  have hX : XG ∈ Subgroup.closure ({XG, SG} : Set SL2) := Subgroup.subset_closure (by simp)
  have hS : SG ∈ Subgroup.closure ({XG, SG} : Set SL2) := Subgroup.subset_closure (by simp)
  rcases all_sl2 A with rfl | rfl | rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact hX
  · exact mul_mem hX hX
  · exact hS
  · exact mul_mem hS hX
  · exact mul_mem (mul_mem hS hX) hX

private theorem coe_mul_inv (A : SL2) : (A : Mat2) * ((A⁻¹ : SL2) : Mat2) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
  rfl

private theorem coe_inv_mul (A : SL2) : ((A⁻¹ : SL2) : Mat2) * (A : Mat2) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
  rfl

private def lamPerm (p : SL2 × SL2) : Equiv.Perm Mat2 where
  toFun Y := (p.1 : Mat2) * Y * (p.2 : Mat2)ᵀ
  invFun Y := ((p.1⁻¹ : SL2) : Mat2) * Y * ((p.2⁻¹ : SL2) : Mat2)ᵀ
  left_inv Y := by
    calc ((p.1⁻¹ : SL2) : Mat2) * ((p.1 : Mat2) * Y * (p.2 : Mat2)ᵀ) * ((p.2⁻¹ : SL2) : Mat2)ᵀ
        = (((p.1⁻¹ : SL2) : Mat2) * (p.1 : Mat2)) * Y *
            (((p.2⁻¹ : SL2) : Mat2) * (p.2 : Mat2))ᵀ := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = Y := by rw [coe_inv_mul, coe_inv_mul]; simp
  right_inv Y := by
    calc (p.1 : Mat2) * (((p.1⁻¹ : SL2) : Mat2) * Y * ((p.2⁻¹ : SL2) : Mat2)ᵀ) * (p.2 : Mat2)ᵀ
        = ((p.1 : Mat2) * ((p.1⁻¹ : SL2) : Mat2)) * Y *
            ((p.2 : Mat2) * ((p.2⁻¹ : SL2) : Mat2))ᵀ := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = Y := by rw [coe_mul_inv, coe_mul_inv]; simp

private def lam : SL2 × SL2 →* Equiv.Perm Mat2 where
  toFun := lamPerm
  map_one' := by
    ext Y : 1
    simp [lamPerm]
  map_mul' p q := by
    ext Y : 1
    simp [lamPerm, Matrix.transpose_mul, Matrix.mul_assoc]

private theorem lam_apply (p : SL2 × SL2) (Y : Mat2) :
    lam p Y = (p.1 : Mat2) * Y * (p.2 : Mat2)ᵀ := rfl

private theorem lam_injective : Function.Injective lam := by
  rw [injective_iff_map_eq_one]
  rintro ⟨A, B⟩ h
  have h' : ∀ Y : Mat2, (A : Mat2) * Y * (B : Mat2)ᵀ = Y := fun Y => by
    have := DFunLike.congr_fun h Y
    simpa [lam_apply] using this
  obtain ⟨rfl, rfl⟩ := sl2_faithful A B h'
  rfl

private theorem actX (Y : Mat2) :
    XM * Y * (1 : Mat2)ᵀ = !![Y 1 0, Y 1 1; Y 0 0 + Y 1 0, Y 0 1 + Y 1 1] := by
  revert Y
  decide

private theorem actS (Y : Mat2) :
    SM * Y * (1 : Mat2)ᵀ = !![Y 0 0 + Y 1 0, Y 0 1 + Y 1 1; Y 1 0, Y 1 1] := by
  revert Y
  decide

private theorem actXt (Y : Mat2) :
    (1 : Mat2) * Y * XMᵀ = !![Y 0 1, Y 0 0 + Y 0 1; Y 1 1, Y 1 0 + Y 1 1] := by
  revert Y
  decide

private theorem actSt (Y : Mat2) :
    (1 : Mat2) * Y * SMᵀ = !![Y 0 0 + Y 0 1, Y 0 1; Y 1 0 + Y 1 1, Y 1 1] := by
  revert Y
  decide

private theorem hom_mem_of_gen (f : SL2 →* Equiv.Perm Mat2) (R : Subgroup (Equiv.Perm Mat2))
    (hX : f XG ∈ R) (hS : f SG ∈ R) (A : SL2) : f A ∈ R := by
  have hle : Subgroup.closure ({XG, SG} : Set SL2) ≤ R.comap f := by
    rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact hX
    · exact hS
  exact hle (mem_closure_XS A)

section Module

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

open CFSG.Quasithin.SzN31 CFSG.Quasithin.SzN31.CntLin

private theorem cube_apply {x : GLV V} (hx : x ^ 3 = 1) (v : V) : x (x (x v)) = v := by
  have h := congrArg (fun f : GLV V => f v) hx
  simpa [pow_succ] using h

private theorem inv_apply_cube {x : GLV V} (hx : x ^ 3 = 1) (v : V) : x⁻¹ v = x (x v) := by
  calc x⁻¹ v = x⁻¹ (x (x (x v))) := by rw [cube_apply hx]
    _ = x (x v) := inv_apply_apply x _

private theorem comm_apply {f g : GLV V} (h : f * g = g * f) (v : V) : f (g v) = g (f v) := by
  have := congrArg (fun k : GLV V => k v) h
  simpa only [LinearEquiv.mul_apply] using this

private theorem sq_apply {x : GLV V} (hx : x ^ 3 = 1) {U : Submodule (ZMod 2) V}
    (hU : ∀ u ∈ U, x u ∈ U) (hfp : ∀ u ∈ U, x u = u → u = 0) {u : V} (hu : u ∈ U) :
    x (x u) = x u + u := by
  have hxu : x u ∈ U := hU u hu
  have hxxu : x (x u) ∈ U := hU _ hxu
  have hs : x (x u) + x u + u ∈ U := U.add_mem (U.add_mem hxxu hxu) hu
  have hfix : x (x (x u) + x u + u) = x (x u) + x u + u := by
    rw [map_add, map_add, cube_apply hx]
    abel
  have h0 := hfp _ hs hfix
  have h2 : x (x u) + (x u + u) = 0 := by rw [← add_assoc]; exact h0
  exact (eq_neg_of_add_eq_zero_left h2).trans (zmod2_neg _)

private theorem dih_apply {x a : GLV V} (hx : x ^ 3 = 1) (hax : a * x * a⁻¹ = x⁻¹)
    {U : Submodule (ZMod 2) V} (hxU : ∀ u ∈ U, x u ∈ U) (haU : ∀ u ∈ U, a u ∈ U)
    (hfp : ∀ u ∈ U, x u = u → u = 0) {u : V} (hu : u ∈ U) : a (x u) = x (a u) + a u := by
  rw [dihedral_apply_x hax, inv_apply_cube hx]
  exact sq_apply hx hxU hfp (haU u hu)

private theorem exists_vec [Finite V] (x₁ a₁ x₂ a₂ : GLV V) (U : Submodule (ZMod 2) V)
    (hdim : Module.finrank (ZMod 2) U = 4)
    (hx₁ : x₁ ^ 3 = 1) (hx₂ : x₂ ^ 3 = 1) (ha₁ : a₁ * a₁ = 1) (ha₂ : a₂ * a₂ = 1)
    (hax₁ : a₁ * x₁ * a₁⁻¹ = x₁⁻¹) (hax₂ : a₂ * x₂ * a₂⁻¹ = x₂⁻¹)
    (hax : a₁ * x₂ = x₂ * a₁) (haa : a₁ * a₂ = a₂ * a₁)
    (hx₁U : ∀ u ∈ U, x₁ u ∈ U) (ha₁U : ∀ u ∈ U, a₁ u ∈ U)
    (hx₂U : ∀ u ∈ U, x₂ u ∈ U) (ha₂U : ∀ u ∈ U, a₂ u ∈ U)
    (hfp₁ : ∀ u ∈ U, x₁ u = u → u = 0) (hfp₂ : ∀ u ∈ U, x₂ u = u → u = 0) :
    ∃ w ∈ U, a₁ w = w ∧ a₂ w = w ∧ ∀ u ∈ U, ∃ c₁ c₂ c₃ c₄ : ZMod 2,
      u = c₁ • w + c₂ • x₂ w + c₃ • x₁ w + c₄ • x₁ (x₂ w) := by
  have hodd : Odd 3 := ⟨1, rfl⟩
  have hfpx₁ : fixSp V x₁ U = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvU, hv'⟩ := mem_fixSp.1 hv
    rw [hfp₁ v hvU hv']
    exact zero_mem _
  obtain ⟨-, hsup₁⟩ := dihedral_split x₁ a₁ hx₁ hodd ha₁ hax₁ U hx₁U ha₁U hfpx₁
  have hdimW : Module.finrank (ZMod 2) (fixSp V a₁ U) = 2 := by
    have := dihedral_finrank x₁ a₁ hx₁ hodd ha₁ hax₁ U hx₁U ha₁U hfpx₁
    omega
  have hWx : ∀ w ∈ fixSp V a₁ U, x₂ w ∈ fixSp V a₁ U := by
    intro w hw
    obtain ⟨hwU, hw'⟩ := mem_fixSp.1 hw
    refine mem_fixSp.2 ⟨hx₂U w hwU, ?_⟩
    rw [comm_apply hax, hw']
  have hWa : ∀ w ∈ fixSp V a₁ U, a₂ w ∈ fixSp V a₁ U := by
    intro w hw
    obtain ⟨hwU, hw'⟩ := mem_fixSp.1 hw
    refine mem_fixSp.2 ⟨ha₂U w hwU, ?_⟩
    rw [comm_apply haa, hw']
  have hfpW : fixSp V x₂ (fixSp V a₁ U) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvW, hv'⟩ := mem_fixSp.1 hv
    rw [hfp₂ v (mem_fixSp.1 hvW).1 hv']
    exact zero_mem _
  obtain ⟨-, hsup₂⟩ := dihedral_split x₂ a₂ hx₂ hodd ha₂ hax₂ _ hWx hWa hfpW
  have hdimZ : Module.finrank (ZMod 2) (fixSp V a₂ (fixSp V a₁ U)) = 1 := by
    have := dihedral_finrank x₂ a₂ hx₂ hodd ha₂ hax₂ _ hWx hWa hfpW
    omega
  obtain ⟨v, -, hv⟩ := finrank_eq_one_iff'.1 hdimZ
  have hv1 := mem_fixSp.1 v.2
  have hv2 := mem_fixSp.1 hv1.1
  have hZ : ∀ z ∈ fixSp V a₂ (fixSp V a₁ U), ∃ c : ZMod 2, c • (v : V) = z := by
    intro z hz
    obtain ⟨c, hc⟩ := hv ⟨z, hz⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  refine ⟨(v : V), hv2.1, hv2.2, hv1.2, ?_⟩
  intro u hu
  have hu' : u ∈ fixSp V a₁ U ⊔ (fixSp V a₁ U).map (x₁ : V →ₗ[ZMod 2] V) := by
    rw [hsup₁]
    exact hu
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hu'
  obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.1 hz
  have hy' : y ∈ fixSp V a₂ (fixSp V a₁ U) ⊔
      (fixSp V a₂ (fixSp V a₁ U)).map (x₂ : V →ₗ[ZMod 2] V) := by
    rw [hsup₂]
    exact hy
  have hw'' : w' ∈ fixSp V a₂ (fixSp V a₁ U) ⊔
      (fixSp V a₂ (fixSp V a₁ U)).map (x₂ : V →ₗ[ZMod 2] V) := by
    rw [hsup₂]
    exact hw'
  obtain ⟨y₁, hy₁, t, ht, rfl⟩ := Submodule.mem_sup.1 hy'
  obtain ⟨y₂, hy₂, rfl⟩ := Submodule.mem_map.1 ht
  obtain ⟨w₁, hw₁, t', ht', rfl⟩ := Submodule.mem_sup.1 hw''
  obtain ⟨w₂, hw₂, rfl⟩ := Submodule.mem_map.1 ht'
  obtain ⟨c₁, rfl⟩ := hZ y₁ hy₁
  obtain ⟨c₂, rfl⟩ := hZ y₂ hy₂
  obtain ⟨c₃, rfl⟩ := hZ w₁ hw₁
  obtain ⟨c₄, rfl⟩ := hZ w₂ hw₂
  refine ⟨c₁, c₂, c₃, c₄, ?_⟩
  simp [add_assoc]

private def thetaFun {E : Type} [AddCommGroup E] [Module (ZMod 2) E] (w₀₀ w₀₁ w₁₀ w₁₁ : E)
    (Y : Mat2) : E :=
  Y 0 0 • w₀₀ + Y 0 1 • w₀₁ + Y 1 0 • w₁₀ + Y 1 1 • w₁₁

private def theta {E : Type} [AddCommGroup E] [Module (ZMod 2) E] (w₀₀ w₀₁ w₁₀ w₁₁ : E) :
    Mat2 →ₗ[ZMod 2] E where
  toFun := thetaFun w₀₀ w₀₁ w₁₀ w₁₁
  map_add' Y Z := by
    simp only [thetaFun, Matrix.add_apply, add_smul]
    abel
  map_smul' c Y := by
    simp only [thetaFun, Matrix.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add]

private theorem theta_apply {E : Type} [AddCommGroup E] [Module (ZMod 2) E]
    (w₀₀ w₀₁ w₁₀ w₁₁ : E) (Y : Mat2) :
    theta w₀₀ w₀₁ w₁₀ w₁₁ Y = Y 0 0 • w₀₀ + Y 0 1 • w₀₁ + Y 1 0 • w₁₀ + Y 1 1 • w₁₁ := rfl

private theorem exists_psi [Finite V] (x₁ a₁ x₂ a₂ : GLV V) (U : Submodule (ZMod 2) V)
    (hdim : Module.finrank (ZMod 2) U = 4)
    (hx₁ : x₁ ^ 3 = 1) (hx₂ : x₂ ^ 3 = 1) (ha₁ : a₁ * a₁ = 1) (ha₂ : a₂ * a₂ = 1)
    (hax₁ : a₁ * x₁ * a₁⁻¹ = x₁⁻¹) (hax₂ : a₂ * x₂ * a₂⁻¹ = x₂⁻¹)
    (hxx : x₁ * x₂ = x₂ * x₁) (hxa : x₁ * a₂ = a₂ * x₁) (hax : a₁ * x₂ = x₂ * a₁)
    (haa : a₁ * a₂ = a₂ * a₁)
    (hx₁U : ∀ u ∈ U, x₁ u ∈ U) (ha₁U : ∀ u ∈ U, a₁ u ∈ U)
    (hx₂U : ∀ u ∈ U, x₂ u ∈ U) (ha₂U : ∀ u ∈ U, a₂ u ∈ U)
    (hfp₁ : ∀ u ∈ U, x₁ u = u → u = 0) (hfp₂ : ∀ u ∈ U, x₂ u = u → u = 0) :
    ∃ ψ : ↥U ≃ₗ[ZMod 2] Mat2,
      (∀ u u' : ↥U, (u' : V) = x₁ u → ψ u' = XM * ψ u * (1 : Mat2)ᵀ) ∧
      (∀ u u' : ↥U, (u' : V) = a₁ u → ψ u' = SM * ψ u * (1 : Mat2)ᵀ) ∧
      (∀ u u' : ↥U, (u' : V) = x₂ u → ψ u' = (1 : Mat2) * ψ u * XMᵀ) ∧
      (∀ u u' : ↥U, (u' : V) = a₂ u → ψ u' = (1 : Mat2) * ψ u * SMᵀ) := by
  obtain ⟨w, hwU, hwa₁, hwa₂, hspan⟩ := exists_vec x₁ a₁ x₂ a₂ U hdim hx₁ hx₂ ha₁ ha₂ hax₁ hax₂
    hax haa hx₁U ha₁U hx₂U ha₂U hfp₁ hfp₂
  have hw₂U : x₂ w ∈ U := hx₂U w hwU
  have hw₁U : x₁ w ∈ U := hx₁U w hwU
  have hw₁₂U : x₁ (x₂ w) ∈ U := hx₁U _ hw₂U
  let Θ : Mat2 →ₗ[ZMod 2] V := theta w (x₂ w) (x₁ w) (x₁ (x₂ w))
  have hΘ : ∀ Y, Θ Y = Y 0 0 • w + Y 0 1 • x₂ w + Y 1 0 • x₁ w + Y 1 1 • x₁ (x₂ w) :=
    fun Y => theta_apply _ _ _ _ Y
  have hΘU : ∀ Y, Θ Y ∈ U := fun Y => by
    rw [hΘ]
    exact U.add_mem (U.add_mem (U.add_mem (U.smul_mem _ hwU) (U.smul_mem _ hw₂U))
      (U.smul_mem _ hw₁U)) (U.smul_mem _ hw₁₂U)
  let Θ' : Mat2 →ₗ[ZMod 2] U := Θ.codRestrict U hΘU
  have hsurj : Function.Surjective Θ' := by
    intro u
    obtain ⟨c₁, c₂, c₃, c₄, hc⟩ := hspan u u.2
    refine ⟨!![c₁, c₂; c₃, c₄], Subtype.ext ?_⟩
    show Θ _ = _
    rw [hΘ, hc]
    simp
  have hfinrank : Module.finrank (ZMod 2) Mat2 = Module.finrank (ZMod 2) U := by
    rw [hdim]
    simp [Module.finrank_matrix]
  have : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  have hinj : Function.Injective Θ' :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfinrank).2 hsurj
  let e : Mat2 ≃ₗ[ZMod 2] U := LinearEquiv.ofBijective Θ' ⟨hinj, hsurj⟩
  have he : ∀ Y, ((e Y : U) : V) = Θ Y := fun Y => rfl
  have transfer : ∀ (g : GLV V) (A B : Mat2), (∀ Y, g (Θ Y) = Θ (A * Y * Bᵀ)) →
      ∀ u u' : ↥U, (u' : V) = g u → e.symm u' = A * e.symm u * Bᵀ := by
    intro g A B hg u u' h
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [he, ← hg, h]
    congr 1
    exact (congrArg Subtype.val (e.apply_symm_apply u)).symm
  refine ⟨e.symm, transfer x₁ _ _ ?_, transfer a₁ _ _ ?_, transfer x₂ _ _ ?_, transfer a₂ _ _ ?_⟩
  · intro Y
    have e3 : x₁ (x₁ w) = x₁ w + w := sq_apply hx₁ hx₁U hfp₁ hwU
    have e4 : x₁ (x₁ (x₂ w)) = x₁ (x₂ w) + x₂ w := sq_apply hx₁ hx₁U hfp₁ hw₂U
    rw [actX, hΘ, hΘ]
    simp only [map_add, map_smul, e3, e4]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one]
    module
  · intro Y
    have e2 : a₁ (x₂ w) = x₂ w := by rw [comm_apply hax, hwa₁]
    have e3 : a₁ (x₁ w) = x₁ w + w := by
      rw [dih_apply hx₁ hax₁ hx₁U ha₁U hfp₁ hwU, hwa₁]
    have e4 : a₁ (x₁ (x₂ w)) = x₁ (x₂ w) + x₂ w := by
      rw [dih_apply hx₁ hax₁ hx₁U ha₁U hfp₁ hw₂U, e2]
    rw [actS, hΘ, hΘ]
    simp only [map_add, map_smul, hwa₁, e2, e3, e4]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one]
    module
  · intro Y
    have f1 : x₂ (x₂ w) = x₂ w + w := sq_apply hx₂ hx₂U hfp₂ hwU
    have f2 : x₂ (x₁ w) = x₁ (x₂ w) := (comm_apply hxx w).symm
    have f3 : x₂ (x₁ (x₂ w)) = x₁ (x₂ w) + x₁ w := by
      rw [← comm_apply hxx, f1, map_add]
    rw [actXt, hΘ, hΘ]
    simp only [map_add, map_smul, f1, f2, f3]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one]
    module
  · intro Y
    have g2 : a₂ (x₂ w) = x₂ w + w := by
      rw [dih_apply hx₂ hax₂ hx₂U ha₂U hfp₂ hwU, hwa₂]
    have g3 : a₂ (x₁ w) = x₁ w := by rw [← comm_apply hxa, hwa₂]
    have g4 : a₂ (x₁ (x₂ w)) = x₁ (x₂ w) + x₁ w := by
      rw [← comm_apply hxa, g2, map_add]
    rw [actSt, hΘ, hΘ]
    simp only [map_add, map_smul, hwa₂, g2, g3, g4]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one]
    module

end Module

section Group

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

open CFSG.Quasithin.SzN31.CntLin

private theorem closure_preserves (x₁ a₁ x₂ a₂ : GLV V) (U : Submodule (ZMod 2) V)
    (hx₁ : x₁ ^ 3 = 1) (hx₂ : x₂ ^ 3 = 1) (ha₁ : a₁ * a₁ = 1) (ha₂ : a₂ * a₂ = 1)
    (hU : ∀ g ∈ ({x₁, a₁, x₂, a₂} : Set (GLV V)), ∀ u ∈ U, g u ∈ U)
    (g : GLV V) (hg : g ∈ Subgroup.closure ({x₁, a₁, x₂, a₂} : Set (GLV V))) :
    ∀ u ∈ U, g u ∈ U ∧ g⁻¹ u ∈ U := by
  have h1 : x₁ ∈ ({x₁, a₁, x₂, a₂} : Set (GLV V)) := by simp
  have h2 : a₁ ∈ ({x₁, a₁, x₂, a₂} : Set (GLV V)) := by simp
  have h3 : x₂ ∈ ({x₁, a₁, x₂, a₂} : Set (GLV V)) := by simp
  have h4 : a₂ ∈ ({x₁, a₁, x₂, a₂} : Set (GLV V)) := by simp
  refine Subgroup.closure_induction (p := fun g _ => ∀ u ∈ U, g u ∈ U ∧ g⁻¹ u ∈ U) ?_ ?_ ?_ ?_ hg
  · intro g hgS u hu
    refine ⟨hU g hgS u hu, ?_⟩
    rcases hgS with rfl | rfl | rfl | rfl
    · rw [inv_apply_cube hx₁]
      exact hU _ h1 _ (hU _ h1 u hu)
    · rw [inv_eq_of_mul_eq_one_right ha₁]
      exact hU _ h2 u hu
    · rw [inv_apply_cube hx₂]
      exact hU _ h3 _ (hU _ h3 u hu)
    · rw [inv_eq_of_mul_eq_one_right ha₂]
      exact hU _ h4 u hu
  · intro u hu
    exact ⟨by simpa using hu, by simpa using hu⟩
  · intro g h _ _ hg hh u hu
    refine ⟨?_, ?_⟩
    · rw [LinearEquiv.mul_apply]
      exact (hg _ (hh u hu).1).1
    · rw [mul_inv_rev, LinearEquiv.mul_apply]
      exact (hh _ (hg u hu).2).2
  · intro g _ hg u hu
    exact ⟨(hg u hu).2, by simpa using (hg u hu).1⟩

private def restrictU (K : Subgroup (GLV V)) (U : Submodule (ZMod 2) V)
    (hinv : ∀ g ∈ K, ∀ u ∈ U, g u ∈ U ∧ g⁻¹ u ∈ U) : K →* Equiv.Perm U where
  toFun g :=
    { toFun := fun u => ⟨(g : GLV V) u, (hinv g g.2 u u.2).1⟩
      invFun := fun u => ⟨(g : GLV V)⁻¹ u, (hinv g g.2 u u.2).2⟩
      left_inv := fun u => Subtype.ext (inv_apply_apply _ _)
      right_inv := fun u => Subtype.ext (apply_inv_apply _ _) }
  map_one' := by
    ext u : 1
    rfl
  map_mul' g h := by
    ext u : 1
    rfl

private theorem orth_of_psi (x₁ a₁ x₂ a₂ : GLV V) (K : Subgroup (GLV V))
    (hK : K = Subgroup.closure ({x₁, a₁, x₂, a₂} : Set (GLV V))) (U : Submodule (ZMod 2) V)
    (hinv : ∀ g ∈ K, ∀ u ∈ U, g u ∈ U ∧ g⁻¹ u ∈ U)
    (hfaith : ∀ g ∈ K, (∀ u ∈ U, g u = u) → g = 1)
    (ψ : ↥U ≃ₗ[ZMod 2] Mat2)
    (h₁ : ∀ u u' : ↥U, (u' : V) = x₁ u → ψ u' = XM * ψ u * (1 : Mat2)ᵀ)
    (h₂ : ∀ u u' : ↥U, (u' : V) = a₁ u → ψ u' = SM * ψ u * (1 : Mat2)ᵀ)
    (h₃ : ∀ u u' : ↥U, (u' : V) = x₂ u → ψ u' = (1 : Mat2) * ψ u * XMᵀ)
    (h₄ : ∀ u u' : ↥U, (u' : V) = a₂ u → ψ u' = (1 : Mat2) * ψ u * SMᵀ) :
    IsOrth4ModuleG92 K U := by
  have hKS : ∀ g ∈ ({x₁, a₁, x₂, a₂} : Set (GLV V)), g ∈ K := fun g hg =>
    hK ▸ Subgroup.subset_closure hg
  let ρ : K →* Equiv.Perm U := restrictU K U hinv
  let res : K →* Equiv.Perm Mat2 := ψ.toEquiv.permCongrHom.toMonoidHom.comp ρ
  have res_apply : ∀ (g : K) (u u' : U), (u' : V) = (g : GLV V) u → res g (ψ u) = ψ u' := by
    intro g u u' h
    have h' : ρ g u = u' := Subtype.ext h.symm
    show ψ.toEquiv (ρ g (ψ.toEquiv.symm (ψ u))) = ψ u'
    rw [show ψ.toEquiv.symm (ψ u) = u from ψ.toEquiv.symm_apply_apply u, h']
    rfl
  have gen : ∀ (g : K) (p : SL2 × SL2) (A B : Mat2), (p.1 : Mat2) = A → (p.2 : Mat2) = B →
      (∀ u u' : ↥U, (u' : V) = (g : GLV V) u → ψ u' = A * ψ u * Bᵀ) → res g = lam p := by
    intro g p A B hA hB hrel
    ext Y : 1
    obtain ⟨u, rfl⟩ := ψ.surjective Y
    rw [res_apply g u ⟨(g : GLV V) u, (hinv g g.2 u u.2).1⟩ rfl, lam_apply, hA, hB]
    exact hrel u _ rfl
  have hx₁K : x₁ ∈ K := hKS _ (by simp)
  have ha₁K : a₁ ∈ K := hKS _ (by simp)
  have hx₂K : x₂ ∈ K := hKS _ (by simp)
  have ha₂K : a₂ ∈ K := hKS _ (by simp)
  have hX₁ : res ⟨x₁, hx₁K⟩ = lam (XG, 1) := gen _ _ XM 1 rfl rfl h₁
  have hA₁ : res ⟨a₁, ha₁K⟩ = lam (SG, 1) := gen _ _ SM 1 rfl rfl h₂
  have hX₂ : res ⟨x₂, hx₂K⟩ = lam (1, XG) := gen _ _ 1 XM rfl rfl h₃
  have hA₂ : res ⟨a₂, ha₂K⟩ = lam (1, SG) := gen _ _ 1 SM rfl rfl h₄
  have hres_inj : Function.Injective res := by
    rw [injective_iff_map_eq_one]
    intro g hg
    apply Subtype.ext
    apply hfaith g g.2
    intro u hu
    have h1 := res_apply g ⟨u, hu⟩ ⟨(g : GLV V) u, (hinv g g.2 u hu).1⟩ rfl
    rw [hg] at h1
    exact (congrArg Subtype.val (ψ.injective h1)).symm
  have hex : ∀ g : K, ∃ p : SL2 × SL2, lam p = res g := by
    subst hK
    rintro ⟨g, hg⟩
    refine Subgroup.closure_induction
      (p := fun g hg => ∃ p : SL2 × SL2, lam p = res ⟨g, hg⟩) ?_ ?_ ?_ ?_ hg
    · intro g hgS
      rcases hgS with rfl | rfl | rfl | rfl
      · exact ⟨(XG, 1), hX₁.symm⟩
      · exact ⟨(SG, 1), hA₁.symm⟩
      · exact ⟨(1, XG), hX₂.symm⟩
      · exact ⟨(1, SG), hA₂.symm⟩
    · exact ⟨1, by rw [map_one]; exact (map_one res).symm⟩
    · rintro x y hx hy ⟨p, hp⟩ ⟨q, hq⟩
      exact ⟨p * q, by rw [map_mul, hp, hq]; exact (map_mul res ⟨x, hx⟩ ⟨y, hy⟩).symm⟩
    · rintro x hx ⟨p, hp⟩
      exact ⟨p⁻¹, by rw [map_inv, hp]; exact (map_inv res ⟨x, hx⟩).symm⟩
  have hrange : ∀ p : SL2 × SL2, ∃ g : K, res g = lam p := by
    have hA := hom_mem_of_gen (lam.comp (MonoidHom.inl SL2 SL2)) res.range
      ⟨_, hX₁⟩ ⟨_, hA₁⟩
    have hB := hom_mem_of_gen (lam.comp (MonoidHom.inr SL2 SL2)) res.range
      ⟨_, hX₂⟩ ⟨_, hA₂⟩
    rintro ⟨A, B⟩
    have hmem : lam (A, 1) * lam (1, B) ∈ res.range := mul_mem (hA A) (hB B)
    rw [← map_mul] at hmem
    simpa using hmem
  choose ξ hξ using hex
  have hξmul : ∀ g h : K, ξ (g * h) = ξ g * ξ h := fun g h =>
    lam_injective (by simp only [hξ, map_mul])
  let ξhom : K →* SL2 × SL2 := MonoidHom.mk' ξ hξmul
  have hξinj : Function.Injective ξhom := by
    intro g h hgh
    apply hres_inj
    rw [← hξ g, ← hξ h]
    exact congrArg lam hgh
  have hξsurj : Function.Surjective ξhom := by
    intro p
    obtain ⟨g, hg⟩ := hrange p
    refine ⟨g, lam_injective ?_⟩
    show lam (ξ g) = lam p
    rw [hξ, hg]
  refine ⟨MulEquiv.ofBijective ξhom ⟨hξinj, hξsurj⟩, ψ, ?_⟩
  intro g u u' h
  have h1 := res_apply g u u' h
  rw [← hξ g, lam_apply] at h1
  exact h1.symm

end Group

theorem isOrth4ModuleG92_of_pairs {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (x₁ a₁ x₂ a₂ : GLV V) (K : Subgroup (GLV V))
    (hK : K = Subgroup.closure {x₁, a₁, x₂, a₂})
    (U : Submodule (ZMod 2) V) (hdim : Module.finrank (ZMod 2) U = 4)
    (hx₁ : x₁ ^ 3 = 1) (hx₂ : x₂ ^ 3 = 1) (ha₁ : a₁ * a₁ = 1) (ha₂ : a₂ * a₂ = 1)
    (hax₁ : a₁ * x₁ * a₁⁻¹ = x₁⁻¹) (hax₂ : a₂ * x₂ * a₂⁻¹ = x₂⁻¹)
    (hxx : x₁ * x₂ = x₂ * x₁) (hxa : x₁ * a₂ = a₂ * x₁) (hax : a₁ * x₂ = x₂ * a₁)
    (haa : a₁ * a₂ = a₂ * a₁)
    (hU : ∀ g ∈ ({x₁, a₁, x₂, a₂} : Set (GLV V)), ∀ u ∈ U, g u ∈ U)
    (hfp₁ : ∀ u ∈ U, x₁ u = u → u = 0) (hfp₂ : ∀ u ∈ U, x₂ u = u → u = 0)
    (hfaith : ∀ g ∈ K, (∀ u ∈ U, g u = u) → g = 1) :
    IsOrth4ModuleG92 K U := by
  have hx₁U : ∀ u ∈ U, x₁ u ∈ U := fun u hu => hU x₁ (by simp) u hu
  have ha₁U : ∀ u ∈ U, a₁ u ∈ U := fun u hu => hU a₁ (by simp) u hu
  have hx₂U : ∀ u ∈ U, x₂ u ∈ U := fun u hu => hU x₂ (by simp) u hu
  have ha₂U : ∀ u ∈ U, a₂ u ∈ U := fun u hu => hU a₂ (by simp) u hu
  obtain ⟨ψ, h₁, h₂, h₃, h₄⟩ := exists_psi x₁ a₁ x₂ a₂ U hdim hx₁ hx₂ ha₁ ha₂ hax₁ hax₂ hxx hxa
    hax haa hx₁U ha₁U hx₂U ha₂U hfp₁ hfp₂
  have hinv : ∀ g ∈ K, ∀ u ∈ U, g u ∈ U ∧ g⁻¹ u ∈ U := fun g hg =>
    closure_preserves x₁ a₁ x₂ a₂ U hx₁ hx₂ ha₁ ha₂ hU g (hK ▸ hg)
  exact orth_of_psi x₁ a₁ x₂ a₂ K hK U hinv hfaith ψ h₁ h₂ h₃ h₄

end CFSG.Quasithin.G92
