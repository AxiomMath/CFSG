module

public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.Algebra.Field.ZMod
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
import Mathlib.Tactic.LinearCombination
import Mathlib.FieldTheory.Finiteness

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.ComponentClassification.PresentationLocal
open scoped Matrix IsMulCommutative

variable {Q : Type*} [Group Q] [IsElementaryAbelian 2 Q]

@[expose] noncomputable def bilinOf (b : Q → Q → ZMod 2)
    (hb₁ : ∀ u v t, b (u * v) t = b u t + b v t) (hb₂ : ∀ u v t, b u (v * t) = b u v + b u t) :
    LinearMap.BilinForm (ZMod 2) (Additive Q) :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := fun u => AddMonoidHom.toZModLinearMap 2
        { toFun := fun v => b (Additive.toMul u) (Additive.toMul v)
          map_zero' := by
            have h := hb₂ (Additive.toMul u) 1 1
            rw [mul_one] at h
            change b (Additive.toMul u) 1 = 0
            linear_combination -h
          map_add' := fun v w => hb₂ _ _ _ }
      map_zero' := by
        ext v
        have h := hb₁ 1 1 (Additive.toMul v)
        rw [mul_one] at h
        change b 1 (Additive.toMul v) = 0
        linear_combination -h
      map_add' := fun u u' => by
        ext v
        exact hb₁ _ _ _ }

theorem bilinOf_apply (b : Q → Q → ZMod 2) (hb₁ : ∀ u v t, b (u * v) t = b u t + b v t)
    (hb₂ : ∀ u v t, b u (v * t) = b u v + b u t) (u v : Additive Q) :
    bilinOf b hb₁ hb₂ u v = b (Additive.toMul u) (Additive.toMul v) := by
  unfold bilinOf
  rfl

@[expose] def antidiagEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4 where
  toFun := Sum.elim (fun i => if i = 0 then 0 else 1) (fun i => if i = 0 then 3 else 2)
  invFun := ![Sum.inl 0, Sum.inl 1, Sum.inr 1, Sum.inr 0]
  left_inv := by decide
  right_inv := by decide

theorem J_antidiagEquiv (i j : Fin 4) :
    Matrix.J (Fin 2) (ZMod 2) (antidiagEquiv.symm i) (antidiagEquiv.symm j) = antidiagGram i j := by
  fin_cases i <;> fin_cases j <;> decide

theorem exists_basis_antidiag [Finite Q] (hcard : Nat.card Q = 16) (b : Q → Q → ZMod 2)
    (hb₁ : ∀ u v t, b (u * v) t = b u t + b v t) (hb₂ : ∀ u v t, b u (v * t) = b u v + b u t)
    (hb₃ : ∀ u, b u u = 0) (hb₄ : ∀ u, (∀ v, b u v = 0) → u = 1) :
    ∃ bs : Module.Basis (Fin 4) (ZMod 2) (Additive Q),
      ∀ i j, b (Additive.toMul (bs i)) (Additive.toMul (bs j)) = antidiagGram i j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := bilinOf b hb₁ hb₂ with hB
  have hsymm : ∀ u v, b v u = b u v := by
    intro u v
    have h := hb₃ (u * v)
    rw [hb₁, hb₂, hb₂, hb₃, hb₃] at h
    have h2 : (2 : ZMod 2) = 0 := rfl
    linear_combination h - b u v * h2
  have hBa : B.IsAlt := fun u => hb₃ _
  have hBn : B.Nondegenerate := by
    refine ⟨fun u hu => ?_, fun v hv => ?_⟩
    · have := hb₄ (Additive.toMul u) fun v => hu (Additive.ofMul v)
      exact congrArg Additive.ofMul this
    · have := hb₄ (Additive.toMul v) fun u => by
        rw [hsymm]
        exact hv (Additive.ofMul u)
      exact congrArg Additive.ofMul this
  have : Finite (Additive Q) := inferInstanceAs (Finite Q)
  have : Module.Finite (ZMod 2) (Additive Q) := Module.Finite.of_finite
  have hfin : Module.finrank (ZMod 2) (Additive Q) = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive Q)
    rw [show Nat.card (Additive Q) = 16 from hcard, Nat.card_zmod,
      show (16 : ℕ) = 2 ^ 4 by norm_num] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  obtain ⟨m, bs₀, hbs₀⟩ := hBa.exists_basis_toMatrix_eq_J hBn
  have hm : m = 2 := by
    have := Module.finrank_eq_card_basis bs₀
    rw [hfin, Fintype.card_sum, Fintype.card_fin] at this
    omega
  subst hm
  refine ⟨bs₀.reindex antidiagEquiv, fun i j => ?_⟩
  rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, ← J_antidiagEquiv, ← hbs₀,
    LinearMap.BilinForm.toMatrix_apply]
  rfl

@[expose] noncomputable def autToEnd2 : MulAut Q →* Module.End (ZMod 2) (Additive Q) where
  toFun σ := AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive σ.toMonoidHom)
  map_one' := LinearMap.ext fun _ => rfl
  map_mul' _ _ := LinearMap.ext fun _ => rfl

theorem autToEnd2_apply (σ : MulAut Q) (x : Q) :
    autToEnd2 σ (Additive.ofMul x) = Additive.ofMul (σ x) :=
  rfl

@[expose] noncomputable def sympRepGL (bs : Module.Basis (Fin 4) (ZMod 2) (Additive Q))
    {Γ : Type*} [Group Γ] (φ : Γ →* MulAut Q) : Γ →* GL (Fin 4) (ZMod 2) :=
  (Units.map (LinearMap.toMatrixAlgEquiv bs).toMonoidHom).comp (autToEnd2.comp φ).toHomUnits

variable {Γ : Type*} [Group Γ]

theorem sympRepGL_coe (bs : Module.Basis (Fin 4) (ZMod 2) (Additive Q)) (φ : Γ →* MulAut Q)
    (γ : Γ) : (sympRepGL bs φ γ : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      LinearMap.toMatrix bs bs (autToEnd2 (φ γ)) :=
  rfl

theorem sympRepGL_mulVec (bs : Module.Basis (Fin 4) (ZMod 2) (Additive Q)) (φ : Γ →* MulAut Q)
    (γ : Γ) (x : Q) :
    (sympRepGL bs φ γ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ bs.equivFun (Additive.ofMul x) =
      bs.equivFun (Additive.ofMul (φ γ x)) := by
  rw [sympRepGL_coe, Module.Basis.equivFun_apply, Module.Basis.equivFun_apply,
    LinearMap.toMatrix_mulVec_repr]
  rfl

theorem sympRepGL_eq_one_iff (bs : Module.Basis (Fin 4) (ZMod 2) (Additive Q))
    (φ : Γ →* MulAut Q) (γ : Γ) : sympRepGL bs φ γ = 1 ↔ φ γ = 1 := by
  constructor
  · intro h
    ext x
    have h1 := sympRepGL_mulVec bs φ γ x
    rw [h, Units.val_one, Matrix.one_mulVec] at h1
    have := bs.equivFun.injective h1
    exact (congrArg Additive.toMul this).symm
  · intro h
    apply Units.ext
    rw [sympRepGL_coe, h, map_one, Units.val_one]
    exact LinearMap.toMatrix_id bs

theorem sympRepGL_mem (b : Q → Q → ZMod 2) (hb₁ : ∀ u v t, b (u * v) t = b u t + b v t)
    (hb₂ : ∀ u v t, b u (v * t) = b u v + b u t)
    (bs : Module.Basis (Fin 4) (ZMod 2) (Additive Q))
    (hbs : ∀ i j, b (Additive.toMul (bs i)) (Additive.toMul (bs j)) = antidiagGram i j)
    (φ : Γ →* MulAut Q) (hφ : ∀ γ x y, b (φ γ x) (φ γ y) = b x y) (γ : Γ) :
    sympRepGL bs φ γ ∈ sympFour := by
  rw [mem_sympFour_iff, sympRepGL_coe]
  set B := bilinOf b hb₁ hb₂ with hB
  have hBmat : LinearMap.BilinForm.toMatrix bs B = antidiagGram := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    exact hbs i j
  have hcomp := LinearMap.BilinForm.toMatrix_comp bs bs B (autToEnd2 (φ γ)) (autToEnd2 (φ γ))
  have hinv : B.comp (autToEnd2 (φ γ)) (autToEnd2 (φ γ)) = B :=
    LinearMap.ext₂ fun u v => hφ γ (Additive.toMul u) (Additive.toMul v)
  rw [hinv, hBmat] at hcomp
  exact hcomp.symm

@[expose] noncomputable def sympRep (b : Q → Q → ZMod 2)
    (hb₁ : ∀ u v t, b (u * v) t = b u t + b v t) (hb₂ : ∀ u v t, b u (v * t) = b u v + b u t)
    (bs : Module.Basis (Fin 4) (ZMod 2) (Additive Q))
    (hbs : ∀ i j, b (Additive.toMul (bs i)) (Additive.toMul (bs j)) = antidiagGram i j)
    (φ : Γ →* MulAut Q) (hφ : ∀ γ x y, b (φ γ x) (φ γ y) = b x y) : Γ →* sympFour :=
  (sympRepGL bs φ).codRestrict sympFour (sympRepGL_mem b hb₁ hb₂ bs hbs φ hφ)

theorem pi_eq_sum_single (v : Fin 4 → ZMod 2) :
    v = ∑ i : Fin 4, (v i).val • (Pi.single i 1 : Fin 4 → ZMod 2) := by
  ext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · rw [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  · intro i _ hij
    rw [Pi.smul_apply, Pi.single_eq_of_ne' hij, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem eq_quadForm_of_polar (f : (Fin 4 → ZMod 2) → ZMod 2)
    (hf : ∀ v w, f (v + w) = f v + f w + v ⬝ᵥ antidiagGram *ᵥ w) (v : Fin 4 → ZMod 2) :
    f v = quadForm (fun i => f (Pi.single i 1)) v := by
  set a : Fin 4 → ZMod 2 := fun i => f (Pi.single i 1) with ha
  have hQ : ∀ v w, quadForm a (v + w) = quadForm a v + quadForm a w +
      v ⬝ᵥ antidiagGram *ᵥ w := by
    intro v w
    simp only [quadForm, antidiagGram, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Matrix.of_apply, Pi.add_apply]
    norm_num
    ring
  set g : (Fin 4 → ZMod 2) →+ ZMod 2 :=
    { toFun := fun v => f v - quadForm a v
      map_zero' := by
        have h0 := hf 0 0
        have h0' := hQ 0 0
        simp only [add_zero, Matrix.mulVec_zero, dotProduct_zero] at h0 h0'
        change f 0 - quadForm a 0 = 0
        linear_combination -h0 + h0'
      map_add' := fun v w => by
        change f (v + w) - quadForm a (v + w) = f v - quadForm a v + (f w - quadForm a w)
        rw [hf, hQ]
        ring } with hg
  have hgs : ∀ i, g (Pi.single i 1) = 0 := by
    intro i
    change f (Pi.single i 1) - quadForm a (Pi.single i 1) = 0
    rw [quadForm_single, sub_self]
  have hgv : g v = 0 := by
    rw [pi_eq_sum_single v, map_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [map_nsmul, hgs, smul_zero]
  have : f v - quadForm a v = 0 := hgv
  linear_combination this

variable [Finite Q]

omit [Finite Q] in
theorem b_eq_dotProduct (b : Q → Q → ZMod 2) (hb₁ : ∀ u v t, b (u * v) t = b u t + b v t)
    (hb₂ : ∀ u v t, b u (v * t) = b u v + b u t)
    (bs : Module.Basis (Fin 4) (ZMod 2) (Additive Q))
    (hbs : ∀ i j, b (Additive.toMul (bs i)) (Additive.toMul (bs j)) = antidiagGram i j)
    (x y : Q) :
    b x y = bs.equivFun (Additive.ofMul x) ⬝ᵥ antidiagGram *ᵥ bs.equivFun (Additive.ofMul y) := by
  have hBmat : LinearMap.BilinForm.toMatrix bs (bilinOf b hb₁ hb₂) = antidiagGram := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    exact hbs i j
  rw [← hBmat, LinearMap.BilinForm.dotProduct_toMatrix_mulVec, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply, bilinOf_apply]
  rfl

omit [Finite Q] in
theorem quad_eq_quadForm (b : Q → Q → ZMod 2) (hb₁ : ∀ u v t, b (u * v) t = b u t + b v t)
    (hb₂ : ∀ u v t, b u (v * t) = b u v + b u t)
    (bs : Module.Basis (Fin 4) (ZMod 2) (Additive Q))
    (hbs : ∀ i j, b (Additive.toMul (bs i)) (Additive.toMul (bs j)) = antidiagGram i j)
    (q : Q → ZMod 2) (hq : ∀ x y, q (x * y) = q x + q y + b x y) (x : Q) :
    q x = quadForm (fun i => q (Additive.toMul (bs i))) (bs.equivFun (Additive.ofMul x)) := by
  set f : (Fin 4 → ZMod 2) → ZMod 2 :=
    fun v => q (Additive.toMul (bs.equivFun.symm v)) with hfdef
  have hf : ∀ v w, f (v + w) = f v + f w + v ⬝ᵥ antidiagGram *ᵥ w := by
    intro v w
    have h := hq (Additive.toMul (bs.equivFun.symm v)) (Additive.toMul (bs.equivFun.symm w))
    have hb := b_eq_dotProduct b hb₁ hb₂ bs hbs (Additive.toMul (bs.equivFun.symm v))
      (Additive.toMul (bs.equivFun.symm w))
    simp only [ofMul_toMul, LinearEquiv.apply_symm_apply] at hb
    rw [hb] at h
    simp only [hfdef, map_add]
    exact h
  have h1 := eq_quadForm_of_polar f hf (bs.equivFun (Additive.ofMul x))
  have h2 : ∀ i, f (Pi.single i 1) = q (Additive.toMul (bs i)) := by
    intro i
    simp only [hfdef, Module.Basis.equivFun_symm_apply, Pi.single_apply, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [h2] at h1
  rw [← h1, hfdef]
  simp

end CFSG.RankThree.PartTwo.Sec4.Census
