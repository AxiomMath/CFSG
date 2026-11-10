
module

public import CFSG.Sporadic.Schreier.J4SGLBase

public import CFSG.Sporadic.Schreier.J4SOrderBase1
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.J4.Local

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

theorem etaV_eq
    (a : Fin 11 → ZMod 2) : etaV a = etaHom (Multiplicative.ofAdd a) := by
  rw [etaHom_apply]
  rfl

theorem etaV_toVecD (i : ℕ) : etaV (toVecD 11 i) = η i := by
  rw [etaV_eq, η_eq]

def eN : Multiplicative (Fin 11 → ZMod 2) ≃* N :=
  (MonoidHom.ofInjective etaHom_injective).trans (MulEquiv.subgroupCongr etaHom_range)

theorem eN_apply (a : Multiplicative (Fin 11 → ZMod 2)) :
    (eN a : J) = etaV (Multiplicative.toAdd a) := by
  rw [etaV_eq]
  rfl

def addOf
    (g : NN) : (Fin 11 → ZMod 2) →+ (Fin 11 → ZMod 2) where
  toFun a := Multiplicative.toAdd (eN.symm (ρN g (eN (Multiplicative.ofAdd a))))
  map_zero' := by
    rw [ofAdd_zero, map_one, map_one, map_one, toAdd_one]
  map_add' a b := by
    rw [ofAdd_add, map_mul, map_mul, map_mul, toAdd_mul]

def linOf
    (g : NN) : (Fin 11 → ZMod 2) →ₗ[ZMod 2] (Fin 11 → ZMod 2) where
  toFun := addOf g
  map_add' := (addOf g).map_add
  map_smul' c a := by
    rcases zmod_two_cases c with rfl | rfl
    · rw [zero_smul, RingHom.id_apply, zero_smul, map_zero]
    · rw [one_smul, RingHom.id_apply, one_smul]

theorem linOf_apply (g : NN) (a : Fin 11 → ZMod 2) :
    linOf g a = Multiplicative.toAdd (eN.symm (ρN g (eN (Multiplicative.ofAdd a)))) := rfl

theorem linOf_one : linOf 1 = LinearMap.id := by
  refine LinearMap.ext fun a => ?_
  rw [linOf_apply, map_one, MulAut.one_apply, MulEquiv.symm_apply_apply, toAdd_ofAdd]
  rfl

theorem linOf_mul
    (g h : NN) : linOf (g * h) = linOf g ∘ₗ linOf h := by
  refine LinearMap.ext fun a => ?_
  rw [LinearMap.comp_apply, linOf_apply, linOf_apply, linOf_apply, map_mul, MulAut.mul_apply,
    ofAdd_toAdd, MulEquiv.apply_symm_apply]

def matOf : NN →* Matrix (Fin 11) (Fin 11) (ZMod 2) where
  toFun g := LinearMap.toMatrix' (linOf g)
  map_one' := by rw [linOf_one, LinearMap.toMatrix'_id]
  map_mul' g h := by rw [linOf_mul, LinearMap.toMatrix'_comp]

def ρGLN : NN →* GL (Fin 11) (ZMod 2) := matOf.toHomUnits

def ρGL :
    K →* GL (Fin 11) (ZMod 2) := ρGLN.comp (Subgroup.inclusion K_le_normalizer)

theorem ρGLN_mulVec (g : NN) (a : Fin 11 → ZMod 2) :
    (ρGLN g : Matrix (Fin 11) (Fin 11) (ZMod 2)) *ᵥ a = linOf g a := by
  rw [ρGLN, MonoidHom.coe_toHomUnits]
  exact LinearMap.toMatrix'_mulVec _ _

theorem etaV_ρGLN (g : NN) (a : Fin 11 → ZMod 2) :
    etaV ((ρGLN g : Matrix (Fin 11) (Fin 11) (ZMod 2)) *ᵥ a) = g * etaV a * (g : J)⁻¹ := by
  rw [ρGLN_mulVec, linOf_apply, ← eN_apply, MulEquiv.apply_symm_apply,
    Subgroup.normalizerMonoidHom_apply_apply_coe, eN_apply, toAdd_ofAdd]

theorem etaV_ρGL (k : K) (a : Fin 11 → ZMod 2) :
    etaV ((ρGL k : Matrix (Fin 11) (Fin 11) (ZMod 2)) *ᵥ a) = k * etaV a * (k : J)⁻¹ :=
  etaV_ρGLN _ a

theorem etaV_injective : Function.Injective etaV := by
  intro a b h
  rw [etaV_eq, etaV_eq] at h
  exact Multiplicative.ofAdd.injective (etaHom_injective h)

theorem ρGLN_eq_colsMatrix
    {g : NN} {C : Array ℕ} (hg : ∀ j : Fin 11, (g : J) * u j * (g : J)⁻¹ =
    η C[j.val]!) : (ρGLN g : Matrix (Fin 11) (Fin 11) (ZMod 2)) = colsMatrix C := by
  ext i j
  have hu : u j = etaV (Pi.single j 1) := by
    rw [← η_two_pow, ← etaV_toVecD]
    congr 1
    funext k
    rw [toVecD_apply, Nat.testBit_two_pow, Pi.single_apply]
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk, Ne.symm (Fin.val_ne_of_ne hk)]
  have h1 : (ρGLN g : Matrix (Fin 11) (Fin 11) (ZMod 2)) *ᵥ Pi.single j 1 =
      toVecD 11 (C[j.val]?.getD 0) := by
    apply etaV_injective
    rw [etaV_ρGLN, ← hu, hg, etaV_toVecD, getElem!_eq_getD']
  have h2 := congrFun h1 i
  rw [Matrix.mulVec_single_one] at h2
  rw [colsMatrix_apply, ← h2]
  rfl

theorem ρGL_x :
    (ρGL ⟨x, x_mem_K⟩ : Matrix (Fin 11) (Fin 11) (ZMod 2)) = colsMatrix xColumns :=
  ρGLN_eq_colsMatrix x_conj_u

theorem ρGL_y :
    (ρGL ⟨y, y_mem_K⟩ : Matrix (Fin 11) (Fin 11) (ZMod 2)) = colsMatrix yColumns :=
  ρGLN_eq_colsMatrix y_conj_u

end CFSG.Sporadic.J4Schreier
