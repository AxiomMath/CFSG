module

public import CFSG.Permutation.UnitaryThreeRecognition.Bridge3Defs
public import CFSG.Permutation.UnitaryThreeRecognition.BridgeHyp

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model CFSG.UnitaryThreeRecognition.WeylAlg

variable {K : Type*} [Field K] {J : HermitianForm 3 K}

theorem torus_inv_apply (k : Kˣ) (c : Coord J) :
    hermitianTorusAction J k⁻¹ (hermitianTorusAction J k c) = c := by
  rw [← torus_mul_apply, inv_mul_cancel, torus_one_apply]

theorem torus_apply_inv (k : Kˣ) (c : Coord J) :
    hermitianTorusAction J k (hermitianTorusAction J k⁻¹ c) = c := by
  rw [← torus_mul_apply, mul_inv_cancel, torus_one_apply]

variable (J) in
@[expose] noncomputable def tPerm : Kˣ →* Equiv.Perm (Coord J) where
  toFun k :=
    { toFun := hermitianTorusAction J k
      invFun := hermitianTorusAction J k⁻¹
      left_inv := torus_inv_apply k
      right_inv := torus_apply_inv k }
  map_one' := Equiv.ext torus_one_apply
  map_mul' k k' := Equiv.ext (torus_mul_apply k k')

theorem tPerm_apply (k : Kˣ) (c : Coord J) : tPerm J k c = hermitianTorusAction J k c := rfl

theorem tPerm_eq_iff {k k' : Kˣ} :
    tPerm J k = tPerm J k' ↔ ∀ c, hermitianTorusAction J k c = hermitianTorusAction J k' c :=
  Equiv.ext_iff

namespace CoordHyp

variable {G Ω : Type*} [Group G] [MulAction G Ω] {Q : Subgroup G} {a b : Ω} {j s : G}
  {p f d : ℕ} {φ : Q ≃* Coord J} (C : CoordHyp Q a b j J φ) (S : StdHyp G Q a b j s p f d)
include S

@[expose] noncomputable def torusPerm : pairStab G a b →* Equiv.Perm (Coord J) where
  toFun x := tPerm J (C.kOf x)
  map_one' := Equiv.ext C.kOf_one_act
  map_mul' x y := by rw [← map_mul]; exact Equiv.ext (C.kOf_mul_act S x y)

theorem torusPerm_apply (x : pairStab G a b) :
    C.torusPerm S x = tPerm J (C.kOf x) := rfl

theorem torusPerm_tOf (k : Kˣ) : C.torusPerm S (C.tOf k) = tPerm J k :=
  Equiv.ext (C.kOf_tOf_act S k)

theorem torusPerm_injective [Finite G] [Finite Ω] : Function.Injective (C.torusPerm S) :=
  fun _ _ h => C.eq_of_kOf_act S (fun c => DFunLike.congr_fun h c)

@[expose] noncomputable def sigma3 (k : Kˣ) : Kˣ := C.kOf (S.conjS (C.tOf k))

theorem sigma3_def (k : Kˣ) : C.sigma3 S k = C.kOf (S.conjS (C.tOf k)) := rfl

theorem tPerm_sigma3 (k : Kˣ) : tPerm J (C.sigma3 S k) = C.torusPerm S (S.conjS (C.tOf k)) :=
  rfl

@[expose] noncomputable def hmap3 (c : Coord J) : Kˣ := by
  classical
  exact if hc : c = 1 then 1 else
    C.kOf ⟨sTor Q a b s (φ.symm c), S.root.sTor_mem S.hb S.hsa S.hs2 (φ.symm c).2
      (StdHyp.symm_ne_one' φ hc)⟩

theorem hmap3_apply (u : Q) (hu : (u : G) ≠ 1) :
    C.hmap3 S (φ u) = C.kOf ⟨sTor Q a b s u, S.root.sTor_mem S.hb S.hsa S.hs2 u.2 hu⟩ := by
  classical
  have hc : φ u ≠ 1 := phi_ne_one.mp hu
  rw [hmap3, dite_eq_right hc]
  simp only [MulEquiv.symm_apply_apply]

end CoordHyp

end CFSG.UnitaryThreeRecognition
