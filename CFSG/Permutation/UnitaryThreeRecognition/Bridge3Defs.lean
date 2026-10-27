module

public import CFSG.Permutation.UnitaryThreeRecognition.BridgeSetup

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model CFSG.UnitaryThreeRecognition.WeylAlg

namespace CoordHyp

variable {G Ω : Type*} [Group G] [MulAction G Ω] {Q : Subgroup G} {a b : Ω} {j s : G}
  {p f d : ℕ} {K : Type*} [Field K] {J : HermitianForm 3 K} {φ : Q ≃* Coord J}
  (C : CoordHyp Q a b j J φ)

@[expose] noncomputable def tOf (k : Kˣ) : pairStab G a b :=
  ⟨Classical.choose (C.torus_surj k), (Classical.choose_spec (C.torus_surj k)).1⟩

theorem tOf_spec (k : Kˣ) (x : Q) (hx : ((C.tOf k : pairStab G a b) : G) * x *
      ((C.tOf k : pairStab G a b) : G)⁻¹ ∈ Q) :
    φ ⟨_, hx⟩ = hermitianTorusAction J k (φ x) :=
  (Classical.choose_spec (C.torus_surj k)).2 x hx

theorem kOf_act (x : pairStab G a b) (u : Q) (hu : (x : G) * u * (x : G)⁻¹ ∈ Q) :
    φ ⟨_, hu⟩ = hermitianTorusAction J (C.kOf x) (φ u) :=
  C.kOf_spec' x u ⟨_, hu⟩ rfl

variable (S : StdHyp G Q a b j s p f d)
include S

theorem eq_of_act [Finite G] [Finite Ω] {x y : pairStab G a b}
    (h : ∀ u : Q, (x : G) * u * (x : G)⁻¹ = (y : G) * u * (y : G)⁻¹) : x = y := by
  by_contra hxy
  have hz : y⁻¹ * x ≠ 1 := fun e => hxy (inv_mul_eq_one.mp e).symm
  have hz' : ((y⁻¹ * x : pairStab G a b) : G) ≠ 1 := fun e => hz (Subtype.ext e)
  obtain ⟨u, hu, huZ⟩ := S.exists_mem_not_centQ
  apply huZ
  apply S.mem_centQ_of_commute (y⁻¹ * x).2 hz' hu
  have e := h ⟨u, hu⟩
  change (x : G) * u * (x : G)⁻¹ = (y : G) * u * (y : G)⁻¹ at e
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  calc (y : G)⁻¹ * x * u = (y : G)⁻¹ * ((x : G) * u * (x : G)⁻¹) * x := by group
    _ = (y : G)⁻¹ * ((y : G) * u * (y : G)⁻¹) * x := by rw [e]
    _ = u * ((y : G)⁻¹ * x) := by group

theorem kOf_mul_act (x y : pairStab G a b) (c : Coord J) :
    hermitianTorusAction J (C.kOf (x * y)) c = hermitianTorusAction J (C.kOf x * C.kOf y) c := by
  obtain ⟨u, rfl⟩ := φ.surjective c
  let yu : Q := ⟨(y : G) * u * (y : G)⁻¹, S.root.normal y y.2.1 u u.2⟩
  let xyu : Q := ⟨(x : G) * yu * (x : G)⁻¹, S.root.normal x x.2.1 _ yu.2⟩
  have e1 := C.kOf_spec' (x * y) u xyu (by
    change (x : G) * ((y : G) * u * (y : G)⁻¹) * (x : G)⁻¹ =
      ((x * y : pairStab G a b) : G) * u * ((x * y : pairStab G a b) : G)⁻¹
    simp only [Subgroup.coe_mul, mul_inv_rev]; group)
  have e2 := C.kOf_spec' x yu xyu rfl
  have e3 := C.kOf_spec' y u yu rfl
  rw [torus_mul_apply, ← e3, ← e2, ← e1]

omit S in
theorem kOf_one_act (c : Coord J) : hermitianTorusAction J (C.kOf 1) c = c := by
  obtain ⟨u, rfl⟩ := φ.surjective c
  have e := C.kOf_spec' 1 u u (by simp)
  rw [← e]

theorem kOf_inv_act (x : pairStab G a b) (c : Coord J) :
    hermitianTorusAction J (C.kOf x⁻¹) c = hermitianTorusAction J (C.kOf x)⁻¹ c := by
  have h1 : ∀ c', hermitianTorusAction J (C.kOf x) (hermitianTorusAction J (C.kOf x⁻¹) c') = c' :=
    fun c' => by
      rw [← torus_mul_apply, ← C.kOf_mul_act S, mul_inv_cancel, C.kOf_one_act]
  calc hermitianTorusAction J (C.kOf x⁻¹) c
      = hermitianTorusAction J (C.kOf x)⁻¹ (hermitianTorusAction J (C.kOf x)
          (hermitianTorusAction J (C.kOf x⁻¹) c)) := by
        rw [← torus_mul_apply, inv_mul_cancel, torus_one_apply]
    _ = hermitianTorusAction J (C.kOf x)⁻¹ c := by rw [h1]

theorem kOf_tOf_act (k : Kˣ) (c : Coord J) :
    hermitianTorusAction J (C.kOf (C.tOf k)) c = hermitianTorusAction J k c := by
  obtain ⟨u, rfl⟩ := φ.surjective c
  rw [← C.kOf_act (C.tOf k) u (S.root.normal _ (C.tOf k).2.1 u u.2), C.tOf_spec]

theorem eq_of_kOf_act [Finite G] [Finite Ω] {x y : pairStab G a b}
    (h : ∀ c, hermitianTorusAction J (C.kOf x) c = hermitianTorusAction J (C.kOf y) c) :
    x = y := by
  apply eq_of_act S
  intro u
  have e1 := C.kOf_act x u (S.root.normal x x.2.1 u u.2)
  have e2 := C.kOf_act y u (S.root.normal y y.2.1 u u.2)
  have := φ.injective (e1.trans ((h (φ u)).trans e2.symm))
  exact congrArg Subtype.val this

theorem tOf_mul [Finite G] [Finite Ω] (k k' : Kˣ) : C.tOf (k * k') = C.tOf k * C.tOf k' := by
  apply C.eq_of_kOf_act S
  intro c
  calc hermitianTorusAction J (C.kOf (C.tOf (k * k'))) c
      = hermitianTorusAction J k (hermitianTorusAction J k' c) := by
        rw [C.kOf_tOf_act S, torus_mul_apply]
    _ = hermitianTorusAction J (C.kOf (C.tOf k * C.tOf k')) c := by
        rw [C.kOf_mul_act S, torus_mul_apply, C.kOf_tOf_act S, C.kOf_tOf_act S]

end CoordHyp

end CFSG.UnitaryThreeRecognition
