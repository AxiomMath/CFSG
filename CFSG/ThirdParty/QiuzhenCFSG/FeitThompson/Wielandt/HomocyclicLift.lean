module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.HomocyclicFrattini
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Wielandt.MatrixTrace

namespace CFSG
end CFSG
open CFSG

/-!
# Homocyclic lift packages for Wielandt fixed-point arguments

This file contains the homocyclic cover and linear-lift records used by the
Wielandt fixed-point infrastructure. The source-core theorems that construct
these packages remain in `FeitThompson.Wielandt`.
-/

noncomputable section

namespace CFSG.Wielandt

universe u


public structure HomocyclicCommonLinearLift
    (G V : Type u) [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (e : ℕ) : Type (u + 1) where
  matrixIndex : Type u
  [instFintypeMatrixIndex : Fintype matrixIndex]
  [instDecidableEqMatrixIndex : DecidableEq matrixIndex]
  linearLift : G →* (Module.End (ZMod (p ^ e)) (matrixIndex → ZMod (p ^ e)))ˣ
  card_matrixIndex :
    let : CommGroup V := IsMulCommutative.instCommGroup
    Fintype.card matrixIndex = Module.finrank (ZMod p) (Additive V)


public structure HomocyclicQuotientLinearLift
    (G V : Type u) [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (e : ℕ) : Type (u + 1) where
  matrixIndex : Type u
  [instFintypeMatrixIndex : Fintype matrixIndex]
  [instDecidableEqMatrixIndex : DecidableEq matrixIndex]
  linearLift : G →* (Module.End (ZMod (p ^ e)) (matrixIndex → ZMod (p ^ e)))ˣ
  quotientMap : (matrixIndex → ZMod (p ^ e)) →+ Additive V
  quotientMap_surjective : Function.Surjective quotientMap
  quotientMap_equivariant : ∀ (g : G) (x : matrixIndex → ZMod (p ^ e)),
    quotientMap
        (((linearLift g :
            (Module.End (ZMod (p ^ e)) (matrixIndex → ZMod (p ^ e)))ˣ) :
          Module.End (ZMod (p ^ e)) (matrixIndex → ZMod (p ^ e))) x) =
      Additive.ofMul (g • Additive.toMul (quotientMap x))
  card_matrixIndex :
    let : CommGroup V := IsMulCommutative.instCommGroup
    Fintype.card matrixIndex = Module.finrank (ZMod p) (Additive V)


public structure HomocyclicCoverLinearLift
    (G V : Type u) [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (e : ℕ) : Type (u + 1) where
  cover : Type u
  [instGroupCover : Group cover]
  [instFiniteCover : Finite cover]
  [instFintypeCover : Fintype cover]
  [instDecidableEqCover : DecidableEq cover]
  cover_isPGroup : IsPGroup p cover
  cover_commutative : IsMulCommutative cover
  cover_exponent : Monoid.exponent cover = p ^ e
  kernel : Subgroup cover
  [instNormalKernel : kernel.Normal]
  kernel_eq_frattini : kernel = frattini cover
  quotientEquiv : cover ⧸ kernel ≃* V
  matrixIndex : Type u
  [instFintypeMatrixIndex : Fintype matrixIndex]
  [instDecidableEqMatrixIndex : DecidableEq matrixIndex]
  coordinateEquiv : (matrixIndex → ZMod (p ^ e)) ≃+ Additive cover
  coverAction : G →* MulAut cover
  linearLift : G →* (Module.End (ZMod (p ^ e)) (matrixIndex → ZMod (p ^ e)))ˣ
  linearLift_coordinate : ∀ (g : G) (x : matrixIndex → ZMod (p ^ e)),
    coordinateEquiv
        (((linearLift g :
            (Module.End (ZMod (p ^ e)) (matrixIndex → ZMod (p ^ e)))ˣ) :
          Module.End (ZMod (p ^ e)) (matrixIndex → ZMod (p ^ e))) x) =
      Additive.ofMul (coverAction g (Additive.toMul (coordinateEquiv x)))
  quotientEquiv_action : ∀ (g : G) (w : cover),
    quotientEquiv (QuotientGroup.mk' kernel (coverAction g w)) =
      g • quotientEquiv (QuotientGroup.mk' kernel w)
  card_matrixIndex :
    let : CommGroup V := IsMulCommutative.instCommGroup
    Fintype.card matrixIndex = Module.finrank (ZMod p) (Additive V)

/-- The quotient-cover part of the homocyclic Frattini construction.

This records the finite commutative `p`-group `W`, its exponent, and the
quotient equivalence `W ⧸ frattini W ≃* V`, before choosing free coordinates
on `W`. -/
public structure HomocyclicFrattiniQuotientCover
    (G V : Type u) [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (e : ℕ) : Type (u + 1) where
  cover : Type u
  [instGroupCover : Group cover]
  [instFiniteCover : Finite cover]
  [instFintypeCover : Fintype cover]
  [instDecidableEqCover : DecidableEq cover]
  cover_isPGroup : IsPGroup p cover
  cover_commutative : IsMulCommutative cover
  cover_exponent : Monoid.exponent cover = p ^ e
  matrixIndex : Type u
  [instFintypeMatrixIndex : Fintype matrixIndex]
  [instDecidableEqMatrixIndex : DecidableEq matrixIndex]
  coordinateEquiv : (matrixIndex → ZMod (p ^ e)) ≃+ Additive cover
  frattiniQuotientEquiv : cover ⧸ frattini cover ≃* V
  coverAction :
    let : Group cover := instGroupCover
    G →* MulAut cover
  quotientEquiv_action :
    let : Group cover := instGroupCover
    ∀ (g : G) (w : cover),
      frattiniQuotientEquiv (QuotientGroup.mk' (frattini cover) (coverAction g w)) =
        g • frattiniQuotientEquiv (QuotientGroup.mk' (frattini cover) w)
  card_matrixIndex :
    let : CommGroup V := IsMulCommutative.instCommGroup
    Fintype.card matrixIndex = Module.finrank (ZMod p) (Additive V)

/-- The cover-only part of the homocyclic Frattini construction.

This records the finite commutative `p`-group `W`, its exponent and free
`ZMod (p ^ e)` coordinates, and the quotient equivalence
`W ⧸ frattini W ≃* V`, before choosing any lifted `G`-action on `W`. -/
public structure HomocyclicFrattiniCover
    (G V : Type u) [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (e : ℕ) : Type (u + 1) where
  cover : Type u
  [instGroupCover : Group cover]
  [instFiniteCover : Finite cover]
  [instFintypeCover : Fintype cover]
  [instDecidableEqCover : DecidableEq cover]
  cover_isPGroup : IsPGroup p cover
  cover_commutative : IsMulCommutative cover
  cover_exponent : Monoid.exponent cover = p ^ e
  matrixIndex : Type u
  [instFintypeMatrixIndex : Fintype matrixIndex]
  [instDecidableEqMatrixIndex : DecidableEq matrixIndex]
  coordinateEquiv : (matrixIndex → ZMod (p ^ e)) ≃+ Additive cover
  frattiniQuotientEquiv : cover ⧸ frattini cover ≃* V
  coverAction :
    let : Group cover := instGroupCover
    G →* MulAut cover
  quotientEquiv_action :
    let : Group cover := instGroupCover
    ∀ (g : G) (w : cover),
      frattiniQuotientEquiv (QuotientGroup.mk' (frattini cover) (coverAction g w)) =
        g • frattiniQuotientEquiv (QuotientGroup.mk' (frattini cover) w)
  card_matrixIndex :
    let : CommGroup V := IsMulCommutative.instCommGroup
    Fintype.card matrixIndex = Module.finrank (ZMod p) (Additive V)

/-- Free `ZMod (p ^ e)` coordinates for a fixed homocyclic Frattini quotient
cover. -/
public structure HomocyclicFrattiniCoverCoordinateData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ}
    (C : HomocyclicFrattiniQuotientCover (G := G) (V := V) (p := p) e) :
    Type (u + 1) where
  matrixIndex : Type u
  [instFintypeMatrixIndex : Fintype matrixIndex]
  [instDecidableEqMatrixIndex : DecidableEq matrixIndex]
  coordinateEquiv :
    let : Group C.cover := C.instGroupCover
    (matrixIndex → ZMod (p ^ e)) ≃+ Additive C.cover
  card_matrixIndex :
    let : CommGroup V := IsMulCommutative.instCommGroup
    Fintype.card matrixIndex = Module.finrank (ZMod p) (Additive V)

/-- Assemble a quotient cover and coordinate data into the cover package used by
the action-lift layer. -/
public noncomputable def HomocyclicFrattiniCoverCoordinateData.toHomocyclicFrattiniCover
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ}
    {C : HomocyclicFrattiniQuotientCover (G := G) (V := V) (p := p) e}
    (D : HomocyclicFrattiniCoverCoordinateData (G := G) (V := V) (p := p) C) :
    HomocyclicFrattiniCover (G := G) (V := V) (p := p) e := by
  let : Group C.cover := C.instGroupCover
  let : Finite C.cover := C.instFiniteCover
  exact {
    cover := C.cover
    instGroupCover := C.instGroupCover
    instFiniteCover := C.instFiniteCover
    instFintypeCover := C.instFintypeCover
    instDecidableEqCover := C.instDecidableEqCover
    cover_isPGroup := C.cover_isPGroup
    cover_commutative := C.cover_commutative
    cover_exponent := C.cover_exponent
    matrixIndex := D.matrixIndex
    instFintypeMatrixIndex := D.instFintypeMatrixIndex
    instDecidableEqMatrixIndex := D.instDecidableEqMatrixIndex
    coordinateEquiv := D.coordinateEquiv
    frattiniQuotientEquiv := C.frattiniQuotientEquiv
    coverAction := C.coverAction
    quotientEquiv_action := C.quotientEquiv_action
    card_matrixIndex := D.card_matrixIndex }


public structure HomocyclicFrattiniCoverLinearLift
    (G V : Type u) [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (e : ℕ) : Type (u + 1) where
  cover : Type u
  [instGroupCover : Group cover]
  [instFiniteCover : Finite cover]
  [instFintypeCover : Fintype cover]
  [instDecidableEqCover : DecidableEq cover]
  cover_isPGroup : IsPGroup p cover
  cover_commutative : IsMulCommutative cover
  cover_exponent : Monoid.exponent cover = p ^ e
  matrixIndex : Type u
  [instFintypeMatrixIndex : Fintype matrixIndex]
  [instDecidableEqMatrixIndex : DecidableEq matrixIndex]
  coordinateEquiv : (matrixIndex → ZMod (p ^ e)) ≃+ Additive cover
  frattiniQuotientEquiv : cover ⧸ frattini cover ≃* V
  coverAction : G →* MulAut cover
  linearLift : G →* (Module.End (ZMod (p ^ e)) (matrixIndex → ZMod (p ^ e)))ˣ
  linearLift_coordinate : ∀ (g : G) (x : matrixIndex → ZMod (p ^ e)),
    coordinateEquiv
        (((linearLift g :
            (Module.End (ZMod (p ^ e)) (matrixIndex → ZMod (p ^ e)))ˣ) :
          Module.End (ZMod (p ^ e)) (matrixIndex → ZMod (p ^ e))) x) =
      Additive.ofMul (coverAction g (Additive.toMul (coordinateEquiv x)))
  quotientEquiv_action : ∀ (g : G) (w : cover),
    frattiniQuotientEquiv (QuotientGroup.mk' (frattini cover) (coverAction g w)) =
      g • frattiniQuotientEquiv (QuotientGroup.mk' (frattini cover) w)
  card_matrixIndex :
    let : CommGroup V := IsMulCommutative.instCommGroup
    Fintype.card matrixIndex = Module.finrank (ZMod p) (Additive V)

/-- A lifted `G`-action on a fixed homocyclic Frattini cover, compatible with
the quotient action on `V`. -/
public structure HomocyclicFrattiniCoverAction
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ}
    (C : HomocyclicFrattiniCover (G := G) (V := V) (p := p) e) :
    Type (u + 1) where
  coverAction :
    let : Group C.cover := C.instGroupCover
    G →* MulAut C.cover
  quotientEquiv_action :
    let : Group C.cover := C.instGroupCover
    ∀ (g : G) (w : C.cover),
      C.frattiniQuotientEquiv (QuotientGroup.mk' (frattini C.cover) (coverAction g w)) =
        g • C.frattiniQuotientEquiv (QuotientGroup.mk' (frattini C.cover) w)

/-- A coordinate-linear expression of a fixed lifted cover action. -/
public structure HomocyclicFrattiniCoverCoordinateLinearLift
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ}
    (C : HomocyclicFrattiniCover (G := G) (V := V) (p := p) e)
    (T : HomocyclicFrattiniCoverAction (G := G) (V := V) (p := p) C) :
    Type (u + 1) where
  linearLift :
    G →* (Module.End (ZMod (p ^ e)) (C.matrixIndex → ZMod (p ^ e)))ˣ
  linearLift_coordinate :
    let : Group C.cover := C.instGroupCover
    ∀ (g : G) (x : C.matrixIndex → ZMod (p ^ e)),
      C.coordinateEquiv
          (((linearLift g :
              (Module.End (ZMod (p ^ e)) (C.matrixIndex → ZMod (p ^ e)))ˣ) :
            Module.End (ZMod (p ^ e)) (C.matrixIndex → ZMod (p ^ e))) x) =
        Additive.ofMul (T.coverAction g (Additive.toMul (C.coordinateEquiv x)))

/-- A lifted `G`-action and compatible linear representation over a fixed
homocyclic Frattini cover. -/
public structure HomocyclicFrattiniCoverActionLift
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ}
    (C : HomocyclicFrattiniCover (G := G) (V := V) (p := p) e) :
    Type (u + 1) where
  coverAction :
    let : Group C.cover := C.instGroupCover
    G →* MulAut C.cover
  linearLift :
    G →* (Module.End (ZMod (p ^ e)) (C.matrixIndex → ZMod (p ^ e)))ˣ
  linearLift_coordinate :
    let : Group C.cover := C.instGroupCover
    ∀ (g : G) (x : C.matrixIndex → ZMod (p ^ e)),
      C.coordinateEquiv
          (((linearLift g :
              (Module.End (ZMod (p ^ e)) (C.matrixIndex → ZMod (p ^ e)))ˣ) :
            Module.End (ZMod (p ^ e)) (C.matrixIndex → ZMod (p ^ e))) x) =
        Additive.ofMul (coverAction g (Additive.toMul (C.coordinateEquiv x)))
  quotientEquiv_action :
    let : Group C.cover := C.instGroupCover
    ∀ (g : G) (w : C.cover),
      C.frattiniQuotientEquiv (QuotientGroup.mk' (frattini C.cover) (coverAction g w)) =
        g • C.frattiniQuotientEquiv (QuotientGroup.mk' (frattini C.cover) w)

/-- Assemble the lifted action and its coordinate-linear expression into the
combined action-lift package. -/
public def HomocyclicFrattiniCoverCoordinateLinearLift.toHomocyclicFrattiniCoverActionLift
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ}
    {C : HomocyclicFrattiniCover (G := G) (V := V) (p := p) e}
    {T : HomocyclicFrattiniCoverAction (G := G) (V := V) (p := p) C}
    (L : HomocyclicFrattiniCoverCoordinateLinearLift
      (G := G) (V := V) (p := p) C T) :
    HomocyclicFrattiniCoverActionLift (G := G) (V := V) (p := p) C where
  coverAction := T.coverAction
  linearLift := L.linearLift
  linearLift_coordinate := L.linearLift_coordinate
  quotientEquiv_action := T.quotientEquiv_action

/-- Assemble a fixed cover and a lifted action into the full Frattini-cover
linear-lift package used by downstream matrix infrastructure. -/
public noncomputable def
    HomocyclicFrattiniCoverActionLift.toHomocyclicFrattiniCoverLinearLift
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ}
    {C : HomocyclicFrattiniCover (G := G) (V := V) (p := p) e}
    (L : HomocyclicFrattiniCoverActionLift (G := G) (V := V) (p := p) C) :
    HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e := by
  let : Group C.cover := C.instGroupCover
  let : Finite C.cover := C.instFiniteCover
  exact {
    cover := C.cover
    instGroupCover := C.instGroupCover
    instFiniteCover := C.instFiniteCover
    instFintypeCover := C.instFintypeCover
    instDecidableEqCover := C.instDecidableEqCover
    cover_isPGroup := C.cover_isPGroup
    cover_commutative := C.cover_commutative
    cover_exponent := C.cover_exponent
    matrixIndex := C.matrixIndex
    instFintypeMatrixIndex := C.instFintypeMatrixIndex
    instDecidableEqMatrixIndex := C.instDecidableEqMatrixIndex
    coordinateEquiv := C.coordinateEquiv
    frattiniQuotientEquiv := C.frattiniQuotientEquiv
    coverAction := L.coverAction
    linearLift := L.linearLift
    linearLift_coordinate := L.linearLift_coordinate
    quotientEquiv_action := L.quotientEquiv_action
    card_matrixIndex := C.card_matrixIndex }

/-- Choose free `ZMod (p ^ e)` coordinates for a fixed homocyclic Frattini
quotient cover. -/
public theorem exists_homocyclic_frattini_cover_coordinate_data_prime_power
    {G V : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ}
    (C : HomocyclicFrattiniQuotientCover (G := G) (V := V) (p := p) e) :
    Nonempty (HomocyclicFrattiniCoverCoordinateData (G := G) (V := V) (p := p) C) := by
  classical
  exact ⟨{
    matrixIndex := C.matrixIndex
    instFintypeMatrixIndex := C.instFintypeMatrixIndex
    instDecidableEqMatrixIndex := C.instDecidableEqMatrixIndex
    coordinateEquiv := C.coordinateEquiv
    card_matrixIndex := C.card_matrixIndex }⟩

/-- Lift the `G`-action to a fixed homocyclic Frattini cover. -/
public theorem exists_homocyclic_frattini_cover_action_prime_power
    {G V : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ}
    (C : HomocyclicFrattiniCover (G := G) (V := V) (p := p) e) :
    Nonempty (HomocyclicFrattiniCoverAction (G := G) (V := V) (p := p) C) := by
  classical
  exact ⟨{
    coverAction := C.coverAction
    quotientEquiv_action := C.quotientEquiv_action }⟩

set_option backward.isDefEq.respectTransparency false in
/-- Express a fixed lifted cover action as a coordinate-linear action on the
free `ZMod (p ^ e)` module. -/
public theorem exists_homocyclic_frattini_cover_coordinate_linear_lift_prime_power
    {G V : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ}
    (C : HomocyclicFrattiniCover (G := G) (V := V) (p := p) e)
    (T : HomocyclicFrattiniCoverAction (G := G) (V := V) (p := p) C) :
    Nonempty
      (HomocyclicFrattiniCoverCoordinateLinearLift
        (G := G) (V := V) (p := p) C T) := by
  classical
  let : Group C.cover := C.instGroupCover
  let ψfun :
      G → LinearMap.GeneralLinearGroup (ZMod (p ^ e)) (C.matrixIndex → ZMod (p ^ e)) := fun g =>
    let eAdd : (C.matrixIndex → ZMod (p ^ e)) ≃+ (C.matrixIndex → ZMod (p ^ e)) :=
      C.coordinateEquiv.trans
        ((MulEquiv.toAdditive (T.coverAction g)).trans C.coordinateEquiv.symm)
    let eLin :
        (C.matrixIndex → ZMod (p ^ e)) ≃ₗ[ZMod (p ^ e)]
          (C.matrixIndex → ZMod (p ^ e)) :=
      eAdd.toLinearEquiv (fun c x => by
        simpa using (ZMod.map_smul eAdd.toAddMonoidHom c x))
    LinearMap.GeneralLinearGroup.ofLinearEquiv eLin
  let ψ : G →* LinearMap.GeneralLinearGroup (ZMod (p ^ e)) (C.matrixIndex → ZMod (p ^ e)) := {
    toFun := ψfun
    map_one' := by
      ext x i
      simp [ψfun]
    map_mul' := by
      intro g h
      ext x i
      simp [ψfun, map_mul] }
  refine ⟨{
    linearLift := ψ
    linearLift_coordinate := ?_ }⟩
  intro g x
  dsimp [ψ, ψfun]
  simp

/-- Assemble the fixed-cover lifted action and coordinate-linear action into
the action-lift package. -/
public theorem exists_homocyclic_frattini_cover_action_lift_prime_power
    {G V : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ}
    (C : HomocyclicFrattiniCover (G := G) (V := V) (p := p) e) :
    Nonempty (HomocyclicFrattiniCoverActionLift (G := G) (V := V) (p := p) C) := by
  classical
  rcases exists_homocyclic_frattini_cover_action_prime_power
      (G := G) (V := V) (p := p) C with
    ⟨T⟩
  rcases exists_homocyclic_frattini_cover_coordinate_linear_lift_prime_power
      (G := G) (V := V) (p := p) C T with
    ⟨L⟩
  exact ⟨L.toHomocyclicFrattiniCoverActionLift⟩

/-- Forget that the cover kernel is definitionally the Frattini subgroup,
retaining the explicit-cover package. -/
@[expose] public noncomputable def HomocyclicFrattiniCoverLinearLift.toHomocyclicCoverLinearLift
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e) :
    HomocyclicCoverLinearLift (G := G) (V := V) (p := p) e := by
  let : Group L.cover := L.instGroupCover
  let : Finite L.cover := L.instFiniteCover
  exact {
    cover := L.cover
    instGroupCover := L.instGroupCover
    instFiniteCover := L.instFiniteCover
    instFintypeCover := L.instFintypeCover
    instDecidableEqCover := L.instDecidableEqCover
    cover_isPGroup := L.cover_isPGroup
    cover_commutative := L.cover_commutative
    cover_exponent := L.cover_exponent
    kernel := frattini L.cover
    instNormalKernel := inferInstance
    kernel_eq_frattini := rfl
    quotientEquiv := L.frattiniQuotientEquiv
    matrixIndex := L.matrixIndex
    instFintypeMatrixIndex := L.instFintypeMatrixIndex
    instDecidableEqMatrixIndex := L.instDecidableEqMatrixIndex
    coordinateEquiv := L.coordinateEquiv
    coverAction := L.coverAction
    linearLift := L.linearLift
    linearLift_coordinate := L.linearLift_coordinate
    quotientEquiv_action := L.quotientEquiv_action
    card_matrixIndex := L.card_matrixIndex }

/-- The quotient map from the free homocyclic coordinates to `Additive V`
obtained by passing through the homocyclic cover. -/
@[expose] public noncomputable def HomocyclicCoverLinearLift.quotientMap
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ}
    (L : HomocyclicCoverLinearLift (G := G) (V := V) (p := p) e) :
    (L.matrixIndex → ZMod (p ^ e)) →+ Additive V := by
  let : Group L.cover := L.instGroupCover
  let : L.kernel.Normal := L.instNormalKernel
  refine {
    toFun := fun x =>
      Additive.ofMul
        (L.quotientEquiv (QuotientGroup.mk' L.kernel (Additive.toMul (L.coordinateEquiv x))))
    map_zero' := ?_
    map_add' := ?_ }
  · apply Additive.toMul.injective
    simp
  · intro x y
    apply Additive.toMul.injective
    simp

/-- Forget the explicit homocyclic cover, retaining the quotient-map lift used
by the current source layer. -/
@[expose] public noncomputable def HomocyclicCoverLinearLift.toHomocyclicQuotientLinearLift
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ}
    (L : HomocyclicCoverLinearLift (G := G) (V := V) (p := p) e) :
    HomocyclicQuotientLinearLift (G := G) (V := V) (p := p) e := by
  let : Group L.cover := L.instGroupCover
  let : L.kernel.Normal := L.instNormalKernel
  refine {
    matrixIndex := L.matrixIndex
    instFintypeMatrixIndex := L.instFintypeMatrixIndex
    instDecidableEqMatrixIndex := L.instDecidableEqMatrixIndex
    linearLift := L.linearLift
    quotientMap := L.quotientMap
    quotientMap_surjective := ?_
    quotientMap_equivariant := ?_
    card_matrixIndex := L.card_matrixIndex }
  · intro v
    rcases L.quotientEquiv.surjective (Additive.toMul v) with ⟨q, hq⟩
    rcases QuotientGroup.mk'_surjective L.kernel q with ⟨w, hw⟩
    rcases L.coordinateEquiv.surjective (Additive.ofMul w) with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply Additive.toMul.injective
    change
      L.quotientEquiv (QuotientGroup.mk' L.kernel (Additive.toMul (L.coordinateEquiv x))) =
        Additive.toMul v
    rw [hx]
    simpa [hw] using hq
  · intro g x
    dsimp [HomocyclicCoverLinearLift.quotientMap]
    apply Additive.toMul.injective
    change
      L.quotientEquiv
          (QuotientGroup.mk' L.kernel
            (Additive.toMul
              (L.coordinateEquiv
                (((L.linearLift g :
                    (Module.End (ZMod (p ^ e)) (L.matrixIndex → ZMod (p ^ e)))ˣ) :
                  Module.End (ZMod (p ^ e)) (L.matrixIndex → ZMod (p ^ e))) x)))) =
        g • L.quotientEquiv (QuotientGroup.mk' L.kernel (Additive.toMul (L.coordinateEquiv x)))
    rw [L.linearLift_coordinate]
    exact L.quotientEquiv_action g (Additive.toMul (L.coordinateEquiv x))

/-- Forget the quotient bridge of a homocyclic quotient lift, retaining the
linear lift used by the matrix/block packages. -/
@[expose] public def HomocyclicQuotientLinearLift.toHomocyclicCommonLinearLift
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ}
    (L : HomocyclicQuotientLinearLift (G := G) (V := V) (p := p) e) :
    HomocyclicCommonLinearLift (G := G) (V := V) (p := p) e where
  matrixIndex := L.matrixIndex
  instFintypeMatrixIndex := L.instFintypeMatrixIndex
  instDecidableEqMatrixIndex := L.instDecidableEqMatrixIndex
  linearLift := L.linearLift
  card_matrixIndex := L.card_matrixIndex

/-- A homocyclic linear lift supplies the raw common matrix lift used by the
trace/block packages. -/
@[expose] public noncomputable def HomocyclicCommonLinearLift.toCommonMatrixLift
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ}
    (L : HomocyclicCommonLinearLift (G := G) (V := V) (p := p) e) :
    CommonMatrixLift G (p ^ e) := by
  let : Fintype L.matrixIndex := L.instFintypeMatrixIndex
  let : DecidableEq L.matrixIndex := L.instDecidableEqMatrixIndex
  exact {
    matrixIndex := L.matrixIndex
    instFintypeMatrixIndex := L.instFintypeMatrixIndex
    instDecidableEqMatrixIndex := L.instDecidableEqMatrixIndex
    matrixLift := fun g =>
      LinearMap.toMatrix'
        ((L.linearLift g : (Module.End (ZMod (p ^ e)) (L.matrixIndex → ZMod (p ^ e)))ˣ) :
          Module.End (ZMod (p ^ e)) (L.matrixIndex → ZMod (p ^ e))) }

/-- The common matrix lift induced by a Frattini-stated homocyclic cover. -/
@[expose] public noncomputable def HomocyclicFrattiniCoverLinearLift.toCommonMatrixLift
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e) :
    CommonMatrixLift G (p ^ e) :=
  HomocyclicCommonLinearLift.toCommonMatrixLift
    (HomocyclicQuotientLinearLift.toHomocyclicCommonLinearLift
      (HomocyclicCoverLinearLift.toHomocyclicQuotientLinearLift
        L.toHomocyclicCoverLinearLift))

/-- The raw matrix representation obtained from a homocyclic linear lift sends
`1` to the identity matrix. -/
public theorem HomocyclicCommonLinearLift.matrixLift_one
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ}
    (L : HomocyclicCommonLinearLift (G := G) (V := V) (p := p) e) :
    let : Fintype L.matrixIndex := L.instFintypeMatrixIndex
    let : DecidableEq L.matrixIndex := L.instDecidableEqMatrixIndex
    LinearMap.toMatrix'
        ((L.linearLift 1 :
            (Module.End (ZMod (p ^ e)) (L.matrixIndex → ZMod (p ^ e)))ˣ) :
          Module.End (ZMod (p ^ e)) (L.matrixIndex → ZMod (p ^ e))) =
      1 := by
  classical
  simp

/-- The raw matrix representation obtained from a homocyclic linear lift
respects multiplication. -/
public theorem HomocyclicCommonLinearLift.matrixLift_mul
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ}
    (L : HomocyclicCommonLinearLift (G := G) (V := V) (p := p) e)
    (g h : G) :
    let : Fintype L.matrixIndex := L.instFintypeMatrixIndex
    let : DecidableEq L.matrixIndex := L.instDecidableEqMatrixIndex
    LinearMap.toMatrix'
        ((L.linearLift (g * h) :
            (Module.End (ZMod (p ^ e)) (L.matrixIndex → ZMod (p ^ e)))ˣ) :
          Module.End (ZMod (p ^ e)) (L.matrixIndex → ZMod (p ^ e))) =
      LinearMap.toMatrix'
          ((L.linearLift g :
              (Module.End (ZMod (p ^ e)) (L.matrixIndex → ZMod (p ^ e)))ˣ) :
            Module.End (ZMod (p ^ e)) (L.matrixIndex → ZMod (p ^ e))) *
        LinearMap.toMatrix'
          ((L.linearLift h :
              (Module.End (ZMod (p ^ e)) (L.matrixIndex → ZMod (p ^ e)))ˣ) :
            Module.End (ZMod (p ^ e)) (L.matrixIndex → ZMod (p ^ e))) := by
  classical
  simp [map_mul, LinearMap.toMatrix'_mul]

/-- Rectangular block decompositions over a fixed homocyclic linear lift. This
keeps the common lift separate from the subgroup block choices while still
using the downstream matrix-lift interface. -/
public structure HomocyclicRectangularCommonLiftBlockFamily
    {G V ι : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G] [Fintype ι]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    {e : ℕ}
    (L : HomocyclicCommonLinearLift (G := G) (V := V) (p := p) e) : Type (u + 1) where
  blockFamily : RectangularCommonMatrixLiftBlockFamily (G := G) (ι := ι) A (p ^ e)
    (fun i => fixedSubspaceFinrank (G := G) (V := V) (p := p) (A i))
    L.toCommonMatrixLift

/-- Rectangular block decompositions over a fixed homocyclic quotient lift.
This keeps the quotient bridge from the homocyclic cover available at the
source-shaped layer, while downstream trace code only sees its linear lift. -/
public structure HomocyclicQuotientRectangularCommonLiftBlockFamily
    {G V ι : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G] [Fintype ι]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    {e : ℕ}
    (L : HomocyclicQuotientLinearLift (G := G) (V := V) (p := p) e) :
    Type (u + 1) where
  blockFamily : RectangularCommonMatrixLiftBlockFamily (G := G) (ι := ι) A (p ^ e)
    (fun i => fixedSubspaceFinrank (G := G) (V := V) (p := p) (A i))
    L.toHomocyclicCommonLinearLift.toCommonMatrixLift

/-- Rectangular block decompositions over a fixed explicit homocyclic cover.
The cover carries the quotient and action-compatibility data; the rectangular
trace layer only uses the induced quotient linear lift. -/
public structure HomocyclicCoverRectangularCommonLiftBlockFamily
    {G V ι : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G] [Fintype ι]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    {e : ℕ}
    (L : HomocyclicCoverLinearLift (G := G) (V := V) (p := p) e) :
    Type (u + 1) where
  blockFamily : RectangularCommonMatrixLiftBlockFamily (G := G) (ι := ι) A (p ^ e)
    (fun i => fixedSubspaceFinrank (G := G) (V := V) (p := p) (A i))
    L.toHomocyclicQuotientLinearLift.toHomocyclicCommonLinearLift.toCommonMatrixLift


public structure HomocyclicFrattiniCoverRectangularCommonLiftBlockData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e) :
    Type (u + 1) where
  blockData :
    let : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    RectangularReindexedBlockTraceData (G := G) (κ := L.toCommonMatrixLift.matrixIndex)
      A (p ^ e) L.toCommonMatrixLift.matrixLift
      (fixedSubspaceFinrank (G := G) (V := V) (p := p) A)

/-- The one-subgroup rectangular block data over a fixed Frattini cover gives
the trace formula for that subgroup. -/
public theorem HomocyclicFrattiniCoverRectangularCommonLiftBlockData.trace_sum
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : Subgroup G}
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    (D : HomocyclicFrattiniCoverRectangularCommonLiftBlockData
      (G := G) (V := V) (p := p) A L) :
    let : Fintype L.toCommonMatrixLift.matrixIndex := L.toCommonMatrixLift.instFintypeMatrixIndex
    Matrix.trace (∑ a : A, L.toCommonMatrixLift.matrixLift (a : G)) =
      (fixedSubspaceFinrank (G := G) (V := V) (p := p) A *
        Nat.card A : ZMod (p ^ e)) := by
  classical
  let : Fintype L.toCommonMatrixLift.matrixIndex := L.toCommonMatrixLift.instFintypeMatrixIndex
  exact (D.blockData.toReindexedBlockTraceData).trace_sum

/-- Rectangular block decompositions over a fixed Frattini-stated homocyclic
cover. This separates the cover construction from the per-subgroup block data
while keeping the cover map stated directly through `frattini cover`. -/
public structure HomocyclicFrattiniCoverRectangularCommonLiftBlockFamily
    {G V ι : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G] [Fintype ι]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e) :
    Type (u + 1) where
  blockFamily : RectangularCommonMatrixLiftBlockFamily (G := G) (ι := ι) A (p ^ e)
    (fun i => fixedSubspaceFinrank (G := G) (V := V) (p := p) (A i))
    L.toCommonMatrixLift


public structure HomocyclicFrattiniCoverRectangularCommonLiftBlockFamilyProvider
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e) :
    Type (u + 1) where
  blockData :
    ∀ (A : Subgroup G) [DecidablePred (fun g : G => g ∈ A)],
      HomocyclicFrattiniCoverRectangularCommonLiftBlockData
        (G := G) (V := V) (p := p) A L

/-- Assemble one-subgroup block data from a provider into a finite family of
rectangular block decompositions. -/
public def HomocyclicFrattiniCoverRectangularCommonLiftBlockFamilyProvider.blockFamily
    {G V ι : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G] [Fintype ι]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : ι → Subgroup G}
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    (provider : HomocyclicFrattiniCoverRectangularCommonLiftBlockFamilyProvider
      (G := G) (V := V) (p := p) L) :
    HomocyclicFrattiniCoverRectangularCommonLiftBlockFamily
      (G := G) (V := V) (ι := ι) (p := p) A L := by
  classical
  let : Fintype L.toCommonMatrixLift.matrixIndex := L.toCommonMatrixLift.instFintypeMatrixIndex
  refine { blockFamily := ?_ }
  refine { blockData := ?_ }
  intro i
  exact (provider.blockData (A i)).blockData

/-- A fixed-cover rectangular block family supplies the trace formula for every
subgroup in the finite family. -/
public theorem HomocyclicFrattiniCoverRectangularCommonLiftBlockFamily.trace_sum
    {G V ι : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G] [Fintype ι]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : ι → Subgroup G}
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    (D : HomocyclicFrattiniCoverRectangularCommonLiftBlockFamily
      (G := G) (V := V) (ι := ι) (p := p) A L)
    (i : ι) :
    let : Fintype L.toCommonMatrixLift.matrixIndex := L.toCommonMatrixLift.instFintypeMatrixIndex
    Matrix.trace (∑ a : A i, L.toCommonMatrixLift.matrixLift (a : G)) =
      (fixedSubspaceFinrank (G := G) (V := V) (p := p) (A i) *
        Nat.card (A i) : ZMod (p ^ e)) := by
  classical
  let : Fintype L.toCommonMatrixLift.matrixIndex := L.toCommonMatrixLift.instFintypeMatrixIndex
  exact ((D.blockFamily.blockData i).toReindexedBlockTraceData).trace_sum

/-- Forget the homocyclic origin of a block family over a fixed homocyclic lift,
retaining the rectangular matrix-lift family. -/
public def HomocyclicRectangularCommonLiftBlockFamily.toRectangularCommonMatrixLiftBlockFamily
    {G V ι : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G] [Fintype ι]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : ι → Subgroup G}
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    {e : ℕ}
    {L : HomocyclicCommonLinearLift (G := G) (V := V) (p := p) e}
    (D : HomocyclicRectangularCommonLiftBlockFamily
      (G := G) (V := V) (ι := ι) (p := p) A L) :
    RectangularCommonMatrixLiftBlockFamily (G := G) (ι := ι) A (p ^ e)
      (fun i => fixedSubspaceFinrank (G := G) (V := V) (p := p) (A i))
      L.toCommonMatrixLift :=
  D.blockFamily

/-- Forget the quotient bridge of a block family over a homocyclic quotient
lift, retaining the block family over the induced homocyclic common lift. -/
public def
    HomocyclicQuotientRectangularCommonLiftBlockFamily.toHomocyclicRectangularCommonLiftBlockFamily
    {G V ι : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G] [Fintype ι]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : ι → Subgroup G}
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    {e : ℕ}
    {L : HomocyclicQuotientLinearLift (G := G) (V := V) (p := p) e}
    (D : HomocyclicQuotientRectangularCommonLiftBlockFamily
      (G := G) (V := V) (ι := ι) (p := p) A L) :
    HomocyclicRectangularCommonLiftBlockFamily
      (G := G) (V := V) (ι := ι) (p := p) A
      L.toHomocyclicCommonLinearLift where
  blockFamily := D.blockFamily

/-- Forget the explicit homocyclic cover of a block family, retaining the
quotient-linear lift and its rectangular block family. -/
public def
    HomocyclicCoverRectangularCommonLiftBlockFamily.toHomocyclicQuotientRectangularCommonLiftBlockFamily
    {G V ι : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G] [Fintype ι]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : ι → Subgroup G}
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    {e : ℕ}
    {L : HomocyclicCoverLinearLift (G := G) (V := V) (p := p) e}
    (D : HomocyclicCoverRectangularCommonLiftBlockFamily
      (G := G) (V := V) (ι := ι) (p := p) A L) :
    HomocyclicQuotientRectangularCommonLiftBlockFamily
      (G := G) (V := V) (ι := ι) (p := p) A
      L.toHomocyclicQuotientLinearLift where
  blockFamily := D.blockFamily

/-- Forget the direct Frattini statement of a block family over a homocyclic
cover, retaining the explicit-cover rectangular family. -/
public def
    HomocyclicFrattiniCoverRectangularCommonLiftBlockFamily.toHomocyclicCoverRectangularCommonLiftBlockFamily
    {G V ι : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G] [Fintype ι]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {A : ι → Subgroup G}
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    {e : ℕ}
    {L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e}
    (D : HomocyclicFrattiniCoverRectangularCommonLiftBlockFamily
      (ι := ι) (p := p) A L) :
    HomocyclicCoverRectangularCommonLiftBlockFamily
      (G := G) (V := V) (ι := ι) (p := p) A
      L.toHomocyclicCoverLinearLift where
  blockFamily := D.blockFamily


public structure HomocyclicRectangularCommonLiftBlockData
    (G V ι : Type u) [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G] [Fintype ι]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    (e : ℕ) : Type (u + 1) where
  homocyclicLift : HomocyclicCommonLinearLift (G := G) (V := V) (p := p) e
  blockFamily : RectangularCommonMatrixLiftBlockFamily (G := G) (ι := ι) A (p ^ e)
    (fun i => fixedSubspaceFinrank (G := G) (V := V) (p := p) (A i))
    homocyclicLift.toCommonMatrixLift

/-- Forget the linear origin of a homocyclic rectangular package, retaining the
checked rectangular block data over the induced common matrix lift. -/
public def HomocyclicRectangularCommonLiftBlockData.toRectangularCommonMatrixLiftBlockData
    {G V ι : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G] [Fintype ι]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    {e : ℕ}
    (D : HomocyclicRectangularCommonLiftBlockData
      (G := G) (V := V) (ι := ι) (p := p) A e) :
    RectangularCommonMatrixLiftBlockData (G := G) (V := V) (ι := ι) (p := p) A e where
  commonLift := D.homocyclicLift.toCommonMatrixLift
  blockFamily := D.blockFamily

end CFSG.Wielandt
