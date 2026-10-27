module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTorus
public import CFSG.LieType.Chevalley.FoldedWeylIdentification
public import CFSG.LocalAnalysis.StandardType.GGTwE6ToralMax
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
public import CFSG.Blueprint.ChevalleyRoots
public import CFSG.Timmesfeld.Orders.ExceptionalTwistedBruhat
public import CFSG.ClassicalInvolution.Orders.Twisted
public import CFSG.LieType.Chevalley.GraphFixedE6DiagonalCubes

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.Timmesfeld.ExceptionalOrders

namespace ExcFrames

local instance : NeZero (TwistTag.E6.tag.rank) := ⟨by decide⟩
local instance : NeZero (TwistTag.E6.foldedTag.rank) := ⟨by decide⟩

@[expose] noncomputable def twE6ThreeFrame (s : Fin Tag.F4.rank → ZMod 3) :
    Fin Tag.E6.rank → ZMod 3 :=
  frameCoord .E6 3 (TableBExc.redMod .E6 3
    (TwistTag.foldMap TwistTag.E6 (TableBExc.liftMod .F4 3 s)))

@[expose] noncomputable def twE6ThreeTheta (s : Fin Tag.F4.rank → ZMod 3) :
    Fin Tag.E6.rank → ZMod 3 :=
  TableBExc.redMod .E6 3 (TwistTag.foldMap TwistTag.E6 (TableBExc.liftMod .F4 3 s))

@[expose] def e6OrbitIdx (j : Fin Tag.E6.rank) : Fin Tag.F4.rank :=
  ⟨(TwistTag.E6.orbitIndex j).val, by
    have h := (TwistTag.E6.orbitIndex j).isLt
    exact h⟩

@[expose] def e6Idx (i : Fin 4) : Fin Tag.E6.rank :=
  ⟨i.val, lt_of_lt_of_le i.isLt (by decide)⟩

@[expose] def e6Four : Fin Tag.E6.rank := ⟨4, by decide⟩
@[expose] def e6Five : Fin Tag.E6.rank := ⟨5, by decide⟩
@[expose] def e6Equiv : Fin 6 ≃ Fin Tag.E6.rank := finCongr (by decide)

@[expose] def e6Perm (j : Fin Tag.E6.rank) : Fin Tag.E6.rank :=
  show Fin Tag.E6.rank from TwistTag.E6.perm (show Fin TwistTag.E6.tag.rank from j)

private theorem foldMap_apply_apply_E6 (u : Fin Tag.F4.rank → ℤ) (i : Fin Tag.E6.rank) :
    TwistTag.foldMap TwistTag.E6 u i = u (e6OrbitIdx i) := by
  have h := TwistTag.foldMap_apply_apply TwistTag.E6 u i
  rw [h]
  exact congrArg u (Fin.ext rfl)

theorem twE6ThreeTheta_apply (s : Fin Tag.F4.rank → ZMod 3) (i : Fin Tag.E6.rank) :
    twE6ThreeTheta s i = s (e6OrbitIdx i) := by
  simp only [twE6ThreeTheta, TableBExc.redMod, TableBExc.liftMod]
  rw [foldMap_apply_apply_E6]
  congr 1
  simp only [TableBExc.liftMod, Int.cast_natCast, ZMod.natCast_zmod_val]

theorem twE6ThreeFrame_apply (s : Fin Tag.F4.rank → ZMod 3) (i : Fin Tag.E6.rank) :
    twE6ThreeFrame s i =
      ∑ j : Fin Tag.E6.rank, ((Tag.E6.cartan i j : ℤ) : ZMod 3) * s (e6OrbitIdx j) := by
  simp only [twE6ThreeFrame, frameCoord, TableBExc.redMod, TableBExc.liftMod,
    Tag.symmetrizedCartan, Tag.symmetrizer, Matrix.one_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [foldMap_apply_apply_E6]
  congr 1
  simp only [TableBExc.liftMod, Int.cast_natCast, ZMod.natCast_zmod_val]

private theorem twE6ThreeFrame_zero_eq_five (s : Fin Tag.F4.rank → ZMod 3) :
    twE6ThreeFrame s (e6Idx 0) = twE6ThreeFrame s e6Five := by
  rw [twE6ThreeFrame_apply, twE6ThreeFrame_apply]
  decide +revert

private theorem twE6ThreeFrame_two_eq_four (s : Fin Tag.F4.rank → ZMod 3) :
    twE6ThreeFrame s (e6Idx 2) = twE6ThreeFrame s e6Four := by
  rw [twE6ThreeFrame_apply, twE6ThreeFrame_apply]
  decide +revert

theorem twE6ThreeFrame_add (s t : Fin Tag.F4.rank → ZMod 3) :
    twE6ThreeFrame (s + t) = twE6ThreeFrame s + twE6ThreeFrame t := by
  funext i
  rw [twE6ThreeFrame_apply]
  rw [Pi.add_apply, twE6ThreeFrame_apply, twE6ThreeFrame_apply]
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem twE6ThreeFrame_zero : twE6ThreeFrame (0 : Fin Tag.F4.rank → ZMod 3) = 0 := by
  funext i
  rw [twE6ThreeFrame_apply]
  simp

private theorem redMod_foldMap_congr_E6 {u v : Fin Tag.F4.rank → ℤ}
    (h : TableBExc.redMod .F4 3 u = TableBExc.redMod .F4 3 v) :
    TableBExc.redMod .E6 3 (TwistTag.foldMap TwistTag.E6 u) =
      TableBExc.redMod .E6 3 (TwistTag.foldMap TwistTag.E6 v) := by
  funext i
  simp only [TableBExc.redMod, foldMap_apply_apply_E6 u i, foldMap_apply_apply_E6 v i]
  have := congrFun h (e6OrbitIdx i)
  simpa [TableBExc.redMod] using this

theorem twE6ThreeFrame_perm (s : Fin Tag.F4.rank → ZMod 3) (i : Fin Tag.E6.rank) :
    twE6ThreeFrame s (e6Perm i) = twE6ThreeFrame s i := by
  rw [twE6ThreeFrame_apply, twE6ThreeFrame_apply]
  decide +revert

section Weyl

private theorem smul_foldMap_foldedWeylEquiv_E6 (w : relWeylTwist TwistTag.E6)
    (v : Fin Tag.F4.rank → ℤ) :
    (show WeylGroup Tag.E6 from w.1) •
        (show Fin Tag.E6.rank → ℤ from TwistTag.foldMap TwistTag.E6 v) =
      (show Fin Tag.E6.rank → ℤ from TwistTag.foldMap TwistTag.E6
        ((show WeylGroup Tag.F4 from foldedWeylEquiv TwistTag.E6 w) • v)) :=
  smul_foldMap_foldedWeylEquiv (t := TwistTag.E6) w v

private theorem adAct_frameCoord_E6 (w : WeylGroup Tag.E6) (x : Fin Tag.E6.rank → ZMod 3) :
    TableBExc.E6Three.adAct .E6 3 w (frameCoord .E6 3 x) =
      frameCoord .E6 3 (TableBExc.torusAct .E6 3 w x) :=
  adAct_frameCoord w x

theorem adAct_twE6ThreeFrame (w : relWeylTwist TwistTag.E6)
    (s : Fin Tag.F4.rank → ZMod 3) :
    TableBExc.E6Three.adAct .E6 3 (show WeylGroup Tag.E6 from w.1) (twE6ThreeFrame s) =
      twE6ThreeFrame
        (TableBExc.torusAct .F4 3 (show WeylGroup Tag.F4 from foldedWeylEquiv TwistTag.E6 w) s) := by
  let wE : WeylGroup Tag.E6 := w.1
  let wbar : WeylGroup Tag.F4 := foldedWeylEquiv TwistTag.E6 w
  let Z : Fin Tag.F4.rank → ℤ := TableBExc.liftMod .F4 3 s
  let X : Fin Tag.E6.rank → ℤ :=
    show Fin Tag.E6.rank → ℤ from TwistTag.foldMap TwistTag.E6 Z
  have hx : twE6ThreeFrame s = frameCoord .E6 3 (TableBExc.redMod .E6 3 X) := rfl
  have hx' : twE6ThreeFrame (TableBExc.torusAct .F4 3 wbar s) =
      frameCoord .E6 3 (TableBExc.redMod .E6 3
        (TwistTag.foldMap TwistTag.E6 (TableBExc.liftMod .F4 3
          (TableBExc.torusAct .F4 3 wbar s)))) := rfl
  rw [hx, hx']
  change TableBExc.E6Three.adAct .E6 3 wE (frameCoord .E6 3 (TableBExc.redMod .E6 3 X)) =
    frameCoord .E6 3 (TableBExc.redMod .E6 3
      (TwistTag.foldMap TwistTag.E6 (TableBExc.liftMod .F4 3 (TableBExc.torusAct .F4 3 wbar s))))
  rw [adAct_frameCoord_E6]
  congr 1
  change TableBExc.redMod .E6 3
      (wE • TableBExc.liftMod .E6 3 (TableBExc.redMod .E6 3 X)) =
    TableBExc.redMod .E6 3
      (TwistTag.foldMap TwistTag.E6 (TableBExc.liftMod .F4 3 (TableBExc.torusAct .F4 3 wbar s)))
  have hstep1 : TableBExc.redMod .E6 3
      (wE • TableBExc.liftMod .E6 3 (TableBExc.redMod .E6 3 X)) =
      TableBExc.redMod .E6 3 (wE • X) := by
    simpa using TableBExc.redMod_smul_eq (τ := .E6) (p := 3) (w := wE)
      (v := TableBExc.liftMod .E6 3 (TableBExc.redMod .E6 3 X)) (v' := X)
      (by rw [TableBExc.redMod_liftMod])
  rw [hstep1]
  have hstep2 : wE • X = TwistTag.foldMap TwistTag.E6 (wbar • Z) := by
    exact smul_foldMap_foldedWeylEquiv_E6 w Z
  rw [hstep2]
  have hstep3 : TableBExc.torusAct .F4 3 wbar s = TableBExc.redMod .F4 3 (wbar • Z) := rfl
  rw [hstep3]
  exact (redMod_foldMap_congr_E6 (u := TableBExc.liftMod .F4 3 (TableBExc.redMod .F4 3 (wbar • Z)))
    (v := wbar • Z) (by rw [TableBExc.redMod_liftMod])).symm

end Weyl

private def twE6ThreeFrameBasis : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  ![![2, 2, 0, 0], ![0, 0, 2, 2], ![2, 2, 2, 0], ![0, 1, 2, 2]]

private def twE6ThreeFrameBasisInv : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  ![![2, 1, 0, 2], ![0, 2, 0, 1], ![1, 0, 2, 0], ![2, 2, 1, 0]]

private theorem twE6ThreeFrameBasisInv_mul : twE6ThreeFrameBasisInv * twE6ThreeFrameBasis = 1 := by
  decide +kernel

private theorem twE6ThreeFrameBasis_mul_inv : twE6ThreeFrameBasis * twE6ThreeFrameBasisInv = 1 := by
  decide +kernel

private def f4Idx (i : Fin 4) : Fin Tag.F4.rank :=
  ⟨i.val, lt_of_lt_of_le i.isLt (by decide)⟩

private def f4Inv (a : Fin Tag.F4.rank) : Fin 4 :=
  ⟨a.val, lt_of_lt_of_le a.isLt (by decide)⟩

private theorem twE6ThreeFrame_rest (s : Fin Tag.F4.rank → ZMod 3) (i : Fin 4) :
    twE6ThreeFrame s (e6Idx i) =
      ∑ b : Fin 4, twE6ThreeFrameBasis i b * s (f4Idx b) := by
  rw [twE6ThreeFrame_apply]
  decide +revert

theorem twE6ThreeFrame_injective : Function.Injective twE6ThreeFrame := by
  intro s t h
  have h4 : (fun i : Fin 4 => twE6ThreeFrame s (e6Idx i)) =
      fun i : Fin 4 => twE6ThreeFrame t (e6Idx i) := by
    funext i
    exact congrFun h (e6Idx i)
  have h4' : Matrix.mulVec twE6ThreeFrameBasis (fun b => s (f4Idx b)) =
      Matrix.mulVec twE6ThreeFrameBasis (fun b => t (f4Idx b)) := by
    funext i
    change (∑ b, twE6ThreeFrameBasis i b * s (f4Idx b)) =
      ∑ b, twE6ThreeFrameBasis i b * t (f4Idx b)
    rw [← twE6ThreeFrame_rest, ← twE6ThreeFrame_rest]
    exact congrFun h4 i
  have hst : (fun b => s (f4Idx b)) = fun b => t (f4Idx b) := by
    have h := congrArg (fun v => Matrix.mulVec twE6ThreeFrameBasisInv v) h4'
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, twE6ThreeFrameBasisInv_mul] at h
    simpa using h
  funext a
  obtain ⟨b, rfl⟩ : ∃ b : Fin 4, f4Idx b = a := ⟨f4Inv a, Fin.ext rfl⟩
  exact congrFun hst b

private theorem exists_twE6ThreeFrame_eq_of_fixed (x : Fin Tag.E6.rank → ZMod 3)
    (h0 : x (e6Idx 0) = x e6Five) (h2 : x (e6Idx 2) = x e6Four) :
    ∃ s : Fin Tag.F4.rank → ZMod 3, twE6ThreeFrame s = x := by
  let xv : Fin 4 → ZMod 3 := fun i => x (e6Idx i)
  let sv : Fin 4 → ZMod 3 := Matrix.mulVec twE6ThreeFrameBasisInv xv
  let s : Fin Tag.F4.rank → ZMod 3 := fun a => sv (f4Inv a)
  have hsv : Matrix.mulVec twE6ThreeFrameBasis sv = xv := by
    rw [show sv = Matrix.mulVec twE6ThreeFrameBasisInv xv from rfl, Matrix.mulVec_mulVec,
      twE6ThreeFrameBasis_mul_inv, Matrix.one_mulVec]
  have hrest : ∀ i : Fin 4, twE6ThreeFrame s (e6Idx i) = xv i := by
    intro i
    rw [twE6ThreeFrame_rest]
    change (∑ b, twE6ThreeFrameBasis i b * sv b) = xv i
    rw [← congrFun hsv i]
    rfl
  refine ⟨s, ?_⟩
  funext a
  obtain ⟨i, rfl⟩ := e6Equiv.surjective a
  fin_cases i
  · exact hrest 0
  · exact hrest 1
  · exact hrest 2
  · exact hrest 3
  · change twE6ThreeFrame s (e6Equiv (4 : Fin 6)) = x (e6Equiv (4 : Fin 6))
    rw [show e6Equiv (4 : Fin 6) = e6Four from rfl]
    rw [← twE6ThreeFrame_two_eq_four, hrest 2]
    exact h2
  · change twE6ThreeFrame s (e6Equiv (5 : Fin 6)) = x (e6Equiv (5 : Fin 6))
    rw [show e6Equiv (5 : Fin 6) = e6Five from rfl]
    rw [← twE6ThreeFrame_zero_eq_five, hrest 0]
    exact h0

theorem exists_twE6ThreeFrame_eq_iff (x : Fin Tag.E6.rank → ZMod 3) :
    (∃ s : Fin Tag.F4.rank → ZMod 3, twE6ThreeFrame s = x) ↔
      x (e6Idx 0) = x e6Five ∧ x (e6Idx 2) = x e6Four := by
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨twE6ThreeFrame_zero_eq_five s, twE6ThreeFrame_two_eq_four s⟩
  · rintro ⟨h0, h2⟩
    exact exists_twE6ThreeFrame_eq_of_fixed x h0 h2

end ExcFrames

end CFSG.StandardType
