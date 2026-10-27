
module

public import CFSG.Monster.B.TwoA.Unitary.Orbit1408PointsBase
import all CFSG.Monster.B.TwoA.Unitary.Orbit1408PointsBase

public import CFSG.Monster.B.TwoA.Unitary.Semilinear
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Data
public meta import CFSG.Monster.B.TwoA.Unitary.Orbit1408Data
public meta import CFSG.Monster.B.TwoA.Unitary.Form
public meta import CFSG.Monster.B.TwoA.Unitary.PlanesPrelude
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408PointsInputs
public import Certificates.Certificate3080
import CFSG.Fischer.F4
public import CFSG.Monster.B.TwoA.Unitary.OrbitInputs
public import CFSG.Monster.B.TwoA.Unitary.WStabInputs
public import CFSG.Monster.B.TwoA.Unitary.Stab891Inputs
public import CFSG.Monster.B.TwoA.Unitary.BData
public import CFSG.Monster.B.TwoA.Unitary.PlanesInputs
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Unitary.Bridge
public import CFSG.Monster.B.TwoA.Unitary.ActionInputs

public noncomputable section

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Fischer
open CFSG.Monster.B.Classical.UnitarySix (bar)

theorem singVec_ok :
    ∀ i : Fin 693, singVec i ≠ 0 ∧ hU (singVec i) (singVec i) = 0 :=
  Certificates.certificate3080.1

theorem singVec_distinct :
    ∀ i j : Fin 693, ∀ c : F4, singVec i = c • singVec j → i = j :=
  Certificates.certificate3080.2.1

theorem singLook_ok :
    ∀ v : V6, v ≠ 0 → hU v v = 0 → v = v (piv v) • singVec (singLook v) :=
  Certificates.certificate3080.2.2.1

theorem isSingPt_singPt (i : Fin 693) : IsSingPt (singPt i) :=
  isSingPt_span (singVec_ok i).1 (singVec_ok i).2

theorem singPt_injective : Function.Injective singPt := by
  intro i j h
  have hi : singVec i ∈ singPt j := by
    rw [← h]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hi
  exact singVec_distinct i j c hc.symm

theorem span_eq_singPt {v : V6} (hv : v ≠ 0) (hvv : hU v v = 0) :
    Submodule.span F4 {v} = singPt (singLook v) := by
  have e := singLook_ok v hv hvv
  have hc : v (piv v) ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at e
    exact hv e
  calc Submodule.span F4 {v} = Submodule.span F4 {v (piv v) • singVec (singLook v)} :=
        congrArg (fun x => Submodule.span F4 {x}) e
    _ = singPt (singLook v) := Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 hc) _

theorem exists_singPt_of_isSingPt {P : Submodule F4 V6}
    (hP : IsSingPt P) :
    ∃ i, singPt i = P := by
  obtain ⟨v, hv, hw⟩ := finrank_eq_one_iff'.1 hP.1
  have hv0 : (v : V6) ≠ 0 := fun h => hv (Subtype.ext h)
  have hP' : P = Submodule.span F4 {(v : V6)} := by
    apply le_antisymm
    · intro w hw'
      obtain ⟨c, hc⟩ := hw ⟨w, hw'⟩
      rw [Submodule.mem_span_singleton]
      exact ⟨c, congrArg Subtype.val hc⟩
    · rw [Submodule.span_singleton_le_iff_mem]
      exact v.2
  exact ⟨_, (span_eq_singPt hv0 (hP.2 _ v.2 _ v.2)).symm.trans hP'.symm⟩

theorem setOf_isSingPt : {P | IsSingPt P} = Set.range singPt := by
  ext P
  constructor
  · intro hP
    exact exists_singPt_of_isSingPt hP
  · rintro ⟨i, rfl⟩
    exact isSingPt_singPt i

theorem b6Map_singVec_ok : ∀ (k : Fin 17) (i : Fin 693),
    b6Map k (singVec i) ≠ 0 ∧ hU (b6Map k (singVec i)) (b6Map k (singVec i)) = 0 :=
  Certificates.certificate3080.2.2.2

theorem sigmaAct_singPt_slElt
    (k : Fin 17) (i : Fin 693) :
    sigmaAct (singPt i) (slElt k) = singPt (singGen k i) := by
  rw [singPt, sigmaAct_slElt_span, Set.image_singleton, singGen]
  exact span_eq_singPt (b6Map_singVec_ok k i).1 (b6Map_singVec_ok k i).2

theorem PermutesS.inv {x : SigmaU6} (hx : PermutesS x) : PermutesS
    x⁻¹ := by
  classical
  let f : Fin 693 → Fin 693 := fun i => Classical.choose (hx i)
  have hf : ∀ i, sigmaAct (singPt i) x = singPt (f i) := fun i => Classical.choose_spec (hx i)
  have hinj : Function.Injective f := by
    intro i j h
    apply singPt_injective
    rw [← sigmaAct_inv_cancel (singPt i) x, ← sigmaAct_inv_cancel (singPt j) x, hf, hf, h]
  intro j
  obtain ⟨i, hi⟩ := (Finite.injective_iff_surjective.1 hinj) j
  refine ⟨i, ?_⟩
  rw [← hi, ← hf, sigmaAct_inv_cancel]

theorem permutesS_of_mem_Gp
    {x : SigmaU6} (hx : x ∈ Gp) : PermutesS x
    := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact fun i => ⟨singGen k i, sigmaAct_singPt_slElt k i⟩
  | one => exact fun i => ⟨i, sigmaAct_one _⟩
  | mul x y _ _ hx hy => exact hx.mul hy
  | inv x _ hx => exact hx.inv

theorem permutesS
    (x : SigmaU6) : PermutesS x :=
  permutesS_of_mem_Gp (by rw [Gp_eq_top]; trivial)

@[expose] def singIdx
    (u : Usig) (i : Fin 693) : Fin 693 :=
    Classical.choose (permutesS (phiU u) i)

theorem singPt_singIdx
    (u : Usig) (i : Fin 693) :
    singPt (singIdx u i) = sigmaAct (singPt i) (phiU u) :=
  (Classical.choose_spec (permutesS (phiU u) i)).symm

theorem singIdx_mul
    (u u' : Usig) (i : Fin 693) : singIdx (u * u') i
    = singIdx u' (singIdx u i) :=
  singPt_injective (by rw [singPt_singIdx, singPt_singIdx, singPt_singIdx, map_mul, sigmaAct_mul])

theorem singIdx_one
    (i : Fin 693) : singIdx 1 i = i :=
  singPt_injective (by rw [singPt_singIdx, map_one, sigmaAct_one])

theorem singIdx_genU
    (k : Fin 17) (i : Fin 693) : singIdx (genU k) i
    = singGen k i :=
  singPt_injective (by rw [singPt_singIdx, phiU_genU, sigmaAct_singPt_slElt])

end CFSG.Monster.B.TwoA.Unitary
