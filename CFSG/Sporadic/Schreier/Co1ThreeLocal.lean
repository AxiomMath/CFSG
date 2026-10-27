module

public import CFSG.Sporadic.Schreier.Co1Base
public import CFSG.Sporadic.Co1
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public import CFSG.Sporadic.Schreier.Co1ThreeLocalInputs
public import Certificates.Certificate2150
public import Certificates.Certificate3024

public section

namespace CFSG.Sporadic.Co1Schreier

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

namespace Native

open CFSG.Sporadic.Co1Schreier.Native

@[expose] def zR : Rows := pow (mul (mul (mul tR yR) (inv tR)) (inv yR)) 7

end Native

noncomputable abbrev A₁ : GL24 := gA CFSG.Sporadic.Co1.Native.co1Data

noncomputable abbrev A₂ : GL24 := gB CFSG.Sporadic.Co1.Native.co1Data

noncomputable abbrev GA : Subgroup GL24 := J CFSG.Sporadic.Co1.Native.co1Data

theorem GA_eq : GA = Subgroup.closure {A₁, A₂} := rfl

theorem A₁_mem : A₁ ∈ GA := Subgroup.subset_closure (Set.mem_insert _ _)

theorem A₂_mem : A₂ ∈ GA := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem val_A₁ : ((A₁ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) =
    mA CFSG.Sporadic.Co1.Native.co1Data := by
  unfold A₁
  rw [gA_eq CFSG.Sporadic.Co1.co1Facts.toBaseFacts]
  rfl

theorem val_A₂ : ((A₂ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) =
    mB CFSG.Sporadic.Co1.Native.co1Data := by
  unfold A₂
  rw [gB_eq CFSG.Sporadic.Co1.co1Facts.toBaseFacts]
  rfl

theorem rep_A₁ : MRep Native.aR A₁ := by
  unfold MRep
  rw [val_A₁]
  exact rowsMatrix_rowsA CFSG.Sporadic.Co1.Native.co1Data

theorem rep_A₂ : MRep Native.bR A₂ := by
  unfold MRep
  rw [val_A₂]
  exact rowsMatrix_rowsB CFSG.Sporadic.Co1.Native.co1Data

namespace ThreeLocal

@[expose] noncomputable def c : GL24 := A₁ * A₂

@[expose] noncomputable def d : GL24 := A₁ * A₂ * A₂

@[expose] noncomputable def u : GL24 := c ^ 2 * d

@[expose] noncomputable def w : GL24 := u ^ 2 * c

@[expose] noncomputable def x : GL24 := c⁻¹ ^ 2 * A₁ * c ^ 2

@[expose] noncomputable def y : GL24 := d⁻¹ ^ 2 * w ^ 8 * d ^ 2

@[expose] noncomputable def t : GL24 := x * y * x

@[expose] noncomputable def z : GL24 := (t * y * t⁻¹ * y⁻¹) ^ 7

@[expose] noncomputable def B : Subgroup GL24 := Subgroup.closure {x, y}

@[expose] noncomputable def K : Subgroup GL24 := Subgroup.closure {y, t}

end ThreeLocal

theorem threeLocal_check : Native.threeLocalCheck = true :=
  Certificates.certificate2150

open ThreeLocal in
theorem rep_threeLocal : MRep Native.cR c ∧ MRep Native.dR d ∧ MRep Native.xR x ∧
    MRep Native.yR y ∧ MRep Native.tR t ∧ MRep Native.zR z := by
  have h := threeLocal_check
  simp only [Native.threeLocalCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hc, hd⟩, ht⟩, hy⟩ := h
  have rc : MRep Native.cR c := rep_A₁.mul rep_A₂
  have rd : MRep Native.dR d := (rep_A₁.mul rep_A₂).mul rep_A₂
  have ru : MRep Native.uR u := (rc.pow 2).mul rd
  have rw : MRep Native.wR w := (ru.pow 2).mul rc
  have rx : MRep Native.xR x := (((rc.inv hc).pow 2).mul rep_A₁).mul (rc.pow 2)
  have ry : MRep Native.yR y := (((rd.inv hd).pow 2).mul (rw.pow 8)).mul (rd.pow 2)
  have rt : MRep Native.tR t := (rx.mul ry).mul rx
  refine ⟨rc, rd, rx, ry, rt, ?_⟩
  exact (((rt.mul ry).mul (rt.inv ht)).mul (ry.inv hy)).pow 7

theorem rep_y : MRep Native.yR ThreeLocal.y := rep_threeLocal.2.2.2.1

theorem rep_t : MRep Native.tR ThreeLocal.t := rep_threeLocal.2.2.2.2.1

theorem rep_z : MRep Native.zR ThreeLocal.z := rep_threeLocal.2.2.2.2.2

theorem rep_x : MRep Native.xR ThreeLocal.x := rep_threeLocal.2.2.1

theorem threeLocal_mem : ThreeLocal.x ∈ GA ∧ ThreeLocal.y ∈ GA ∧ ThreeLocal.t ∈ GA ∧
    ThreeLocal.z ∈ GA := by
  have hc : ThreeLocal.c ∈ GA := mul_mem A₁_mem A₂_mem
  have hd : ThreeLocal.d ∈ GA := mul_mem (mul_mem A₁_mem A₂_mem) A₂_mem
  have hu : ThreeLocal.u ∈ GA := mul_mem (pow_mem hc 2) hd
  have hw : ThreeLocal.w ∈ GA := mul_mem (pow_mem hu 2) hc
  have hx : ThreeLocal.x ∈ GA :=
    mul_mem (mul_mem (pow_mem (inv_mem hc) 2) A₁_mem) (pow_mem hc 2)
  have hy : ThreeLocal.y ∈ GA :=
    mul_mem (mul_mem (pow_mem (inv_mem hd) 2) (pow_mem hw 8)) (pow_mem hd 2)
  have ht : ThreeLocal.t ∈ GA := mul_mem (mul_mem hx hy) hx
  exact ⟨hx, hy, ht, pow_mem (mul_mem (mul_mem (mul_mem ht hy) (inv_mem ht)) (inv_mem hy)) 7⟩

end CFSG.Sporadic.Co1Schreier
