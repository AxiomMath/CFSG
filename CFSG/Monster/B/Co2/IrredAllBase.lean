
module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Certificates.SchreierChainData
public import CFSG.Monster.B.Short.ShortStab

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Co2

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Certificates
  CFSG.Monster.B.Short

theorem kOp_mem_vPerpL_of (g : OLq) {x z : L2} (hz : z ∈ vPerpL x) :
    kOp g z ∈ vPerpL (kOp g x) := by
  change bL (kOp g x) (kOp g z) = 0
  rw [bL_kOp]
  exact hz

theorem kOp_mem_vLineL_of (g : OLq) {x z : L2} (hz : z ∈ vLineL x) :
    kOp g z ∈ vLineL (kOp g x) := by
  rcases mem_vLineL.1 hz with rfl | rfl
  · rw [map_zero]
    exact zero_mem _
  · exact Submodule.mem_span_singleton_self _

@[expose] def perpMap (g : OLq) (x : L2) : vPerpL x →ₗ[ZMod 2] vPerpL (kOp g x) :=
  (kOp g).restrict fun _ hz => kOp_mem_vPerpL_of g hz

@[expose] def trW (g : OLq) (x : L2) : Wv x →ₗ[ZMod 2] Wv (kOp g x) :=
  Submodule.mapQ (vLineInL x) (vLineInL (kOp g x)) (perpMap g x) fun _ hz =>
    kOp_mem_vLineL_of g hz

theorem trW_mk (g : OLq) (x : L2) (z : vPerpL x) :
    trW g x (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨kOp g z, kOp_mem_vPerpL_of g z.2⟩ := rfl

end CFSG.Monster.B.Co2
