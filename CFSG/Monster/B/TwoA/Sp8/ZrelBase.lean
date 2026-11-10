
module

public import CFSG.Monster.B.TwoA.Sp8.PsiBase
public meta import CFSG.Monster.B.TwoA.Co2Inv.SixActionBase
public import CFSG.Monster.B.TwoA.Sp8.ZrelInputs
public import CFSG.Monster.B.TwoA.Sp8.LiftsInputs
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Base.WCls
public import CFSG.Monster.B.TwoA.Census.PermBFS
public import CFSG.Monster.B.TwoA.Co2Inv.Data
public import CFSG.Monster.B.TwoA.Co2Inv.RowsInputs
public import CFSG.Monster.B.TwoA.Sp8.A8Base
public import CFSG.Monster.B.TwoA.Co2Inv.SixActionBase
public import CFSG.Monster.B.TwoA.Base.Space34ABase
public import CFSG.Monster.B.TwoA.Sp8.PsiInputs
public import CFSG.Monster.B.TwoA.Base.PairSpace
public import CFSG.Monster.B.TwoA.Base.Space34AInputs

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371
  CFSG.Monster.B.TwoA.Census CFSG.Monster.VisCert CFSG.Monster.B.Co2

theorem decW_actD (n : ℕ) (rows : Array ℕ) (c : ℕ) :
    decW (Native.actD n rows c) =
      ∑ i ∈ Finset.range n, if c.testBit i then decW rows[i]! else 0 := by
  rw [Native.actD, xorHom_actGo decW decW_xor, decW_zero, zero_add]

theorem decW_actD_mem_span (rows : Array ℕ) (n c : ℕ) :
    decW (Native.actD n rows c) ∈
      Submodule.span (ZMod 2) (Set.range fun i : Fin n => decW rows[(i : ℕ)]!) := by
  rw [decW_actD]
  refine Submodule.sum_mem _ fun i hi => ?_
  split_ifs
  · exact Submodule.subset_span ⟨⟨i, Finset.mem_range.1 hi⟩, rfl⟩
  · exact Submodule.zero_mem _

def bImg : Array ℕ := #[31, 12288, 20480, 36864, 69632, 30721]

def bVec (t : Fin 6) : Wv v0 := decW bImg[(t : ℕ)]!

theorem bImg_comb : ∀ t : Fin 6,
    Native.actD 6 zBasis ([1, 3, 5, 9, 33, 22].getD t 0) = bImg[(t : ℕ)]! := by
  decide

theorem zBasis_comb : ∀ t : Fin 6,
    Native.actD 6 bImg ([1, 3, 5, 9, 38, 17].getD t 0) = zBasis[(t : ℕ)]! := by
  decide

theorem bVec_mem (t : Fin 6) : bVec t ∈ Zsp := by
  rw [bVec, ← bImg_comb t]
  exact zComb_mem _

theorem zVec_mem_span (t : Fin 6) : zVec t ∈ Submodule.span (ZMod 2) (Set.range bVec) := by
  rw [zVec, ← zBasis_comb t]
  exact decW_actD_mem_span bImg 6 _

theorem span_bVec : Submodule.span (ZMod 2) (Set.range bVec) = Zsp := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    exact bVec_mem t
  · rw [Zsp, Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    exact zVec_mem_span t

theorem linearIndependent_bVec : LinearIndependent (ZMod 2) bVec := by
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, span_bVec, finrank_Zsp,
    Fintype.card_fin]

def psiGen : Fin 8 → Wv v0 := ![0, bVec 0, bVec 1, bVec 2, bVec 3, bVec 4, bVec 5, 0]

theorem psiGen_mem (k : Fin 8) : psiGen k ∈ Zsp := by
  fin_cases k
  · exact Zsp.zero_mem
  · exact bVec_mem 0
  · exact bVec_mem 1
  · exact bVec_mem 2
  · exact bVec_mem 3
  · exact bVec_mem 4
  · exact bVec_mem 5
  · exact Zsp.zero_mem

theorem decW_two_pow (t : Fin 22) : decW (2 ^ (t : ℕ)) = qbW t := by
  rw [decW, Finset.sum_eq_single t]
  · simp [bvec_apply, Nat.testBit_two_pow_self]
  · intro s _ hs
    simp [bvec_apply, Nat.testBit_two_pow_of_ne (fun h => hs (Fin.ext h).symm)]
  · simp

end CFSG.Monster.B.TwoA.Sp8
