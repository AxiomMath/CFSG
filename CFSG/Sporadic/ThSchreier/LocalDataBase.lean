
module

public import CFSG.Sporadic.ThSchreier.RowBase
public import CFSG.Sporadic.Th.ChainBase
public import CFSG.Sporadic.Th.Max3.PacketBase
public import CFSG.Sporadic.Th.Max3.AllConjBase
public meta import CFSG.Sporadic.ThSchreier.Text
public import CFSG.Sporadic.ThSchreier.LocalDataInputs
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

@[expose] def localProgram : List Packet.Instr :=
  [.mu 1 2 3, .mu 3 2 4, .mu 3 4 5, .mu 3 5 6, .mu 6 3 7, .mu 7 4 8, .mu 3 8 9, .mu 7 9 8,
    .pwr 5 8 2, .pwr 8 3 4, .iv 4 3, .mu 3 1 5, .mu 5 4 1]

theorem localProgram_sourcesOk : Packet.sourcesOk localProgram [1, 2] = true := by decide

@[expose] def localRow (i : ℕ) : RowV := toRow (rowOfNat (localRowNats.getD i 0))

@[expose] def localOmega : Set RowV := {v | ∃ i < 2457, localRow i = v}

@[expose] def wRow1 : RowV :=
  toRow (rowOfNat 0xb9318bc60b06215ff4eb15e228ba41526fe75848bd0133807208caa1fa8551)

@[expose] def wRow2 : RowV :=
  toRow (rowOfNat 0x1e1057aa10c4abdf6972134ec61140ccf2027af03f80a7ed5002b65e4b1cca)

@[expose] noncomputable def planeW : Submodule (ZMod 2) RowV :=
  Submodule.span (ZMod 2) {wRow1, wRow2}

@[expose] def localDerivations : List (List ℤ) :=
  [[-2, 1, -2, 1, -2, -2, 1, -2, 1, 2, 1, 2, 2, 1, 2, 1, 2],
    [-2, -2, 1, -2, -2, 1, -2, -2, 1, -2, -2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2],
    [-2, 1, -2, -2, 1, -2, 1, -2, -2, 1, -2, -2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2],
    [-2, -2, 1, -2, 1, -2, -2, 1, -2, -2, 1, -2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2],
    [3, 6, 4, 6, 3],
    [1, -2, 1, -2, 1, -2, 1, -2, -2, 1, -2, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2],
    [4, -8, 6, 8, 8, 4],
    [9, 7, 9, 7, 9, 7]]

@[expose] noncomputable def evalSigned {G : Type*} [Group G] (hs : List G) (w : List ℤ) : G :=
  (w.map fun l => if 0 < l then hs.getD (l.natAbs - 1) 1 else (hs.getD (l.natAbs - 1) 1)⁻¹).prod

theorem evalSigned_mem {G : Type*} [Group G] (K : Subgroup G) {hs : List G}
    (hhs : ∀ g ∈ hs, g ∈ K) (w : List ℤ) : evalSigned hs w ∈ K := by
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hg
  have hget : hs.getD (l.natAbs - 1) 1 ∈ K := by
    rw [List.getD_eq_getElem?_getD]
    cases h : hs[l.natAbs - 1]? with
    | none => exact K.one_mem
    | some g => exact hhs g (List.mem_of_getElem? h)
  split_ifs
  · exact hget
  · exact K.inv_mem hget

end CFSG.Sporadic.ThSchreier
