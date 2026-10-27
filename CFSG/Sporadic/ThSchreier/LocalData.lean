
module

public import CFSG.Sporadic.ThSchreier.LocalDataBase

public import CFSG.Sporadic.ThSchreier.Row
public import CFSG.Sporadic.Th.ChainBase1
public import CFSG.Sporadic.Th.Max3.PacketBase1
public import CFSG.Sporadic.Th.Max3.AllConjBase1
public meta import CFSG.Sporadic.ThSchreier.Text
public import CFSG.Sporadic.ThSchreier.LocalDataInputs
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.Th.Max3.AllConjInputs
public import CFSG.Sporadic.Th.Max3.InvolutionsBase1
public import CFSG.Sporadic.Th.Max3.InvolutionsInputs
public import CFSG.Sporadic.Th.Max3.QuotientBase1
public import CFSG.Sporadic.Th.Max3.QuotientInputs

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

@[expose] noncomputable def localX : J := Packet.run localProgram 1

@[expose] noncomputable def localY : J := Packet.run localProgram 2

@[expose] noncomputable def localH : Subgroup J := Subgroup.closure {localX, localY}

theorem localX_eq_word : localX = ((a * b) ^ 8)⁻¹ * a * (a * b) ^ 8 := by
  simp [localX, Packet.run, localProgram, Packet.Instr.exec, Packet.initRegs]

theorem localY_eq_word : localY =
    ((a * b * (a * b * (a * b * b)) * (a * b)) *
      ((a * b) * ((a * b * (a * b * (a * b * b)) * (a * b)) * (a * b * b)))) ^ 5 := by
  simp [localY, Packet.run, localProgram, Packet.Instr.exec, Packet.initRegs]

theorem localX_eq : localX = xJ := by
  rw [localX_eq_word, xJ]
  simp only [wordG, xWord, pairLetters, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, pow_succ, pow_zero, one_mul, mul_inv_rev, mul_one]
  norm_num
  group

theorem localY_eq : localY = yJ := by
  rw [localY_eq_word, yJ]
  simp only [wordG, yWord, pairLetters, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, pow_succ, pow_zero, one_mul, mul_one]
  norm_num
  group

theorem localH_eq : localH = H := by
  rw [localH, localX_eq, localY_eq]
  rfl

@[expose] noncomputable def localStrongList : List J :=
  localDerivations.foldl (fun hs w => hs ++ [evalSigned hs w]) [localX, localY]

@[expose] noncomputable def localStrong (j : ℕ) : J := localStrongList.getD j 1

theorem localStrongList_length : localStrongList.length = 10 := by
  simp [localStrongList, localDerivations]

theorem localStrongList_mem : ∀ g ∈ localStrongList, g ∈ localH := by
  have key : ∀ (ws : List (List ℤ)) (hs : List J), (∀ g ∈ hs, g ∈ localH) →
      ∀ g ∈ ws.foldl (fun hs w => hs ++ [evalSigned hs w]) hs, g ∈ localH := by
    intro ws
    induction ws with
    | nil => exact fun hs h => h
    | cons w ws ih =>
      intro hs h
      refine ih _ fun g hg => ?_
      rcases List.mem_append.1 hg with hg | hg
      · exact h g hg
      · rw [List.mem_singleton.1 hg]
        exact evalSigned_mem localH h w
  refine key _ _ fun g hg => ?_
  rcases List.mem_cons.1 hg with rfl | hg
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · rw [List.mem_singleton.1 hg]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem localStrong_mem (j : ℕ) : localStrong j ∈ localH := by
  rw [localStrong, List.getD_eq_getElem?_getD]
  cases h : localStrongList[j]? with
  | none => exact localH.one_mem
  | some g => exact localStrongList_mem g (List.mem_of_getElem? h)

theorem localStrong_zero : localStrong 0 = localX := by
  simp [localStrong, localStrongList, localDerivations]

theorem localStrong_one : localStrong 1 = localY := by
  simp [localStrong, localStrongList, localDerivations]

end CFSG.Sporadic.ThSchreier
