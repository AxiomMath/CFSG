module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Milestones.ASVolI.C31.J4NP.TreeDefs
public import CFSG.Sporadic.J4.QT2AGen
public import Certificates.Data.CFSGNative.J4Tree.Verdict

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
open CFSG.J4Tree.Native CFSG.J4Tree.Native.Col
open CFSG.Quasithin.J4Loc (omegaZ)

@[expose] noncomputable def burnsideJ4NP_colBasis (k i : ℕ) : J :=
  burnsideJ4NP_treeElt ((treeWv k).getD i (0, 0))

theorem burnsideJ4NP_col_Wv_eq_Eg (k : ℕ) :
    burnsideJ4NP_Wv k = Eg (burnsideJ4NP_colBasis k) (treeWv k).length := by
  unfold burnsideJ4NP_Wv Eg
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, List.mem_map]
  constructor
  · rintro ⟨ce, hce, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hce
    refine ⟨i, hi, ?_⟩
    rw [burnsideJ4NP_colBasis, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some]
  · rintro ⟨i, hi, rfl⟩
    refine ⟨(treeWv k)[i], List.getElem_mem hi, ?_⟩
    rw [burnsideJ4NP_colBasis, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some]

section Verdict

theorem burnsideJ4NP_col_eq_of_xor_eq_zero {i j : ℕ} (h : i ^^^ j = 0) : i = j := by
  calc i = i ^^^ (j ^^^ j) := by rw [Nat.xor_self, Nat.xor_zero]
    _ = (i ^^^ j) ^^^ j := by rw [Nat.xor_assoc]
    _ = j := by rw [h, Nat.zero_xor]

@[expose] noncomputable def burnsideJ4NP_colO (d : VNode) : Set J :=
  (fun o => eta (burnsideJ4NP_colBasis d.k) (treeWv d.k).length o) '' {o | o ∈ d.o}

end Verdict

end CFSG.ASVolI
