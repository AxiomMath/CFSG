
module

public import CFSG.Sporadic.HNOddCore.InvRow2Base

public import CFSG.Sporadic.HNOddCore.InvRow6
public import CFSG.Sporadic.HNOddCore.RkCheck
public import CFSG.Sporadic.HNSchreier.ThreeCent
public import CFSG.Sporadic.HNOddCore.NatCheckInputs
public meta import CFSG.Sporadic.HNOddCore.InvData
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public import CFSG.Sporadic.HNOddCore.RkCheckInputs
public meta import CFSG.Sporadic.HNSchreier.RankCheck
public meta import CFSG.Sporadic.HNOddCore.RankData
public import CFSG.Sporadic.HNOddCore.XCheckInputs
public meta import CFSG.Sporadic.HNOddCore.CCheck
public meta import CFSG.Sporadic.HNOddCore.InvArrays
public meta import Certificates.Data.CFSGNative.ONSchreier.Tools
public import CFSG.Sporadic.HNSchreier.ChainCheckInputs
public import CFSG.Sporadic.HNSchreier.LevelInputs
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
public import CFSG.Sporadic.HNSchreier.InvolCheckInputs
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck
public import CFSG.Sporadic.HNSchreier.LocalCheckInputs
public meta import CFSG.Sporadic.HNSchreier.PrimCheck
public meta import CFSG.Sporadic.HNSchreier.LocalData
public meta import CFSG.Sporadic.HNSchreier.MaskCheck
public import CFSG.Sporadic.HNSchreier.OrbitCheckInputs
public import CFSG.Sporadic.HNSchreier.PrimCheckInputs
public meta import Certificates.Data.CFSGNative.Perm.Chain
public import CFSG.Sporadic.HNSchreier.VectorData

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.He.Native Equiv

theorem row2_parts :
    fixCount hnsData.n t2Tab = 8800 ∧ InvData.a8Words.size = 6 ∧
    fixedSet hnsData.n a8Tabs = [0] := by
  have h := x_parts.2.2.2
  unfold row2OK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem card_fix_t2 :
    Nat.card {x : X // jR t2J • x = x} = 8800 := by
  rw [← row2_parts.1, ← fixCount_spec prep_t2]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [jR_smul]; rfl)

theorem a8_facts
    {w : List ℤ} (hw : w ∈ InvData.a8Words) :
    plettersOK 17 w = true ∧ hWordJ w ∈ A8J := by
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 hw
  have hj6 : j < 6 := by rw [← row2_parts.2.1]; exact hj
  rw [← getElem!_pos InvData.a8Words j hj]
  refine ⟨letters_of_natOK (nat_parts.2.2.2.2.2.2.2.2.2 j hj6),
    Subgroup.mem_map.2 ⟨hWordH InvData.a8Words[j]!, ?_, rfl⟩⟩
  rw [Subgroup.mem_comap, mem_fixingSubgroup_iff]
  intro i hi
  replace hi : i.val < 4 := hi
  rw [Perm.smul_def, thetaHom_apply, thetaJ_hWordH]
  apply Fin.ext
  rw [← prep_a8 hj6 i, cyc45_get_lt (by omega) hi]

theorem fix_t2_A8 :
    {x : X | jR t2J • x = x ∧ ∀ g ∈ A8J, g • x = x} = {x0} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h2, hA⟩
    have hmem : x.val ∈ fixedSet hnsData.n a8Tabs := by
      apply mem_fixedSet_of x.isLt
      intro g hg
      rw [Array.mem_append, Array.mem_singleton, Array.mem_map] at hg
      rcases hg with hg | ⟨w, hw, hgw⟩
      · rw [hg, prep_t2 x]
        rw [jR_smul] at h2
        exact congrArg Fin.val h2
      · obtain ⟨hl, hm⟩ := a8_facts hw
        rw [← hgw, prep_hWord hl x]
        exact congrArg Fin.val (hA _ hm)
    rw [row2_parts.2.2] at hmem
    exact Fin.ext (List.mem_singleton.1 hmem)
  · rintro rfl
    refine ⟨?_, fun g hg => (mem_HJ_iff_fix _).1 (A8J_le_HJ hg)⟩
    rw [jR_smul]
    exact (mem_HJ_iff_fix _).1 t2H.2

end CFSG.Sporadic.HNOddCore
