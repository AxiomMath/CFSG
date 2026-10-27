
module

public import CFSG.Sporadic.HNOddCore.InvRow6Base
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

@[expose] public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.He.Native Equiv

theorem fixCount_spec {n : ℕ} {t : Array ℕ} {g : Perm (Fin n)} (ht : PRep n t g) :
    Nat.card {x : Fin n // g x = x} = fixCount n t := by
  rw [card_fix_eq, fixCount, ← List.countP_eq_length_filter]
  have e : (List.range n).countP (fun i => t[i]! == i) =
      ((Finset.range n).filter fun i => t[i]! = i).card := by
    rw [card_filter_range_eq_countP']
    exact List.countP_congr fun i _ => by simp
  rw [e]
  refine Finset.card_bij (fun x _ => x.val) ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_range.2 x.isLt, by rw [ht x, hx.2]⟩
  · intro x _ y _ hxy
    exact Fin.ext hxy
  · intro i hi
    have hi' := Finset.mem_filter.1 hi
    have hin : i < n := Finset.mem_range.1 hi'.1
    refine ⟨⟨i, hin⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, Fin.ext ?_⟩
    rw [← ht ⟨i, hin⟩]
    exact hi'.2

theorem mem_fixedSet_of {n : ℕ} {gens : Array (Array ℕ)} {i : ℕ} (hi : i < n)
    (h : ∀ g ∈ gens, g[i]! = i) : i ∈ fixedSet n gens := by
  unfold fixedSet
  rw [List.mem_filter, List.mem_range]
  refine ⟨hi, Array.all_eq_true_iff_forall_mem.2 fun g hg => ?_⟩
  simpa using h g hg

abbrev t2Tab : Array ℕ := pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) InvData.t2Word

abbrev a8Tabs : Array (Array ℕ) :=
  #[t2Tab] ++ InvData.a8Words.map (pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr))

theorem prep_t2 :
    PRep hnsData.n t2Tab (permJ t2J) := by
  rw [t2J_eq]
  exact prep_hWord (letters_of_natOK nat_parts.1)

@[expose] def A8J :
    Subgroup JH :=
  ((fixingSubgroup (Perm (Fin 12)) {i : Fin 12 | i.val < 4}).comap thetaHom).map
    HJ.subtype

theorem A8J_le_HJ :
    A8J ≤ HJ := by
  rintro _ ⟨h, -, rfl⟩
  exact h.2

theorem cyc45_get_lt {k i : ℕ} (hk : 6 ≤ k) (hi : i < 4) : (cyc45 k)[i]! = i := by
  unfold cyc45
  rw [getElem!_ofFn_nat _ (by omega)]
  dsimp only
  split_ifs <;> omega

theorem prep_a8
    {j : ℕ} (hj : j < 6) : PRep 12 (cyc45 (j + 6)) (natWord InvData.a8Words[j]!) := by
  have h := nat_parts.2.2.2.2.2.2.2.2.2 j hj
  unfold natOK at h
  simp only [Bool.and_eq_true] at h
  exact prep_of_peq_left h.2 (prep_natWord h.1)

theorem rank_of_cert {M : Array (Array ℕ)} {cert : Array (Array (Array ℕ))} {r : ℕ}
    {N : Matrix (Fin 133) (Fin 133) (ZMod 5)} (hM : toMat 5 133 M = N)
    (h : rankCertOK M cert r = true) :
    N.rank = Fintype.card {i : Fin 133 // (if i.val < r then (1 : ZMod 5) else 0) ≠ 0} := by
  unfold rankCertOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨-, hP⟩, hQ⟩, hE⟩ := h
  have e := congrArg (toMat 5 133) hE
  rw [toMat_mulM, toMat_mulM, hM] at e
  have huP : IsUnit (toMat 5 133 (cert[0]!)).det :=
    Matrix.isUnit_det_of_right_inverse (by rw [← toMat_mulM, hP, toMat_idM])
  have huQ : IsUnit (toMat 5 133 (cert[2]!)).det :=
    Matrix.isUnit_det_of_right_inverse (by rw [← toMat_mulM, hQ, toMat_idM])
  rw [← Matrix.rank_mul_eq_right_of_isUnit_det _ _ huP,
    ← Matrix.rank_mul_eq_left_of_isUnit_det _ _ huQ, e, toMat_diagR, Matrix.rank_diagonal]

theorem rank_parts :
    plettersOK 17 InvData.t2Word = true ∧ plettersOK 17 InvData.t4Word = true ∧
    rankCertOK (subId (mword mH mHi InvData.t2Word)) invRankRows[0]! 56 = true ∧
    rankCertOK (subId (mword mH mHi InvData.t4Word)) invRankRows[1]! 64 = true ∧
    rankCertOK (subId rowsA) invRankRows[2]! 56 = true := by
  have h := inv_rank_cert
  unfold invRankChecks at h
  rw [← mRegs_eq, ← mH_eq, ← mHi_eq] at h
  unfold invRankChecksH at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem rank_t2 :
    (matJ t2J - 1).rank = 56 := by
  have hM : toMat 5 133 (subId (mword mH mHi InvData.t2Word)) = matJ t2J - 1 := by
    rw [toMat_subId, toMat_mword_hWord _ (letters_of_plettersOK rank_parts.1), ← t2J_eq]
  rw [rank_of_cert hM rank_parts.2.2.1]
  decide

theorem rank_t4 :
    (matJ t4J - 1).rank = 64 := by
  have hM : toMat 5 133 (subId (mword mH mHi InvData.t4Word)) = matJ t4J - 1 := by
    rw [toMat_subId, toMat_mword_hWord _ (letters_of_plettersOK rank_parts.2.1), ← t4J_eq]
  rw [rank_of_cert hM rank_parts.2.2.2.1]
  decide

theorem rank_t6 :
    (matJ aJ - 1).rank = 56 := by
  have hM : toMat 5 133 (subId rowsA) = matJ aJ - 1 := by
    rw [toMat_subId, toMat_rowsA, mat_aJ]
  rw [rank_of_cert hM rank_parts.2.2.2.2]
  decide

end CFSG.Sporadic.HNOddCore
