
module

public import CFSG.Sporadic.HNOddCore.InvRow4Base

public import CFSG.Sporadic.HNOddCore.InvRow1b
public import CFSG.Sporadic.HNOddCore.DCheckInputs
public import CFSG.Sporadic.HNOddCore.NatCheckInputs
public meta import CFSG.Sporadic.HNOddCore.InvData
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
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
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.F5.Native Equiv

theorem row4_parts :
    fixListOK hnsData.n t4Tab InvData.f4Arr.toList = true ∧
    pointsOK hnsData.n InvData.f4Arr (posArr hnsData.n InvData.f4Arr) = true ∧
    InvData.s4Perms.size = 11 ∧ InvData.c4Words.size = 9 ∧
    (∀ j < 9, restrictOK (pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr)
      InvData.c4Words[j]!) InvData.f4Arr (posArr hnsData.n InvData.f4Arr) InvData.s4Perms[j]! =
        true) ∧
    restrictOK x4Tab InvData.f4Arr (posArr hnsData.n InvData.f4Arr) InvData.s4Perms[9]! = true ∧
    restrictOK cRec InvData.f4Arr (posArr hnsData.n InvData.f4Arr) InvData.s4Perms[10]! = true ∧
    peq hnsData.n (pcomp hnsData.n x4Tab t4Tab) (pcomp hnsData.n t4Tab x4Tab) = true := by
  have h := x_parts.2.1
  unfold row4OK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, fun j hj => allBelowN_spec h5 hj, h6, h7, h8⟩

theorem hF4 :
    PtList hnsData.n InvData.f4Arr := ptList_of_pointsOK row4_parts.2.1

theorem fix_t4 :
    ∀ x : X, jR t4J • x = x ↔ ∃ k : Fin InvData.f4Arr.size, hF4.pt k = x :=
  fix_iff_listed (by rw [permR_jR]; exact prep_t4) row4_parts.1 hF4

theorem card_fix_t4 :
    Nat.card {x : X // jR t4J • x = x} = 800 := by
  rw [card_fix_listed (by rw [permR_jR]; exact prep_t4) row4_parts.1, data_parts.2.1]

theorem c4Nat_size :
    InvData.c4Nat.size = 9 := by
  rw [← c4_spec.1, row4_parts.2.2.2.1]

theorem nat_c4G
    {j : ℕ} (hj : j < 9) :
    PRep 12 (natArr InvData.c4Nat[j]!) (thetaJ ⟨c4G j, c4G_mem_HJ j⟩ : Perm (Fin 12)) := by
  have := (c4_spec.2 j (by rw [row4_parts.2.2.2.1]; exact hj)).2
  rw [← thetaJ_hWordH] at this
  exact this

theorem c4G_comm
    {j : ℕ} (hj : j < 9) : c4G j * t4J = t4J * c4G j :=
  commute_of_thetaJ (c4G_mem_HJ j) t4J_mem_HJ (commute_of_prep (nat_c4G hj) nat_t4
    (natComm_parts.2.1 j (by rw [c4Nat_size]; exact hj)))

theorem prep_c4G
    {j : ℕ} (hj : j < 9) : PRep hnsData.n
    (pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) InvData.c4Words[j]!)
    (permJ (c4G j)) :=
  prep_hWord (c4_spec.2 j (by rw [row4_parts.2.2.2.1]; exact hj)).1

theorem x4J_comm :
    x4J * t4J = t4J * x4J := by
  have h := eq_of_peq (prep_pcomp prep_x4 prep_t4) (prep_pcomp prep_t4 prep_x4)
    row4_parts.2.2.2.2.2.2.2
  rw [← map_mul, ← map_mul] at h
  exact permJ_injective h

theorem g4_comm
    (s : ℕ) (_hs : s < 10) : g4 s * t4J = t4J * g4 s := by
  unfold g4
  split_ifs with h
  · exact c4G_comm h
  · exact x4J_comm

theorem g4_mem
    (s : ℕ) (hs : s < 10) : g4 s ∈ Subgroup.centralizer {t4J} :=
  (Subgroup.mem_centralizer_singleton_iff (g := t4J) (k := g4 s)).2 (g4_comm s hs)

theorem g4_preserves
    {s : ℕ} (hs : s < 10) :
    ∀ k : Fin InvData.f4Arr.size, ∃ l, g4 s • hF4.pt k = hF4.pt l := fun k =>
  let ⟨l, hl⟩ := (fix_t4 _).1 (fix_t4_smul (g4_comm s hs) ((fix_t4 _).2 ⟨k, rfl⟩))
  ⟨l, hl.symm⟩

theorem s4J_size : s4J.size = 10 := by
  unfold s4J
  simp [row4_parts.2.2.1]

theorem s4J_get
    {s : ℕ} (hs : s < 10) : s4J[s]! = InvData.s4Perms[s]! := by
  unfold s4J
  rw [getElem!_pos _ s (by simp [row4_parts.2.2.1]; omega), Array.getElem_extract,
    getElem!_pos _ s (by rw [row4_parts.2.2.1]; omega)]
  simp

theorem hact4 :
    ∀ s < s4J.size, ∀ k : Fin InvData.f4Arr.size,
    ∃ h : (s4J[s]!)[(k : ℕ)]! < InvData.f4Arr.size,
      g4 s • hF4.pt k = hF4.pt ⟨(s4J[s]!)[(k : ℕ)]!, h⟩ := by
  intro s hs
  rw [s4J_size] at hs
  rw [s4J_get hs]
  by_cases h9 : s < 9
  · have hg : g4 s = c4G s := ite_eq_left h9
    rw [hg]
    exact smul_pt_of_restrict hF4 row4_parts.2.1 (prep_c4G h9) (hg ▸ g4_preserves hs)
      (row4_parts.2.2.2.2.1 s h9)
  · have hs9 : s = 9 := by omega
    subst hs9
    have hg : g4 9 = x4J := ite_eq_right (by norm_num)
    rw [hg]
    exact smul_pt_of_restrict hF4 row4_parts.2.1 prep_x4 (hg ▸ g4_preserves hs)
      row4_parts.2.2.2.2.2.1

theorem S4_le :
    S4 ≤ Subgroup.centralizer {t4J} := by
  rw [Subgroup.closure_le]
  rintro _ ⟨s, rfl⟩
  exact g4_mem s (by rw [← s4J_size]; exact s.2)

end CFSG.Sporadic.HNOddCore
