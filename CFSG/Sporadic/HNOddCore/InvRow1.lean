
module

public import CFSG.Sporadic.HNOddCore.InvRow1Base

public import CFSG.Sporadic.HNOddCore.InvRow
public import CFSG.Sporadic.HNOddCore.Alt12
public import CFSG.Sporadic.HNOddCore.OrbitX
public import CFSG.Sporadic.HNOddCore.CCheckInputs
public meta import CFSG.Sporadic.HNSchreier.ThreeCheck
public import CFSG.Sporadic.HNOddCore.DCheckInputs
public import CFSG.Sporadic.HNOddCore.NatCheckInputs
public meta import CFSG.Sporadic.HNOddCore.InvData
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public import CFSG.Sporadic.HNOddCore.SCheckInputs
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
public import CFSG.Sporadic.HNOddCore.InvFix

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv

theorem row1_parts :
    fixListOK hnsData.n cRec InvData.f1Arr.toList = true ∧
    pointsOK hnsData.n InvData.f1Arr (posArr hnsData.n InvData.f1Arr) = true ∧
    InvData.s1Perms.size = 9 ∧ InvData.c1Words.size = 9 ∧
    ∀ j < 9, restrictOK (pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr)
      InvData.c1Words[j]!) InvData.f1Arr (posArr hnsData.n InvData.f1Arr) InvData.s1Perms[j]! =
        true := by
  have h := x_parts.1
  unfold row1OK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, fun j hj => allBelowN_spec h5 hj⟩

theorem hF1 :
    PtList hnsData.n InvData.f1Arr := ptList_of_pointsOK row1_parts.2.1

theorem fix_t1 :
    ∀ x : X, cR • x = x ↔ ∃ k : Fin InvData.f1Arr.size, hF1.pt k = x :=
  fix_iff_listed prep_cRec row1_parts.1 hF1

theorem card_fix_t1 :
    Nat.card {x : X // cR • x = x} = 1156 := by
  rw [card_fix_listed prep_cRec row1_parts.1, data_parts.1]

theorem nat_c1G
    {j : ℕ} (hj : j < 9) :
    PRep 12 (natArr InvData.c1Nat[j]!) (thetaJ ⟨c1G j, c1G_mem_HJ j⟩ : Perm (Fin 12)) := by
  have := (c1_spec.2 j (by rw [row1_parts.2.2.2.1]; exact hj)).2
  rw [← thetaJ_hWordH] at this
  exact this

theorem prep_c1G
    {j : ℕ} (hj : j < 9) : PRep hnsData.n
    (pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) InvData.c1Words[j]!)
    (permJ (c1G j)) :=
  prep_hWord (c1_spec.2 j (by rw [row1_parts.2.2.2.1]; exact hj)).1

theorem c1Nat_size :
    InvData.c1Nat.size = 9 := by
  rw [← c1_spec.1, row1_parts.2.2.2.1]

theorem c1G_comm
    {j : ℕ} (hj : j < 9) : jR (c1G j) * cR = cR * jR (c1G j) :=
  jR_comm_cR (c1G_mem_HJ j) (commute_of_prep (nat_c1G hj) prep_tau
    (natComm_parts.1 j (by rw [c1Nat_size]; exact hj)))

theorem c1G_mem_CJ
    {j : ℕ} (hj : j < 9) : c1G j ∈ CJ cR := mem_CJ.2 (c1G_comm hj)

theorem c1G_preserves
    {j : ℕ} (hj : j < 9) :
    ∀ k : Fin InvData.f1Arr.size, ∃ l, c1G j • hF1.pt k = hF1.pt l := fun k =>
  let ⟨l, hl⟩ := (fix_t1 _).1 (fix_cR_smul (c1G_mem_CJ hj) ((fix_t1 _).2 ⟨k, rfl⟩))
  ⟨l, hl.symm⟩

theorem hact1 :
    ∀ s < InvData.s1Perms.size, ∀ k : Fin InvData.f1Arr.size,
    ∃ h : (InvData.s1Perms[s]!)[(k : ℕ)]! < InvData.f1Arr.size,
      c1G s • hF1.pt k = hF1.pt ⟨(InvData.s1Perms[s]!)[(k : ℕ)]!, h⟩ := by
  intro s hs
  rw [row1_parts.2.2.1] at hs
  exact smul_pt_of_restrict hF1 row1_parts.2.1 (prep_c1G hs) (c1G_preserves hs)
    (row1_parts.2.2.2.2 s hs)

@[expose] def S1 (i : ℕ) : Set X :=
  {x | ∃ j < (InvData.o1Lists[i]!).size, ∃ h : (InvData.o1Lists[i]!)[j]! < InvData.f1Arr.size,
    hF1.pt ⟨_, h⟩ = x}

@[expose] def b1
    (i : ℕ) (hi : i < 3) : X :=
  hF1.pt ((ptList_of_pointsOK (orbitCertOK_spec (orbitCert1 hi)).2.1).pt
    ⟨0, (orbitCertOK_spec (orbitCert1 hi)).1⟩)

theorem orbit1_eq
    {i : ℕ} (hi : i < 3) : MulAction.orbit K1 (b1 i hi) =
    hF1.pt '' Set.range (ptList_of_pointsOK (orbitCertOK_spec (orbitCert1 hi)).2.1).pt :=
  orbit_eq_of_cert hF1 hact1 (orbitCert1 hi)

theorem orbit1_ncard
    {i : ℕ} (hi : i < 3) :
    (MulAction.orbit K1 (b1 i hi)).ncard = [1, 945, 210][i]! := by
  rw [orbit1_eq, Set.ncard_image_of_injective _ hF1.pt_injective,
    Set.ncard_range_of_injective (PtList.pt_injective _), Nat.card_eq_fintype_card,
    Fintype.card_fin, o1_size i hi]

theorem b1_zero :
    b1 0 (by norm_num) = x0 := by
  apply Fin.ext
  show InvData.f1Arr[(InvData.o1Lists[0]!)[0]!]! = 0
  rw [data_parts.2.2.2.2.2.2.1, data_parts.2.2.2.1]

theorem orbit1_subset_fix
    {i : ℕ} (hi : i < 3) :
    MulAction.orbit K1 (b1 i hi) ⊆ {x : X | cR • x = x} := by
  rw [orbit1_eq]
  rintro _ ⟨k, -, rfl⟩
  exact (fix_t1 _).2 ⟨k, rfl⟩

theorem K1_le_CJ :
    K1 ≤ CJ cR := by
  rw [Subgroup.closure_le]
  rintro _ ⟨s, rfl⟩
  exact c1G_mem_CJ (by rw [← row1_parts.2.2.1]; exact s.2)

theorem ncard_fix_t1 :
    {x : X | cR • x = x}.ncard = 1156 := by
  rw [← Nat.card_coe_set_eq]
  exact card_fix_t1

theorem fix_t1_cover :
    {x : X | cR • x = x} ⊆ MulAction.orbit K1 (b1 0 (by norm_num)) ∪
    MulAction.orbit K1 (b1 1 (by norm_num)) ∪ MulAction.orbit K1 (b1 2 (by norm_num)) := by
  have hsub : MulAction.orbit K1 (b1 0 (by norm_num)) ∪ MulAction.orbit K1 (b1 1 (by norm_num)) ∪
      MulAction.orbit K1 (b1 2 (by norm_num)) ⊆ {x : X | cR • x = x} :=
    Set.union_subset (Set.union_subset (orbit1_subset_fix _) (orbit1_subset_fix _))
      (orbit1_subset_fix _)
  have d01 := disjoint_orbit_of_ncard_ne (G := K1)
    (a := b1 0 (by norm_num)) (b := b1 1 (by norm_num)) (by rw [orbit1_ncard, orbit1_ncard]; decide)
  have d02 := disjoint_orbit_of_ncard_ne (G := K1)
    (a := b1 0 (by norm_num)) (b := b1 2 (by norm_num)) (by rw [orbit1_ncard, orbit1_ncard]; decide)
  have d12 := disjoint_orbit_of_ncard_ne (G := K1)
    (a := b1 1 (by norm_num)) (b := b1 2 (by norm_num)) (by rw [orbit1_ncard, orbit1_ncard]; decide)
  have hcard : {x : X | cR • x = x}.ncard ≤ (MulAction.orbit K1 (b1 0 (by norm_num)) ∪
      MulAction.orbit K1 (b1 1 (by norm_num)) ∪ MulAction.orbit K1 (b1 2 (by norm_num))).ncard := by
    rw [Set.ncard_union_eq (Disjoint.union_left d02 d12) (Set.toFinite _) (Set.toFinite _),
      Set.ncard_union_eq d01 (Set.toFinite _) (Set.toFinite _), orbit1_ncard, orbit1_ncard,
      orbit1_ncard, ncard_fix_t1]
    decide
  exact (Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)).symm.le

theorem orbit_CJc :
    MulAction.orbit (CJ cR) x0 = {x0} := by
  set O := MulAction.orbit (CJ cR) x0 with hO
  have hOfix : O ⊆ {x : X | cR • x = x} := by
    rintro _ ⟨g, rfl⟩
    exact fix_cR_smul g.2 cR_smul_x0
  have hinv : ∀ g : K1, ∀ y ∈ O, g • y ∈ O := by
    rintro ⟨g, hg⟩ y ⟨h, rfl⟩
    refine ⟨⟨g, K1_le_CJ hg⟩ * h, ?_⟩
    show (⟨g, K1_le_CJ hg⟩ * h) • x0 = (⟨g, hg⟩ : K1) • (h • x0)
    rw [mul_smul]
    rfl
  have hmeet : ∀ {i : ℕ} (hi : i < 3), O ∩ MulAction.orbit K1 (b1 i hi) = ∅ ∨
      O ∩ MulAction.orbit K1 (b1 i hi) = MulAction.orbit K1 (b1 i hi) := fun hi =>
    inter_eq_empty_or fun ⟨_, hyO, hyS⟩ => orbit_subset_of_invariant hinv hyO hyS
  have h0 : O ∩ MulAction.orbit K1 (b1 0 (by norm_num)) =
      MulAction.orbit K1 (b1 0 (by norm_num)) := by
    rcases hmeet (i := 0) (by norm_num) with h | h
    · exfalso
      have hx0 : x0 ∈ O ∩ MulAction.orbit K1 (b1 0 (by norm_num)) :=
        ⟨MulAction.mem_orbit_self x0, by rw [b1_zero]; exact MulAction.mem_orbit_self x0⟩
      rw [h] at hx0
      exact hx0
    · exact h
  have hcard := ncard_of_three_orbits (hOfix.trans fix_t1_cover)
    (disjoint_orbit_of_ncard_ne (by rw [orbit1_ncard, orbit1_ncard]; decide))
    (disjoint_orbit_of_ncard_ne (by rw [orbit1_ncard, orbit1_ncard]; decide))
    (disjoint_orbit_of_ncard_ne (by rw [orbit1_ncard, orbit1_ncard]; decide)) h0
    (hmeet (by norm_num)) (hmeet (by norm_num))
  rw [orbit1_ncard, orbit1_ncard, orbit1_ncard] at hcard
  have hdvd : O.ncard ∣ 273030912000000 := by
    rw [hO, ← MulAction.index_stabilizer, ← card_JH]
    exact (Subgroup.index_dvd_card _).trans (Subgroup.card_subgroup_dvd_card _)
  have h1 : O.ncard = 1 := by
    simp only [List.getElem!_cons_zero, List.getElem!_cons_succ] at hcard
    rcases hcard with h | h | h | h
    · exact h
    · rw [h] at hdvd; exact absurd hdvd (by decide)
    · rw [h] at hdvd; exact absurd hdvd (by decide)
    · rw [h] at hdvd; exact absurd hdvd (by decide)
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h1
  have hx0 : x0 ∈ O := MulAction.mem_orbit_self x0
  rw [ha, Set.mem_singleton_iff] at hx0
  rw [ha, hx0]

theorem CJc_le_HJ :
    CJ cR ≤ HJ := by
  intro g hg
  rw [mem_HJ_iff_fix]
  have : (⟨g, hg⟩ : CJ cR) • x0 ∈ MulAction.orbit (CJ cR) x0 := MulAction.mem_orbit _ _
  rw [orbit_CJc, Set.mem_singleton_iff] at this
  exact this

end CFSG.Sporadic.HNOddCore
