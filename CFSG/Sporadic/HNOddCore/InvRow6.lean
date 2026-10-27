
module

public import CFSG.Sporadic.HNOddCore.InvRow6Base

public import CFSG.Sporadic.HNOddCore.InvRow4b
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

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv

theorem row6_parts :
    m2Run.2 = true ∧ pisInv hnsData.n g6Tab (pinvCand hnsData.n g6Tab) = true ∧
    fixListOK hnsData.n (natTab (hnsData.orbit ()).alpha) InvData.f6Arr.toList = true ∧
    pointsOK hnsData.n InvData.f6Arr (posArr hnsData.n InvData.f6Arr) = true ∧
    InvData.s6Perms.size = 12 ∧ InvData.c6Words.size = 10 ∧
    (∀ j < 10, restrictOK (pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr)
      InvData.c6Words[j]!) InvData.f6Arr (posArr hnsData.n InvData.f6Arr) InvData.s6Perms[j]! =
        true) ∧
    restrictOK (e6Tab 1) InvData.f6Arr (posArr hnsData.n InvData.f6Arr) InvData.s6Perms[10]! =
      true ∧
    restrictOK (e6Tab 2) InvData.f6Arr (posArr hnsData.n InvData.f6Arr) InvData.s6Perms[11]! =
      true ∧
    peq hnsData.n (pcomp hnsData.n (e6Tab 1) (natTab (hnsData.orbit ()).alpha))
      (pcomp hnsData.n (natTab (hnsData.orbit ()).alpha) (e6Tab 1)) = true ∧
    peq hnsData.n (pcomp hnsData.n (e6Tab 2) (natTab (hnsData.orbit ()).alpha))
      (pcomp hnsData.n (natTab (hnsData.orbit ()).alpha) (e6Tab 2)) = true := by
  have h := x_parts.2.2.1
  unfold row6Run row6OK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, ⟨⟨⟨⟨⟨⟨⟨⟨h3, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, fun j hj => allBelowN_spec h7 hj, h8, h9, h10, h11⟩

theorem regs6_rep :
    RegsRep m2Run.1 (progRunG permRegs0 InvData.m2Prog) :=
  regsRep_progRun _ _ _ m2Prog_bounds regsRep_init row6_parts.1

theorem prep_e6
    {i : ℕ} (hi : i < 11) : PRep hnsData.n (e6Tab i) (permJ (e6J i)) := by
  rw [e6J, map_mul, map_mul, map_inv]
  refine prep_pcomp (prep_inv_of_pisInv prep_g6c row6_parts.2.1) (prep_pcomp ?_ prep_g6c)
  rw [permJ_m2RegsJ]
  exact regs6_rep.2 i hi

theorem e6J_comm
    {i : ℕ} (hi : i = 1 ∨ i = 2) : e6J i * aJ = aJ * e6J i := by
  have hpe : peq hnsData.n (pcomp hnsData.n (e6Tab i) (natTab (hnsData.orbit ()).alpha))
      (pcomp hnsData.n (natTab (hnsData.orbit ()).alpha) (e6Tab i)) = true := by
    rcases hi with rfl | rfl
    · exact row6_parts.2.2.2.2.2.2.2.2.2.1
    · exact row6_parts.2.2.2.2.2.2.2.2.2.2
  have h := eq_of_peq (prep_pcomp (prep_e6 (by omega)) prep_a0J)
    (prep_pcomp prep_a0J (prep_e6 (by omega))) hpe
  rw [← map_mul, ← map_mul] at h
  exact permJ_injective h

theorem hF6 :
    PtList hnsData.n InvData.f6Arr := ptList_of_pointsOK row6_parts.2.2.2.1

theorem fix_t6 :

    ∀ x : X, jR aJ • x = x ↔ ∃ k : Fin InvData.f6Arr.size, hF6.pt k = x :=
  fix_iff_listed (by rw [permR_jR]; exact prep_a0J) row6_parts.2.2.1 hF6

theorem card_fix_t6 :
    Nat.card {x : X // jR aJ • x = x} = 8800 := by
  rw [card_fix_listed (by rw [permR_jR]; exact prep_a0J) row6_parts.2.2.1, data_parts.2.2.1]

theorem fix_t6_set :
    {x : X | jR aJ • x = x} = Set.range hF6.pt := by
  ext x
  exact fix_t6 x

theorem c6Nat_size :
    InvData.c6Nat.size = 10 := by
  rw [← c6_spec.1, row6_parts.2.2.2.2.2.1]

theorem nat_c6G
    {j : ℕ} (hj : j < 10) :
    PRep 12 (natArr InvData.c6Nat[j]!) (thetaJ ⟨c6G j, c6G_mem_HJ j⟩ : Perm (Fin 12)) := by
  have := (c6_spec.2 j (by rw [row6_parts.2.2.2.2.2.1]; exact hj)).2
  rw [← thetaJ_hWordH] at this
  exact this

theorem c6G_comm
    {j : ℕ} (hj : j < 10) : c6G j * aJ = aJ * c6G j :=
  commute_of_thetaJ (c6G_mem_HJ j) aJ_mem_HJ (commute_of_prep (nat_c6G hj) nat_t6
    (natComm_parts.2.2.1 j (by rw [c6Nat_size]; exact hj)))

theorem prep_c6G
    {j : ℕ} (hj : j < 10) : PRep hnsData.n
    (pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) InvData.c6Words[j]!)
    (permJ (c6G j)) :=
  prep_hWord (c6_spec.2 j (by rw [row6_parts.2.2.2.2.2.1]; exact hj)).1

theorem g6_comm
    {s : ℕ} (hs : s < 12) : g6 s * aJ = aJ * g6 s := by
  unfold g6
  split_ifs with h
  · exact c6G_comm h
  · exact e6J_comm (by omega)

theorem g6_mem
    {s : ℕ} (hs : s < 12) : g6 s ∈ Subgroup.centralizer {aJ} :=
  mem_centralizer_of_comm (g6_comm hs)

theorem g6_preserves
    {s : ℕ} (hs : s < 12) :
    ∀ k : Fin InvData.f6Arr.size, ∃ l, g6 s • hF6.pt k = hF6.pt l := fun k =>
  let ⟨l, hl⟩ := (fix_t6 _).1 (fix_jR_smul (g6_comm hs) ((fix_t6 _).2 ⟨k, rfl⟩))
  ⟨l, hl.symm⟩

theorem hact6 :
    ∀ s < InvData.s6Perms.size, ∀ k : Fin InvData.f6Arr.size,
    ∃ h : (InvData.s6Perms[s]!)[(k : ℕ)]! < InvData.f6Arr.size,
      g6 s • hF6.pt k = hF6.pt ⟨(InvData.s6Perms[s]!)[(k : ℕ)]!, h⟩ := by
  intro s hs
  rw [row6_parts.2.2.2.2.1] at hs
  by_cases h10 : s < 10
  · have hg : g6 s = c6G s := ite_eq_left h10
    rw [hg]
    exact smul_pt_of_restrict hF6 row6_parts.2.2.2.1 (prep_c6G h10) (hg ▸ g6_preserves hs)
      (row6_parts.2.2.2.2.2.2.1 s h10)
  · have hg : g6 s = e6J (s - 9) := ite_eq_right h10
    have hrs : restrictOK (e6Tab (s - 9)) InvData.f6Arr (posArr hnsData.n InvData.f6Arr)
        InvData.s6Perms[s]! = true := by
      rcases (show s = 10 ∨ s = 11 by omega) with rfl | rfl
      · exact row6_parts.2.2.2.2.2.2.2.1
      · exact row6_parts.2.2.2.2.2.2.2.2.1
    rw [hg]
    exact smul_pt_of_restrict hF6 row6_parts.2.2.2.1 (prep_e6 (by omega)) (hg ▸ g6_preserves hs)
      hrs

theorem S6_le :
    S6 ≤ Subgroup.centralizer {aJ} := by
  rw [Subgroup.closure_le]
  rintro _ ⟨s, rfl⟩
  exact g6_mem (by rw [← row6_parts.2.2.2.2.1]; exact s.2)

@[expose] def b6
    (i : ℕ) (hi : i < 2) : X :=
  hF6.pt ((ptList_of_pointsOK (orbitCertOK_spec (orbitCert6 hi)).2.1).pt
    ⟨0, (orbitCertOK_spec (orbitCert6 hi)).1⟩)

theorem orbit6_eq
    {i : ℕ} (hi : i < 2) : MulAction.orbit S6 (b6 i hi) =
    hF6.pt '' Set.range (ptList_of_pointsOK (orbitCertOK_spec (orbitCert6 hi)).2.1).pt :=
  orbit_eq_of_cert hF6 hact6 (orbitCert6 hi)

theorem orbit6_ncard
    {i : ℕ} (hi : i < 2) :
    (MulAction.orbit S6 (b6 i hi)).ncard = [7700, 1100][i]! := by
  rw [orbit6_eq, Set.ncard_image_of_injective _ hF6.pt_injective,
    Set.ncard_range_of_injective (PtList.pt_injective _), Nat.card_eq_fintype_card,
    Fintype.card_fin, o6_size hi]

theorem b6_zero :
    b6 0 (by norm_num) = x0 := by
  apply Fin.ext
  show InvData.f6Arr[(InvData.o6Lists[0]!)[0]!]! = 0
  rw [data_parts.2.2.2.2.2.2.2, data_parts.2.2.2.2.2.1]

theorem orbit6_subset_fix
    {i : ℕ} (hi : i < 2) :
    MulAction.orbit S6 (b6 i hi) ⊆ {x : X | jR aJ • x = x} := by
  rw [orbit6_eq]
  rintro _ ⟨k, -, rfl⟩
  exact (fix_t6 _).2 ⟨k, rfl⟩

theorem ncard_fix_t6 :
    {x : X | jR aJ • x = x}.ncard = 8800 := by
  rw [← Nat.card_coe_set_eq]
  exact card_fix_t6

theorem disjoint_orbit6 :
    Disjoint (MulAction.orbit S6 (b6 0 (by norm_num)))
    (MulAction.orbit S6 (b6 1 (by norm_num))) :=
  disjoint_orbit_of_ncard_ne (by rw [orbit6_ncard, orbit6_ncard]; decide)

theorem fix_t6_eq :

    {x : X | jR aJ • x = x} = MulAction.orbit S6 (b6 0 (by norm_num)) ∪
    MulAction.orbit S6 (b6 1 (by norm_num)) := by
  have hsub : MulAction.orbit S6 (b6 0 (by norm_num)) ∪ MulAction.orbit S6 (b6 1 (by norm_num)) ⊆
      {x : X | jR aJ • x = x} :=
    Set.union_subset (orbit6_subset_fix _) (orbit6_subset_fix _)
  have hcard : {x : X | jR aJ • x = x}.ncard ≤ (MulAction.orbit S6 (b6 0 (by norm_num)) ∪
      MulAction.orbit S6 (b6 1 (by norm_num))).ncard := by
    rw [Set.ncard_union_eq disjoint_orbit6 (Set.toFinite _) (Set.toFinite _), orbit6_ncard,
      orbit6_ncard, ncard_fix_t6]
    decide
  exact (Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)).symm

theorem card_K6 :
    Nat.card K6 = 23040 := by
  rw [card_closure_eq_nat (fun s : Fin InvData.c6Nat.size => c6G s) (fun s => c6G_mem_HJ s)]
  have hO : ∀ k < (natArrs InvData.c6Nat).size,
      PRep 12 (natArrs InvData.c6Nat)[k]! (thetaJ ⟨c6G k, c6G_mem_HJ k⟩ : Perm (Fin 12)) := by
    intro k hk
    have hk' : k < 10 := by simpa [natArrs, c6Nat_size] using hk
    have := nat_c6G hk'
    rwa [natArrs, getElem!_pos _ k (by simpa [natArrs] using hk), Array.getElem_map,
      ← getElem!_pos InvData.c6Nat k (by rw [c6Nat_size]; exact hk')]
  have h1 := arrGen_eq hO
  have h2 : Set.range (fun s : Fin InvData.c6Nat.size =>
      (thetaJ ⟨c6G s, c6G_mem_HJ s⟩ : Perm (Fin 12))) =
      Set.range (fun k : Fin (natArrs InvData.c6Nat).size =>
        (thetaJ ⟨c6G k, c6G_mem_HJ k⟩ : Perm (Fin 12))) := by
    rw [range_fin_eq (fun k => (thetaJ ⟨c6G k, c6G_mem_HJ k⟩ : Perm (Fin 12))),
      range_fin_eq (fun k => (thetaJ ⟨c6G k, c6G_mem_HJ k⟩ : Perm (Fin 12)))]
    congr 2
    simp [natArrs]
  rw [h2, ← h1]
  have hc := natChain_cert
  unfold natChainChecks at hc
  simp only [Bool.and_eq_true] at hc
  rw [card_arrGen_of_chainCheck (by norm_num) (List.nodup_finRange 12) hc.1.2]
  decide

theorem K6_le_S6 :
    K6 ≤ S6 := by
  rw [Subgroup.closure_le]
  rintro _ ⟨s, rfl⟩
  have hs : (s : ℕ) < 10 := by rw [← c6Nat_size]; exact s.2
  refine Subgroup.subset_closure ⟨⟨s, by rw [row6_parts.2.2.2.2.1]; omega⟩, ?_⟩
  show g6 s = c6G s
  exact ite_eq_left hs

theorem CH_t6_eq :
    (Subgroup.centralizer {aJ} ⊓ HJ : Subgroup JH) = K6 ∧ S6 ⊓ HJ = K6 := by
  have h1 : K6 ≤ S6 ⊓ HJ := le_inf K6_le_S6 K6_le_HJ
  have h2 : S6 ⊓ HJ ≤ Subgroup.centralizer {aJ} ⊓ HJ := inf_le_inf_right _ S6_le
  have h3 : Nat.card (Subgroup.centralizer {aJ} ⊓ HJ : Subgroup JH) ≤ Nat.card K6 := by
    rw [card_K6]
    exact card_CH_t6_le
  have e1 : K6 = Subgroup.centralizer {aJ} ⊓ HJ :=
    Subgroup.eq_of_le_of_card_ge (h1.trans h2) h3
  refine ⟨e1.symm, le_antisymm ?_ h1⟩
  rw [e1]
  exact h2

theorem orbit6_ncard_x0 :
    (MulAction.orbit S6 x0).ncard = 7700 := by
  rw [← b6_zero, orbit6_ncard]
  rfl

theorem card_S6 :
    Nat.card S6 = 177408000 := by
  rw [card_eq_orbit_mul, orbit6_ncard_x0, CH_t6_eq.2, card_K6]

theorem CJ_t6_eq :
    S6 = Subgroup.centralizer {aJ} := by
  have hOfix : MulAction.orbit (Subgroup.centralizer {aJ}) x0 ⊆ {x : X | jR aJ • x = x} := by
    rintro _ ⟨g, rfl⟩
    exact fix_jR_smul (comm_of_mem_centralizer g.2) x0_fix_t6
  have hinv := orbit_invariant_of_le S6_le x0
  have hmeet : ∀ {i : ℕ} (hi : i < 2),
      MulAction.orbit (Subgroup.centralizer {aJ}) x0 ∩ MulAction.orbit S6 (b6 i hi) = ∅ ∨
      MulAction.orbit (Subgroup.centralizer {aJ}) x0 ∩ MulAction.orbit S6 (b6 i hi) =
        MulAction.orbit S6 (b6 i hi) := fun hi =>
    inter_eq_empty_or fun ⟨_, hyO, hyS⟩ => orbit_subset_of_invariant hinv hyO hyS
  have h0 : MulAction.orbit (Subgroup.centralizer {aJ}) x0 ∩
      MulAction.orbit S6 (b6 0 (by norm_num)) = MulAction.orbit S6 (b6 0 (by norm_num)) := by
    rcases hmeet (i := 0) (by norm_num) with h | h
    · exfalso
      have hx0 : x0 ∈ MulAction.orbit (Subgroup.centralizer {aJ}) x0 ∩
          MulAction.orbit S6 (b6 0 (by norm_num)) :=
        ⟨MulAction.mem_orbit_self x0, by rw [b6_zero]; exact MulAction.mem_orbit_self x0⟩
      rw [h] at hx0
      exact hx0
    · exact h
  have hcard := ncard_of_two_orbits (hOfix.trans fix_t6_eq.le) disjoint_orbit6 h0
    (hmeet (by norm_num))
  rw [orbit6_ncard, orbit6_ncard] at hcard
  have hC : Nat.card (Subgroup.centralizer {aJ}) =
      (MulAction.orbit (Subgroup.centralizer {aJ}) x0).ncard * 23040 := by
    rw [card_eq_orbit_mul, CH_t6_eq.1, card_K6]
  have hdvd : Nat.card S6 ∣ Nat.card (Subgroup.centralizer {aJ}) := Subgroup.card_dvd_of_le S6_le
  rw [card_S6, hC] at hdvd
  have h7700 : (MulAction.orbit (Subgroup.centralizer {aJ}) x0).ncard = 7700 := by
    simp only [List.getElem!_cons_zero, List.getElem!_cons_succ] at hcard
    rcases hcard with h | h
    · exact h
    · rw [h] at hdvd
      exact absurd hdvd (by decide)
  apply Subgroup.eq_of_le_of_card_ge S6_le
  rw [hC, h7700, card_S6]

theorem card_CJ_t6 :
    Nat.card (Subgroup.centralizer {aJ}) = 177408000 := by
  rw [← CJ_t6_eq, card_S6]

end CFSG.Sporadic.HNOddCore
