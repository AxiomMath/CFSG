module

public import CFSG.Sporadic.HNOddCore.FiveF
public import Certificates.Certificate2085
public import Certificates.Certificate2096
public import Certificates.Certificate2097
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate16041
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv Equiv.Perm

theorem aOrbit_parts : aSm.size = 5 ∧ (∀ k < 5, aSm[k]! = iSm[k]!) ∧
    orbitOK 50 aSm orb1 = true ∧ orb1.size = 1 ∧ orb1[0]! = 0 ∧
    orbitOK 50 aSm orb7 = true ∧ orb7.size = 7 ∧ orb7[0]! = 17 ∧
    orbitOK 50 aSm orb42 = true ∧ orb42.size = 42 ∧ orb42[0]! = 1 ∧
    ∀ i < 50, orb1.contains i = true ∨ orb7.contains i = true ∨ orb42.contains i = true := by
  have h := five_small_parts.2.2.2.1
  unfold aOrbitsOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  refine ⟨h1, fun k hk => by simpa using allBelowN_spec h2 hk, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, fun i hi => ?_⟩
  have := allBelowN_spec h12 hi
  exact or_assoc.1 (by simpa only [Bool.or_eq_true] using this)

theorem hactA :
    ∀ s < aSm.size, ∀ k : Fin FAData.fFixed.toArray.size,
    ∃ h : (aSm[s]!)[(k : ℕ)]! < FAData.fFixed.toArray.size,
      aGenJ s • omList.pt k = omList.pt ⟨(aSm[s]!)[(k : ℕ)]!, h⟩ := by
  intro s hs
  rw [aOrbit_parts.1] at hs
  have e : iGen s = aGenJ s := ite_eq_left hs
  rw [aOrbit_parts.2.1 s hs, ← e]
  exact hactI s (by simp [iSm, iSmall_size]; omega)

theorem closure_aSm_eq :

    Subgroup.closure (Set.range fun s : Fin aSm.size => aGenJ s) = AJ := by
  have hsz : aSm.size = 5 := aOrbit_parts.1
  rw [AJ_eq]
  congr 1
  refine Set.ext fun _ => ⟨?_, ?_⟩
  · rintro ⟨s, rfl⟩
    exact ⟨⟨s, by have := s.2; omega⟩, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨⟨s, by have := s.2; omega⟩, rfl⟩

theorem orbitCertA {L : Array ℕ} (h : orbitOK 50 aSm L = true) :
    orbitCertOK FAData.fFixed.toArray.size aSm L (posArr 50 L) (orbitRecs aSm L (posArr 50 L)).1
      (orbitRecs aSm L (posArr 50 L)).2 = true := by
  rw [fFixed_size]
  exact h

theorem orbit_AJ_of_cert
    {L : Array ℕ} (h : orbitOK 50 aSm L = true) :
    MulAction.orbit AJ (omList.pt ((ptList_of_pointsOK (orbitCertOK_spec (orbitCertA h)).2.1).pt
      ⟨0, (orbitCertOK_spec (orbitCertA h)).1⟩)) =
      omList.pt '' Set.range (ptList_of_pointsOK (orbitCertOK_spec (orbitCertA h)).2.1).pt := by
  have e := orbit_eq_of_cert omList hactA (orbitCertA h)
  dsimp only at e
  rw [closure_aSm_eq] at e
  exact e

theorem omList_pos
    {L : Array ℕ} (hL : PtList FAData.fFixed.toArray.size L) (k : Fin L.size) :
    omList.pt (hL.pt k) = omPt ⟨L[(k : ℕ)]!, by rw [← fFixed_size]; exact hL.lt k k.2⟩ := rfl

theorem mem_orbit_AJ_iff
    {L : Array ℕ} (h : orbitOK 50 aSm L = true) {r : ℕ} (hr : L[0]! = r)
    (hr50 : r < 50) (j : Fin 50) :
    omPt j ∈ MulAction.orbit AJ (omPt ⟨r, hr50⟩) ↔ L.contains (j : ℕ) = true := by
  have hroot : omList.pt ((ptList_of_pointsOK (orbitCertOK_spec (orbitCertA h)).2.1).pt
      ⟨0, (orbitCertOK_spec (orbitCertA h)).1⟩) = omPt ⟨r, hr50⟩ := by
    rw [omList_pos]
    congr 1
    exact Fin.ext hr
  rw [← hroot, orbit_AJ_of_cert h]
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, hk⟩
    rw [omList_pos] at hk
    have e := congrArg Fin.val (omPt_injective hk)
    rw [Array.contains_iff_mem, Array.mem_iff_getElem]
    refine ⟨k, k.2, ?_⟩
    have e' : L[(k : ℕ)]! = (j : ℕ) := e
    rw [getElem!_pos L (k : ℕ) k.2] at e'
    exact e'
  · intro hj
    rw [Array.contains_iff_mem, Array.mem_iff_getElem] at hj
    obtain ⟨k, hk, hkj⟩ := hj
    refine ⟨_, ⟨⟨k, hk⟩, rfl⟩, ?_⟩
    rw [omList_pos]
    congr 1
    apply Fin.ext
    show L[k]! = (j : ℕ)
    rw [getElem!_pos L k hk]
    exact hkj

theorem ncard_orbit_AJ
    {L : Array ℕ} (h : orbitOK 50 aSm L = true) {r : ℕ} (hr : L[0]! = r)
    (hr50 : r < 50) : (MulAction.orbit AJ (omPt ⟨r, hr50⟩)).ncard = L.size := by
  have hroot : omList.pt ((ptList_of_pointsOK (orbitCertOK_spec (orbitCertA h)).2.1).pt
      ⟨0, (orbitCertOK_spec (orbitCertA h)).1⟩) = omPt ⟨r, hr50⟩ := by
    rw [omList_pos]
    congr 1
    exact Fin.ext hr
  rw [← hroot, orbit_AJ_of_cert h, Set.ncard_image_of_injective _ omList.pt_injective,
    Set.ncard_range_of_injective (PtList.pt_injective _), Nat.card_eq_fintype_card,
    Fintype.card_fin]

abbrev orbit7 :
    Set X := MulAction.orbit AJ (omPt 17)

abbrev orbit42 :
    Set X := MulAction.orbit AJ (omPt 1)

theorem mem_orbit7_iff
    (j : Fin 50) : omPt j ∈ orbit7 ↔ orb7.contains (j : ℕ) = true :=
  mem_orbit_AJ_iff aOrbit_parts.2.2.2.2.2.1 aOrbit_parts.2.2.2.2.2.2.2.1 (by norm_num) j

theorem mem_orbit42_iff
    (j : Fin 50) : omPt j ∈ orbit42 ↔ orb42.contains (j : ℕ) = true :=
  mem_orbit_AJ_iff aOrbit_parts.2.2.2.2.2.2.2.2.1 aOrbit_parts.2.2.2.2.2.2.2.2.2.2.1
    (by norm_num) j

theorem mem_orbit1_iff
    (j : Fin 50) :
    omPt j ∈ MulAction.orbit AJ x0 ↔ orb1.contains (j : ℕ) = true := by
  rw [show x0 = omPt ⟨0, by norm_num⟩ from x0_eq_pt0.symm]
  exact mem_orbit_AJ_iff aOrbit_parts.2.2.1 aOrbit_parts.2.2.2.2.1 (by norm_num) j

theorem ncard_orbit7 :
    orbit7.ncard = 7 := by
  show (MulAction.orbit AJ (omPt ⟨17, by norm_num⟩)).ncard = 7
  rw [ncard_orbit_AJ aOrbit_parts.2.2.2.2.2.1 aOrbit_parts.2.2.2.2.2.2.2.1 (by norm_num),
    aOrbit_parts.2.2.2.2.2.2.1]

theorem ncard_orbit42 :
    orbit42.ncard = 42 := by
  show (MulAction.orbit AJ (omPt ⟨1, by norm_num⟩)).ncard = 42
  rw [ncard_orbit_AJ aOrbit_parts.2.2.2.2.2.2.2.2.1 aOrbit_parts.2.2.2.2.2.2.2.2.2.2.1
    (by norm_num), aOrbit_parts.2.2.2.2.2.2.2.2.2.1]

theorem ncard_orbit1 :
    (MulAction.orbit AJ x0).ncard = 1 := by
  rw [show x0 = omPt ⟨0, by norm_num⟩ from x0_eq_pt0.symm,
    ncard_orbit_AJ aOrbit_parts.2.2.1 aOrbit_parts.2.2.2.2.1 (by norm_num),
    aOrbit_parts.2.2.2.1]

theorem orbit_subset_omega
    {p : X} (hp : p ∈ Set.range omPt) :
    MulAction.orbit AJ p ⊆ Set.range omPt := by
  rintro _ ⟨a, rfl⟩
  exact mem_omega_of_comm (IJ_le_CJ (AJ_le_IJ a.2)) hp

theorem omega_eq_union :
    Set.range omPt = MulAction.orbit AJ x0 ∪ orbit7 ∪ orbit42 := by
  apply Set.Subset.antisymm
  · rintro _ ⟨j, rfl⟩
    rcases aOrbit_parts.2.2.2.2.2.2.2.2.2.2.2 j j.2 with h | h | h
    · exact Or.inl (Or.inl ((mem_orbit1_iff j).2 h))
    · exact Or.inl (Or.inr ((mem_orbit7_iff j).2 h))
    · exact Or.inr ((mem_orbit42_iff j).2 h)
  · rintro x ((hx | hx) | hx)
    · exact orbit_subset_omega ⟨⟨0, by norm_num⟩, x0_eq_pt0⟩ hx
    · exact orbit_subset_omega ⟨17, rfl⟩ hx
    · exact orbit_subset_omega ⟨1, rfl⟩ hx

@[expose] def gammaAdj (i j : Fin 50) : Prop := (j : ℕ) ∈ FAData.gamma[(i : ℕ)]!

instance (i j : Fin 50) : Decidable (gammaAdj i j) := by
  unfold gammaAdj
  infer_instance

theorem gamma_parts : FAData.gamma.size = 50 ∧
    (∀ i < 50, (FAData.gamma[i]!).length = 7 ∧ (FAData.gamma[i]!).Nodup ∧
      ∀ j ∈ FAData.gamma[i]!, j < 50 ∧ j ≠ i ∧ i ∈ FAData.gamma[j]!) ∧
    (∀ i < 50, orb42.contains i = true →
      (FAData.gamma[i]!).countP (fun j => orb7.contains j) = 1) ∧
    (∀ j < 50, orb7.contains j = true →
      (List.range 50).countP (fun i => orb42.contains i && (FAData.gamma[i]!).contains j) = 6) := by
  have h := five_small_parts.2.2.2.2.2.1
  unfold gammaOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, fun i hi => ?_, fun i hi hO => ?_, fun j hj hO => ?_⟩
  · have := allBelowN_spec h2 hi
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, bne_iff_ne,
      ne_eq, List.contains_iff_mem] at this
    obtain ⟨⟨hl, hn⟩, ha⟩ := this
    exact ⟨hl, hn, fun j hj => ⟨(ha j hj).1.1, (ha j hj).1.2, (ha j hj).2⟩⟩
  · have := allBelowN_spec h3 hi
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at this
    rcases this with h | h
    · rw [hO] at h
      exact absurd h (by decide)
    · exact h
  · have := allBelowN_spec h4 hj
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at this
    rcases this with h | h
    · rw [hO] at h
      exact absurd h (by decide)
    · exact h

theorem gamma_loopless (i : Fin 50) : ¬ gammaAdj i i := fun h =>
  ((gamma_parts.2.1 i i.2).2.2 i h).2.1 rfl

theorem gamma_symm
    {i j : Fin 50} (h : gammaAdj i j) : gammaAdj j i :=
  ((gamma_parts.2.1 i i.2).2.2 j h).2.2

theorem card_filter_fin_mem (L : List ℕ) (hL : L.Nodup) (hlt : ∀ j ∈ L, j < 50) :
    Nat.card {j : Fin 50 // (j : ℕ) ∈ L} = L.length := by
  rw [← List.toFinset_card_of_nodup hL, Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_filter] at hj
    exact List.mem_toFinset.2 hj.2
  · intro a _ b _ hab
    exact Fin.ext hab
  · intro j hj
    rw [List.mem_toFinset] at hj
    exact ⟨⟨j, hlt j hj⟩, by simpa using hj, rfl⟩

theorem gamma_regular
    (i : Fin 50) : Nat.card {j : Fin 50 // gammaAdj i j} = 7 := by
  obtain ⟨hl, hn, ha⟩ := gamma_parts.2.1 i i.2
  rw [← hl]
  exact card_filter_fin_mem _ hn fun j hj => (ha j hj).1

theorem gamma_unique_nbr
    (i : Fin 50) (hi : omPt i ∈ orbit42) :
    ∃! j : Fin 50, gammaAdj i j ∧ omPt j ∈ orbit7 := by
  rw [mem_orbit42_iff] at hi
  have hc := gamma_parts.2.2.1 i i.2 hi
  obtain ⟨hl, hn, ha⟩ := gamma_parts.2.1 i i.2
  have hcard : ((FAData.gamma[(i : ℕ)]!).filter fun j => orb7.contains j).length = 1 := by
    rw [← List.countP_eq_length_filter]
    exact hc
  obtain ⟨j0, hj0⟩ := List.length_eq_one_iff.1 hcard
  have hmem : j0 ∈ (FAData.gamma[(i : ℕ)]!).filter fun j => orb7.contains j := by
    rw [hj0]; exact List.mem_singleton_self _
  rw [List.mem_filter] at hmem
  refine ⟨⟨j0, (ha j0 hmem.1).1⟩, ⟨hmem.1, (mem_orbit7_iff _).2 hmem.2⟩, ?_⟩
  rintro ⟨j, hj50⟩ ⟨hadj, h7⟩
  rw [mem_orbit7_iff] at h7
  have hj : j ∈ (FAData.gamma[(i : ℕ)]!).filter fun j => orb7.contains j :=
    List.mem_filter.2 ⟨hadj, h7⟩
  rw [hj0, List.mem_singleton] at hj
  exact Fin.ext hj

theorem card_fin_countP (p : ℕ → Bool) :
    Nat.card {c : Fin 50 // p c = true} = (List.range 50).countP p := by
  have h := card_filter_range_eq_countP' 50 (fun k => p k = true)
  simp only [Bool.decide_eq_true] at h
  rw [← h, Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine Finset.card_bij (fun k _ => k.val) ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_filter] at hk ⊢
    exact ⟨Finset.mem_range.2 k.2, by simpa using hk.2⟩
  · intro a _ b _ hab
    exact Fin.ext hab
  · intro i hi
    rw [Finset.mem_filter, Finset.mem_range] at hi
    exact ⟨⟨i, hi.1⟩, by simpa using hi.2, rfl⟩

theorem gamma_fiber
    (j : Fin 50) (hj : omPt j ∈ orbit7) :
    Nat.card {i : Fin 50 // omPt i ∈ orbit42 ∧ gammaAdj i j} = 6 := by
  rw [mem_orbit7_iff] at hj
  rw [← gamma_parts.2.2.2 j j.2 hj, ← card_fin_countP]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun i => ?_)
  rw [mem_orbit42_iff, Bool.and_eq_true, List.contains_iff_mem]
  rfl

end CFSG.Sporadic.HNOddCore
