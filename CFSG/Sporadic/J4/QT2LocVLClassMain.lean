module

public import CFSG.Sporadic.J4.QT2LocVLRep
public import CFSG.Sporadic.J4.QT2LocVLClassCheck

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A Matrix

theorem mem_vlAll_of_mem
    {A : Array (Array V2)} (h : A ∈ vlAll) : ∃ g < 149, vlAll[g]! = A := by
  obtain ⟨i, hi, e⟩ := Array.mem_iff_getElem.1 h
  have hsz : vlAll.size = 149 := vlAll_size_eq
  refine ⟨i, by omega, ?_⟩
  rw [getElem!_pos vlAll i (by exact hi)]
  exact e

theorem etaE_mem_line {S : List ℕ} (hS : S ∈ lines17) :
    (S.map etaE).toArray ∈ vlAll := by
  unfold vlAll
  rw [List.mem_toArray]
  exact List.mem_append_left _ (List.mem_map.2 ⟨S, hS, rfl⟩)

theorem mem_lift {G : List (Array V2)} (hG : G ∈ vlGroups) : G.toArray ∈ vlAll := by
  unfold vlAll
  rw [List.mem_toArray]
  exact List.mem_append_right _ (List.mem_map.2 ⟨G, hG, rfl⟩)

theorem vlClass_data {g : ℕ} (hg : g < 149) :
    ∃ r ∈ vlRepIdx, ∃ c < 6720, vlConjEq r g c = true ∧
      eqRows (mulRows vlCx[c]! vlCxInv[c]!) idRows = true :=
  vlClass_wit g hg

theorem vlCx_elt
    (hM : MatFacts) {c : ℕ} (hc : c < 6720)
    (h31 : eqRows (mulRows vlCx[c]! vlCxInv[c]!) idRows = true) :
    ∃ x : J, Mx x = rowsMatrix vlCx[c]! ∧ Mx x⁻¹ = rowsMatrix vlCxInv[c]! := by
  obtain ⟨x, -, hx⟩ := mem_X0Sub_of_lt hM c hc
  have e1 : Mx x * rowsMatrix vlCxInv[c]! = 1 := by
    have := eqRows_iff.1 h31
    have h' := congrArg rowsMatrix this
    rw [rowsMatrix_mulRows, rowsMatrix_idRows] at h'
    rw [hx]
    exact h'
  refine ⟨x, hx, ?_⟩
  calc Mx x⁻¹ = Mx x⁻¹ * (Mx x * rowsMatrix vlCxInv[c]!) := by rw [e1, mul_one]
    _ = (Mx x⁻¹ * Mx x) * rowsMatrix vlCxInv[c]! := by rw [mul_assoc]
    _ = rowsMatrix vlCxInv[c]! := by rw [← map_mul, inv_mul_cancel, map_one, one_mul]

theorem vlAll_size {g : ℕ} (hg : g < 149) : vlAll[g]!.size ≤ 16 :=
  (vlAll_sizes g hg).le

theorem vlRepIdx_length : vlRepIdx.length = 10 := by
  unfold vlRepIdx vlPref
  simp [vlNamedGs]

theorem vlNamedGs_length : vlNamedGs.length = 10 := by
  simp [vlNamedGs]

theorem chkNamed_k {k : ℕ} (hk : k < 10) :
    VrClosed (vlAll[vlRepIdx[k]!]!) ∧ (vlAll[vlRepIdx[k]!]!).size = 16 ∧
      (∀ i < 4, wfRows (vlNamedGs[k]!)[i]! = true ∧
        ∃ K ∈ vlAll[vlRepIdx[k]!]!, eqRows (vlNamedGs[k]!)[i]! K = true) ∧
      (∀ m < 16, ∃ K ∈ vlAll[vlRepIdx[k]!]!, eqRows (vlSubsetProd (vlNamedGs[k]!) m) K = true) ∧
      (∀ m < 16, ∀ m' < 16, eqRows (vlSubsetProd (vlNamedGs[k]!) m)
        (vlSubsetProd (vlNamedGs[k]!) m') = true → m = m') := by
  have h := chkNamed_true
  unfold chkNamed at h
  rw [Bool.and_eq_true] at h
  have h2 := h.2
  rw [List.all_eq_true] at h2
  have hk1 : k < vlRepIdx.length := by rw [vlRepIdx_length]; exact hk
  have hk2 : k < vlNamedGs.length := by rw [vlNamedGs_length]; exact hk
  have hmem : (vlRepIdx[k]!, vlNamedGs[k]!) ∈ List.zip vlRepIdx vlNamedGs := by
    rw [getElem!_pos vlRepIdx k (by exact hk1), getElem!_pos vlNamedGs k (by exact hk2),
      List.mem_iff_getElem]
    exact ⟨k, by simp [hk1, hk2], by simp⟩
  have h3 := h2 _ hmem
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Array.any_eq_true'] at h3
  obtain ⟨⟨⟨⟨hc, hs⟩, hg⟩, hm⟩, hd⟩ := h3
  refine ⟨VrClosed.of_check hc, by simpa using hs, fun i hi => ?_, fun m hm' => ?_,
    fun m hm' m' hm'' he => ?_⟩
  · obtain ⟨h1, K, hK, hk'⟩ := hg i hi
    exact ⟨h1, K, hK, hk'⟩
  · obtain ⟨K, hK, hk'⟩ := hm m hm'
    exact ⟨K, hK, hk'⟩
  · have := hd m hm' m' hm''
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at this
    rcases this with h | h
    · rw [he] at h
      exact absurd h (by simp)
    · exact h

theorem image_getD_eq (l : List J) (hl : l.length = 4) :
    (fun i => l.getD i 1) '' {i | i < 4} = {x | x ∈ l} := by
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  · intro hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    exact ⟨i, by omega, by rw [List.getD_eq_getElem _ _ hi]⟩

theorem named_facts
    {k : ℕ} (hk : k < 10) (gens : List J) (hlen : gens.length = 4)
    (hgs : ∀ i < 4, Mx (gens.getD i 1) = rowsMatrix (vlNamedGs[k]!)[i]!) :
    Nat.card (Subgroup.closure {x | x ∈ gens}) = 16 ∧
      ∀ u ∈ Subgroup.closure {x | x ∈ gens}, ∃ M ∈ vlAll[vlRepIdx[k]!]!, Mx u = rowsMatrix M := by
  obtain ⟨hcl, hsz, hg, -, hd⟩ := chkNamed_k hk
  have hA : (vlAll[vlRepIdx[k]!]!).size ≤ 16 := by omega
  obtain ⟨hcard, hle⟩ := closure_card hcl hA (fun i => gens.getD i 1) (vlNamedGs[k]!) hgs
    (fun i hi => (hg i hi).1) (fun i hi => (hg i hi).2) hd
  rw [← image_getD_eq gens hlen]
  refine ⟨hcard, fun u hu => ?_⟩
  obtain ⟨M, hM, e⟩ := hle hu
  exact ⟨M, hM, e.symm⟩

theorem hgs_masks (hM : MatFacts) (cs : List ℕ) (hcs : cs.length = 4) {i : ℕ} (hi : i < 4) :
    Mx ((cs.map (eta uJ 11)).getD i 1) = rowsMatrix (gsMasks cs)[i]! := by
  have hi' : i < cs.length := by omega
  rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map]
  have e : (gsMasks cs)[i]! = etaE cs[i] := by
    unfold gsMasks
    rw [getElem!_pos _ i (by simpa using hi')]
    simp
  rw [e]
  exact Mx_eta hM 11 le_rfl _

theorem hgs_words (hM : MatFacts) (ws : List (List ℤ)) (hws : ws.length = 4) {i : ℕ}
    (hi : i < 4) : Mx ((ws.map el5).getD i 1) = rowsMatrix (gsWords ws)[i]! := by
  have hi' : i < ws.length := by omega
  rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map]
  have e : (gsWords ws)[i]! = wR ws[i] := by
    unfold gsWords
    rw [getElem!_pos _ i (by simpa using hi')]
    simp
  rw [e]
  exact QT2A.Mx_el5 hM _

end CFSG.Sporadic.J4.QT2
