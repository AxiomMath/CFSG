module

public import Certificates.Kernel.Co2Smith.F0
public import Certificates.Kernel.Co2Smith.Cox
public import Certificates.Kernel.Co2Smith.D1K
public import Certificates.Kernel.Co2Smith.D1KT0
public import Certificates.Kernel.Co2Smith.D1KT1
public import Certificates.Kernel.Co2Smith.D1KT2
import CFSG.Certificates.Kernel.Common.ForallChunks

public section

set_option maxRecDepth 400000
set_option exponentiation.threshold 600

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith
open CFSG.Sporadic.Co2Smith.Native CFSG.Sporadic.SmallF2.Native

theorem eWords_k : ((List.range 4).all fun j => (d1EWords.getD j []).all (· < 22)) = true := by
  decide

theorem eWords_lt (j : Nat) : ∀ k ∈ d1EWords.getD j [], k < 22 := by
  by_cases hj : j < 3
  · have h := eWords_k
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    exact h j (by omega)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [d1EWords]; omega)]
    simp

theorem inv_lt {w : List Nat} (hw : ∀ k ∈ w, k < 22) : ∀ k ∈ d1Inv w, k < 22 := by
  intro k hk
  simp only [d1Inv, List.mem_flatMap, List.mem_reverse, List.mem_replicate] at hk
  obtain ⟨a, ha, -, rfl⟩ := hk
  exact hw _ ha

theorem markWords_k : ((List.range 6).all fun g => (d1MarkWords.getD g []).all (· < 22)) = true := by
  decide

theorem markWords_lt (g : Nat) : ∀ k ∈ d1MarkWords.getD g [], k < 22 := by
  by_cases hg : g < 5
  · have h := markWords_k
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    exact h g (by omega)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [d1MarkWords]; omega)]
    simp

theorem d1ER_eq (j : Nat) : d1ER j = unpackR 22 (d1eK j) := glR_eq (eWords_lt j)

theorem d1EIR_eq (j : Nat) : d1EIR j = unpackR 22 (d1eiK j) := glR_eq (inv_lt (eWords_lt j))

theorem mark_eq (g : Nat) : glR (d1MarkWords.getD g []) = unpackR 22 (wK LP (d1MarkWords.getD g [])) :=
  glR_eq (markWords_lt g)

theorem d1G_eq (j : Nat) : d1G j = unpackR 22 (d1gK j) := by
  unfold d1G d1gK
  split_ifs <;> simp only [d1ER_eq, d1EIR_eq]

theorem d1GI_eq (j : Nat) : d1GI j = unpackR 22 (d1giK j) := by
  unfold d1GI d1giK
  split_ifs <;> simp only [d1ER_eq, d1EIR_eq]

theorem getD_unpack (l : List Nat) (i : Nat) :
    (l.map (unpackR 22)).toArray.getD i (idRows 22) = unpackR 22 (l.getD i IDP) := by
  rw [idRows_eq, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getD_eq_getElem?_getD]
  cases l[i]? <;> rfl

theorem step_eq (ent : List Nat) (s : Nat × Nat × Nat) :
    d1Step (ent.map (unpackR 22)).toArray s = ((d1stepK ent s).map (unpackR 22)).toArray := by
  unfold d1Step d1stepK
  split_ifs <;>
    simp only [getD_unpack, d1G_eq, d1GI_eq, mulRows_unpack, List.push_toArray, List.map_append,
      List.map_cons, List.map_nil]

theorem run_eq (start : List Nat) (l : List (Nat × Nat × Nat)) :
    d1Run (start.map (unpackR 22)).toArray l = ((d1runK start l).map (unpackR 22)).toArray := by
  unfold d1Run d1runK
  induction l generalizing start with
  | nil => rfl
  | cons s l ih => rw [List.foldl_cons, List.foldl_cons, step_eq, ih]

theorem eqK_comm (A B : Nat) : eqK A B = eqK B A := by
  unfold eqK
  apply Bool.eq_iff_iff.2
  rw [Nat.beq_eq, Nat.beq_eq]
  exact eq_comm

theorem contains_arr (l : List Nat) (x : Nat) :
    (l.map (unpackR 22)).toArray.contains (unpackR 22 x) = d1In l x := by
  rw [List.contains_toArray]
  unfold d1In
  induction l with
  | nil => rfl
  | cons y l ih =>
    rw [List.map_cons, List.contains_cons, ih, List.any_cons, beq_unpack, eqK_comm]

theorem contains_list (l : List Nat) (x : Nat) :
    (l.map (unpackR 22)).contains (unpackR 22 x) = d1In l x := by
  rw [← contains_arr, List.contains_toArray]

theorem qRows_eq (e : Nat) : glQRows e = unpackR 22 (d1qK e) := glQRows_eq e

theorem QD_eq : d1QD = d1QK := by
  unfold d1QD d1QK
  apply List.filter_congr
  intro e _
  rw [qRows_eq, (frame_eqs).2.2.2.2.2.1, commRows_unpack]

theorem X0_eq : d1X0R = d1X0K.map (unpackR 22) := by
  unfold d1X0R d1X0K
  rw [List.map_map]
  apply List.map_congr_left
  intro t _
  exact glRootRows_eq 0 t

theorem B8_eq : d1B8R = d1B8K.map (unpackR 22) := by
  have e : (d1X0K.map (unpackR 22)).map (mulRows 22 glX25) =
      (d1X0K.map (mulV x25K)).map (unpackR 22) := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro t _
    rw [Function.comp_apply, Function.comp_apply, (frame_eqs).2.2.2.2.2.1, mulRows_unpack]
  unfold d1B8R d1B8K
  rw [X0_eq, e, List.map_append]

theorem Tgt_eq : d1Tgt = d1TgtK.map (unpackR 22) := by
  simp only [d1Tgt, d1TgtK, glRootRows_eq, List.map_cons, List.map_nil]

theorem FR_eq (e : Nat) : d1FR e = unpackR 22 (d1fK e) := by
  rw [d1FR, qRows_eq, (el_eqs).2.2.1, glConj_unpack]
  rfl

theorem d1Elt_eq : d1EltOK = d1EltK := by
  unfold d1EltOK d1EltK glF0Valid glFixZ
  rw [QD_eq]
  simp only [glZ_eq, subId_zK, (frame_eqs).2.2.2.2.2.1, mulRows_unpack, validM_unpack,
    Bool.true_and, beq_unpack, d1ER_eq, d1EIR_eq, commRows_unpack, idRows_eq, mark_eq]
  rfl

theorem d1Lam1_eq : d1Lam1OK = d1Lam1K := by
  unfold d1Lam1OK d1Lam1K
  rw [QD_eq]
  apply all_congr_mem
  intro i _
  rw [X0_eq, qRows_eq, contains_list, glZ_eq,
    show #[unpackR 22 (d1qK (d1QK.getD i 0))] = ([d1qK (d1QK.getD i 0)].map (unpackR 22)).toArray
      from rfl, run_eq, contains_arr]
  rfl

theorem d1Lam2_eq : d1Lam2OK = d1Lam2K := by
  unfold d1Lam2OK d1Lam2K
  rw [QD_eq]
  apply all_congr_mem
  intro i _
  rw [B8_eq, FR_eq, contains_list, (frame_eqs).2.2.2.2.2.1,
    show #[unpackR 22 (d1fK (d1QK.getD i 0)), unpackR 22 x25K] =
      ([d1fK (d1QK.getD i 0), x25K].map (unpackR 22)).toArray from rfl, run_eq, Tgt_eq,
    List.all_map]
  congr 1
  apply all_congr_mem
  intro t _
  exact contains_arr _ t

theorem decR_eq (c : Nat) : d1DecR c = unpackR 22 (d1decK c) := by
  unfold d1DecR d1decK
  rw [glRootRows_eq, glRootRows_eq, glRootRows_eq]
  split_ifs
  · rw [(frame_eqs).2.2.2.2.2.1, mulRows_unpack, mulRows_unpack, mulRows_unpack]
  · rw [idRows_eq, mulRows_unpack, mulRows_unpack, mulRows_unpack]

theorem d1Dec_eq : d1DecOK = d1DecK := by
  unfold d1DecOK d1DecK
  rw [QD_eq]
  simp only [decR_eq, FR_eq, beq_unpack]

theorem PR_eq (p : List Nat) : d1PR p = unpackR 22 (d1pK p) := by
  unfold d1PR d1pK
  rw [idRows_eq]
  generalize IDP = a
  induction p generalizing a with
  | nil => rfl
  | cons j p ih => rw [List.foldl_cons, List.foldl_cons, d1ER_eq, mulRows_unpack, ih]

theorem PIR_eq (p : List Nat) : d1PIR p = unpackR 22 (d1piK p) := by
  unfold d1PIR d1piK
  rw [idRows_eq]
  generalize IDP = a
  generalize p.reverse = q
  induction q generalizing a with
  | nil => rfl
  | cons j p ih => rw [List.foldl_cons, List.foldl_cons, d1EIR_eq, mulRows_unpack, ih]

theorem q4_eq (j : Nat) : d1Q4 j = unpackR 22 (d1q4K j) := glRootRows_eq _ _

theorem UNode_eq (p : List Nat) :
    d1UNode (d1PR p) (d1PIR p) = ((d1uK p).map (unpackR 22)).toArray := by
  unfold d1UNode d1uK
  rw [PR_eq, PIR_eq]
  apply Array.ext
  · simp
  · intro j h1 h2
    simp [q4_eq, mulRows_unpack]

theorem U_get {i j : Nat} (hi : i < 576) (hj : j < 4) (hs : d1Tree.size = 576) :
    (d1U.getD i #[]).getD j #[] = unpackR 22 ((d1UL.getD i []).getD j IDP) := by
  have hi' : i < d1Tree.size := by rw [hs]; exact hi
  have hl : i < d1UL.length := by simpa [d1UL] using hi'
  have h1 : d1U.getD i #[] = d1UNode (d1PR d1Tree[i]) (d1PIR d1Tree[i]) := by
    unfold d1U
    simp [Array.getD_eq_getD_getElem?, hi']
    try rfl
  rw [h1, UNode_eq, List.getD_eq_getElem _ _ hl]
  have hu : d1UL[i] = d1uK d1Tree[i] := by
    simp [d1UL]
    try rfl
  rw [hu]
  have hjl : j < (d1uK d1Tree[i]).length := by simp [d1uK, hj]
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_eq_getElem hjl, List.getD_eq_getElem _ _ hjl]
  rfl

theorem take_all {α : Type} (l : List α) (d : α) (f : α → Bool) {i : Nat} (hi : i ≤ l.length) :
    ((List.range i).all fun k => f (l.getD k d)) = (l.take i).all f := by
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true, List.mem_range]
  constructor
  · intro h x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
    have hk' : k < i := by simp at hk; omega
    have := h k hk'
    rwa [List.getD_eq_getElem _ _ (by omega), ← List.getElem_take (h := hk)] at this
  · intro h k hk
    rw [List.getD_eq_getElem _ _ (by omega)]
    have hk2 : k < (l.take i).length := by simp; omega
    have := h _ (List.getElem_mem hk2)
    rwa [List.getElem_take] at this

theorem UL_length : d1UL.length = d1Tree.size := by simp [d1UL]

theorem d1Tree_eq (hs : d1Tree.size = 576) (hrow : ∀ i < 576, d1TreeRow i = true) :
    d1TreeOK = true := by
  have h1 : (d1X0R.all validM) = true := by
    rw [X0_eq, List.all_eq_true]
    intro x hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    exact validM_unpack _
  have h2 : ((List.range 576).all fun i => (List.range 4).all fun j =>
      validM ((d1U.getD i #[]).getD j #[])) = true := by
    rw [List.all_eq_true]
    intro i hi
    rw [List.all_eq_true]
    intro j hj
    rw [List.mem_range] at hi hj
    rw [U_get hi hj hs]
    exact validM_unpack _
  unfold d1TreeOK d1TreeChk
  rw [hs, h1, h2]
  simp only [beq_self_eq_true, Bool.true_and]
  · rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range] at hi
    have h := hrow i hi
    unfold d1TreeRow at h
    rw [← take_all d1UL [] _ (by rw [UL_length, hs]; omega)] at h
    rw [← h]
    apply all_congr_mem
    intro k hk
    rw [List.mem_range] at hk
    unfold d1Sep
    apply Bool.eq_iff_iff.2
    simp only [List.any_eq_true, List.mem_range, Bool.not_eq_true']
    refine exists_congr fun j => and_congr_right fun hj => ?_
    rw [U_get hi hj hs, U_get (by omega) hj hs, mulRows_unpack, X0_eq, contains_list]

theorem orbWords_lt (h : (d1Orb.toList.all fun p => p.all (· < 22)) = true) {p : List Nat}
    (hp : p ∈ d1Orb.toList) : ∀ k ∈ p, k < 22 := by
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h p hp

theorem OR_eq {p : List Nat} (hp : ∀ k ∈ p, k < 22) : d1OR p = unpackR 22 (d1oK p) := by
  unfold d1OR d1oK
  rw [glR_eq hp, glR_eq (inv_lt hp), (frame_eqs).2.2.2.2.2.1, mulRows_unpack, mulRows_unpack,
    cK_eq, unpack_mod]

theorem d1Nodup_iff : ∀ l : List Nat, d1Nodup l = true ↔ l.Nodup
  | [] => by simp [d1Nodup]
  | x :: l => by
    rw [d1Nodup, Bool.and_eq_true, d1Nodup_iff l, List.nodup_cons, List.all_eq_true]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun hx => ?_, h2⟩
      have := h1 x hx
      simp at this
    · rintro ⟨h1, h2⟩
      refine ⟨fun y hy => ?_, h2⟩
      have hne : y ≠ x := fun e => h1 (e ▸ hy)
      cases e : Nat.beq y x
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) hne

theorem d1Orb_eq (hw : (d1Orb.toList.all fun p => p.all (· < 22)) = true) (h : d1OrbK = true) :
    d1OrbOK = true := by
  unfold d1OrbK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hs, hm⟩, hn⟩ := h
  have hs' : d1Orb.size = 1260 := by simpa using hs
  unfold d1OrbOK
  simp only [Bool.and_eq_true]
  have hORA : d1ORA = (d1Orb.toList.map fun p => unpackR 22 (d1oK p)).toArray := by
    unfold d1ORA
    apply Array.ext
    · simp
    · intro i h1 h2
      simp only [Array.getElem_map, List.getElem_toArray, List.getElem_map]
      exact OR_eq (orbWords_lt hw (List.getElem_mem (by simpa using h1)))
  refine ⟨⟨⟨hs, ?_⟩, ?_⟩, ?_⟩
  · rw [← Array.all_toList]
    rw [← hm]
    apply all_congr_mem
    intro p hp
    rw [glR_eq (orbWords_lt hw hp), glR_eq (inv_lt (orbWords_lt hw hp)), mulRows_unpack, idRows_eq,
      beq_unpack]
  · rw [hORA, ← Array.all_toList, List.toList_toArray, List.all_map, List.all_eq_true]
    intro p _
    rw [Function.comp_apply]
    exact validM_unpack _
  · rw [List.all_eq_true]
    intro i hi
    rw [List.all_eq_true]
    intro k hk
    rw [List.mem_range] at hi hk
    have hnd := (d1Nodup_iff _).1 hn
    have hl : (d1Orb.toList.map d1oK).length = 1260 := by simp [hs']
    have hi' : i < d1Orb.toList.length := by simp [hs']; omega
    have hk' : k < d1Orb.toList.length := by simp [hs']; omega
    have gi : ∀ m (hm : m < d1Orb.toList.length),
        d1ORA.getD m #[] = unpackR 22 (d1oK d1Orb.toList[m]) := by
      intro m hm
      rw [hORA, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
        List.getElem?_eq_getElem hm]
      rfl
    rw [gi i hi', gi k hk', bne_unpack]
    have hne : d1oK d1Orb.toList[i] ≠ d1oK d1Orb.toList[k] := by
      intro e
      have h3 : (d1Orb.toList.map d1oK)[i]'(by rw [hl]; omega) =
          (d1Orb.toList.map d1oK)[k]'(by rw [hl]; omega) := by
        simpa using e
      have := (List.Nodup.getElem_inj_iff hnd).1 h3
      omega
    have hc : ∀ p, cK (d1oK p) = d1oK p := fun p => by simp [d1oK, cK_eq, Nat.mod_mod]
    cases e : eqK (d1oK d1Orb.toList[i]) (d1oK d1Orb.toList[k])
    · rfl
    · unfold eqK at e
      rw [hc, hc] at e
      exact absurd (Nat.eq_of_beq_eq_true e) hne

theorem prod_eq (l : List Nat) : d1Prod (l.map (unpackR 22)) = unpackR 22 (l.foldl mulV IDP) := by
  unfold d1Prod
  rw [idRows_eq]
  generalize IDP = a
  induction l generalizing a with
  | nil => rfl
  | cons x l ih => rw [List.map_cons, List.foldl_cons, List.foldl_cons, mulRows_unpack, ih]

theorem phi_eq (s q : Nat) : d1Phi (unpackR 22 s) (unpackR 22 q) = unpackR 22 (d1phiK s q) := by
  unfold d1Phi d1phiK
  rw [glAl_eq, ← prod_eq]
  rfl

theorem inX_eq (r R : Nat) : d1InX r (unpackR 22 R) = d1InXK r R := by
  unfold d1InX d1InXK
  simp only [glRootRows_eq, beq_unpack]

theorem d1Phi_eq : d1PhiOK = d1PhiK := by
  unfold d1PhiOK d1PhiK
  rw [QD_eq]
  simp only [qRows_eq, FR_eq, (frame_eqs).2.2.2.2.1, (frame_eqs).2.2.2.2.2.2.1, phi_eq, inX_eq,
    glRootRows_eq, beq_unpack]

theorem d1Root_eq : d1RootOK = d1RootK := by
  unfold d1RootOK d1RootK
  simp only [glRootRows_eq, validM_unpack, Bool.true_and, bne_unpack, glZ_eq, commRows_unpack,
    Bool.and_true]
  rfl

theorem bg_eq (g : Nat) : d1BG g = unpackR 22 (d1bgK g) := by
  unfold d1BG d1bgK
  split_ifs
  · exact mark_eq g
  · exact glAl_eq
  · exact glRootRows_eq _ _

theorem bt_eq (ν : List Nat) (g : Nat) : d1BT ν g = unpackR 22 (d1btK ν g) := by
  unfold d1BT d1btK
  split_ifs
  · exact bg_eq g
  · exact glRootRows_eq _ _

theorem wr_eq (F : Nat → Array Nat) (G : Nat → Nat) (hF : ∀ g, F g = unpackR 22 (G g))
    (w : List Nat) : d1WR F w = unpackR 22 (d1wK G w) := by
  unfold d1WR d1wK
  rw [idRows_eq]
  generalize IDP = a
  induction w generalizing a with
  | nil => rfl
  | cons g w ih => rw [List.foldl_cons, List.foldl_cons, hF, mulRows_unpack, ih]

theorem d1Break_eq : d1BreakOK = d1BreakK := by
  unfold d1BreakOK d1BreakK
  simp only [wr_eq d1BG d1bgK bg_eq, wr_eq (d1BT _) (d1btK _) (bt_eq _), beq_unpack, bne_unpack,
    validM_unpack, Bool.and_true]

#kc_forall_chunks d1Tree_all (fun k => d1TreeBlk k = true) 18 CertificateChecks.KernelCo2Smith.d1TreeBlk 1

theorem d1_ok : d1OK = true := by
  have hrow : ∀ i < 576, d1TreeRow i = true := by
    intro i hi
    have h := d1Tree_all (i / 32) (show i / 32 < 18 by omega)
    unfold d1TreeBlk at h
    rw [List.all_eq_true] at h
    have := h (i % 32) (List.mem_range.2 (Nat.mod_lt _ (by norm_num)))
    rwa [show 32 * (i / 32) + i % 32 = i by omega] at this
  have hs : d1Tree.size = 576 := by simpa [d1TreeK] using d1Tree_k
  unfold d1OK
  rw [d1Elt_eq, d1Lam1_eq, d1Lam2_eq, d1Dec_eq, d1Tree_eq hs hrow, d1Orb_eq d1OrbW_k d1Orb_k,
    d1Phi_eq, d1Root_eq, d1Break_eq, d1Elt_k, d1Lam1_k, d1Lam2_k, d1Dec_k, d1Phi_k, d1Root_k,
    d1Break_k]
  rfl

end CertificateChecks.KernelCo2Smith
