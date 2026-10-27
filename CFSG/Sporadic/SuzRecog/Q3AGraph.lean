module

public import CFSG.Sporadic.SuzRecog.Q3AGraphBase

public import Certificates.Certificate15088

public noncomputable section

namespace CFSG.Sporadic.SuzRecog.Q3A

open Subgroup CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native Check
  CFSG.Sporadic.SuzRecog.LevelTwoData

section Check

theorem q3a_parts : vertOK = true ∧ forestOK = true ∧ nbrOrbOK = true ∧ distOK = true ∧
    spanOK = true ∧ q2OK = true ∧ layer3OK = true := by
  have h : q3aOK = true := Certificates.certificate15088
  simpa only [q3aOK, Bool.and_eq_true, and_assoc] using h

theorem distOK_true : distOK = true := q3a_parts.2.2.2.1

theorem spanOK_true : spanOK = true := q3a_parts.2.2.2.2.1

theorem q2OK_true : q2OK = true := q3a_parts.2.2.2.2.2.1

theorem layer3OK_true : layer3OK = true := q3a_parts.2.2.2.2.2.2

theorem vert_parts :
    isInvA 1782 rhoArr rhoInv = true ∧ fix0.size = 162 ∧
      eqA 1782 (compA 1782 rhoArr (compA 1782 rhoArr rhoArr)) (idA 1782) = true ∧
      (∀ s < 2, isInvA 1782 (bA s) (bAi s) = true) ∧ fimg.size = 22880 ∧ tpar.size = 22880 ∧
      tlab.size = 22880 ∧ fimg[0]! = fix0 ∧
      ∀ i < 22880, keyIdx (keyOf fimg[i]!) = i ∧
        (i = 0 ∨ tpar[i]! < i ∧ tlab[i]! < 2 ∧ fimg[i]! = imgA (bA tlab[i]!) fimg[tpar[i]!]!) := by
  have h := q3a_parts.1
  unfold vertOK at h
  simpa only [Bool.and_eq_true, beq_iff_eq, allLt_iff, Bool.or_eq_true, decide_eq_true_eq,
    and_assoc] using h

theorem tlab_lt {i : ℕ} (hi : 0 < i) (hp : tpar[i]! < i) : tlab[i]! < 2 := by
  by_cases h : i < 22880
  · rcases (vert_parts.2.2.2.2.2.2.2.2 i h).2 with rfl | h'
    · omega
    · exact h'.2.1
  · have hs : tlab.size = 22880 := vert_parts.2.2.2.2.2.2.1
    rw [getElem!_neg tlab i (by omega)]
    exact Nat.zero_lt_two

theorem key_table {i : ℕ} (hi : i < 22880) : keyIdx (keyOf fimg[i]!) = i :=
  (vert_parts.2.2.2.2.2.2.2.2 i hi).1

theorem rep_rho : Rep 1782 rhoArr Model.rho1 := (rep_permC vert_parts.1).1

theorem rho1_pow_three : Model.rho1 ^ 3 = 1 := by
  have := eq_of_eqA (rep_compA rep_rho (rep_compA rep_rho rep_rho)) rep_idA vert_parts.2.2.1
  rw [pow_succ, pow_two, mul_assoc]
  exact this

theorem isFixList_v0 : IsFixList v0 fix0 := by
  refine ⟨?_, fun y hy => ((mem_fix0_iff y).1 hy).1, fun p => ?_⟩
  · unfold fix0
    rw [Array.toList_filter, Array.toList_range]
    exact (List.nodup_range).filter _
  · rw [fixSet_zpowers (x := v0) (q := Model.rho1) rfl, Set.mem_ofPred_eq, mem_fix0_iff,
      rep_rho.apply p.2]
    constructor
    · intro h
      exact ⟨p.2, by rw [show (⟨(p : ℕ), p.2⟩ : Fin 1782) = p from rfl, h]⟩
    · intro h
      exact Fin.ext h.2

theorem forest_gens {s : ℕ} (hs : s < 2) :
    isInvA 1782 (xA s) (invCand 1782 (xA s)) = true ∧
      eqA 1782 (compA 1782 (xA s) rhoArr) (compA 1782 rhoArr (xA s)) = true ∧
      inM (xA s) = true := by
  have h := q3a_parts.2.1
  unfold forestOK at h
  simp only [Bool.and_eq_true] at h
  have := allLt_iff.1 h.1.1.1.1.1 s hs
  simpa only [Bool.and_eq_true, and_assoc] using this

theorem forest_node {i : ℕ} (hi : i < 22880) :
    froot[i]! < 22880 ∧ froot[froot[i]!]! = froot[i]! ∧
      (froot[i]! = i ∨ fpar[i]! < 22880 ∧ flab[i]! < 2 ∧ fdep[fpar[i]!]! < fdep[i]! ∧
        froot[fpar[i]!]! = froot[i]! ∧ (xTab[flab[i]!]!)[fpar[i]!]! = i) := by
  have h := q3a_parts.2.1
  unfold forestOK at h
  simp only [Bool.and_eq_true] at h
  have h' := allLt_iff.1 h.2 i hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h'
  obtain ⟨⟨h1, h2⟩, h3⟩ := h'
  refine ⟨h1, h2, ?_⟩
  by_cases hc : froot[i]! = i
  · exact Or.inl hc
  · right
    simpa only [hc, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc]
      using h3

theorem rep_xP {s : ℕ} (hs : s < 2) : Rep 1782 (xA s) (xP s) := (rep_permC (forest_gens hs).1).1

theorem xP_comm {s : ℕ} (hs : s < 2) : xP s * Model.rho1 = Model.rho1 * xP s :=
  eq_of_eqA (rep_compA (rep_xP hs) rep_rho) (rep_compA rep_rho (rep_xP hs)) (forest_gens hs).2.1

theorem nbrOrb_root {k : ℕ} (hk : k < 22880) (h : isNbr0 k = true) :
    froot[k]! = froot[nbr0[0]!]! := by
  have h' := allLt_iff.1 q3a_parts.2.2.1 k hk
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h'
  rcases h' with h' | h'
  · rw [h] at h'
    exact absurd h' (by decide)
  · exact h'

end Check

section Table

theorem rep_bAi {s : ℕ} (hs : s < 2) : Rep 1782 (bAi s) (bP s)⁻¹ :=
  rep_inv_of_isInvA (rep_bA s) (vert_parts.2.2.2.1 s hs)

theorem rep_cArrInv (i : ℕ) : Rep 1782 (cArrInv i) (cPerm i)⁻¹ := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rw [cArrInv_eq, cPerm_eq]
    split_ifs with h
    · rw [_root_.mul_inv_rev]
      exact rep_compA (ih _ h.2) (rep_bAi (tlab_lt h.1 h.2))
    · rw [inv_one]
      exact rep_idA

theorem isFixList_vtx {i : ℕ} (hi : i < 22880) : IsFixList (vtx i) fimg[i]! := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases (vert_parts.2.2.2.2.2.2.2.2 i hi).2 with rfl | ⟨hp, -, he⟩
    · rw [vtx_zero, vert_parts.2.2.2.2.2.2.2.1]
      exact isFixList_v0
    · have hpos : 0 < i := by omega
      rw [vtx_succ ⟨hpos, hp⟩, he]
      exact (ih _ hp (by omega)).smul _ (rep_bA _)

theorem vtx_injective {i j : ℕ} (hi : i < 22880) (hj : j < 22880) (h : vtx i = vtx j) : i = j := by
  have hj' : IsFixList (vtx i) fimg[j]! := by
    rw [h]
    exact isFixList_vtx hj
  have hk := (isFixList_vtx hi).key_eq hj'
  calc i = keyIdx (keyOf fimg[i]!) := (key_table hi).symm
    _ = keyIdx (keyOf fimg[j]!) := by rw [hk]
    _ = j := key_table hj

theorem adj0_iff (r : ℕ) :
    adj0 r = true ↔ r ≠ 0 ∧
      ((orderOf (Model.rho1 * (cPerm r * Model.rho1 * (cPerm r)⁻¹)) = 2 ∨
        orderOf (Model.rho1 * ((cPerm r * Model.rho1 * (cPerm r)⁻¹) *
          (cPerm r * Model.rho1 * (cPerm r)⁻¹))) = 2) ∨
      (orderOf (Model.rho1 * Model.rho1 * (cPerm r * Model.rho1 * (cPerm r)⁻¹)) = 2 ∨
        orderOf (Model.rho1 * Model.rho1 * ((cPerm r * Model.rho1 * (cPerm r)⁻¹) *
          (cPerm r * Model.rho1 * (cPerm r)⁻¹))) = 2)) := by
  have hq : Rep 1782 (qArr r) (cPerm r * Model.rho1 * (cPerm r)⁻¹) := by
    have := rep_compA (rep_cArr r) (rep_compA rep_rho (rep_cArrInv r))
    rwa [← mul_assoc] at this
  have hq2 := rep_compA hq hq
  have hp1 : Rep 1782 (rhoPow 1) Model.rho1 := by
    rw [rhoPow_one]
    exact rep_rho
  have hp2 : Rep 1782 (rhoPow 2) (Model.rho1 * Model.rho1) := by
    rw [rhoPow_two]
    exact rep_compA rep_rho rep_rho
  rw [show adj0 r = ((r != 0) && ((isInvol (compA 1782 (rhoPow 1) (qArr r)) ||
      isInvol (compA 1782 (rhoPow 1) (compA 1782 (qArr r) (qArr r)))) ||
      (isInvol (compA 1782 (rhoPow 2) (qArr r)) ||
      isInvol (compA 1782 (rhoPow 2) (compA 1782 (qArr r) (qArr r)))))) by
    simp only [adj0, List.any_cons, List.any_nil, Bool.or_false]]
  rw [Bool.and_eq_true, bne_iff_ne, Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true,
    isInvol_iff (rep_compA hp1 hq), isInvol_iff (rep_compA hp1 hq2),
    isInvol_iff (rep_compA hp2 hq), isInvol_iff (rep_compA hp2 hq2)]

theorem adj_v0_vtx_iff_adj0 {r : ℕ} (hr : r < 22880) : a4Graph.Adj v0 (vtx r) ↔ adj0 r = true := by
  have h := adj_smul_v0_iff rho1_pow_three 1 (cG r)
  rw [one_smul] at h
  rw [show vtx r = cG r • v0 from rfl, h, adj0_iff, exists_pow_iff]
  simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one]
  refine and_congr ⟨fun h0 e => ?_, fun h0 e => ?_⟩ Iff.rfl
  · subst e
    exact h0 vtx_zero.symm
  · exact h0 (vtx_injective hr (by norm_num) (by rw [vtx_zero]; exact e.symm))

theorem exists_vtx (hN : NrhoBound) (x : Vtx) : ∃ i < 22880, vtx i = x := by
  have hmul := card_vtx_mul
  have hne : Nat.card Vtx ≠ 0 := fun h => by
    rw [h, zero_mul] at hmul
    exact absurd hmul (by norm_num)
  have hle : Nat.card Vtx ≤ 22880 := by
    have h2 : Nat.card Vtx * 19595520 ≤ 22880 * 19595520 :=
      calc Nat.card Vtx * 19595520
          ≤ Nat.card Vtx * Nat.card ↥(normalizer (base : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) :=
            Nat.mul_le_mul_left _ hN
        _ = 22880 * 19595520 := by rw [hmul]
    exact Nat.le_of_mul_le_mul_right h2 (by norm_num)
  have : Finite Vtx := Nat.finite_of_card_ne_zero hne
  have : Fintype Vtx := Fintype.ofFinite Vtx
  let f : Fin 22880 → Vtx := fun i => vtx i
  have hf : Function.Injective f := fun i j h => Fin.ext (vtx_injective i.2 j.2 h)
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hf, ?_⟩
    have h1 := Fintype.card_le_of_injective f hf
    rw [Fintype.card_fin] at h1 ⊢
    rw [← Nat.card_eq_fintype_card] at h1 ⊢
    omega
  obtain ⟨i, hi⟩ := hbij.2 x
  exact ⟨i, i.2, hi⟩

theorem smul_vtx (hN : NrhoBound) {g : ↥suzM} {a : Array ℕ}
    (ha : Rep 1782 a (g : Equiv.Perm (Fin 1782))) {i : ℕ} (hi : i < 22880) :
    g • vtx i = vtx (actIdx a i) ∧ actIdx a i < 22880 := by
  obtain ⟨j, hj, hjx⟩ := exists_vtx hN (g • vtx i)
  have hj' : IsFixList (g • vtx i) fimg[j]! := by
    rw [← hjx]
    exact isFixList_vtx hj
  have hk := ((isFixList_vtx hi).smul g ha).key_eq hj'
  have e : actIdx a i = j := by
    unfold actIdx
    rw [hk, key_table hj]
  rw [e]
  exact ⟨hjx.symm, hj⟩

theorem xP_mem {s : ℕ} (hs : s < 2) : xP s ∈ suzM :=
  (mem_suzM_iff_siftA (rep_xP hs)).1 (forest_gens hs).2.2

theorem xP_smul_v0 {s : ℕ} (hs : s < 2) : (⟨xP s, xP_mem hs⟩ : ↥suzM) • v0 = v0 :=
  (smul_v0_eq_iff _).2 (mem_normalizer_of_comm (xP_comm hs))

theorem exists_stab_root (hN : NrhoBound) {i : ℕ} (hi : i < 22880) :
    ∃ g : ↥suzM, g • v0 = v0 ∧ g • vtx froot[i]! = vtx i := by
  suffices h : ∀ n i, fdep[i]! = n → i < 22880 →
      ∃ g : ↥suzM, g • v0 = v0 ∧ g • vtx froot[i]! = vtx i from h _ i rfl hi
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hn hi
    obtain ⟨-, -, hc⟩ := forest_node hi
    rcases hc with hc | ⟨hp, hl, hd, hr, hx⟩
    · exact ⟨1, one_smul _ _, by rw [hc, one_smul]⟩
    · obtain ⟨g, hg0, hg⟩ := ih _ (hn ▸ hd) _ rfl hp
      have hs := smul_vtx hN (g := ⟨xP flab[i]!, xP_mem hl⟩) (rep_xP hl) hp
      rw [← xTab_get hl hp, hx] at hs
      refine ⟨⟨xP flab[i]!, xP_mem hl⟩ * g, ?_, ?_⟩
      · rw [mul_smul, hg0, xP_smul_v0 hl]
      · rw [mul_smul, ← hr, hg, hs.1]

theorem adj_v0_vtx_iff (hN : NrhoBound) {k : ℕ} (hk : k < 22880) :
    a4Graph.Adj v0 (vtx k) ↔ isNbr0 k = true := by
  obtain ⟨hrlt, hrr, -⟩ := forest_node hk
  obtain ⟨g, hg0, hg⟩ := exists_stab_root hN hk
  have e : a4Graph.Adj v0 (vtx k) ↔ a4Graph.Adj v0 (vtx froot[k]!) := by
    have := a4Graph_adj_smul_iff g (x := v0) (y := vtx froot[k]!)
    rwa [hg0, hg] at this
  rw [e, adj_v0_vtx_iff_adj0 hrlt]
  unfold isNbr0
  rw [adj0Arr_get hrlt, hrr]
  simp [hk]

theorem adj_vtx_iff (hN : NrhoBound) {i j : ℕ} (_hi : i < 22880) (hj : j < 22880) :
    a4Graph.Adj (vtx i) (vtx j) ↔ adjIdx i j = true := by
  show _ ↔ isNbr0 (actIdx (cArrInv i) j) = true
  have hc : Rep 1782 (cArrInv i) (((cG i)⁻¹ : ↥suzM) : Equiv.Perm (Fin 1782)) := by
    rw [Subgroup.coe_inv]
    exact rep_cArrInv i
  obtain ⟨e1, hlt⟩ := smul_vtx hN hc hj
  have e0 : (cG i)⁻¹ • vtx i = v0 := inv_smul_smul _ _
  rw [← a4Graph_adj_smul_iff (cG i)⁻¹, e0, e1, adj_v0_vtx_iff hN hlt]

theorem mem_nbrsOf (hN : NrhoBound) {r y : ℕ} (hy : y ∈ nbrsOf r) :
    y < 22880 ∧ a4Graph.Adj (vtx r) (vtx y) := by
  unfold nbrsOf at hy
  obtain ⟨n, hn, rfl⟩ := Array.mem_map.1 hy
  unfold nbr0 at hn
  obtain ⟨hnlt, hnb⟩ := Array.mem_filter.1 hn
  rw [Array.mem_range] at hnlt
  obtain ⟨e, hlt⟩ := smul_vtx hN (g := cG r) (rep_cArr r) hnlt
  refine ⟨hlt, ?_⟩
  rw [← e]
  exact a4Graph_adj_smul (cG r) ((adj_v0_vtx_iff hN hnlt).2 hnb)

theorem exists_mem_nbrsOf (hN : NrhoBound) {r : ℕ} {z : Vtx}
    (hz : a4Graph.Adj (vtx r) z) : ∃ y ∈ nbrsOf r, vtx y = z := by
  obtain ⟨n, hn, hnz⟩ := exists_vtx hN ((cG r)⁻¹ • z)
  have hadj : a4Graph.Adj v0 (vtx n) := by
    rw [hnz, ← a4Graph_adj_smul_iff (cG r), smul_inv_smul]
    exact hz
  have hmem : n ∈ nbr0 := Array.mem_filter.2 ⟨Array.mem_range.2 hn, (adj_v0_vtx_iff hN hn).1 hadj⟩
  obtain ⟨e, -⟩ := smul_vtx hN (g := cG r) (rep_cArr r) hn
  refine ⟨actIdx (cArr r) n, Array.mem_map.2 ⟨n, hmem, rfl⟩, ?_⟩
  rw [← e, hnz, smul_inv_smul]

theorem exists_stab_of_adj (hN : NrhoBound) {x y : Vtx} (hx : a4Graph.Adj v0 x)
    (hy : a4Graph.Adj v0 y) : ∃ g : ↥suzM, g • v0 = v0 ∧ g • x = y := by
  obtain ⟨i, hi, rfl⟩ := exists_vtx hN x
  obtain ⟨j, hj, rfl⟩ := exists_vtx hN y
  have hri := nbrOrb_root hi ((adj_v0_vtx_iff hN hi).1 hx)
  have hrj := nbrOrb_root hj ((adj_v0_vtx_iff hN hj).1 hy)
  obtain ⟨g, hg0, hg⟩ := exists_stab_root hN hi
  obtain ⟨h, hh0, hh⟩ := exists_stab_root hN hj
  refine ⟨h * g⁻¹, ?_, ?_⟩
  · rw [mul_smul, inv_smul_eq_iff.2 hg0.symm, hh0]
  · rw [mul_smul, ← hg, inv_smul_smul, hri, ← hrj, hh]

end Table

end CFSG.Sporadic.SuzRecog.Q3A
