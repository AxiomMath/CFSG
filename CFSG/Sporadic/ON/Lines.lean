
module

public import CFSG.Sporadic.ON.LinesBase

public import CFSG.Sporadic.ON.Chain

public section

namespace CFSG.Sporadic.ON

open Native Matrix
open CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Perm CFSG.Perm.Native

theorem line_parts : ap lineT 0 = 0 ∧
    (∀ j < nLines, ap reps j < nPts ∧ ap lineT (ap reps j) = j) ∧
    (∀ k < nPts, ap lineT k < nLines ∧ ap lineT (ap negT k) = ap lineT k ∧
      (ap reps (ap lineT k) = k ∨ ap reps (ap lineT k) = ap negT k)) := by
  have h := facts.lines
  unfold lineChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  refine ⟨h0, fun j hj => ?_, fun k hk => ?_⟩
  · have := (allIn_eq_true.1 h1) j (Nat.zero_le _) hj
    simpa using this
  · have := (allIn_eq_true.1 h2) k (Nat.zero_le _) hk
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true] at this
    exact ⟨this.1.1, this.1.2, this.2⟩

@[expose] noncomputable def negF (k : Fin nPts) : Fin nPts :=
  ⟨ap negT k.val, (neg_parts k.val k.isLt).1⟩

theorem P_negF
    (k : Fin nPts) : P (negF k).val = -P k.val := P_neg k.isLt

theorem negF_negF (k : Fin nPts) : negF (negF k) = k := by
  apply Fin.ext
  apply P_injective _ (negF (negF k)).isLt _ k.isLt
  rw [P_negF, P_negF]
  exact neg_neg _

theorem smul_negF
    (g : J) (k : Fin nPts) : g • negF k = negF (g • k) := by
  apply Fin.ext
  apply P_injective _ (g • negF k).isLt _ (negF (g • k)).isLt
  rw [P_smul, P_negF, P_negF, P_smul, smul_vec, smul_vec]
  exact Matrix.mulVec_neg _ _

@[expose] noncomputable def repF (j : Fin nLines) : Fin nPts :=
  ⟨ap reps j.val, (line_parts.2.1 j.val j.isLt).1⟩

@[expose] noncomputable def lineF (k : Fin nPts) : Fin nLines :=
  ⟨ap lineT k.val, (line_parts.2.2 k.val k.isLt).1⟩

theorem lineF_repF (j : Fin nLines) : lineF (repF j) = j :=
  Fin.ext (line_parts.2.1 j.val j.isLt).2

theorem lineF_negF (k : Fin nPts) : lineF (negF k) = lineF k :=
  Fin.ext (line_parts.2.2 k.val k.isLt).2.1

theorem repF_lineF
    (k : Fin nPts) : repF (lineF k) = k ∨ repF (lineF k) = negF k := by
  rcases (line_parts.2.2 k.val k.isLt).2.2 with h | h
  · left; exact Fin.ext h
  · right; exact Fin.ext h

theorem lineF_eq_iff
    (k k' : Fin nPts) : lineF k = lineF k' ↔ k' = k ∨ k' = negF k := by
  constructor
  · intro h
    have h' : repF (lineF k) = repF (lineF k') := by rw [h]
    rcases repF_lineF k with e1 | e1 <;> rcases repF_lineF k' with e2 | e2 <;>
      rw [e1, e2] at h'
    · exact Or.inl h'.symm
    · right; rw [h', negF_negF]
    · right; exact h'.symm
    · left
      have := congrArg negF h'
      rwa [negF_negF, negF_negF, eq_comm] at this
  · rintro (rfl | rfl)
    · rfl
    · exact (lineF_negF k).symm

noncomputable instance lineAction : MulAction J (Fin nLines) where
  smul g j := lineF (g • repF j)
  one_smul j := by
    show lineF ((1 : J) • repF j) = j
    rw [one_smul, lineF_repF]
  mul_smul g h j := by
    show lineF ((g * h) • repF j) = lineF (g • repF (lineF (h • repF j)))
    rw [mul_smul]
    rcases repF_lineF (h • repF j) with e | e
    · rw [e]
    · rw [e, smul_negF, lineF_negF]

theorem line_smul_def
    (g : J) (j : Fin nLines) : g • j = lineF (g • repF j) := rfl

theorem lineF_smul
    (g : J) (k : Fin nPts) : lineF (g • k) = g • lineF k := by
  rw [line_smul_def]
  rcases repF_lineF k with e | e
  · rw [e]
  · rw [e, smul_negF, lineF_negF]

instance lineTransitive :
    MulAction.IsPretransitive J (Fin nLines) := by
  refine ⟨fun j j' => ?_⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J (repF j) (repF j')
  exact ⟨g, by rw [line_smul_def, hg, lineF_repF]⟩

theorem support_parts :
    (∀ s < checkVecs.size, checkVecs[s]! < nPts) ∧
    (∀ s < checkVecs.size,
      combW 154 basisR (coefs basisX orb.keys[checkVecs[s]!]!) = orb.keys[checkVecs[s]!]! ∧
      ((coefs basisX orb.keys[checkVecs[s]!]!).bitP 0 ||
        (coefs basisX orb.keys[checkVecs[s]!]!).bitM 0) = true) ∧
    (∀ t < 154, ∃ s < checkVecs.size,
      ((coefs basisX orb.keys[checkVecs[s]!]!).bitP t ||
        (coefs basisX orb.keys[checkVecs[s]!]!).bitM t) = true) := by
  have h := facts.support
  unfold supportChecks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [Array.all_eq_true] at h1 h2
  refine ⟨fun s hs => ?_, fun s hs => ?_, fun t ht => ?_⟩
  · rw [getElem!_pos checkVecs s hs]; simpa using h1 s hs
  · have := h2 s hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    rw [getElem!_pos checkVecs s hs]
    exact this
  · have := (allIn_eq_true.1 h3) t (Nat.zero_le _) ht
    rw [Array.any_eq_true] at this
    obtain ⟨s, hs, hst⟩ := this
    exact ⟨s, hs, by rw [getElem!_pos checkVecs s hs]; exact hst⟩

theorem vecOf_basisR
    (t : Fin 154) : vecOf basisR[t.val]! = Umat t := by
  rw [Umat_row, basisR_getElem t.isLt]

theorem checkVec_eq {s : ℕ} (hs : s < checkVecs.size) :
    P checkVecs[s]! = ∑ t : Fin 154, vecOf (coefs basisX orb.keys[checkVecs[s]!]!) t • Umat t := by
  have hw := (support_parts.2.1 s hs).1
  have hc : (coefs basisX orb.keys[checkVecs[s]!]!).toV.wf = true :=
    wf_combW rowsWF_basisX (keys_wf (support_parts.1 s hs))
  calc P checkVecs[s]! = vecOf (combW 154 basisR (coefs basisX orb.keys[checkVecs[s]!]!)) := by
        rw [hw]
    _ = ∑ t : Fin 154, vecOf (coefs basisX orb.keys[checkVecs[s]!]!) t • vecOf basisR[t.val]! :=
        vecOf_combW rowsWF_basisR hc
    _ = _ := Finset.sum_congr rfl fun t _ =>
        congrArg (fun v => vecOf (coefs basisX orb.keys[checkVecs[s]!]!) t • v) (vecOf_basisR t)

theorem eigen_eq
    {M : Matrix (Fin 154) (Fin 154) (ZMod 3)} {ε : Fin 154 → ZMod 3}
    (hε : ∀ t, M *ᵥ Umat t = ε t • Umat t) {c : Fin 154 → ZMod 3} {δ : ZMod 3}
    (hw : M *ᵥ (∑ t, c t • Umat t) = δ • ∑ t, c t • Umat t) {t : Fin 154} (ht : c t ≠ 0) :
    ε t = δ := by
  have h1 : M *ᵥ (∑ t, c t • Umat t) = (fun t => c t * ε t) ᵥ* Umat := by
    calc M *ᵥ (∑ t, c t • Umat t) = ∑ t, M *ᵥ (c t • Umat t) := Matrix.mulVec_sum _ _ _
      _ = ∑ t, (c t * ε t) • Umat t := Finset.sum_congr rfl fun t _ => by
          calc M *ᵥ (c t • Umat t) = c t • (M *ᵥ Umat t) := Matrix.mulVec_smul _ _ _
            _ = c t • (ε t • Umat t) := by rw [hε t]
            _ = (c t * ε t) • Umat t := smul_smul _ _ _
      _ = (fun t => c t * ε t) ᵥ* Umat := (Matrix.vecMul_eq_sum _ _).symm
  have h2 : δ • (∑ t, c t • Umat t) = (fun t => δ * c t) ᵥ* Umat := by
    calc δ • (∑ t, c t • Umat t) = ∑ t, δ • (c t • Umat t) := Finset.smul_sum
      _ = ∑ t, (δ * c t) • Umat t := Finset.sum_congr rfl fun t _ => smul_smul _ _ _
      _ = (fun t => δ * c t) ᵥ* Umat := (Matrix.vecMul_eq_sum _ _).symm
  have hx : ((fun t => c t * ε t) - fun t => δ * c t) ᵥ* Umat = 0 := by
    calc ((fun t => c t * ε t) - fun t => δ * c t) ᵥ* Umat
        = (fun t => c t * ε t) ᵥ* Umat - (fun t => δ * c t) ᵥ* Umat := Matrix.sub_vecMul _ _ _
      _ = 0 := by
        rw [← h1, ← h2, hw]
        exact sub_self _
  have h0 : c t * ε t - δ * c t = 0 := congrFun (eq_zero_of_vecMul_eq_zero Xmat_mul_Umat hx) t
  have h3 : c t * (ε t - δ) = 0 := by linear_combination h0
  rcases mul_eq_zero.1 h3 with h | h
  · exact absurd h ht
  · exact sub_eq_zero.1 h

theorem eq_one_of_fix_lines
    {g : J} (h : ∀ j : Fin nLines, g • j = j) : g = 1 := by
  classical
  have hk : ∀ k : Fin nPts, g • k = k ∨ g • k = negF k := by
    intro k
    have e := lineF_smul g k
    rw [h] at e
    exact (lineF_eq_iff k (g • k)).1 e.symm
  let sg : Fin nPts → ZMod 3 := fun k => if g • k = k then 1 else -1
  have hsg : ∀ k : Fin nPts, mat g *ᵥ P k.val = sg k • P k.val := by
    intro k
    rw [← smul_vec, ← P_smul]
    by_cases e : g • k = k
    · have h1 : sg k = 1 := ite_eq_left e
      rw [h1, e]
      exact (one_smul (ZMod 3) (P k.val)).symm
    · have h1 : sg k = -1 := ite_eq_right e
      rw [h1, (hk k).resolve_left e, P_negF]
      funext j
      exact (neg_one_mul (P k.val j)).symm
  have hQ : ∀ t : Fin 154, chainQ[t.val]! < nPts := fun t =>
    chainQ_lt (by rw [chainQ_size]; exact t.isLt)
  let ε : Fin 154 → ZMod 3 := fun t => sg ⟨chainQ[t.val]!, hQ t⟩
  have hε : ∀ t, mat g *ᵥ Umat t = ε t • Umat t := fun t => by
    rw [Umat_row]; exact hsg ⟨chainQ[t.val]!, hQ t⟩
  have hδ : ∀ s (hs : s < checkVecs.size), ∀ t : Fin 154,
      vecOf (coefs basisX orb.keys[checkVecs[s]!]!) t ≠ 0 →
        ε t = sg ⟨checkVecs[s]!, support_parts.1 s hs⟩ := by
    intro s hs t ht
    refine eigen_eq hε ?_ ht
    rw [← checkVec_eq hs]
    exact hsg ⟨checkVecs[s]!, support_parts.1 s hs⟩
  have hall : ∀ t : Fin 154, ε t = ε 0 := by
    intro t
    obtain ⟨s, hs, hst⟩ := support_parts.2.2 t.val t.isLt
    have h1 := hδ s hs t (vecOf_ne_zero t.isLt hst)
    have h2 := hδ s hs 0 (vecOf_ne_zero (t := 0) (by norm_num) (support_parts.2.1 s hs).2)
    rw [h1, h2]
  have hM : mat g = ε 0 • 1 := eq_smul_one_of_rows Xmat_mul_Umat (ε 0) fun t => by
    rw [hε t, hall t]
  have hε0 : ε 0 = 1 ∨ ε 0 = -1 := by
    simp only [ε, sg]
    split_ifs <;> simp
  rcases hε0 with h0 | h0
  · apply mat_injective
    rw [hM, h0, mat_one]
    exact one_smul (ZMod 3) (1 : Matrix (Fin 154) (Fin 154) (ZMod 3))
  · refine (mat_ne_neg_one g ?_).elim
    rw [hM, h0]
    ext i j
    exact neg_one_mul _

instance lineFaithful : FaithfulSMul J (Fin nLines) := by
  refine ⟨fun {g h} hgh => ?_⟩
  have : h⁻¹ * g = 1 := eq_one_of_fix_lines fun j => by rw [mul_smul, hgh, inv_smul_smul]
  rw [inv_mul_eq_one] at this
  exact this.symm

theorem lineF_root : lineF root = line0 := Fin.ext line_parts.1

theorem lvl_one_fix_line
    {g : J} (hg : g ∈ lvl 1) : g • line0 = line0 := by
  rw [← lineF_root, ← lineF_smul, lvl_one_fix hg]

theorem card_stabilizer_line0 :
    Nat.card (MulAction.stabilizer J line0) = 3753792 := by
  have h := Subgroup.card_mul_index (MulAction.stabilizer J line0)
  rw [MulAction.index_stabilizer_of_transitive, Nat.card_fin, card_J] at h
  have h' : Nat.card (MulAction.stabilizer J line0) * 122760 = 460815505920 := h
  have h3 : Nat.card (MulAction.stabilizer J line0) = 460815505920 / 122760 := by
    rw [← h', Nat.mul_div_cancel _ (by norm_num : 0 < 122760)]
  exact h3.trans (by norm_num)

end CFSG.Sporadic.ON
