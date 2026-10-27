
module

public import CFSG.Sporadic.Th.SimpleBase

public import CFSG.Sporadic.Th.ChainBase1

@[expose] public section

namespace CFSG.Sporadic.Th

open Native Pointwise

theorem abPow19_eq
    {α β : Table} (hα : Rep nX α a) (hβ : Rep nX β b) (m : ℕ) {p : ℕ}
    (hp : p < nX) :
    (List.range m).foldl (fun q _ => ap α (ap β q)) p = idx nX ((a * b) ^ m) p := by
  induction m with
  | zero => simp [idx_one]
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil, pow_succ',
      idx_mul, idx_mul]
    have h1 : idx nX ((a * b) ^ m) p < nX := idx_lt _ hp
    rw [hβ _ h1, hα _ (idx_lt _ h1)]

section TreeId

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)] {g₁ g₂ : G} {pl : Table}

end TreeId

section Global

variable {c : ℕ} (hC : CertFacts c)
include hC

theorem treeData_J : TreeData nX a b nX 0 id id gplT := by
  have hF := hC.orbit
  refine TreeData.of_id hF.pos (fun k hk hk0 => ?_) (fun k hk => ?_)
  · rw [gplT_ap hk]
    exact (hF.tree k hk hk0).1
  · induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [treeElt_zero, idx_one]
      · obtain ⟨hpar, hcase⟩ := hF.tree k hk hk0
        have hguard : 0 < k ∧ treePar (gplT[k]!).toNat < k := by
          rw [gplT_ap hk]; exact ⟨hk0, hpar⟩
        rw [treeElt, dite_eq_left hguard, idx_mul, gplT_ap hk]
        have hpk : parIdx k < nX := lt_trans hpar hk
        rw [ih (parIdx k) hpar hpk]
        rcases hcase with ⟨hl, ha⟩ | ⟨hl, hb⟩
        · have : lettersG a b (treeLab (readU32 thSt.par k)) = a := by
            simp [lettersG, labIdx] at hl ⊢; simp [hl]
          rw [this]
          show idx nX a (parIdx k) = k
          rw [← rep_a hC _ hpk, alphaT, ap_tblOfBytes _ hpk]
          exact ha
        · have : lettersG a b (treeLab (readU32 thSt.par k)) = b := by
            simp [lettersG, labIdx] at hl ⊢; simp [hl]
          rw [this]
          show idx nX b (parIdx k) = k
          rw [← rep_b hC _ hpk, betaT, ap_tblOfBytes _ hpk]
          exact hb

theorem rep_ab_letters :
    ∀ s, Rep nX (letters alphaT betaT s) (lettersG a b s) :=
  Rep.letters (rep_a hC) (rep_b hC)

theorem rep_ab_letters_inv :
    ∀ s, Rep nX (letters alphaT betaInvT s) (lettersG a b s)⁻¹ :=
  rep_letters_inv (rep_a_inv hC) (rep_b_inv hC)

theorem H_fix_zero : ∀ h ∈ H, idx nX h 0 = 0 := by
  intro h hh
  have hx : idx nX xJ 0 = 0 := by rw [← rep_x hC 0 (zero_lt_nX hC)]; exact hC.tables.x0
  have hy : idx nX yJ 0 = 0 := by rw [← rep_y hC 0 (zero_lt_nX hC)]; exact hC.tables.y0
  induction hh using Subgroup.closure_induction with
  | mem x hx' =>
    rcases hx' with rfl | rfl
    · exact hx
    · exact hy
  | one => exact idx_one 0
  | mul x y _ _ hx hy => rw [idx_mul, hy, hx]
  | inv x _ hx => rw [← hx, idx_inv_idx, hx]

theorem isPretransitive : MulAction.IsPretransitive J (Fin nX) := by
  have hT := treeData_J hC
  refine ⟨fun p q => ?_⟩
  have hreach : ∀ r : Fin nX, ∃ g : J, g • root hC = r := by
    intro r
    have hmem : r ∈ MulAction.orbit (Subgroup.closure ({a, b} : Set J)) (⟨0, hT.r_lt⟩ : Fin nX) :=
      (hT.mem_orbit_iff r).2 ⟨r.val, r.isLt, rfl⟩
    obtain ⟨⟨g, _⟩, hg⟩ := hmem
    exact ⟨g, hg⟩
  obtain ⟨g, hg⟩ := hreach p
  obtain ⟨h, hh⟩ := hreach q
  exact ⟨h * g⁻¹, by rw [mul_smul, ← hg, inv_smul_smul, hh]⟩

@[expose] noncomputable def subLab : Fin nX → Fin 11 := fun p =>
  ⟨compsT.labelOf p.val, by
    rw [← hC.tables.reps]
    exact ((compOK_spec (rep_x hC) (rep_y hC) hC.tables.comp).1 p.val p.isLt).2.2⟩

theorem subLab_val
    (p : Fin nX) : (subLab hC p).val = compsT.labelOf p.val := rfl

theorem subLab_inv :
    ∀ h ∈ H, ∀ p : Fin nX, subLab hC (h • p) = subLab hC p := by
  have hspec := (compOK_spec (rep_x hC) (rep_y hC) hC.tables.comp).1
  intro h hh
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    intro p
    apply Fin.ext
    rw [subLab_val hC, subLab_val hC, ← idx_val]
    rcases hx with rfl | rfl
    · exact (hspec p.val p.isLt).1
    · exact (hspec p.val p.isLt).2.1
  | one => intro p; rw [one_smul]
  | mul x y _ _ hx hy => intro p; rw [mul_smul, hx, hy]
  | inv x _ hx => intro p; rw [← hx (x⁻¹ • p), smul_inv_smul]

theorem subLab_orb :
    ∀ p q : Fin nX, subLab hC p = subLab hC q → ∃ h ∈ H, h • p = q := by
  have hspec := (compOK_spec (rep_x hC) (rep_y hC) hC.tables.comp).2
  intro p q hpq
  obtain ⟨hp, hpH, hpe⟩ := hspec p.val p.isLt
  obtain ⟨hq, hqH, hqe⟩ := hspec q.val q.isLt
  have hlab : compsT.labelOf p.val = compsT.labelOf q.val := by
    rw [← subLab_val hC, ← subLab_val hC, hpq]
  refine ⟨hq * hp⁻¹, H.mul_mem hqH (H.inv_mem hpH), ?_⟩
  apply smul_eq_of_idx
  rw [idx_mul, ← hpe, idx_inv_idx, hlab, hqe]

theorem card_subLab_class (i : Fin 11) :
    (Finset.univ.filter (fun p : Fin nX => subLab hC p = i)).card = subSizes i := by
  have hlab : ∀ p < nX, compsT.labelOf p < 11 := fun p hp => by
    rw [← hC.tables.reps]
    exact ((compOK_spec (rep_x hC) (rep_y hC) hC.tables.comp).1 p hp).2.2
  have hcount := countLabels_spec hlab i.val i.isLt
  have hlist : (countLabels nX 11 compsT)[i.val]! = suborbitSizes[i.val]! :=
    getElem!_of_toList_eq hC.tables.counts i.val
  rw [← suborbitSizes_getElem, ← hlist, hcount]
  apply Finset.card_bij (fun p _ => p.val)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨p.isLt, by rw [← subLab_val hC, hp]⟩
  · intro p _ q _ h
    exact Fin.ext h
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    refine ⟨⟨p, hp.1⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Fin.ext hp.2

theorem subLab_root : subLab hC (root hC) = 0 := by
  apply subSizes_eq_one
  rw [← card_subLab_class hC]
  rw [Finset.card_eq_one]
  refine ⟨root hC, ?_⟩
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hp
    obtain ⟨h, hh, hhp⟩ := subLab_orb hC p (root hC) hp
    have hfix : h • root hC = root hC :=
      smul_eq_of_idx h (root hC) (root hC) (H_fix_zero hC h hh)
    exact smul_left_cancel h (hhp.trans hfix.symm)
  · rintro rfl; rfl

theorem isPreprimitive : MulAction.IsPreprimitive J (Fin nX) := by
  have := isPretransitive hC
  apply isPreprimitive_of_suborbit_labels (root hC) H
    (fun h hh => smul_eq_of_idx h _ _ (H_fix_zero hC h hh)) (subLab hC) (subLab_inv hC)
    (subLab_orb hC)
  intro S hS hdvd
  rw [subLab_root hC] at hS ⊢
  have hsum : (∑ i ∈ S, (Finset.univ.filter (fun p : Fin nX => subLab hC p = i)).card) =
      ∑ i ∈ S, subSizes i := Finset.sum_congr rfl fun i _ => card_subLab_class hC i
  rw [hsum, Fintype.card_fin, hC.count] at hdvd
  exact subSizes_blocks S hS hdvd

theorem a_ne_one : a ≠ 1 := by
  intro h
  have := rep_a hC 0 (zero_lt_nX hC)
  rw [h, idx_one, hC.a0] at this
  exact absurd this (by decide)

theorem b_ne_one : b ≠ 1 := by
  intro h
  have := rep_b hC 0 (zero_lt_nX hC)
  rw [h, idx_one, hC.b0] at this
  exact absurd this (by decide)

theorem ab_ne_one : a * b ≠ 1 := by
  intro h
  have h0 : idx nX (a * b) 0 = 0 := by rw [h, idx_one]
  rw [idx_mul, ← rep_b hC 0 (zero_lt_nX hC), hC.b0] at h0
  have h1 : idx nX a 1 = 0 := by
    have := idx_sq_of_invoOK (rep_a hC) hC.aInvo 0 (zero_lt_nX hC)
    rw [pow_two, idx_mul, ← rep_a hC 0 (zero_lt_nX hC), hC.a0] at this
    exact this
  have h2 : (2 : ℕ) = 1 := by
    have e2 := idx_inv_idx (n := nX) a 2
    have e1 := idx_inv_idx (n := nX) a 1
    rw [h0] at e2
    rw [h1] at e1
    exact e2.symm.trans e1
  exact absurd h2 (by decide)

end Global

end CFSG.Sporadic.Th
