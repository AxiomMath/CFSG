module

public import CFSG.Sporadic.HS.Group
public import CFSG.Perm.ChainSift

public section

namespace CFSG.Sporadic.SmallF2

open Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

variable (D : VecData)

@[expose] noncomputable def genG (z : ℤ) : J D :=
  if z = 1 then a D else if z = -1 then (a D)⁻¹ else if z = 2 then b D else (b D)⁻¹

@[expose] noncomputable def r0 : J D := wordG (genG D) D.w0

@[expose] noncomputable def r1 : J D := wordG (genG D) D.w1

@[expose] noncomputable def regsG (r : ℕ) : J D := if r = 0 then r0 D else if r = 1 then r1 D else 1

@[expose] noncomputable def gs (j : ℕ) : J D := runSLPG D.prog (regsG D) D.sel[j]!

noncomputable abbrev lvl (i : ℕ) : Subgroup (J D) := levelGroup (L D) D.base (pairG (gs D)) i

theorem R0_size_eq : (R0 D).size = D.nregs := by simp [R0, regs0]

theorem L_size : (L D).size = 2 * D.sel.size := by simp [L, lettersOf]

theorem T_size : (T D).size = D.base.size := by simp [T, chainTrees]

theorem regsG_mem (r : ℕ) : regsG D r ∈ Subgroup.closure ({r0 D, r1 D} : Set (J D)) := by
  unfold regsG
  split_ifs
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  · exact Subgroup.one_mem _

theorem runSLPG_mem {G : Type*} [Group G] (K : Subgroup G) (prog : List Instr) :
    ∀ regs : ℕ → G, (∀ r, regs r ∈ K) → ∀ r, runSLPG prog regs r ∈ K := by
  induction prog with
  | nil => intro regs h r; exact h r
  | cons ins prog ih =>
    intro regs h r
    apply ih (stepG regs ins)
    intro s
    cases ins with
    | mu i j k =>
      simp only [stepG, Function.update_apply]
      split_ifs
      · exact K.mul_mem (h i) (h j)
      · exact h s
    | pwr e i k =>
      simp only [stepG, Function.update_apply]
      split_ifs
      · exact K.pow_mem (h i) e
      · exact h s
    | iv i k =>
      simp only [stepG, Function.update_apply]
      split_ifs
      · exact K.inv_mem (h i)
      · exact h s

theorem gs_mem (j : ℕ) : gs D j ∈ Subgroup.closure ({r0 D, r1 D} : Set (J D)) :=
  runSLPG_mem _ D.prog (regsG D) (regsG_mem D) _

theorem lvl_zero_le : lvl D 0 ≤ Subgroup.closure ({r0 D, r1 D} : Set (J D)) := by
  unfold lvl levelGroup lettersGroup
  rw [Subgroup.closure_le]
  rintro _ ⟨l, -, rfl⟩
  unfold pairG
  split_ifs
  · exact gs_mem D _
  · exact Subgroup.inv_mem _ (gs_mem D _)

theorem R0_get {r : ℕ} (hr : r < D.nregs) : (R0 D)[r]! =
    if r = 0 then wordT D.n (genT D.n (O D)) D.w0 else if r = 1 then
      wordT D.n (genT D.n (O D)) D.w1 else idT D.n := by
  rw [getElem!_pos (R0 D) r (by rw [R0_size_eq]; exact hr)]
  simp only [R0, regs0, Array.getElem_ofFn]

theorem instrRegsLt_of_instrLt {r : ℕ} {ins : Instr} (h : instrLt r ins = true) :
    instrRegsLt r ins := by
  cases ins <;> simp_all [instrLt, instrRegsLt]

section Facts

variable {D} {c : ℕ} (hF : Facts D c)
include hF

theorem n_lt_two_pow : D.n < 2 ^ 32 := lt_trans hF.n_lt (by norm_num)

theorem rep_genT (z : ℤ) : Rep D.n (genT D.n (O D) z) (genG D z) := by
  unfold genT genG
  split_ifs
  · exact rep_a hF.toBaseFacts
  · exact Rep.inv_of_invOK (rep_a hF.toBaseFacts) hF.invA
  · exact rep_b hF.toBaseFacts
  · exact Rep.inv_of_invOK (rep_b hF.toBaseFacts) hF.invB

theorem rep_r0 : Rep D.n (wordT D.n (genT D.n (O D)) D.w0) (r0 D) :=
  Rep.wordT (n_lt_two_pow hF) _ fun l _ => rep_genT hF l

theorem rep_r1 : Rep D.n (wordT D.n (genT D.n (O D)) D.w1) (r1 D) :=
  Rep.wordT (n_lt_two_pow hF) _ fun l _ => rep_genT hF l

theorem rep_regs0 : ∀ r < (R0 D).size, Rep D.n (R0 D)[r]! (regsG D r) := by
  intro r hr
  rw [R0_size_eq] at hr
  rw [R0_get D hr]
  unfold regsG
  split_ifs
  · exact rep_r0 hF
  · exact rep_r1 hF
  · exact Rep.idT (n_lt_two_pow hF)

theorem rep_R0_zero : Rep D.n (R0 D)[0]! (r0 D) := by
  have h2 : 2 ≤ D.nregs := hF.nregs
  have := rep_regs0 hF 0 (by rw [R0_size_eq]; omega)
  simpa [regsG] using this

theorem rep_R0_one : Rep D.n (R0 D)[1]! (r1 D) := by
  have h1 : 1 < D.nregs := hF.nregs
  have := rep_regs0 hF 1 (by rw [R0_size_eq]; exact h1)
  simpa [regsG] using this

theorem rep_slp : ∀ r < (R0 D).size, Rep D.n (SLP D).1[r]! (runSLPG D.prog (regsG D) r) :=
  (runSLP_rep (n_lt_two_pow hF) D.prog (R0 D) (regsG D)
    (fun ins hins => by rw [R0_size_eq]; exact instrRegsLt_of_instrLt (hF.prog ins hins))
    (rep_regs0 hF) hF.slp).2

theorem rep_letters : ∀ j < (L D).size / 2, Rep D.n (L D)[2 * j]! (gs D j) := by
  intro j hj
  rw [L_size] at hj
  have hj' : j < D.sel.size := by omega
  have e : (L D)[2 * j]! = (SLP D).1[D.sel[j]!]! := by
    rw [getElem!_pos (L D) (2 * j) (by rw [L_size]; omega)]
    simp only [L, lettersOf, Array.getElem_ofFn]
    rw [ite_eq_left (by omega), show 2 * j / 2 = j by omega]
  rw [e]
  exact rep_slp hF _ (by rw [R0_size_eq]; exact hF.sel j hj')

theorem chain_facts' :
    (∀ i < D.base.size, TreeFacts D.n (T D)[i]! (levelLetters (L D) D.base i) (pairG (gs D))
      D.base[i]!) ∧
      (∀ i < D.base.size, ∀ g ∈ lvl D i, idx D.n g D.base[i]! = D.base[i]! ↔ g ∈ lvl D (i + 1)) ∧
      ∀ i ≤ D.base.size, Nat.card (lvl D i) =
        ∏ l ∈ Finset.Ico i D.base.size, (T D)[l]!.pts.size :=
  chain_facts (rep_letters hF) (eq_one_of_fix_basis hF.toBaseFacts) hF.chain

theorem a_mem_lvl : a D ∈ lvl D 0 := by
  refine chain_sift_mem (rep_letters hF) (eq_one_of_fix_basis hF.toBaseFacts) hF.chain
    (img := apT (O D).alpha D.basis) (apT_size _ _) (fun t ht => ?_) hF.siftA
  rw [apT_get _ _ ht, rep_a hF.toBaseFacts _ (hF.basis_lt t ht)]

theorem b_mem_lvl : b D ∈ lvl D 0 := by
  refine chain_sift_mem (rep_letters hF) (eq_one_of_fix_basis hF.toBaseFacts) hF.chain
    (img := apT (O D).beta D.basis) (apT_size _ _) (fun t ht => ?_) hF.siftB
  rw [apT_get _ _ ht, rep_b hF.toBaseFacts _ (hF.basis_lt t ht)]

theorem lvl_zero : lvl D 0 = ⊤ := by
  rw [eq_top_iff, ← closure_ab D, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact a_mem_lvl hF
  · exact b_mem_lvl hF

theorem closure_r : Subgroup.closure ({r0 D, r1 D} : Set (J D)) = ⊤ := by
  rw [eq_top_iff, ← lvl_zero hF]
  exact lvl_zero_le D

theorem T_pts_size {l : ℕ} (hl : l < D.base.size) : (T D)[l]!.pts.size = D.orbSizes[l]! := by
  have h := congrArg (fun L : List ℕ => L[l]?) hF.orbSizes
  have hl' : l < (T D).size := by rw [T_size]; exact hl
  simp only [orbitSizes, List.getElem?_map, Array.getElem?_toList,
    Array.getElem?_eq_getElem hl', Option.map_some] at h
  rw [getElem!_pos (T D) l hl', getElem!_def, ← h]

theorem card_lvl {i : ℕ} (hi : i ≤ D.base.size) :
    Nat.card (lvl D i) = ∏ l ∈ Finset.Ico i D.base.size, D.orbSizes[l]! := by
  rw [(chain_facts' hF).2.2 i hi]
  refine Finset.prod_congr rfl fun l hl => ?_
  exact T_pts_size hF (Finset.mem_Ico.1 hl).2

theorem n_pos : 0 < D.n := by
  have h0 : 0 < D.basis.size := by rw [hF.basis_size]; exact hF.d_pos
  exact lt_of_le_of_lt (Nat.zero_le _) (hF.basis_lt 0 h0)

noncomputable abbrev root : Fin D.n := ⟨0, n_pos hF⟩

theorem lvl_one_iff (g : J D) : idx D.n g 0 = 0 ↔ g ∈ lvl D 1 := by
  have := (chain_facts' hF).2.1 0 hF.base_pos g (by rw [lvl_zero hF]; trivial)
  rwa [hF.base0] at this

theorem stabilizer_root : MulAction.stabilizer (J D) (root hF) = lvl D 1 := by
  ext g
  rw [MulAction.mem_stabilizer_iff, ← lvl_one_iff hF, idx_of_lt g (n_pos hF)]
  constructor
  · intro h; rw [h]
  · intro h; exact Fin.ext h

theorem card_stabilizer_root :
    Nat.card (MulAction.stabilizer (J D) (root hF)) =
      ∏ l ∈ Finset.Ico 1 D.base.size, D.orbSizes[l]! := by
  rw [stabilizer_root hF]
  exact card_lvl hF hF.base_pos

theorem lvl_one_fix {g : J D} (hg : g ∈ lvl D 1) : g • root hF = root hF := by
  rw [← MulAction.mem_stabilizer_iff, stabilizer_root hF]; exact hg

theorem treeFacts_zero : TreeFacts D.n (T D)[0]! (levelLetters (L D) D.base 0) (pairG (gs D)) 0 := by
  have := (chain_facts' hF).1 0 hF.base_pos
  rwa [hF.base0] at this

theorem isPretransitive (horb0 : D.orbSizes[0]! = D.n) :
    MulAction.IsPretransitive (J D) (Fin D.n) := by
  have hT := treeFacts_zero hF
  have hcard := hT.card_orbit
  rw [T_pts_size hF hF.base_pos, horb0] at hcard
  set Orb := MulAction.orbit (lettersGroup (levelLetters (L D) D.base 0) (pairG (gs D)))
    (⟨0, hT.r_lt⟩ : Fin D.n) with hOrb
  have huniv : Orb = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) _ (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_fin, ← Nat.card_coe_set_eq, hcard]
  have hreach : ∀ p : Fin D.n, ∃ g : J D, g • root hF = p := by
    intro p
    have hp : p ∈ Orb := by rw [huniv]; trivial
    obtain ⟨⟨g, _⟩, hg⟩ := hp
    exact ⟨g, hg⟩
  refine ⟨fun p q => ?_⟩
  obtain ⟨g, hg⟩ := hreach p
  obtain ⟨h, hh⟩ := hreach q
  exact ⟨h * g⁻¹, by rw [mul_smul, ← hg, inv_smul_smul, hh]⟩

end Facts

end CFSG.Sporadic.SmallF2
