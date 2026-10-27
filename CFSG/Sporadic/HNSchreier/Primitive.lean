module

public import CFSG.Sporadic.HNSchreier.SchreierData
public import CFSG.Sporadic.HNSchreier.PrimCheck
public import CFSG.Sporadic.HNSchreier.MergeExists
public import CFSG.Perm.ChainSpec
public import CFSG.Sporadic.Th.GroupTheory
public import CFSG.Sporadic.HN.F5Simple
public import Certificates.Certificate2102
public import Certificates.Certificate2104

public noncomputable section

namespace CFSG.Sporadic.HNSchreier

open CFSG.Sporadic.F5.Native CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Perm CFSG.Perm.Native CFSG.Certificates
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

@[expose] def RegsRep (arr : Array (Array ℕ)) (perm : ℕ → Equiv.Perm X) : Prop :=
  arr.size = 11 ∧ ∀ r < 11, PRep hnsData.n arr[r]! (perm r)

theorem regsRep_step {arr : Array (Array ℕ)} {perm : ℕ → Equiv.Perm X} (h : RegsRep arr perm)
    {a b c : ℕ} (ha : a < 11) (hb : b < 11) (hc : c < 11) :
    RegsRep (arr.set! c (pcomp hnsData.n arr[a]! arr[b]!))
      (Function.update perm c (perm a * perm b)) := by
  obtain ⟨hs, hr⟩ := h
  refine ⟨by simp [hs], fun r hr' => ?_⟩
  by_cases hrc : r = c
  · subst hrc
    rw [Function.update_self, Array.getElem!_set!_self _ _ _ (by omega)]
    exact prep_pcomp (hr a ha) (hr b hb)
  · rw [Function.update_of_ne hrc, Array.getElem!_set!_ne _ _ _ _ (Ne.symm hrc)]
    exact hr r hr'

theorem regsRep_prog : ∀ (prog : List (ℕ × ℕ × ℕ)) (arr : Array (Array ℕ))
    (perm : ℕ → Equiv.Perm X), (∀ t ∈ prog, t.1 < 11 ∧ t.2.1 < 11 ∧ t.2.2 < 11) →
    RegsRep arr perm → RegsRep (progRegs hnsData.n arr prog) (runProg perm prog)
  | [], _, _, _, h => h
  | (a, b, c) :: rest, arr, perm, hp, h => by
    have ht := hp (a, b, c) (List.mem_cons_self ..)
    exact regsRep_prog rest _ _ (fun t ht' => hp t (List.mem_cons_of_mem _ ht'))
      (regsRep_step h ht.1 ht.2.1 ht.2.2)

theorem prog_bounds : ∀ t ∈ Data.subgroupProgram, t.1 < 11 ∧ t.2.1 < 11 ∧ t.2.2 < 11 := by
  decide +kernel

theorem initRegs_facts (n : ℕ) (a b : Array ℕ) :
    (initRegs n a b).size = 11 ∧ (initRegs n a b)[0]! = pid n ∧ (initRegs n a b)[1]! = a ∧
      (initRegs n a b)[2]! = b ∧ ∀ r, 3 ≤ r → r < 11 → (initRegs n a b)[r]! = pid n := by
  have hget : ∀ r < 3, (initRegs n a b)[r]! = #[pid n, a, b][r]! := by
    intro r hr
    rw [initRegs, getElem!_pos _ r (by simp; omega), Array.getElem_append_left (by simp; omega),
      getElem!_pos _ r (by simp; omega)]
  refine ⟨by simp [initRegs], (hget 0 (by norm_num)).trans rfl, (hget 1 (by norm_num)).trans rfl,
    (hget 2 (by norm_num)).trans rfl, fun r h3 h11 => ?_⟩
  rw [initRegs, getElem!_pos _ r (by simp; omega), Array.getElem_append_right (by simp; omega)]
  simp

theorem regsRep_initRegs {a b : Array ℕ} {g₀ g₁ : Equiv.Perm X} (ha : PRep hnsData.n a g₀)
    (hb : PRep hnsData.n b g₁) :
    RegsRep (initRegs hnsData.n a b) (fun r => if r = 1 then g₀ else if r = 2 then g₁ else 1) := by
  obtain ⟨hs, h0, h1, h2, h3⟩ := initRegs_facts hnsData.n a b
  refine ⟨hs, fun r hr => ?_⟩
  rcases Nat.lt_or_ge r 3 with hr3 | hr3
  · interval_cases r
    · rw [h0]; exact prep_pid
    · rw [h1]; exact ha
    · rw [h2]; exact hb
  · show PRep hnsData.n (initRegs hnsData.n a b)[r]! (if r = 1 then g₀ else if r = 2 then g₁ else 1)
    rw [ite_eq_right (by omega), ite_eq_right (by omega), h3 r hr3 hr]
    exact prep_pid

theorem regsRep_init :
    RegsRep (initRegs hnsData.n (natTab (hnsData.orbit ()).alpha) (natTab (hnsData.orbit ()).beta))
      permRegs0 :=
  regsRep_initRegs prep_a0 prep_a1

@[irreducible] def hRegs : Array (Array ℕ) :=
  progRegs hnsData.n (initRegs hnsData.n (natTab (hnsData.orbit ()).alpha)
    (natTab (hnsData.orbit ()).beta)) Data.subgroupProgram

theorem hRegs_eq : hRegs = progRegs hnsData.n (initRegs hnsData.n
    (natTab (hnsData.orbit ()).alpha) (natTab (hnsData.orbit ()).beta)) Data.subgroupProgram := by
  unfold hRegs; rfl

theorem regs_rep : RegsRep hRegs permRegs := by
  rw [hRegs_eq]
  exact regsRep_prog _ _ _ prog_bounds regsRep_init

abbrev hLetters : Array Table := #[toTable hRegs[1]!, toTable hRegs[2]!]

@[irreducible] def hTrees : Array Tree :=
  Data.subgroupOrbitReps.toArray.map fun r => treeBFS hnsData.n r hLetters #[0, 1]

theorem hTrees_eq : hTrees =
    Data.subgroupOrbitReps.toArray.map fun r => treeBFS hnsData.n r hLetters #[0, 1] := by
  unfold hTrees; rfl

@[irreducible] def hLabs : Array ℕ := subLabels hnsData.n hTrees

theorem hLabs_eq : hLabs = subLabels hnsData.n hTrees := by unfold hLabs; rfl

theorem prim_parts :
    hRegs.size = 11 ∧
    (∀ i < hnsData.n, (hRegs[1]!)[i]! < hnsData.n ∧ (hRegs[2]!)[i]! < hnsData.n) ∧
    (toTable hRegs[1]!).size = hnsData.n ∧ (toTable hRegs[2]!).size = hnsData.n ∧
    ap (toTable hRegs[1]!) 0 = 0 ∧ ap (toTable hRegs[2]!) 0 = 0 ∧
    Data.subgroupOrbitReps.toArray.size = 12 ∧
    (hTrees.toList.map fun T => T.pts.size) = Data.subgroupOrbitSizes ∧
    (∀ j < 12, Data.subgroupOrbitReps.toArray[j]! < hnsData.n ∧
      Perm.Native.treeOK hnsData.n Data.subgroupOrbitReps.toArray[j]! hTrees[j]! hLetters
        #[0, 1] = true) ∧
    (∀ p < hnsData.n, hLabs[p]! < 12 ∧ ap hTrees[hLabs[p]!]!.pos p < hTrees[hLabs[p]!]!.pts.size ∧
      ap hTrees[hLabs[p]!]!.pts (ap hTrees[hLabs[p]!]!.pos p) = p) ∧
    (∀ j < 12, ∀ k < 12, j ≠ k →
      ¬ (ap hTrees[j]!.pos Data.subgroupOrbitReps.toArray[k]! < hTrees[j]!.pts.size ∧
        ap hTrees[j]!.pts (ap hTrees[j]!.pos Data.subgroupOrbitReps.toArray[k]!) =
          Data.subgroupOrbitReps.toArray[k]!)) ∧
    (∀ j < 12, ∀ t < hTrees[j]!.pts.size,
      Data.subgroupOrbitReps.toArray[j]! ≤ ap hTrees[j]!.pts t) ∧
    divOK hnsData.n Data.subgroupOrbitSizes = true := by
  have h := prim_cert
  unfold primChecks subChecksH at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [← hRegs_eq, ← hTrees_eq, ← hLabs_eq] at h
  obtain ⟨⟨hsz, hlt⟩, ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, hs1⟩, hs2⟩, hr12⟩, hsizes⟩, htrees⟩, hlab⟩, hdisj⟩,
    hleast⟩, hdiv⟩⟩ := h
  refine ⟨hsz, fun i hi => ?_, hs1, hs2, h0, h1, hr12, hsizes, fun j hj => ?_, fun p hp => ?_,
    fun j hj k hk hjk => ?_, fun j hj t ht => ?_, hdiv⟩
  · have := (allIn_eq_true.1 hlt) i (Nat.zero_le _) hi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this
  · have := (allIn_eq_true.1 htrees) j (Nat.zero_le _) hj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this
  · have := (allIn_eq_true.1 hlab) p (Nat.zero_le _) hp
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · have := (allIn_eq_true.1 ((allIn_eq_true.1 hdisj) j (Nat.zero_le _) hj)) k (Nat.zero_le _) hk
    simp only [Bool.or_eq_true, beq_iff_eq, hjk, false_or, Bool.not_eq_true',
      Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne] at this
    intro ⟨ha, hb⟩
    rcases this with h | h
    · exact h ha
    · exact h hb
  · have := (allIn_eq_true.1 ((allIn_eq_true.1 hleast) j (Nat.zero_le _) hj)) t (Nat.zero_le _) ht
    simp only [decide_eq_true_eq] at this
    exact this

@[expose] def hperm (l : ℕ) : Equiv.Perm X := if l = 0 then permRegs 1 else permRegs 2

theorem rep_toTable {arr : Array ℕ} {g : Equiv.Perm X} (hg : PRep hnsData.n arr g)
    (hsize : (toTable arr).size = hnsData.n) (hlt : ∀ i < hnsData.n, arr[i]! < hnsData.n) :
    Rep hnsData.n (toTable arr) g := by
  intro i hi
  have hs : i < arr.size := by
    have : (toTable arr).size = arr.size := by simp [toTable]
    omega
  have hn32 : hnsData.n < 2 ^ 32 := by rw [hns_n]; norm_num
  rw [idx_of_lt _ hi, ap, toTable, getElem!_pos _ i (by simpa using hs), Array.getElem_map,
    UInt32.toNat_ofNat', Nat.mod_eq_of_lt (lt_trans (getElem!_pos arr i hs ▸ hlt i hi) hn32),
    ← getElem!_pos arr i hs, hg ⟨i, hi⟩]
  rfl

theorem getElem!_pair_zero {α : Type*} [Inhabited α] (x y : α) : #[x, y][0]! = x := rfl

theorem getElem!_pair_one {α : Type*} [Inhabited α] (x y : α) : #[x, y][1]! = y := rfl

theorem rep_h1 :
    Rep hnsData.n (toTable hRegs[1]!) (permRegs 1) := by
  obtain ⟨-, hlt, hs1, -, -⟩ := prim_parts
  exact rep_toTable (regs_rep.2 1 (by norm_num)) hs1 fun i hi => (hlt i hi).1

theorem rep_h2 :
    Rep hnsData.n (toTable hRegs[2]!) (permRegs 2) := by
  obtain ⟨-, hlt, -, hs2, -⟩ := prim_parts
  exact rep_toTable (regs_rep.2 2 (by norm_num)) hs2 fun i hi => (hlt i hi).2

theorem hperm_zero : hperm 0 = permRegs 1 := ite_eq_left rfl

theorem hperm_one : hperm 1 = permRegs 2 := ite_eq_right (by norm_num)

theorem hLetters_rep :
    ∀ l ∈ (#[0, 1] : Array ℕ), Rep hnsData.n hLetters[l]! (hperm l) := by
  intro l hl
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · rw [hLetters, getElem!_pair_zero, hperm_zero]
    exact rep_h1
  · rw [hLetters, getElem!_pair_one, hperm_one]
    exact rep_h2

theorem lettersGroup_eq : lettersGroup (#[0, 1] : Array ℕ) hperm = HP := by
  rw [lettersGroup, HP]
  congr 1
  ext g
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨l, rfl | rfl, rfl⟩
    · exact Or.inl hperm_zero
    · exact Or.inr hperm_one
  · rintro (rfl | rfl)
    · exact ⟨0, Or.inl rfl, hperm_zero⟩
    · exact ⟨1, Or.inr rfl, hperm_one⟩

abbrev repN (j : ℕ) : ℕ := Data.subgroupOrbitReps.toArray[j]!

theorem tree_facts
    {j : ℕ} (hj : j < 12) :
    TreeFacts hnsData.n hTrees[j]! #[0, 1] hperm (repN j) := by
  have h := (prim_parts.2.2.2.2.2.2.2.2.1 j hj).2
  exact treeOK_facts hLetters_rep h

abbrev repX
    (j : Fin 12) : X := ⟨repN j, (tree_facts j.isLt).r_lt⟩

theorem mem_orbit_iff
    {j : Fin 12} (p : X) :
    p ∈ MulAction.orbit HP (repX j) ↔ ∃ k < hTrees[j.val]!.pts.size, ap hTrees[j.val]!.pts k = p :=
  by
    have := (tree_facts j.isLt).mem_orbit_iff p
    rw [lettersGroup_eq] at this
    exact this

theorem getElem!_map_toList {α β : Type*} [Inhabited α] [Inhabited β] (A : Array α) (f : α → β)
    {j : ℕ} (hj : j < A.size) : (A.toList.map f)[j]! = f A[j]! := by
  rw [getElem!_pos _ j (by simpa using hj), List.getElem_map, Array.getElem_toList,
    getElem!_pos A j hj]

theorem hTrees_size : hTrees.size = 12 := by
  have h := congrArg List.length prim_parts.2.2.2.2.2.2.2.1
  rw [List.length_map, Array.length_toList] at h
  rw [h]
  rfl

theorem card_orbit (j : Fin 12) :
    Nat.card (MulAction.orbit HP (repX j)) = Data.subgroupOrbitSizes[j.val]! := by
  have := (tree_facts j.isLt).card_orbit
  rw [lettersGroup_eq] at this
  rw [this, ← prim_parts.2.2.2.2.2.2.2.1,
    getElem!_map_toList hTrees (fun T => T.pts.size) (by rw [hTrees_size]; exact j.isLt)]

@[expose] def hLab (p : X) : Fin 12 :=
  ⟨hLabs[p.val]!, (prim_parts.2.2.2.2.2.2.2.2.2.1 p p.isLt).1⟩

theorem mem_orbit_hLab
    (p : X) : p ∈ MulAction.orbit HP (repX (hLab p)) := by
  obtain ⟨-, hpos, hpts⟩ := prim_parts.2.2.2.2.2.2.2.2.2.1 p p.isLt
  exact (mem_orbit_iff p).2 ⟨_, hpos, hpts⟩

theorem orbit_rep_inj
    {j k : Fin 12} (h : repX k ∈ MulAction.orbit HP (repX j)) : j = k := by
  by_contra hjk
  obtain ⟨t, ht, hte⟩ := (mem_orbit_iff (repX k)).1 h
  apply prim_parts.2.2.2.2.2.2.2.2.2.2.1 j j.isLt k k.isLt (fun e => hjk (Fin.ext e))
  have hpos := (tree_facts j.isLt).pos_pts t ht
  rw [hte] at hpos
  change ap hTrees[j.val]!.pos (repX k : ℕ) < hTrees[j.val]!.pts.size ∧
    ap hTrees[j.val]!.pts (ap hTrees[j.val]!.pos (repX k : ℕ)) = (repX k : ℕ)
  rw [hpos]
  exact ⟨ht, hte⟩

theorem hLab_eq_of_mem
    {p : X} {j : Fin 12} (hp : p ∈ MulAction.orbit HP (repX j)) :
    hLab p = j := by
  have h1 := mem_orbit_hLab p
  have he : MulAction.orbit HP (repX (hLab p)) = MulAction.orbit HP (repX j) := by
    rw [← MulAction.orbit_eq_iff.2 h1, ← MulAction.orbit_eq_iff.2 hp]
  exact (orbit_rep_inj (he ▸ MulAction.mem_orbit_self (repX (hLab p)))).symm

theorem least_rep
    {j : Fin 12} {p : X} (hp : p ∈ MulAction.orbit HP (repX j)) : repX j ≤ p := by
  obtain ⟨t, ht, hte⟩ := (mem_orbit_iff p).1 hp
  have := prim_parts.2.2.2.2.2.2.2.2.2.2.2.1 j j.isLt t ht
  rw [hte] at this
  exact this

theorem perm_smul_def (g : PH) (x : X) : g • x = (g : Equiv.Perm X) x := rfl

instance ph_pretransitive : MulAction.IsPretransitive PH X := by
  refine MulAction.IsPretransitive.mk fun x y => ?_
  obtain ⟨g, hg⟩ := (hns_pretransitive).exists_smul_eq x y
  exact ⟨jEquivP g, by rw [perm_smul_def, jEquivP_apply, hg]⟩

theorem fix_of_rep {g : Equiv.Perm X} {T : Table} (hT : Rep hnsData.n T g) (h0 : ap T 0 = 0) :
    g x0 = x0 := by
  have hn : 0 < hnsData.n := by rw [hns_n]; norm_num
  have := hT 0 hn
  rw [h0, idx_of_lt _ hn] at this
  exact Fin.ext this.symm

theorem permRegs_fix_zero
    {r : ℕ} (hr : r = 1 ∨ r = 2) : permRegs r x0 = x0 := by
  obtain ⟨-, -, -, -, h0, h1, -⟩ := prim_parts
  rcases hr with rfl | rfl
  · exact fix_of_rep rep_h1 h0
  · exact fix_of_rep rep_h2 h1

theorem HP_fix_zero
    {h : Equiv.Perm X} (hh : h ∈ HP) : h x0 = x0 := by
  induction hh using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with rfl | rfl
    · exact permRegs_fix_zero (Or.inl rfl)
    · exact permRegs_fix_zero (Or.inr rfl)
  | one => rfl
  | mul g h _ _ hg hh => rw [Equiv.Perm.mul_apply, hh, hg]
  | inv g _ hg => rw [Equiv.Perm.inv_eq_iff_eq, hg]

theorem hLab_zero :
    hLab x0 = 0 := hLab_eq_of_mem (by
  have : repX 0 = x0 := Fin.ext rfl
  rw [this]
  exact MulAction.mem_orbit_self x0)

theorem card_fiber (i : Fin 12) :
    (Finset.univ.filter fun p : X => hLab p = i).card = Data.subgroupOrbitSizes[i.val]! := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, ← card_orbit i]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun p =>
    ⟨fun h => h ▸ mem_orbit_hLab p, hLab_eq_of_mem⟩)

theorem ph_preprimitive :
    MulAction.IsPreprimitive PH X := by
  classical
  refine isPreprimitive_of_suborbit_labels x0 (HP.subgroupOf PH) (fun h hh => ?_) hLab
    (fun h hh p => ?_) (fun p q hpq => ?_) (fun S hS hdvd => ?_)
  · rw [Subgroup.mem_subgroupOf] at hh
    exact HP_fix_zero hh
  · rw [Subgroup.mem_subgroupOf] at hh
    apply hLab_eq_of_mem
    exact MulAction.mem_orbit_of_mem_orbit ⟨h, hh⟩ (mem_orbit_hLab p)
  · obtain ⟨⟨u, hu⟩, hu'⟩ := mem_orbit_hLab p
    obtain ⟨⟨v, hv⟩, hv'⟩ := mem_orbit_hLab q
    rw [hpq] at hu'
    refine ⟨⟨v * u⁻¹, HP_le (mul_mem hv (inv_mem hu))⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact mul_mem hv (inv_mem hu)
    · rw [perm_smul_def]
      simp only [Equiv.Perm.mul_apply]
      have hu'' : u (repX (hLab q)) = p := hu'
      have hv'' : v (repX (hLab q)) = q := hv'
      rw [← hu'', Equiv.Perm.coe_inv, Equiv.symm_apply_apply, hv'']
  · rw [hLab_zero] at hS ⊢
    have hsum : (∑ i ∈ S, (Finset.univ.filter (fun p : X => hLab p = i)).card) =
        ∑ i ∈ S, Data.subgroupOrbitSizes[i.val]! := Finset.sum_congr rfl fun i _ => card_fiber i
    rw [hsum, Fintype.card_fin] at hdvd
    exact CFSG.Sporadic.F5.finset_of_divOK prim_parts.2.2.2.2.2.2.2.2.2.2.2.2 (by decide) S hS hdvd

theorem range_pair {α : Type*} (x y : α) : Set.range ![x, y] = {x, y} := by
  ext g
  simp [eq_comm, or_comm]

theorem range_a0_a1 : Set.range ![a0, a1] = {a0, a1} := range_pair a0 a1

theorem closure_range_a0_a1 : Subgroup.closure (Set.range ![a0, a1]) = PH := by
  rw [range_a0_a1]

theorem preprimitive_of_eq
    {K : Subgroup (Equiv.Perm X)} (h : K = PH) :
    MulAction.IsPreprimitive K X := by
  subst h
  exact ph_preprimitive

theorem fam_hn_certified_primitive_action :
    (∀ h ∈ HP, h x0 = x0) ∧
    Data.subgroupOrbitReps = [0, 1, 4, 7, 9, 15, 26, 34, 67, 88, 3542, 95153] ∧
    Data.subgroupOrbitSizes =
      [1, 362880, 166320, 10395, 69300, 166320, 311850, 30800, 16632, 2520, 2520, 462] ∧
    (∀ j : Fin 12, Nat.card (MulAction.orbit HP (repX j)) = Data.subgroupOrbitSizes[j.val]!) ∧
    (∀ p : X, ∃ j : Fin 12, p ∈ MulAction.orbit HP (repX j)) ∧
    (∀ j k : Fin 12, repX k ∈ MulAction.orbit HP (repX j) → j = k) ∧
    (∀ j : Fin 12, ∀ p ∈ MulAction.orbit HP (repX j), repX j ≤ p) ∧
    (∀ j : Fin 12, j ≠ 0 → ∃ L, ValidInvariantMerge ![a0, a1] x0 (repX j) L) ∧
    MulAction.IsPreprimitive PH X := by
  refine ⟨fun h hh => HP_fix_zero hh, by decide, by decide, card_orbit,
    fun p => ⟨_, mem_orbit_hLab p⟩, fun j k h => orbit_rep_inj h, fun j p hp => least_rep hp,
    fun j hj => ?_, ph_preprimitive⟩
  have := preprimitive_of_eq closure_range_a0_a1
  refine exists_validInvariantMerge_of_preprimitive ![a0, a1] x0 (repX j) ?_
  intro h
  apply hj
  have : repX j ∈ MulAction.orbit HP (repX 0) := by
    have e : repX 0 = x0 := Fin.ext rfl
    rw [e, h]
    exact MulAction.mem_orbit_self x0
  exact (orbit_rep_inj this).symm

end CFSG.Sporadic.HNSchreier
