module

public import Certificates.Data.CFSGNative.Perm.Chain
public import CFSG.Sporadic.Th.TableSpec
public import CFSG.Sporadic.Th.GroupTheory

public section

namespace CFSG.Perm

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm.Native

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]

@[expose] def pairG (gs : ℕ → G) (l : ℕ) : G := if l % 2 = 0 then gs (l / 2) else (gs (l / 2))⁻¹

theorem invL_lt {l s : ℕ} (hs : s % 2 = 0) (hl : l < s) : invL l < s := by
  unfold invL; split_ifs <;> omega

theorem pairG_invL (gs : ℕ → G) (l : ℕ) : pairG gs (invL l) = (pairG gs l)⁻¹ := by
  unfold pairG invL
  split_ifs with h1 h2 h3 <;> first | omega | skip
  · have : (l + 1) / 2 = l / 2 := by omega
    rw [this]
  · have : (l - 1) / 2 = l / 2 := by omega
    rw [this, inv_inv]

@[expose] def treeG (T : Tree) (lG : ℕ → G) (k : ℕ) : G :=
  if _h : 0 < k ∧ ap T.par k < k then lG (ap T.lab k) * treeG T lG (ap T.par k) else 1
termination_by k

theorem treeG_zero (T : Tree) (lG : ℕ → G) : treeG T lG 0 = 1 := by
  rw [treeG.eq_def]; simp

@[expose] def WalkFacts (n : ℕ) [MulAction G (Fin n)] (T : Tree) (letters : Array Table)
    (lG : ℕ → G) : Prop :=
  ∀ k < T.pts.size, 0 < k → ap T.par k < k ∧ Rep n letters[ap T.lab k]! (lG (ap T.lab k)) ∧
    Rep n letters[invL (ap T.lab k)]! (lG (ap T.lab k))⁻¹

theorem walk_spec {T : Tree} {letters : Array Table} {lG : ℕ → G} (hW : WalkFacts n T letters lG)
    {k : ℕ} (hk : k < T.pts.size) (q : Array ℕ) (hq : ∀ j < q.size, q[j]! < n) :
    (walk T letters k q).size = q.size ∧
      ∀ j < q.size, (walk T letters k q)[j]! = idx n (treeG T lG k) q[j]! := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [walk.eq_def, treeG.eq_def]
    split_ifs with hg
    · obtain ⟨-, hr, -⟩ := hW k hk hg.1
      obtain ⟨hs, he⟩ := ih _ hg.2 (lt_trans hg.2 hk)
      refine ⟨by rw [apT_size, hs], fun j hj => ?_⟩
      rw [apT_get _ _ (by rwa [hs]), he j hj, hr _ (idx_lt _ (hq j hj)), idx_mul]
    · exact ⟨rfl, fun j _ => by rw [idx_one]⟩

theorem walkInv_spec {T : Tree} {letters : Array Table} {lG : ℕ → G}
    (hW : WalkFacts n T letters lG) {k : ℕ} (hk : k < T.pts.size) (q : Array ℕ)
    (hq : ∀ j < q.size, q[j]! < n) :
    (walkInv T letters k q).size = q.size ∧
      ∀ j < q.size, (walkInv T letters k q)[j]! = idx n (treeG T lG k)⁻¹ q[j]! := by
  induction k using Nat.strong_induction_on generalizing q with
  | _ k ih =>
    rw [walkInv.eq_def, treeG.eq_def]
    split_ifs with hg
    · obtain ⟨-, -, hr⟩ := hW k hk hg.1
      have hq' : ∀ j < (apT letters[invL (ap T.lab k)]! q).size,
          (apT letters[invL (ap T.lab k)]! q)[j]! < n := by
        intro j hj
        rw [apT_size] at hj
        rw [apT_get _ _ hj, hr _ (hq j hj)]
        exact idx_lt _ (hq j hj)
      obtain ⟨hs, he⟩ := ih _ hg.2 (lt_trans hg.2 hk) _ hq'
      refine ⟨by rw [hs, apT_size], fun j hj => ?_⟩
      rw [he j (by rwa [apT_size]), apT_get _ _ hj, hr _ (hq j hj), ← idx_mul, mul_inv_rev]
    · exact ⟨rfl, fun j _ => by rw [inv_one, idx_one]⟩

structure TreeFacts (n : ℕ) [MulAction G (Fin n)] (T : Tree) (lv : Array ℕ) (lG : ℕ → G)
    (r : ℕ) : Prop where
  size_pos : 0 < T.pts.size
  root : ap T.pts 0 = r
  pts_lt : ∀ k < T.pts.size, ap T.pts k < n
  pos_pts : ∀ k < T.pts.size, ap T.pos (ap T.pts k) = k
  closed : ∀ k < T.pts.size, ∀ l ∈ lv, ap T.pos (idx n (lG l) (ap T.pts k)) < T.pts.size ∧
    ap T.pts (ap T.pos (idx n (lG l) (ap T.pts k))) = idx n (lG l) (ap T.pts k)
  par : ∀ k < T.pts.size, 0 < k → ap T.par k < k ∧ ap T.lab k ∈ lv
  elt : ∀ k < T.pts.size, idx n (treeG T lG k) r = ap T.pts k

theorem treeOK_facts {T : Tree} {letters : Array Table} {lv : Array ℕ} {lG : ℕ → G} {r : ℕ}
    (hrep : ∀ l ∈ lv, Rep n letters[l]! (lG l)) (h : Perm.Native.treeOK n r T letters lv = true) :
    TreeFacts n T lv lG r := by
  simp only [Perm.Native.treeOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hm, h0⟩, hall⟩ := h
  have hk : ∀ k < T.pts.size, treeAt n T letters lv k = true := fun k hk =>
    (allIn_eq_true.1 hall) k (Nat.zero_le _) hk
  have hat : ∀ k < T.pts.size, ap T.pts k < n ∧ ap T.pos (ap T.pts k) = k ∧
      (∀ l ∈ lv, ap T.pos (ap letters[l]! (ap T.pts k)) < T.pts.size ∧
        ap T.pts (ap T.pos (ap letters[l]! (ap T.pts k))) = ap letters[l]! (ap T.pts k)) ∧
      (k = 0 ∨ (ap T.par k < k ∧ ap T.lab k ∈ lv ∧
        ap letters[ap T.lab k]! (ap T.pts (ap T.par k)) = ap T.pts k)) := by
    intro k hkm
    have := hk k hkm
    simp only [treeAt, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Array.all_eq_true,
      Bool.or_eq_true, Array.contains_iff_mem] at this
    obtain ⟨⟨⟨hlt, hpos⟩, hcl⟩, hpar⟩ := this
    refine ⟨hlt, hpos, fun l hl => ?_, ?_⟩
    · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hl
      have := hcl i hi
      simpa using this
    · rcases hpar with h | ⟨⟨h1, h2⟩, h3⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, h2, h3⟩
  have hcl : ∀ k < T.pts.size, ∀ l ∈ lv, ap T.pos (idx n (lG l) (ap T.pts k)) < T.pts.size ∧
      ap T.pts (ap T.pos (idx n (lG l) (ap T.pts k))) = idx n (lG l) (ap T.pts k) := by
    intro k hkm l hl
    rw [← hrep l hl _ (hat k hkm).1]
    exact (hat k hkm).2.2.1 l hl
  have hpar : ∀ k < T.pts.size, 0 < k → ap T.par k < k ∧ ap T.lab k ∈ lv := by
    intro k hkm hk0
    rcases (hat k hkm).2.2.2 with h | h
    · omega
    · exact ⟨h.1, h.2.1⟩
  refine ⟨hm, h0, fun k hkm => (hat k hkm).1, fun k hkm => (hat k hkm).2.1, hcl, hpar, ?_⟩
  intro k hkm
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [treeG.eq_def]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [idx_one, h0]
    · obtain ⟨hpk, hlab⟩ := hpar k hkm hk0
      rw [dite_eq_left ⟨hk0, hpk⟩, idx_mul, ih _ hpk (lt_trans hpk hkm)]
      rcases (hat k hkm).2.2.2 with h | ⟨-, -, he⟩
      · omega
      · rw [← hrep _ hlab _ ((hat _ (lt_trans hpk hkm)).1), he]

section Facts

variable {T : Tree} {lv : Array ℕ} {lG : ℕ → G} {r : ℕ}

@[expose] def lettersGroup (lv : Array ℕ) (lG : ℕ → G) : Subgroup G :=
  Subgroup.closure {g | ∃ l ∈ lv, lG l = g}

theorem lG_mem {lv : Array ℕ} {lG : ℕ → G} {l : ℕ} (hl : l ∈ lv) : lG l ∈ lettersGroup lv lG :=
  Subgroup.subset_closure ⟨l, hl, rfl⟩

theorem TreeFacts.r_lt (hT : TreeFacts n T lv lG r) : r < n := by
  rw [← hT.root]; exact hT.pts_lt 0 hT.size_pos

theorem TreeFacts.treeG_mem (hT : TreeFacts n T lv lG r) {k : ℕ} (hk : k < T.pts.size) :
    treeG T lG k ∈ lettersGroup lv lG := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [treeG.eq_def]
    split_ifs with hg
    · exact (lettersGroup lv lG).mul_mem (lG_mem (hT.par k hk hg.1).2)
        (ih _ hg.2 (lt_trans hg.2 hk))
    · exact (lettersGroup lv lG).one_mem

theorem smul_val_eq_idx (g : G) (p : Fin n) : (g • p).val = idx n g p.val := by
  rw [idx_of_lt g p.isLt]

theorem TreeFacts.mem_orbit_iff (hT : TreeFacts n T lv lG r) (p : Fin n) :
    p ∈ MulAction.orbit (lettersGroup lv lG) (⟨r, hT.r_lt⟩ : Fin n) ↔
      ∃ k < T.pts.size, ap T.pts k = p.val := by
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    let S : Set (Fin n) := {q | ∃ k < T.pts.size, ap T.pts k = q.val}
    have hstep : ∀ l ∈ lv, ∀ q ∈ S, lG l • q ∈ S := by
      rintro l hl q ⟨k, hk, hkq⟩
      refine ⟨ap T.pos (idx n (lG l) (ap T.pts k)), (hT.closed k hk l hl).1, ?_⟩
      rw [(hT.closed k hk l hl).2, smul_val_eq_idx, hkq]
    have hfin : ∀ x : G, (∀ q ∈ S, x • q ∈ S) → ∀ q ∈ S, x⁻¹ • q ∈ S := by
      intro x hx
      have hmaps : Set.MapsTo (fun q => x • q) S S := fun q hq => hx q hq
      have hinj : Set.InjOn (fun q => x • q) S := fun a _ b _ hab => smul_left_cancel x hab
      have hsurj := (Set.Finite.injOn_iff_bijOn_of_mapsTo (Set.toFinite S) hmaps).1 hinj
      intro q hq
      obtain ⟨q', hq', hq'e⟩ := hsurj.2.2 hq
      simp only at hq'e
      rw [← hq'e, inv_smul_smul]
      exact hq'
    have hall : ∀ x ∈ lettersGroup lv lG, ∀ q ∈ S, x • q ∈ S := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨l, hl, rfl⟩ := hx
        exact hstep l hl
      | one => intro q hq; rwa [one_smul]
      | mul x y _ _ hx hy => intro q hq; rw [mul_smul]; exact hx _ (hy q hq)
      | inv x _ hx => exact hfin x hx
    have hr : (⟨r, hT.r_lt⟩ : Fin n) ∈ S := ⟨0, hT.size_pos, hT.root⟩
    exact hall g hg _ hr
  · rintro ⟨k, hk, hkp⟩
    refine ⟨⟨treeG T lG k, hT.treeG_mem hk⟩, ?_⟩
    apply Fin.ext
    show ((treeG T lG k) • (⟨r, hT.r_lt⟩ : Fin n)).val = p.val
    rw [smul_val_eq_idx, hT.elt k hk, hkp]

theorem TreeFacts.pts_inj (hT : TreeFacts n T lv lG r) {j k : ℕ} (hj : j < T.pts.size)
    (hk : k < T.pts.size) (h : ap T.pts j = ap T.pts k) : j = k := by
  rw [← hT.pos_pts j hj, ← hT.pos_pts k hk, h]

theorem TreeFacts.card_orbit (hT : TreeFacts n T lv lG r) :
    Nat.card (MulAction.orbit (lettersGroup lv lG) (⟨r, hT.r_lt⟩ : Fin n)) = T.pts.size := by
  classical
  have hset : MulAction.orbit (lettersGroup lv lG) (⟨r, hT.r_lt⟩ : Fin n) =
      (Finset.univ.filter fun p : Fin n => ∃ k < T.pts.size, ap T.pts k = p.val : Finset _) := by
    ext p
    rw [hT.mem_orbit_iff]
    simp
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  refine Eq.trans ?_ (Finset.card_range T.pts.size)
  apply Finset.card_bij (fun p _ => ap T.pos p.val)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨k, hk, hkp⟩ := hp
    simp only [Finset.mem_range]
    rw [← hkp, hT.pos_pts k hk]
    exact hk
  · intro p hp q hq hpq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    obtain ⟨j, hj, hjp⟩ := hp
    obtain ⟨k, hk, hkq⟩ := hq
    rw [← hjp, ← hkq, hT.pos_pts j hj, hT.pos_pts k hk] at hpq
    subst hpq
    exact Fin.ext (hjp.symm.trans hkq)
  · intro k hk
    simp only [Finset.mem_range] at hk
    refine ⟨⟨ap T.pts k, hT.pts_lt k hk⟩, ?_, hT.pos_pts k hk⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨k, hk, rfl⟩

theorem TreeFacts.stab_le (hT : TreeFacts n T lv lG r) (K : Subgroup G)
    (hK : ∀ k < T.pts.size, ∀ l ∈ lv,
      (treeG T lG (ap T.pos (idx n (lG l) (ap T.pts k))))⁻¹ * lG l * treeG T lG k ∈ K) :
    ∀ g ∈ lettersGroup lv lG, idx n g r = r → g ∈ K := by
  intro g hg hfix
  set H := lettersGroup lv lG with hHdef
  set r' : Fin n := ⟨r, hT.r_lt⟩ with hr'
  let X := MulAction.orbit H r'
  let x₀ : X := ⟨r', MulAction.mem_orbit_self r'⟩
  have hpos : ∀ q : X, ap T.pos q.val.val < T.pts.size ∧ ap T.pts (ap T.pos q.val.val) =
      q.val.val := by
    intro q
    obtain ⟨k, hk, hkq⟩ := (hT.mem_orbit_iff q.val).1 q.property
    rw [← hkq, hT.pos_pts k hk]
    exact ⟨hk, rfl⟩
  let t : X → H := fun q => ⟨treeG T lG (ap T.pos q.val.val), hT.treeG_mem (hpos q).1⟩
  have ht : ∀ q, t q • x₀ = q := by
    intro q
    apply Subtype.ext
    apply Fin.ext
    show ((treeG T lG (ap T.pos q.val.val)) • r').val = q.val.val
    rw [smul_val_eq_idx, hT.elt _ (hpos q).1, (hpos q).2]
  have ht1 : t x₀ = 1 := by
    apply Subtype.ext
    show treeG T lG (ap T.pos r) = 1
    have : ap T.pos r = 0 := by rw [← hT.root, hT.pos_pts 0 hT.size_pos]
    rw [this, treeG_zero]
  let S : Set H := ((↑) : H → G) ⁻¹' {g | ∃ l ∈ lv, lG l = g}
  have hS : Subgroup.closure S = ⊤ := Subgroup.closure_closure_coe_preimage
  have hstab := stabilizer_le_of_schreier_mem x₀ hS (K.subgroupOf H) t ht ht1 (by
    rintro s ⟨l, hl, hs⟩ q
    replace hs := hs.symm
    rw [Subgroup.mem_subgroupOf]
    have hsq : ((s • q : X) : Fin n).val = idx n (lG l) (ap T.pts (ap T.pos q.val.val)) := by
      show ((s : G) • (q.val : Fin n)).val = _
      rw [smul_val_eq_idx, hs, (hpos q).2]
    show (treeG T lG (ap T.pos ((s • q : X) : Fin n).val))⁻¹ * (s : G) *
      treeG T lG (ap T.pos q.val.val) ∈ K
    rw [hsq, hs]
    exact hK _ (hpos q).1 l hl)
  have hgx : (⟨g, hg⟩ : H) ∈ MulAction.stabilizer H x₀ := by
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    apply Fin.ext
    show (g • r').val = r'.val
    rw [smul_val_eq_idx]
    exact hfix
  exact Subgroup.mem_subgroupOf.1 (hstab hgx)

end Facts

section Sift

variable {letters : Array Table} {lG : ℕ → G} {trees : Array Tree} {qb Q : Array ℕ}

theorem sift_mem (hsep : ∀ g : G, (∀ t < Q.size, idx n g Q[t]! = Q[t]!) → g = 1)
    (hQ : ∀ t < Q.size, Q[t]! < n) (K : Subgroup G) :
    ∀ (d l : ℕ), trees.size - l = d →
      (∀ l' < trees.size, l ≤ l' → WalkFacts n trees[l']! letters lG ∧
        ∀ k < trees[l']!.pts.size, treeG trees[l']! lG k ∈ K) →
      ∀ (g : G) (img : Array ℕ), img.size = Q.size →
        (∀ t < Q.size, img[t]! = idx n g Q[t]!) →
        sift trees letters qb Q l img = true → g ∈ K := by
  intro d
  induction d with
  | zero =>
    intro l hd _ g img hsz himg hs
    rw [sift.eq_def] at hs
    rw [dite_eq_right (by omega)] at hs
    simp only [tupleEq, Bool.and_eq_true, beq_iff_eq] at hs
    have hfix : ∀ t < Q.size, idx n g Q[t]! = Q[t]! := by
      intro t ht
      rw [← himg t ht]
      have := (allIn_eq_true.1 hs.2) t (Nat.zero_le _) ht
      simpa using this
    rw [hsep g hfix]
    exact K.one_mem
  | succ d ih =>
    intro l hd hlev g img hsz himg hs
    have hl : l < trees.size := by omega
    rw [sift.eq_def, dite_eq_left hl] at hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨hk, hrest⟩ := hs
    obtain ⟨hW, hmem⟩ := hlev l hl le_rfl
    rw [getElem!_pos trees l hl] at hW hmem
    have himgn : ∀ t < img.size, img[t]! < n := by
      intro t ht
      rw [hsz] at ht
      rw [himg t ht]
      exact idx_lt _ (hQ t ht)
    obtain ⟨hs', he'⟩ := walkInv_spec (lG := lG) hW hk img himgn
    have hg' := ih (l + 1) (by omega)
      (fun l' hl' hll' => hlev l' hl' (by omega)) ((treeG trees[l] lG
        (ap trees[l].pos img[qb[l]!]!))⁻¹ * g) _ (by rw [hs', hsz])
      (fun t ht => by rw [he' t (by rwa [hsz]), himg t ht, idx_mul]) hrest
    have := K.mul_mem (hmem _ hk) hg'
    rwa [mul_inv_cancel_left] at this

end Sift

section Levels

variable {letters : Array Table} {base : Array ℕ}

theorem mem_levelLetters_zero {l : ℕ} : l ∈ levelLetters letters base 0 ↔ l < letters.size := by
  simp [levelLetters]

theorem mem_levelLetters_succ {i l : ℕ} : l ∈ levelLetters letters base (i + 1) ↔
    l ∈ levelLetters letters base i ∧ ap letters[l]! base[i]! = base[i]! := by
  simp [levelLetters, Array.mem_filter]

theorem levelLetters_lt {i l : ℕ} (h : l ∈ levelLetters letters base i) : l < letters.size := by
  induction i with
  | zero => exact mem_levelLetters_zero.1 h
  | succ i ih => exact ih (mem_levelLetters_succ.1 h).1

theorem levelLetters_anti {i j l : ℕ} (hij : i ≤ j) (h : l ∈ levelLetters letters base j) :
    l ∈ levelLetters letters base i := by
  induction j with
  | zero => obtain rfl : i = 0 := by omega
            exact h
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · exact h
    · exact ih (by omega) (mem_levelLetters_succ.1 h).1

@[expose] def levelGroup (letters : Array Table) (base : Array ℕ) (lG : ℕ → G) (i : ℕ) :
    Subgroup G :=
  lettersGroup (levelLetters letters base i) lG

theorem levelGroup_anti (lG : ℕ → G) {i j : ℕ} (hij : i ≤ j) :
    levelGroup letters base lG j ≤ levelGroup letters base lG i := by
  unfold levelGroup lettersGroup
  apply Subgroup.closure_mono
  rintro _ ⟨l, hl, rfl⟩
  exact ⟨l, levelLetters_anti hij hl, rfl⟩

end Levels

theorem card_eq_orbit_mul {X : Type*} [MulAction G X] (H L : Subgroup G) (p : X) (hLH : L ≤ H)
    (hLp : ∀ l ∈ L, l • p = p) (hHp : ∀ h ∈ H, h • p = p → h ∈ L) [Finite H] :
    Nat.card H = Nat.card (MulAction.orbit H p) * Nat.card L := by
  have hstabH : MulAction.stabilizer H p = L.subgroupOf H := by
    ext h
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    exact ⟨fun hh => hHp h h.2 hh, fun hh => hLp h hh⟩
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer H p)
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq, hstabH,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLH).toEquiv] at h1
  rw [← h1, mul_comm]

section Chain

variable {letters : Array Table} {gs : ℕ → G} {base Q qb : Array ℕ} {trees : Array Tree}
  {chunks : ℕ}

theorem chainOK_parts (h : chainOK n letters base Q qb trees chunks = true) :
    letters.size % 2 = 0 ∧
      (∀ j < letters.size / 2, invOK n letters[2 * j]! letters[2 * j + 1]! = true) ∧
      trees.size = base.size ∧ qb.size = base.size ∧ (∀ t < Q.size, Q[t]! < n) ∧
      (∀ i < base.size, qb[i]! < Q.size ∧ Q[qb[i]!]! = base[i]!) ∧
      (∀ i < base.size, Perm.Native.treeOK n base[i]! trees[i]! letters
        (levelLetters letters base i) = true) ∧
      (∀ i < base.size, ∀ l ∈ levelLetters letters base i, ∀ k < trees[i]!.pts.size,
        schreierAt trees letters qb Q i l k = true) ∧
      (∀ l ∈ levelLetters letters base base.size, tupleEq (apT letters[l]! Q) Q = true) := by
  simp only [chainOK, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h10⟩ := h
  refine ⟨h1, fun j hj => (allIn_eq_true.1 h2) j (Nat.zero_le _) hj, h3, h4,
    fun t ht => by simpa using (allIn_eq_true.1 h5) t (Nat.zero_le _) ht,
    fun i hi => by simpa using (allIn_eq_true.1 h6) i (Nat.zero_le _) hi,
    fun i hi => (allIn_eq_true.1 h7) i (Nat.zero_le _) hi, ?_, ?_⟩
  · intro i hi l hl k hk
    have := (allIn_eq_true.1 h8) i (Nat.zero_le _) hi
    simp only [Array.all_eq_true] at this
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 hl
    exact parAll_eq_true (this j hj) k hk
  · intro l hl
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 hl
    exact h10 j hj

theorem rep_pairG (hrep : ∀ j < letters.size / 2, Rep n letters[2 * j]! (gs j))
    (h2 : letters.size % 2 = 0)
    (hinv : ∀ j < letters.size / 2, invOK n letters[2 * j]! letters[2 * j + 1]! = true) :
    ∀ l < letters.size, Rep n letters[l]! (pairG gs l) := by
  intro l hl
  have hj : l / 2 < letters.size / 2 := by omega
  unfold pairG
  split_ifs with hl2
  · have e : letters[l]! = letters[2 * (l / 2)]! := by congr 1; omega
    rw [e]
    exact hrep _ hj
  · have e : letters[l]! = letters[2 * (l / 2) + 1]! := by congr 1; omega
    rw [e]
    exact Rep.inv_of_invOK (hrep _ hj) (hinv _ hj)

theorem chain_facts [Finite G] (hrep : ∀ j < letters.size / 2, Rep n letters[2 * j]! (gs j))
    (hsep : ∀ g : G, (∀ t < Q.size, idx n g Q[t]! = Q[t]!) → g = 1)
    (h : chainOK n letters base Q qb trees chunks = true) :
    (∀ i < base.size, TreeFacts n trees[i]! (levelLetters letters base i) (pairG gs) base[i]!) ∧
      (∀ i < base.size, ∀ g ∈ levelGroup letters base (pairG gs) i,
        idx n g base[i]! = base[i]! ↔ g ∈ levelGroup letters base (pairG gs) (i + 1)) ∧
      ∀ i ≤ base.size, Nat.card (levelGroup letters base (pairG gs) i) =
        ∏ l ∈ Finset.Ico i base.size, trees[l]!.pts.size := by
  obtain ⟨h2, hinv, htrees, hqb, hQ, hqbQ, htree, hsch, hterm⟩ := chainOK_parts h
  set lG := pairG gs with hlG
  set m := base.size with hm
  have hrepAll := rep_pairG hrep h2 hinv
  have hlvRep : ∀ i, ∀ l ∈ levelLetters letters base i, Rep n letters[l]! (lG l) :=
    fun i l hl => hrepAll l (levelLetters_lt hl)
  have hTF : ∀ i < m, TreeFacts n trees[i]! (levelLetters letters base i) lG base[i]! :=
    fun i hi => treeOK_facts (hlvRep i) (htree i hi)
  have hWF : ∀ i < m, WalkFacts n trees[i]! letters lG := by
    intro i hi k hk hk0
    obtain ⟨hpar, hlab⟩ := (hTF i hi).par k hk hk0
    have hl := levelLetters_lt hlab
    refine ⟨hpar, hrepAll _ hl, ?_⟩
    rw [← pairG_invL]
    exact hrepAll _ (invL_lt h2 hl)
  have hTreeMem : ∀ i < m, ∀ k < trees[i]!.pts.size,
      treeG trees[i]! lG k ∈ levelGroup letters base lG i :=
    fun i hi k hk => (hTF i hi).treeG_mem hk
  have hSch : ∀ i < m, ∀ k < trees[i]!.pts.size, ∀ l ∈ levelLetters letters base i,
      (treeG trees[i]! lG (ap trees[i]!.pos (idx n (lG l) (ap trees[i]!.pts k))))⁻¹ * lG l *
        treeG trees[i]! lG k ∈ levelGroup letters base lG (i + 1) := by
    intro i hi k hk l hl
    have hs := hsch i hi l hl k hk
    simp only [schreierAt, Bool.and_eq_true, decide_eq_true_eq] at hs
    have hpk : ap trees[i]!.pts k < n := (hTF i hi).pts_lt k hk
    have hrl := hlvRep i l hl
    rw [hrl _ hpk] at hs
    obtain ⟨hky, hsift⟩ := hs
    obtain ⟨hs0, he0⟩ := walk_spec (lG := lG) (hWF i hi) hk Q hQ
    set img0 := walk trees[i]! letters k Q
    have hn0 : ∀ j < img0.size, img0[j]! < n := by
      intro j hj
      rw [hs0] at hj
      rw [he0 j hj]
      exact idx_lt _ (hQ j hj)
    have hn1 : ∀ j < (apT letters[l]! img0).size, (apT letters[l]! img0)[j]! < n := by
      intro j hj
      rw [apT_size] at hj
      rw [apT_get _ _ hj, hrl _ (hn0 j hj)]
      exact idx_lt _ (hn0 j hj)
    obtain ⟨hs2, he2⟩ := walkInv_spec (lG := lG) (hWF i hi) hky _ hn1
    refine sift_mem (lG := lG) hsep hQ _ (trees.size - (i + 1)) (i + 1) rfl ?_ _ _
      (by rw [hs2, apT_size, hs0])
      ?_ hsift
    · intro l' hl' hil'
      have hl'm : l' < m := by rw [htrees] at hl'; exact hl'
      exact ⟨hWF l' hl'm, fun k hk => levelGroup_anti lG hil' (hTreeMem l' hl'm k hk)⟩
    · intro t ht
      rw [he2 t (by rwa [apT_size, hs0]), apT_get _ _ (by rwa [hs0]), hrl _ (hn0 t (by rwa [hs0])),
        he0 t ht, ← idx_mul, ← idx_mul]
  have hstab : ∀ i < m, ∀ g ∈ levelGroup letters base lG i, idx n g base[i]! = base[i]! →
      g ∈ levelGroup letters base lG (i + 1) := fun i hi =>
    (hTF i hi).stab_le _ fun k hk l hl => hSch i hi k hk l hl
  have hfixb : ∀ i < m, ∀ g ∈ levelGroup letters base lG (i + 1), idx n g base[i]! = base[i]! := by
    intro i hi g hg
    have hb : base[i]! < n := (hTF i hi).r_lt
    unfold levelGroup lettersGroup at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      obtain ⟨hl', hfix⟩ := mem_levelLetters_succ.1 hl
      rw [← hlvRep i l hl' _ hb, hfix]
    | one => exact idx_one _
    | mul x y _ _ hx hy => rw [idx_mul, hy, hx]
    | inv x _ hx => rw [← hx, idx_inv_idx, hx]
  have hbot : levelGroup letters base lG m = ⊥ := by
    rw [eq_bot_iff]
    unfold levelGroup lettersGroup
    rw [Subgroup.closure_le]
    rintro _ ⟨l, hl, rfl⟩
    have ht := hterm l hl
    simp only [tupleEq, Bool.and_eq_true, beq_iff_eq, apT_size] at ht
    apply hsep
    intro t htQ
    have := (allIn_eq_true.1 ht.2) t (Nat.zero_le _) htQ
    simp only [beq_iff_eq] at this
    rw [apT_get _ _ htQ, hrepAll l (levelLetters_lt hl) _ (hQ t htQ)] at this
    exact this
  refine ⟨hTF, fun i hi g hg => ⟨hstab i hi g hg, hfixb i hi g⟩, ?_⟩
  intro i hi
  induction h' : m - i generalizing i with
  | zero =>
    obtain rfl : i = m := by omega
    rw [hbot, Subgroup.card_bot, Finset.Ico_self, Finset.prod_empty]
  | succ d ih =>
    have him : i < m := by omega
    have hcard := card_eq_orbit_mul (levelGroup letters base lG i)
      (levelGroup letters base lG (i + 1)) (⟨base[i]!, (hTF i him).r_lt⟩ : Fin n)
      (levelGroup_anti lG (Nat.le_succ i))
      (fun g hg => Fin.ext (by rw [smul_val_eq_idx]; exact hfixb i him g hg))
      (fun g hg hfix => hstab i him g hg (by
        have := congrArg Fin.val hfix; rwa [smul_val_eq_idx] at this))
    rw [hcard, ih (i + 1) (by omega) (by omega), Finset.prod_eq_prod_Ico_succ_bot him]
    congr 1
    exact (hTF i him).card_orbit

end Chain


end CFSG.Perm
