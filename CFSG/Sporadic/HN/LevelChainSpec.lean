module

public import Certificates.Data.CFSGNative.HN.LevelChain
public import CFSG.Perm.ChainSpec
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Sporadic.LevelChain

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.LevelChain.Native

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]

theorem levelLv_size (starts : Array ℕ) (i : ℕ) :
    (levelLv starts i).size = 2 * (starts[i + 1]! - starts[i]!) := by
  simp [levelLv]

theorem mem_levelLv {starts : Array ℕ} {i : ℕ} (hle : starts[i]! ≤ starts[i + 1]!) {l : ℕ} :
    l ∈ levelLv starts i ↔ 2 * starts[i]! ≤ l ∧ l < 2 * starts[i + 1]! := by
  unfold levelLv
  rw [Array.mem_ofFn]
  constructor
  · rintro ⟨t, rfl⟩
    have := t.isLt
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨⟨l - 2 * starts[i]!, by omega⟩, by simp only; omega⟩

@[expose] def lvlGroup (starts : Array ℕ) (gs : ℕ → G) (i : ℕ) : Subgroup G :=
  lettersGroup (levelLv starts i) (pairG gs)

theorem gs_mem_lvlGroup {starts : Array ℕ} (gs : ℕ → G) {i j : ℕ} (hj1 : starts[i]! ≤ j)
    (hj2 : j < starts[i + 1]!) : gs j ∈ lvlGroup starts gs i := by
  have h : pairG gs (2 * j) = gs j := by simp [pairG]
  rw [← h]
  exact lG_mem ((mem_levelLv (by omega)).2 ⟨by omega, by omega⟩)

theorem lvlGroup_le {starts : Array ℕ} (gs : ℕ → G) {i : ℕ} (K : Subgroup G)
    (hK : ∀ j, starts[i]! ≤ j → j < starts[i + 1]! → gs j ∈ K) : lvlGroup starts gs i ≤ K := by
  unfold lvlGroup lettersGroup
  rw [Subgroup.closure_le]
  rintro _ ⟨l, hl, rfl⟩
  have hl' : l ∈ levelLv starts i := hl
  unfold levelLv at hl'
  rw [Array.mem_ofFn] at hl'
  obtain ⟨t, rfl⟩ := hl'
  have ht := t.isLt
  unfold pairG
  split_ifs with h2
  · exact hK _ (by omega) (by omega)
  · exact K.inv_mem (hK _ (by omega) (by omega))

theorem lvlGroup_eq_bot_of_le {starts : Array ℕ} (gs : ℕ → G) {i : ℕ}
    (h : starts[i + 1]! ≤ starts[i]!) : lvlGroup starts gs i = ⊥ := by
  rw [eq_bot_iff]
  exact lvlGroup_le gs ⊥ fun j hj1 hj2 => absurd hj2 (by omega)

theorem iterAp_eq {L : Table} {g : G} (hL : Rep n L g) {x : ℕ} (hx : x < n) :
    ∀ i, iterAp L i x = idx n (g ^ i) x
  | 0 => by rw [pow_zero, idx_one]; rfl
  | i + 1 => by
    show ap L (iterAp L i x) = _
    rw [iterAp_eq hL hx i, hL _ (idx_lt _ hx), pow_succ', idx_mul]

theorem repeat_apT {L : Table} {g : G} (hL : Rep n L g) (Q : Array ℕ)
    (hQ : ∀ t < Q.size, Q[t]! < n) :
    ∀ e, (Nat.repeat (apT L) e Q).size = Q.size ∧
      ∀ t < Q.size, (Nat.repeat (apT L) e Q)[t]! = idx n (g ^ e) Q[t]!
  | 0 => ⟨rfl, fun t _ => by simp [Nat.repeat, idx_one]⟩
  | e + 1 => by
    obtain ⟨hs, he⟩ := repeat_apT hL Q hQ e
    refine ⟨by simp only [Nat.repeat]; rw [apT_size, hs], fun t ht => ?_⟩
    simp only [Nat.repeat]
    rw [apT_get _ _ (by rw [hs]; exact ht), he t ht, hL _ (idx_lt _ (hQ t ht)), pow_succ', idx_mul]

theorem pow_eq_one_of_powFixes {L : Table} {g : G} (hL : Rep n L g) {Q : Array ℕ}
    (hQ : ∀ t < Q.size, Q[t]! < n) (hsep : ∀ g : G, (∀ t < Q.size, idx n g Q[t]! = Q[t]!) → g = 1)
    {e : ℕ} (h : powFixes L e Q = true) : g ^ e = 1 := by
  apply hsep
  intro t ht
  obtain ⟨hs, he⟩ := repeat_apT hL Q hQ e
  unfold powFixes tupleEq at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have := (allIn_eq_true.1 h.2) t (Nat.zero_le _) ht
  rw [beq_iff_eq, he t ht] at this
  exact this

@[expose] def schreierG (T : Tree) (lG : ℕ → G) (l k : ℕ) : G :=
  (treeG T lG (ap T.pos (idx n (lG l) (ap T.pts k))))⁻¹ * lG l * treeG T lG k

theorem treeG_succ (T : Tree) (lG : ℕ → G) {k : ℕ} (hk : 0 < k) (hp : ap T.par k < k) :
    treeG T lG k = lG (ap T.lab k) * treeG T lG (ap T.par k) := by
  rw [treeG.eq_def, dite_eq_left ⟨hk, hp⟩]

theorem schreier_eq_one_of_treeEdge {T : Tree} {letters : Array Table} {gs : ℕ → G} {lv : Array ℕ}
    {r : ℕ} (hT : TreeFacts n T lv (pairG gs) r) {j : ℕ} (hs : Rep n letters[2 * j]! (gs j))
    {invo : Bool} (hinvo : invo = true → gs j * gs j = 1) {k : ℕ} (hk : k < T.pts.size)
    (h : edgeTriv T letters (2 * j) invo k = true) :
    schreierG (n := n) T (pairG gs) (2 * j) k = 1 := by
  have hpk : ap T.pts k < n := hT.pts_lt k hk
  have hl : pairG gs (2 * j) = gs j := by simp [pairG]
  have hl1 : pairG gs (2 * j + 1) = (gs j)⁻¹ := by
    simp only [pairG]; rw [ite_eq_right (by omega)]; congr 2; omega
  unfold edgeTriv at h
  rw [hs _ hpk] at h
  unfold schreierG
  rw [hl]
  set ky := ap T.pos (idx n (gs j) (ap T.pts k)) with hky
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rcases h with ⟨⟨⟨h0, hlt⟩, hpar⟩, hlab⟩ | ⟨⟨hk0, hpar⟩, hlab⟩
  · rw [treeG_succ T _ h0 ((hT.par ky hlt h0).1), hpar, hlab, hl]
    group
  · have hpk' := (hT.par k hk hk0).1
    rw [treeG_succ T _ hk0 hpk', hpar]
    rcases hlab with hlab | ⟨hinv, hlab⟩
    · rw [hlab, hl1]; group
    · rw [hlab, hl]
      have h1 := hinvo hinv
      have : gs j = (gs j)⁻¹ := eq_inv_of_mul_eq_one_left h1
      calc (treeG T (pairG gs) ky)⁻¹ * gs j * (gs j * treeG T (pairG gs) ky)
          = (treeG T (pairG gs) ky)⁻¹ * gs j * ((gs j)⁻¹ * treeG T (pairG gs) ky) := by
            rw [← this]
        _ = 1 := by group

theorem schreier_mem_of_schreierAt {trees : Array Tree} {letters : Array Table} {lG : ℕ → G}
    {qb Q : Array ℕ} (hsep : ∀ g : G, (∀ t < Q.size, idx n g Q[t]! = Q[t]!) → g = 1)
    (hQ : ∀ t < Q.size, Q[t]! < n) (K : Subgroup G) {i : ℕ} (hi : i < trees.size)
    {lv : Array ℕ} {r : ℕ} (hT : TreeFacts n trees[i]! lv lG r)
    (hW : ∀ l' < trees.size, WalkFacts n trees[l']! letters lG)
    (hdeep : ∀ l' < trees.size, i + 1 ≤ l' → ∀ k < trees[l']!.pts.size, treeG trees[l']! lG k ∈ K)
    {l : ℕ} (hrl : Rep n letters[l]! (lG l)) {k : ℕ} (hk : k < trees[i]!.pts.size)
    (h : schreierAt trees letters qb Q i l k = true) :
    schreierG (n := n) trees[i]! lG l k ∈ K := by
  simp only [schreierAt, Bool.and_eq_true, decide_eq_true_eq] at h
  have hpk : ap trees[i]!.pts k < n := hT.pts_lt k hk
  rw [hrl _ hpk] at h
  obtain ⟨hky, hsift⟩ := h
  obtain ⟨hs0, he0⟩ := walk_spec (lG := lG) (hW i hi) hk Q hQ
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
  obtain ⟨hs2, he2⟩ := walkInv_spec (lG := lG) (hW i hi) hky _ hn1
  refine sift_mem (lG := lG) hsep hQ _ (trees.size - (i + 1)) (i + 1) rfl ?_ _ _
    (by rw [hs2, apT_size, hs0]) ?_ hsift
  · intro l' hl' hil'
    exact ⟨hW l' hl', hdeep l' hl' hil'⟩
  · intro t ht
    unfold schreierG
    rw [he2 t (by rwa [apT_size, hs0]), apT_get _ _ (by rwa [hs0]), hrl _ (hn0 t (by rwa [hs0])),
      he0 t ht, ← idx_mul, ← idx_mul]

theorem schreier_mem_of_skip {X : Type*} [MulAction G X] (K : Subgroup G) (t : X → G) (s : G)
    {d : ℕ} (hd0 : 0 < d) (hd : s ^ d = 1) (E : Set X)
    (hE : ∀ x ∈ E, (t (s • x))⁻¹ * s * t x ∈ K) {x : X}
    (hx : ∀ i, 0 < i → i < d → s ^ i • x ∈ E) : (t (s • x))⁻¹ * s * t x ∈ K := by
  have hrest : (t (s ^ (d - 1) • s • x))⁻¹ * s ^ (d - 1) * t (s • x) ∈ K := by
    refine schreier_pow_mem K t s (s • x) (d - 1) fun j hj => hE _ ?_
    rw [smul_smul, ← pow_succ]
    exact hx (j + 1) (Nat.succ_pos j) (by omega)
  have hprod : (t (s ^ (d - 1) • s • x))⁻¹ * s ^ (d - 1) * t (s • x) *
      ((t (s • x))⁻¹ * s * t x) = 1 := by
    rw [← schreier_mul_eq, ← pow_succ, Nat.sub_add_cancel hd0, hd, one_smul, mul_one,
      inv_mul_cancel]
  rw [eq_inv_of_mul_eq_one_right hprod]
  exact K.inv_mem hrest

theorem treeFacts_smul_mem {T : Tree} {lv : Array ℕ} {lG : ℕ → G} {r : ℕ}
    (hT : TreeFacts n T lv lG r) {g : G} (hg : g ∈ lettersGroup lv lG) {k : ℕ}
    (hk : k < T.pts.size) :
    ap T.pos (idx n g (ap T.pts k)) < T.pts.size ∧
      ap T.pts (ap T.pos (idx n g (ap T.pts k))) = idx n g (ap T.pts k) := by
  set x : Fin n := ⟨ap T.pts k, hT.pts_lt k hk⟩
  have hx : x ∈ MulAction.orbit (lettersGroup lv lG) (⟨r, hT.r_lt⟩ : Fin n) :=
    (hT.mem_orbit_iff x).2 ⟨k, hk, rfl⟩
  have hgx : (⟨g, hg⟩ : lettersGroup lv lG) • x ∈
      MulAction.orbit (lettersGroup lv lG) (⟨r, hT.r_lt⟩ : Fin n) := by
    obtain ⟨h, hh⟩ := hx
    refine ⟨⟨g, hg⟩ * h, ?_⟩
    show (⟨g, hg⟩ * h) • (⟨r, hT.r_lt⟩ : Fin n) = _
    rw [mul_smul]
    rw [show h • (⟨r, hT.r_lt⟩ : Fin n) = x from hh]
  obtain ⟨k', hk', hpk'⟩ := (hT.mem_orbit_iff _).1 hgx
  have he : ((⟨g, hg⟩ : lettersGroup lv lG) • x).val = idx n g (ap T.pts k) := by
    show (g • x).val = _
    rw [smul_val_eq_idx]
  rw [he] at hpk'
  rw [← hpk', hT.pos_pts k' hk']
  exact ⟨hk', rfl⟩

theorem starts_mono {starts : Array ℕ} {m : ℕ} (hmono : ∀ i < m, starts[i]! ≤ starts[i + 1]!) :
    ∀ a b, a ≤ b → b ≤ m → starts[a]! ≤ starts[b]! := by
  intro a b hab hbm
  induction b with
  | zero => obtain rfl : a = 0 := by omega
            exact le_rfl
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le hab with rfl | hlt
    · exact le_rfl
    · exact le_trans (ih (by omega) (by omega)) (hmono b (by omega))

section Chain

variable {letters : Array Table} {gs : ℕ → G} {starts ords base Q qb : Array ℕ}
  {trees : Array Tree} {chunks : ℕ}

theorem levelChainOK_parts (h : levelChainOK n letters starts ords base Q qb trees chunks = true) :
    letters.size = 2 * starts[base.size]! ∧
      (∀ j < letters.size / 2, invOK n letters[2 * j]! letters[2 * j + 1]! = true) ∧
      starts.size = base.size + 1 ∧ (∀ i < base.size, starts[i]! ≤ starts[i + 1]!) ∧
      trees.size = base.size ∧ qb.size = base.size ∧ (∀ t < Q.size, Q[t]! < n) ∧
      (∀ i < base.size, qb[i]! < Q.size ∧ Q[qb[i]!]! = base[i]!) ∧
      (∀ i < base.size, treeOK n base[i]! trees[i]! letters (levelLv starts i) = true) ∧
      (∀ i, 1 ≤ i → i < base.size → ∀ j, starts[i]! ≤ j → j < starts[i + 1]! →
        ap letters[2 * j]! base[i - 1]! = base[i - 1]!) ∧
      ords.size = starts[base.size]! ∧
      (∀ j < starts[base.size]!, 0 < ords[j]! ∧ powFixes letters[2 * j]! ords[j]! Q = true) ∧
      (∀ i < base.size, ∀ j, starts[i]! ≤ j → j < starts[i + 1]! → ∀ k < trees[i]!.pts.size,
        levelTestAt trees letters qb Q i (2 * j) ords[j]! k = true) := by
  unfold levelChainOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  refine ⟨h1, fun j hj => (allIn_eq_true.1 h2) j (Nat.zero_le _) hj, h3,
    fun i hi => by simpa using (allIn_eq_true.1 h4) i (Nat.zero_le _) hi, h5, h6,
    fun t ht => by simpa using (allIn_eq_true.1 h7) t (Nat.zero_le _) ht,
    fun i hi => by simpa using (allIn_eq_true.1 h8) i (Nat.zero_le _) hi,
    fun i hi => (allIn_eq_true.1 h9) i (Nat.zero_le _) hi, ?_, h11, ?_, ?_⟩
  · intro i hi1 hi j hj1 hj2
    have := (allIn_eq_true.1 ((allIn_eq_true.1 h10) i hi1 hi)) j hj1 hj2
    simpa using this
  · intro j hj
    have := (allIn_eq_true.1 h12) j (Nat.zero_le _) hj
    simpa using this
  · intro i hi j hj1 hj2 k hk
    have := (allIn_eq_true.1 ((allIn_eq_true.1 h13) i (Nat.zero_le _) hi)) j hj1 hj2
    exact parAll_eq_true this k hk

theorem levelChain_facts [Finite G] (hrep : ∀ j < letters.size / 2, Rep n letters[2 * j]! (gs j))
    (hsep : ∀ g : G, (∀ t < Q.size, idx n g Q[t]! = Q[t]!) → g = 1)
    (hnest : ∀ i, 1 ≤ i → i < base.size → ∀ j, starts[i]! ≤ j → j < starts[i + 1]! →
      gs j ∈ lvlGroup starts gs (i - 1))
    (h : levelChainOK n letters starts ords base Q qb trees chunks = true) :
    (∀ i < base.size, TreeFacts n trees[i]! (levelLv starts i) (pairG gs) base[i]!) ∧
      (∀ i < base.size, ∀ g ∈ lvlGroup starts gs i, idx n g base[i]! = base[i]! ↔
        g ∈ lvlGroup starts gs (i + 1)) ∧
      ∀ i ≤ base.size, Nat.card (lvlGroup starts gs i) =
        ∏ l ∈ Finset.Ico i base.size, trees[l]!.pts.size := by
  obtain ⟨hLsz, hinv, hsts, hmono, htrees, hqb, hQ, hqbQ, htree, hfixgen, hords, hpow, htest⟩ :=
    levelChainOK_parts h
  set m := base.size with hm
  set lG := pairG gs with hlG
  have h2 : letters.size % 2 = 0 := by omega
  have hrepAll := rep_pairG hrep h2 hinv
  have hmono' := starts_mono hmono
  have hlvlt : ∀ i < m, ∀ l ∈ levelLv starts i, l < letters.size := by
    intro i hi l hl
    rw [mem_levelLv (hmono i hi)] at hl
    have := hmono' (i + 1) m (by omega) le_rfl
    omega
  have hTF : ∀ i < m, TreeFacts n trees[i]! (levelLv starts i) lG base[i]! :=
    fun i hi => treeOK_facts (fun l hl => hrepAll l (hlvlt i hi l hl)) (htree i hi)
  have hWF : ∀ i < m, WalkFacts n trees[i]! letters lG := by
    intro i hi k hk hk0
    obtain ⟨hpar, hlab⟩ := (hTF i hi).par k hk hk0
    have hl := hlvlt i hi _ hlab
    refine ⟨hpar, hrepAll _ hl, ?_⟩
    rw [← pairG_invL]
    exact hrepAll _ (invL_lt h2 hl)
  have hWF' : ∀ l' < trees.size, WalkFacts n trees[l']! letters lG :=
    fun l' hl' => hWF l' (by omega)
  have hbot : lvlGroup starts gs m = ⊥ := by
    apply lvlGroup_eq_bot_of_le
    rw [getElem!_neg starts (m + 1) (by omega)]
    exact Nat.zero_le _
  have hstep : ∀ l', 1 ≤ l' → l' ≤ m → lvlGroup starts gs l' ≤ lvlGroup starts gs (l' - 1) := by
    intro l' hl1 hl2
    rcases Nat.eq_or_lt_of_le hl2 with rfl | hlt
    · rw [hbot]; exact bot_le
    · exact lvlGroup_le gs _ fun j hj1 hj2 => hnest l' hl1 hlt j hj1 hj2
  have hnestle : ∀ i l', i ≤ l' → l' ≤ m → lvlGroup starts gs l' ≤ lvlGroup starts gs i := by
    intro i l' hil hlm
    induction l' with
    | zero => obtain rfl : i = 0 := by omega
              exact le_rfl
    | succ l' ih =>
      rcases Nat.eq_or_lt_of_le hil with rfl | hlt
      · exact le_rfl
      · exact le_trans (hstep (l' + 1) (by omega) hlm) (ih (by omega) (by omega))
  have hTreeMem : ∀ i < m, ∀ k < trees[i]!.pts.size, treeG trees[i]! lG k ∈ lvlGroup starts gs i :=
    fun i hi k hk => (hTF i hi).treeG_mem hk
  have hSch : ∀ i < m, ∀ k < trees[i]!.pts.size, ∀ l ∈ levelLv starts i,
      schreierG (n := n) trees[i]! lG l k ∈ lvlGroup starts gs (i + 1) := by
    intro i hi
    set T := trees[i]! with hTdef
    set K := lvlGroup starts gs (i + 1) with hK
    have hT := hTF i hi
    have hdeep : ∀ l' < trees.size, i + 1 ≤ l' → ∀ k < trees[l']!.pts.size,
        treeG trees[l']! lG k ∈ K := fun l' hl' hil' k hk =>
      hnestle (i + 1) l' hil' (by omega) (hTreeMem l' (by omega) k hk)
    have hgen : ∀ j, starts[i]! ≤ j → j < starts[i + 1]! → ∀ k < T.pts.size,
        schreierG (n := n) T lG (2 * j) k ∈ K := by
      intro j hj1 hj2
      have hjL : j < letters.size / 2 := by
        have := hmono' (i + 1) m (by omega) le_rfl
        omega
      have hrs : Rep n letters[2 * j]! (gs j) := hrep j hjL
      have hlGs : lG (2 * j) = gs j := by
        show pairG gs (2 * j) = gs j
        unfold pairG
        rw [ite_eq_left (by omega), Nat.mul_div_cancel_left j (by norm_num)]
      have hjm : j < starts[m]! := by
        have := hmono' (i + 1) m (by omega) le_rfl
        omega
      set d := ords[j]! with hd
      have hd0 : 0 < d := (hpow j hjm).1
      have hgd : gs j ^ d = 1 := pow_eq_one_of_powFixes hrs hQ hsep (hpow j hjm).2
      have hinvo : (d == 2) = true → gs j * gs j = 1 := by
        intro h2'
        rw [beq_iff_eq] at h2'
        rw [← pow_two, ← h2', hgd]
      have hgmem : gs j ∈ lettersGroup (levelLv starts i) lG := gs_mem_lvlGroup gs hj1 hj2
      let t : Fin n → G := fun x => treeG T lG (ap T.pos x.val)
      let Y : Set (Fin n) := {x | ∃ k < T.pts.size, ap T.pts k = x.val}
      have hY : ∀ x ∈ Y, ap T.pos x.val < T.pts.size ∧ ap T.pts (ap T.pos x.val) = x.val := by
        rintro x ⟨k, hk, hkx⟩
        rw [← hkx, hT.pos_pts k hk]
        exact ⟨hk, rfl⟩
      have hYs : ∀ x ∈ Y, ∀ e : ℕ, gs j ^ e • x ∈ Y := by
        intro x hx e
        obtain ⟨hpx, hpx'⟩ := hY x hx
        have he := treeFacts_smul_mem hT (Subgroup.pow_mem _ hgmem e) hpx
        rw [hpx'] at he
        exact ⟨_, he.1, by rw [he.2, smul_val_eq_idx]⟩
      let E : Set (Fin n) := {x | x ∈ Y ∧
        (edgeTriv T letters (2 * j) (d == 2) (ap T.pos x.val) = true ∨
          schreierAt trees letters qb Q i (2 * j) (ap T.pos x.val) = true)}
      have hσx : ∀ x ∈ Y, (t (gs j • x))⁻¹ * gs j * t x =
          schreierG (n := n) T lG (2 * j) (ap T.pos x.val) := by
        intro x hx
        obtain ⟨hpx, hpx'⟩ := hY x hx
        simp only [schreierG, t, hlGs, hpx', smul_val_eq_idx]
      have hE : ∀ x ∈ E, (t (gs j • x))⁻¹ * gs j * t x ∈ K := by
        rintro x ⟨hxY, hx⟩
        obtain ⟨hpx, -⟩ := hY x hxY
        rw [hσx x hxY]
        rcases hx with hx | hx
        · rw [schreier_eq_one_of_treeEdge hT hrs hinvo hpx hx]
          exact K.one_mem
        · exact schreier_mem_of_schreierAt hsep hQ K (by omega) hT hWF' hdeep
            (hrepAll _ (by omega)) hpx hx
      intro k hk
      set x : Fin n := ⟨ap T.pts k, hT.pts_lt k hk⟩ with hxdef
      have hxY : x ∈ Y := ⟨k, hk, rfl⟩
      have hposx : ap T.pos x.val = k := hT.pos_pts k hk
      have hgoal : schreierG (n := n) T lG (2 * j) k = (t (gs j • x))⁻¹ * gs j * t x := by
        rw [hσx x hxY, hposx]
      rw [hgoal]
      by_cases hxE : x ∈ E
      · exact hE x hxE
      · refine schreier_mem_of_skip K t (gs j) hd0 hgd E hE fun e he0 hed => ?_
        have htx := htest i hi j hj1 hj2 k hk
        unfold levelTestAt at htx
        simp only [Bool.or_eq_true] at htx
        have hskip : cycleSkip T letters (2 * j) d x.val = true := by
          rcases htx with (h1 | h1) | h1
          · exact absurd ⟨hxY, Or.inl (by rw [hposx]; exact h1)⟩ hxE
          · exact h1
          · exact absurd ⟨hxY, Or.inr (by rw [hposx]; exact h1)⟩ hxE
        have hiter : ∀ e', iterAp letters[2 * j]! e' x.val = (gs j ^ e' • x).val := by
          intro e'
          rw [iterAp_eq hrs x.isLt e', smul_val_eq_idx]
        unfold cycleSkip at hskip
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hskip
        have hz := (allIn_eq_true.1 hskip.2) e (by omega) hed
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at hz
        rw [hiter e] at hz
        obtain ⟨hzx, hzc⟩ := hz
        set z := gs j ^ e • x with hzdef
        have hzY : z ∈ Y := hYs x hxY e
        obtain ⟨hpz, hpz'⟩ := hY z hzY
        rcases hzc with hlt | hedge
        ·
          refine ⟨hzY, ?_⟩
          have htz := htest i hi j hj1 hj2 _ hpz
          unfold levelTestAt at htz
          simp only [Bool.or_eq_true] at htz
          rcases htz with (h1 | h1) | h1
          · exact Or.inl h1
          · exfalso
            have h1' : cycleSkip T letters (2 * j) d z.val = true := by
              rw [← hpz']; exact h1
            unfold cycleSkip at h1'
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h1'
            have h1 := h1'
            have hw := (allIn_eq_true.1 h1.2) (d - e) (by omega) (by omega)
            simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true,
              decide_eq_true_eq] at hw
            have hback : iterAp letters[2 * j]! (d - e) z.val = x.val := by
              rw [iterAp_eq hrs z.isLt (d - e), ← smul_val_eq_idx, hzdef, smul_smul,
                ← pow_add, Nat.sub_add_cancel hed.le, hgd, one_smul]
            rw [hback] at hw
            rcases hw.2 with hlt' | hedge'
            · exact absurd hlt' (by omega)
            · exact hxE ⟨hxY, Or.inl hedge'⟩
          · exact Or.inr h1
        · exact ⟨hzY, Or.inl hedge⟩
    intro k hk l hl
    rw [mem_levelLv (hmono i hi)] at hl
    obtain ⟨j, hj1, hj2, rfl | rfl⟩ : ∃ j, starts[i]! ≤ j ∧ j < starts[i + 1]! ∧
        (l = 2 * j ∨ l = 2 * j + 1) := ⟨l / 2, by omega, by omega, by omega⟩
    · exact hgen j hj1 hj2 k hk
    ·
      set s := gs j
      have hlGi : lG (2 * j + 1) = s⁻¹ := by
        show pairG gs (2 * j + 1) = (gs j)⁻¹
        unfold pairG
        rw [ite_eq_right (by omega)]
        congr 2
        omega
      have hsmem : s⁻¹ ∈ lettersGroup (levelLv starts i) lG :=
        Subgroup.inv_mem _ (gs_mem_lvlGroup gs hj1 hj2)
      obtain ⟨hk', hk''⟩ := treeFacts_smul_mem (hTF i hi) hsmem hk
      have hinvk := hgen j hj1 hj2 _ hk'
      unfold schreierG at hinvk
      have hlGs : lG (2 * j) = s := by
        show pairG gs (2 * j) = gs j
        unfold pairG
        rw [ite_eq_left (by omega), Nat.mul_div_cancel_left j (by norm_num)]
      rw [hlGs, hk'', ← idx_mul, mul_inv_cancel, idx_one, (hTF i hi).pos_pts k hk] at hinvk
      have := (lvlGroup starts gs (i + 1)).inv_mem hinvk
      have e : ((treeG T lG k)⁻¹ * s *
          treeG T lG (ap trees[i]!.pos (idx n s⁻¹ (ap trees[i]!.pts k))))⁻¹ =
          (treeG T lG (ap trees[i]!.pos (idx n s⁻¹ (ap trees[i]!.pts k))))⁻¹ * s⁻¹ *
            treeG T lG k := by group
      rw [e] at this
      show (treeG T lG (ap T.pos (idx n (lG (2 * j + 1)) (ap T.pts k))))⁻¹ * lG (2 * j + 1) *
        treeG T lG k ∈ _
      rw [hlGi]
      exact this
  have hstab : ∀ i < m, ∀ g ∈ lvlGroup starts gs i, idx n g base[i]! = base[i]! →
      g ∈ lvlGroup starts gs (i + 1) := fun i hi =>
    (hTF i hi).stab_le _ fun k hk l hl => hSch i hi k hk l hl
  have hfixb : ∀ i < m, ∀ g ∈ lvlGroup starts gs (i + 1), idx n g base[i]! = base[i]! := by
    intro i hi g hg
    have hb : base[i]! < n := (hTF i hi).r_lt
    rcases (show i + 1 = m ∨ i + 1 < m by omega) with heq | hlt
    · rw [heq, hbot, Subgroup.mem_bot] at hg
      rw [hg, idx_one]
    · have hle := lvlGroup_le (starts := starts) gs
        (MulAction.stabilizer G (⟨base[i]!, hb⟩ : Fin n)) (i := i + 1)
        (fun j hj1 hj2 => by
          rw [MulAction.mem_stabilizer_iff]
          apply Fin.ext
          rw [smul_val_eq_idx]
          have hjL : j < letters.size / 2 := by
            have := hmono' (i + 1 + 1) m (by omega) le_rfl
            omega
          rw [← hrep j hjL _ hb]
          exact hfixgen (i + 1) (by omega) hlt j hj1 hj2)
      have := hle hg
      rw [MulAction.mem_stabilizer_iff] at this
      have := congrArg Fin.val this
      rwa [smul_val_eq_idx] at this
  refine ⟨hTF, fun i hi g hg => ⟨hstab i hi g hg, hfixb i hi g⟩, ?_⟩
  intro i hi
  induction h' : m - i generalizing i with
  | zero =>
    obtain rfl : i = m := by omega
    rw [hbot, Subgroup.card_bot, Finset.Ico_self, Finset.prod_empty]
  | succ d ih =>
    have him : i < m := by omega
    have hcard := card_eq_orbit_mul (lvlGroup starts gs i) (lvlGroup starts gs (i + 1))
      (⟨base[i]!, (hTF i him).r_lt⟩ : Fin n)
      (hnestle i (i + 1) (Nat.le_succ i) (by omega))
      (fun g hg => Fin.ext (by rw [smul_val_eq_idx]; exact hfixb i him g hg))
      (fun g hg hfix => hstab i him g hg (by
        have := congrArg Fin.val hfix; rwa [smul_val_eq_idx] at this))
    rw [hcard, ih (i + 1) (by omega) (by omega), Finset.prod_eq_prod_Ico_succ_bot him]
    congr 1
    exact (hTF i him).card_orbit

end Chain

end CFSG.Sporadic.LevelChain
