module

public import CFSG.Perm.SiftComplete
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Perm

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm.Native

variable {G : Type*} [Group G]

theorem card_eq_orbit_mul_inf {X : Type*} [MulAction G X] [Finite G] (H : Subgroup G) (p : X) :
    Nat.card H = Nat.card (MulAction.orbit H p) *
      Nat.card (H ⊓ MulAction.stabilizer G p : Subgroup G) := by
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer H p)
  rw [MulAction.index_stabilizer] at h1
  have e : MulAction.stabilizer H p ≃ (H ⊓ MulAction.stabilizer G p : Subgroup G) :=
    { toFun := fun x => ⟨x.1.1, Subgroup.mem_inf.2 ⟨x.1.2,
        MulAction.mem_stabilizer_iff.2 (MulAction.mem_stabilizer_iff.1 x.2)⟩⟩
      invFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.1 y.2).1⟩,
        MulAction.mem_stabilizer_iff.2 (MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 y.2).2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← h1, Nat.card_congr e, Nat.card_coe_set_eq, mul_comm]

variable {n : ℕ} [MulAction G (Fin n)]

section Chain

variable {letters : Array Table} {gs : ℕ → G} {base : Array ℕ} {trees : Array Tree}

theorem fix_base_of_mem_levelGroup_succ
    (hrep : ∀ l < letters.size, Rep n letters[l]! (pairG gs l)) {i : ℕ} (hb : base[i]! < n)
    {g : G} (hg : g ∈ levelGroup letters base (pairG gs) (i + 1)) :
    idx n g base[i]! = base[i]! := by
  unfold levelGroup lettersGroup at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    obtain ⟨hl', hfix⟩ := mem_levelLetters_succ.1 hl
    rw [← hrep l (levelLetters_lt hl') _ hb, hfix]
  | one => exact idx_one _
  | mul x y _ _ hx hy => rw [idx_mul, hy, hx]
  | inv x _ hx => rw [← hx, idx_inv_idx, hx]

theorem chain_facts_of_card [Finite G]
    (hrep : ∀ j < letters.size / 2, Rep n letters[2 * j]! (gs j))
    (h2 : letters.size % 2 = 0)
    (hinv : ∀ j < letters.size / 2, invOK n letters[2 * j]! letters[2 * j + 1]! = true)
    (htree : ∀ i < base.size, Perm.Native.treeOK n base[i]! trees[i]! letters
      (levelLetters letters base i) = true)
    (hcard : ∏ l ∈ Finset.range base.size, trees[l]!.pts.size = Nat.card G) :
    (∀ i < base.size, TreeFacts n trees[i]! (levelLetters letters base i) (pairG gs) base[i]!) ∧
      (∀ i < base.size, ∀ g ∈ levelGroup letters base (pairG gs) i,
        idx n g base[i]! = base[i]! ↔ g ∈ levelGroup letters base (pairG gs) (i + 1)) ∧
      levelGroup letters base (pairG gs) base.size = ⊥ ∧
      levelGroup letters base (pairG gs) 0 = ⊤ := by
  set lG := pairG gs with hlG
  set m := base.size with hm
  set K : ℕ → Subgroup G := fun i => levelGroup letters base lG i with hK
  set t : ℕ → ℕ := fun l => trees[l]!.pts.size with ht
  have hrepAll := rep_pairG hrep h2 hinv
  have hlvRep : ∀ i, ∀ l ∈ levelLetters letters base i, Rep n letters[l]! (lG l) :=
    fun i l hl => hrepAll l (levelLetters_lt hl)
  have hTF : ∀ i < m, TreeFacts n trees[i]! (levelLetters letters base i) lG base[i]! :=
    fun i hi => treeOK_facts (hlvRep i) (htree i hi)
  have hfixb : ∀ i < m, ∀ g ∈ K (i + 1), idx n g base[i]! = base[i]! :=
    fun i hi g hg => fix_base_of_mem_levelGroup_succ hrepAll (hTF i hi).r_lt hg
  set pt : ∀ i, i < m → Fin n := fun i hi => ⟨base[i]!, (hTF i hi).r_lt⟩ with hpt
  have hKS : ∀ i (hi : i < m), K (i + 1) ≤ K i ⊓ MulAction.stabilizer G (pt i hi) := by
    intro i hi g hg
    refine Subgroup.mem_inf.2 ⟨levelGroup_anti lG (Nat.le_succ i) hg, ?_⟩
    rw [MulAction.mem_stabilizer_iff]
    apply Fin.ext
    rw [smul_val_eq_idx]
    exact hfixb i hi g hg
  have horbit : ∀ i (hi : i < m), Nat.card (K i) =
      t i * Nat.card (K i ⊓ MulAction.stabilizer G (pt i hi) : Subgroup G) := by
    intro i hi
    rw [card_eq_orbit_mul_inf (K i) (pt i hi)]
    congr 1
    exact (hTF i hi).card_orbit
  have hge : ∀ i < m, t i * Nat.card (K (i + 1)) ≤ Nat.card (K i) := by
    intro i hi
    rw [horbit i hi]
    exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le (hKS i hi))
  have hpos : ∀ i < m, 0 < t i := fun i hi => (hTF i hi).size_pos
  have hlow : ∀ d j, j + d = m → (∏ l ∈ Finset.Ico j m, t l) ≤ Nat.card (K j) := by
    intro d
    induction d with
    | zero =>
      intro j hj
      have : j = m := by omega
      subst this
      simp only [Finset.Ico_self, Finset.prod_empty]
      exact Nat.card_pos
    | succ d ih =>
      intro j hj
      have hjm : j < m := by omega
      rw [Finset.prod_eq_prod_Ico_succ_bot hjm]
      calc t j * ∏ l ∈ Finset.Ico (j + 1) m, t l ≤ t j * Nat.card (K (j + 1)) :=
            Nat.mul_le_mul_left _ (ih (j + 1) (by omega))
        _ ≤ Nat.card (K j) := hge j hjm
  have hchain : ∀ j ≤ m, (∏ l ∈ Finset.range j, t l) * Nat.card (K j) ≤ Nat.card (K 0) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      calc (∏ l ∈ Finset.range (j + 1), t l) * Nat.card (K (j + 1))
          = (∏ l ∈ Finset.range j, t l) * (t j * Nat.card (K (j + 1))) := by
            rw [Finset.prod_range_succ, mul_assoc]
        _ ≤ (∏ l ∈ Finset.range j, t l) * Nat.card (K j) :=
            Nat.mul_le_mul_left _ (hge j (by omega))
        _ ≤ Nat.card (K 0) := ih (by omega)
  have hK0 : Nat.card (K 0) ≤ Nat.card G := Subgroup.card_le_card_group _
  have hexact : ∀ j ≤ m, Nat.card (K j) = ∏ l ∈ Finset.Ico j m, t l := by
    intro j hj
    refine le_antisymm ?_ (hlow (m - j) j (by omega))
    have hP : 0 < ∏ l ∈ Finset.range j, t l :=
      Finset.prod_pos fun l hl => hpos l (by simp at hl; omega)
    have h1 := le_trans (hchain j hj) hK0
    rw [← hcard, ← Finset.prod_range_mul_prod_Ico _ hj] at h1
    exact Nat.le_of_mul_le_mul_left h1 hP
  have hbot : K m = ⊥ :=
    Subgroup.eq_bot_of_card_le _ (by rw [hexact m le_rfl]; simp)
  have htop : K 0 = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [hexact 0 (Nat.zero_le _), ← Finset.range_eq_Ico]
    exact hcard
  have hstab : ∀ i < m, ∀ g ∈ K i, idx n g base[i]! = base[i]! → g ∈ K (i + 1) := by
    intro i hi g hg hgfix
    have hcardS : Nat.card (K i ⊓ MulAction.stabilizer G (pt i hi) : Subgroup G) ≤
        Nat.card (K (i + 1)) := by
      have h1 := horbit i hi
      rw [hexact i hi.le, Finset.prod_eq_prod_Ico_succ_bot hi] at h1
      rw [hexact (i + 1) hi]
      exact le_of_eq (Nat.eq_of_mul_eq_mul_left (hpos i hi) h1).symm
    have heq : K (i + 1) = K i ⊓ MulAction.stabilizer G (pt i hi) :=
      Subgroup.eq_of_le_of_card_ge (hKS i hi) hcardS
    rw [heq]
    refine Subgroup.mem_inf.2 ⟨hg, ?_⟩
    rw [MulAction.mem_stabilizer_iff]
    apply Fin.ext
    rw [smul_val_eq_idx]
    exact hgfix
  exact ⟨hTF, fun i hi g hg => ⟨hstab i hi g hg, hfixb i hi g⟩, hbot, htop⟩

end Chain

end CFSG.Perm

namespace CFSG.Perm.Native

open CFSG.Sporadic.Th.Native

@[expose] def iterAp (Y : Table) : ℕ → ℕ → ℕ
  | 0, ω => ω
  | i + 1, ω => ap Y (iterAp Y i ω)

@[expose] def tupleOf (Y : Table) (m ω : ℕ) : Array ℕ := (Array.range m).map fun i => iterAp Y i ω

end CFSG.Perm.Native

namespace CFSG.Perm

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm.Native

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]

theorem iterAp_spec {Y : Table} {y : G} (hY : Rep n Y y) :
    ∀ (i : ℕ) {ω : ℕ}, ω < n → iterAp Y i ω = idx n (y ^ i) ω := by
  intro i
  induction i with
  | zero => intro ω _; rw [iterAp, pow_zero, idx_one]
  | succ i ih =>
    intro ω hω
    rw [iterAp, ih hω, hY _ (idx_lt _ hω), pow_succ', idx_mul]

theorem tupleOf_size (Y : Table) (m ω : ℕ) : (tupleOf Y m ω).size = m := by
  simp [tupleOf]

theorem tupleOf_get (Y : Table) {m ω t : ℕ} (ht : t < m) :
    (tupleOf Y m ω)[t]! = iterAp Y t ω := by
  rw [tupleOf, getElem!_pos _ t (by simpa using ht), Array.getElem_map, Array.getElem_range]

section Tuple

variable {letters : Array Table} {gs : ℕ → G} {base : Array ℕ} {trees : Array Tree}

theorem card_centralizer_le_of_tupleSift [Finite G]
    (hrep : ∀ j < letters.size / 2, Rep n letters[2 * j]! (gs j))
    (h2 : letters.size % 2 = 0)
    (hinv : ∀ j < letters.size / 2, invOK n letters[2 * j]! letters[2 * j + 1]! = true)
    (hsz : trees.size = base.size)
    (htree : ∀ i < base.size, Perm.Native.treeOK n base[i]! trees[i]! letters
      (levelLetters letters base i) = true)
    (hcard : ∏ l ∈ Finset.range base.size, trees[l]!.pts.size = Nat.card G)
    {y : G} {Y : Table} (hY : Rep n Y y) (hm : 0 < base.size)
    (hbase : ∀ i < base.size, base[i]! = iterAp Y i base[0]!) :
    Nat.card (Subgroup.centralizer ({y} : Set G)) ≤
      Nat.count (fun ω => sift trees letters (Array.range base.size) base 0
        (tupleOf Y base.size ω) = true) n := by
  classical
  obtain ⟨hTF, hstabIff, hbot, htop⟩ :=
    chain_facts_of_card (gs := gs) hrep h2 hinv htree hcard
  set lG := pairG gs with hlG
  set m := base.size with hmdef
  set K : ℕ → Subgroup G := fun i => levelGroup letters base lG i with hK
  have hrepAll := rep_pairG hrep h2 hinv
  have hb0 : base[0]! < n := (hTF 0 hm).r_lt
  have hbn : ∀ t < m, base[t]! < n := fun t ht => (hTF t ht).r_lt
  have hWF : ∀ i < m, WalkFacts n trees[i]! letters lG := by
    intro i hi k hk hk0
    obtain ⟨hpar, hlab⟩ := (hTF i hi).par k hk hk0
    have hl := levelLetters_lt hlab
    refine ⟨hpar, hrepAll _ hl, ?_⟩
    rw [← pairG_invL]
    exact hrepAll _ (invL_lt h2 hl)
  have hcomm : ∀ c ∈ Subgroup.centralizer ({y} : Set G), ∀ i : ℕ, y ^ i * c = c * y ^ i := by
    intro c hc i
    have h := Subgroup.mem_centralizer_singleton_iff.1 hc
    exact ((Commute.pow_left (show Commute y c from h.symm) i)).eq
  have htup : ∀ c ∈ Subgroup.centralizer ({y} : Set G), ∀ t < m,
      (tupleOf Y m (idx n c base[0]!))[t]! = idx n c base[t]! := by
    intro c hc t ht
    rw [tupleOf_get Y ht, iterAp_spec hY t (idx_lt _ hb0), hbase t ht,
      iterAp_spec hY t hb0, ← idx_mul, ← idx_mul, hcomm c hc t]
  have hsift : ∀ c ∈ Subgroup.centralizer ({y} : Set G),
      sift trees letters (Array.range m) base 0 (tupleOf Y m (idx n c base[0]!)) = true := by
    intro c hc
    have hqb : ∀ l < trees.size, (Array.range m)[l]! < base.size := by
      intro l hl
      rw [hsz] at hl
      rw [getElem!_pos _ l (by simpa using hl), Array.getElem_range]
      exact hl
    have hqbv : ∀ l < trees.size, base[(Array.range m)[l]!]! = base[l]! := by
      intro l hl
      rw [hsz] at hl
      rw [getElem!_pos (Array.range m) l (by simpa using hl), Array.getElem_range]
    refine sift_complete (lvs := fun l => levelLetters letters base l) K hbn hqb
      (fun l hl => hWF l (hsz ▸ hl)) (fun l hl => by rw [hqbv l hl]; exact hTF l (hsz ▸ hl))
      (fun l _ => rfl) (fun l hl g hg hfix => ?_) (by rw [hsz]; exact hbot)
      trees.size 0 (by omega) (Nat.zero_le _) c (show c ∈ levelGroup letters base lG 0 by
        rw [htop]; exact Subgroup.mem_top c) _
      (by rw [tupleOf_size]) (fun t ht => htup c hc t ht)
    rw [hqbv l hl] at hfix
    exact (hstabIff l (hsz ▸ hl) g hg).1 hfix
  set S := (Finset.range n).filter fun ω => sift trees letters (Array.range m) base 0
    (tupleOf Y m ω) = true with hS
  have hmem : ∀ c : Subgroup.centralizer ({y} : Set G), idx n c.1 base[0]! ∈ S := by
    intro c
    rw [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨idx_lt _ hb0, hsift c.1 c.2⟩
  let f : Subgroup.centralizer ({y} : Set G) → S := fun c => ⟨idx n c.1 base[0]!, hmem c⟩
  have hinj : Function.Injective f := by
    intro c₁ c₂ h
    have h' : idx n c₁.1 base[0]! = idx n c₂.1 base[0]! := congrArg Subtype.val h
    set d := c₁.1⁻¹ * c₂.1 with hd
    have hdC : d ∈ Subgroup.centralizer ({y} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ c₁.2) c₂.2
    have hd0 : idx n d base[0]! = base[0]! := by
      rw [hd, idx_mul, ← h', ← idx_mul, inv_mul_cancel, idx_one]
    have hdt : ∀ t < m, idx n d base[t]! = base[t]! := by
      intro t ht
      rw [hbase t ht, iterAp_spec hY t hb0, ← idx_mul, ← hcomm d hdC t, idx_mul, hd0]
    have hdK : ∀ i ≤ m, d ∈ K i := by
      intro i
      induction i with
      | zero => intro _; show d ∈ levelGroup letters base lG 0; rw [htop]; exact Subgroup.mem_top d
      | succ i ih =>
        intro hi
        exact (hstabIff i (by omega) d (ih (by omega))).1 (hdt i (by omega))
    have hd1 : d = 1 := by
      have := hdK m le_rfl
      rw [show K m = ⊥ from hbot] at this
      exact Subgroup.mem_bot.1 this
    have : c₁.1 = c₂.1 := by
      rw [hd] at hd1
      exact inv_mul_eq_one.1 hd1
    exact Subtype.ext this
  calc Nat.card (Subgroup.centralizer ({y} : Set G)) ≤ Nat.card S :=
        Nat.card_le_card_of_injective f hinj
    _ = S.card := Nat.card_eq_finsetCard S
    _ = Nat.count (fun ω => sift trees letters (Array.range m) base 0 (tupleOf Y m ω) = true) n :=
        (Nat.count_eq_card_filter_range _ n).symm

end Tuple

end CFSG.Perm
