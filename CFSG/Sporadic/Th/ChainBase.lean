
module

public import CFSG.Sporadic.Th.GroupTheory
public import CFSG.Sporadic.Th.PlaneBase
public import CFSG.Sporadic.Th.CertParts
public import CFSG.Sporadic.Th.OrbitSpec

@[expose] public section

namespace CFSG.Sporadic.Th

open Native Pointwise

@[expose] def pairLetters {G : Type*} [Group G] (g h : G) (l : ℤ) : G :=
  if l = 1 then g else if l = -1 then g⁻¹ else if l = 2 then h else h⁻¹

theorem pairLetters_mem {G : Type*} [Group G] (K : Subgroup G) {g h : G} (hg : g ∈ K)
    (hh : h ∈ K) (l : ℤ) : pairLetters g h l ∈ K := by
  unfold pairLetters
  split_ifs
  · exact hg
  · exact K.inv_mem hg
  · exact hh
  · exact K.inv_mem hh

theorem wordG_mem {G : Type*} [Group G] (K : Subgroup G) {gens : ℤ → G} (h : ∀ l, gens l ∈ K)
    (w : List ℤ) : wordG gens w ∈ K := by
  unfold wordG
  induction w with
  | nil => exact K.one_mem
  | cons l w ih =>
    rw [List.map_cons, List.prod_cons]
    exact K.mul_mem (h l) ih

@[expose] def lettersOK (w : List ℤ) : Bool := w.all fun l => l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2

theorem xWord_ok : lettersOK xWord = true := by decide

theorem yWord_ok : lettersOK yWord = true := by decide

theorem zWord0_ok : lettersOK zWord0 = true := by decide

theorem zWord1_ok : lettersOK zWord1 = true := by decide

theorem rep_wordLetters {G : Type*} [Group G] [MulAction G (Fin nX)] {P Q Qi : Table} {g h : G}
    (hP : Rep nX P g) (hPi : Rep nX P g⁻¹) (hQ : Rep nX Q h) (hQi : Rep nX Qi h⁻¹) {w : List ℤ}
    (hw : lettersOK w = true) : ∀ l ∈ w, Rep nX (wordLetters P Q Qi l) (pairLetters g h l) := by
  intro l hl
  have hl' := List.all_eq_true.1 hw l hl
  simp only [decide_eq_true_eq] at hl'
  unfold wordLetters pairLetters
  rcases hl' with rfl | rfl | rfl | rfl <;> simp_all

structure CertFacts (c : ℕ) : Prop where
  orbit : OrbitFacts
  count : nX = 143127000
  delta : deltaOK thSt = true
  aInvo : invoOK nX alphaT = true
  bOrd3 : order3OK nX betaT = true
  bInv : invOK nX betaT betaInvT = true
  a0 : ap alphaT 0 = 1
  b0 : ap betaT 0 = 2
  tables : TableFacts c

theorem certFacts_of {c : ℕ} (h : thCertificate c = true) : CertFacts c := by
  obtain ⟨hc, ho, hd, ha, hb, hbi, ha0, hb0, ht⟩ := thCertificate_parts h
  exact ⟨orbitFacts_of_orbitOK ho, hc, hd, ha, hb, hbi, ha0, hb0, tableChecks_parts ht⟩

theorem rep_letters_inv {G : Type*} [Group G] [MulAction G (Fin nX)] {P₁ P₂ : Table} {g h : G}
    (h₁ : Rep nX P₁ g⁻¹) (h₂ : Rep nX P₂ h⁻¹) (s : ℕ) :
    Rep nX (letters P₁ P₂ s) (lettersG g h s)⁻¹ := by
  have : (lettersG g h s)⁻¹ = lettersG g⁻¹ h⁻¹ s := by
    unfold lettersG; split_ifs <;> rfl
  rw [this]
  exact Rep.letters h₁ h₂ s

theorem lettersG_mem {G : Type*} [Group G] (K : Subgroup G) {g h : G} (hg : g ∈ K) (hh : h ∈ K)
    (s : ℕ) : lettersG g h s ∈ K := by
  unfold lettersG; split_ifs
  · exact hg
  · exact hh

section TreeOrbit

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]

theorem closure_pair_subtype (g₁ g₂ : G) :
    Subgroup.closure ({⟨g₁, Subgroup.subset_closure (Set.mem_insert _ _)⟩,
      ⟨g₂, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩} :
        Set (Subgroup.closure ({g₁, g₂} : Set G))) = ⊤ := by
  have h := CFSG.Certificates.schreier_subtype_generators_generate ({g₁, g₂} : Set G)
  convert h using 2
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, Subgroup.coe_subtype]
  constructor
  · rintro (rfl | rfl) <;> simp
  · rintro (h | h)
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h

theorem idx_val (g : G) (p : Fin n) : idx n g p.val = (g • p).val := by
  rw [idx, dite_eq_left p.isLt]

theorem smul_eq_of_idx (g : G) (p q : Fin n) (h : idx n g p.val = q.val) : g • p = q :=
  Fin.ext (by rw [← idx_val, h])

theorem treeElt_zero (pl : Table) (gensG : ℕ → G) : treeElt pl gensG 0 = 1 := by
  rw [treeElt]
  simp

structure TreeData (n : ℕ) [MulAction G (Fin n)] (g₁ g₂ : G) (m r : ℕ) (pts lk : ℕ → ℕ)
    (pl : Table) : Prop where
  pos : 0 < m
  root : pts 0 = r
  pts_lt : ∀ k < m, pts k < n
  lk_pts : ∀ k < m, lk (pts k) = k
  c1 : ∀ k < m, lk (idx n g₁ (pts k)) < m ∧ pts (lk (idx n g₁ (pts k))) = idx n g₁ (pts k)
  c2 : ∀ k < m, lk (idx n g₂ (pts k)) < m ∧ pts (lk (idx n g₂ (pts k))) = idx n g₂ (pts k)
  par : ∀ k < m, 0 < k → treePar (pl[k]!).toNat < k
  elt : ∀ k < m, idx n (treeElt pl (lettersG g₁ g₂) k) r = pts k

theorem treeOK_par {n m root : ℕ} {pts pl : Table} {lk : ℕ → ℕ} {T₁ T₂ : Table}
    (h : treeOK n m root pts pl lk T₁ T₂ = true) :
    ∀ k < m, 0 < k → treePar (pl[k]!).toNat < k := by
  intro k hk hk0
  simp only [treeOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have := (allIn_eq_true.1 h.2) k (Nat.zero_le _) hk
  simp only [treeCheckAt, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  rcases this.2 with h0 | h1
  · omega
  · exact h1.1

theorem TreeData.of_treeOK {g₁ g₂ : G} {T₁ T₂ : Table} (h₁ : Rep n T₁ g₁) (h₂ : Rep n T₂ g₂)
    {m root : ℕ} {pts pl : Table} {lk : ℕ → ℕ} (h : treeOK n m root pts pl lk T₁ T₂ = true) :
    TreeData n g₁ g₂ m root (ap pts) lk pl := by
  obtain ⟨hm, h0, hpts, hc1, hc2, htree⟩ := treeOK_spec h₁ h₂ h
  exact ⟨hm, h0, fun k hk => (hpts k hk).1, fun k hk => (hpts k hk).2, hc1, hc2, treeOK_par h,
    htree⟩

section Data

variable {g₁ g₂ : G} {m r : ℕ} {pts lk : ℕ → ℕ} {pl : Table}

theorem TreeData.r_lt (hT : TreeData n g₁ g₂ m r pts lk pl) : r < n := by
  rw [← hT.root]; exact hT.pts_lt 0 hT.pos

theorem TreeData.mem_orbit_iff (hT : TreeData n g₁ g₂ m r pts lk pl) (p : Fin n) :
    p ∈ MulAction.orbit (Subgroup.closure ({g₁, g₂} : Set G)) (⟨r, hT.r_lt⟩ : Fin n) ↔
      ∃ k < m, pts k = p.val := by
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    let S : Set (Fin n) := {q | ∃ k < m, pts k = q.val}
    have hS : S.Finite := Set.toFinite S
    have hmem : ∀ (K : Subgroup.closure ({g₁, g₂} : Set G)), ∀ q ∈ S, K • q ∈ S := by
      intro K
      refine smul_mem_of_closure (closure_pair_subtype g₁ g₂) hS ?_ ?_ K
      · rintro q ⟨k, hk, hq⟩
        refine ⟨lk (idx n g₁ (pts k)), (hT.c1 k hk).1, ?_⟩
        rw [(hT.c1 k hk).2, hq]
        exact idx_val g₁ q
      · rintro q ⟨k, hk, hq⟩
        refine ⟨lk (idx n g₂ (pts k)), (hT.c2 k hk).1, ?_⟩
        rw [(hT.c2 k hk).2, hq]
        exact idx_val g₂ q
    exact hmem ⟨g, hg⟩ _ ⟨0, hT.pos, hT.root⟩
  · rintro ⟨k, hk, hp⟩
    have hmemK : treeElt pl (lettersG g₁ g₂) k ∈ Subgroup.closure ({g₁, g₂} : Set G) :=
      treeElt_mem (Subgroup.closure ({g₁, g₂} : Set G)) pl
        (lettersG_mem (Subgroup.closure ({g₁, g₂} : Set G))
          (Subgroup.subset_closure (Set.mem_insert _ _))
          (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))) k
    refine ⟨⟨treeElt pl (lettersG g₁ g₂) k, hmemK⟩, ?_⟩
    apply smul_eq_of_idx
    rw [← hp]
    exact hT.elt k hk

theorem TreeData.card_orbit (hT : TreeData n g₁ g₂ m r pts lk pl) :
    Nat.card (MulAction.orbit (Subgroup.closure ({g₁, g₂} : Set G)) (⟨r, hT.r_lt⟩ : Fin n)) =
      m := by
  let f : Fin m → MulAction.orbit (Subgroup.closure ({g₁, g₂} : Set G)) (⟨r, hT.r_lt⟩ : Fin n) :=
    fun k => ⟨⟨pts k, hT.pts_lt k k.isLt⟩, (hT.mem_orbit_iff _).2 ⟨k, k.isLt, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro k k' hkk'
      have := congrArg (fun q : MulAction.orbit _ _ => lk q.val.val) hkk'
      simp only [f] at this
      rw [hT.lk_pts k k.isLt, hT.lk_pts k' k'.isLt] at this
      exact Fin.ext this
    · rintro ⟨q, hq⟩
      obtain ⟨k, hk, hkq⟩ := (hT.mem_orbit_iff q).1 hq
      exact ⟨⟨k, hk⟩, Subtype.ext (Fin.ext hkq)⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem TreeData.lt_of_treeEdge (hT : TreeData n g₁ g₂ m r pts lk pl) {s i j : ℕ} (hj : j < m)
    (h : treeEdge pl s i j = true) : i < j := by
  simp only [treeEdge, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rw [← h.1.2]
  exact hT.par j hj h.1.1

theorem TreeData.pos_spec (hT : TreeData n g₁ g₂ m r pts lk pl) {p : Fin n}
    (hp : p ∈ MulAction.orbit (Subgroup.closure ({g₁, g₂} : Set G)) (⟨r, hT.r_lt⟩ : Fin n)) :
    lk p.val < m ∧ pts (lk p.val) = p.val := by
  obtain ⟨k, hk, hkp⟩ := (hT.mem_orbit_iff p).1 hp
  rw [← hkp, hT.lk_pts k hk]
  exact ⟨hk, rfl⟩

theorem TreeData.stab_le_two_three (hT : TreeData n g₁ g₂ m r pts lk pl) (hg₁ : g₁ ^ 2 = 1)
    (hg₂ : g₂ ^ 3 = 1) (K' : Subgroup G) {P₁ P₂ : ℕ → ℕ}
    (hP₁ : ∀ k < m, P₁ k = lk (idx n g₁ (pts k))) (hP₂ : ∀ k < m, P₂ k = lk (idx n g₂ (pts k)))
    (h₁ : ∀ k < m, reqTwo pl P₁ 1 k = true →
      (treeElt pl (lettersG g₁ g₂) (P₁ k))⁻¹ * g₁ * treeElt pl (lettersG g₁ g₂) k ∈ K')
    (h₂ : ∀ k < m, reqThree pl P₂ 2 k = true →
      (treeElt pl (lettersG g₁ g₂) (P₂ k))⁻¹ * g₂ * treeElt pl (lettersG g₁ g₂) k ∈ K') :
    ∀ g ∈ Subgroup.closure ({g₁, g₂} : Set G), idx n g r = r → g ∈ K' := by
  intro g hg hfix
  set K := Subgroup.closure ({g₁, g₂} : Set G) with hKdef
  set r' : Fin n := ⟨r, hT.r_lt⟩ with hr'
  let X := MulAction.orbit K r'
  let x₀ : X := ⟨r', MulAction.mem_orbit_self r'⟩
  let a' : K := ⟨g₁, Subgroup.subset_closure (Set.mem_insert _ _)⟩
  let b' : K := ⟨g₂, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩
  let LG := lettersG g₁ g₂
  have hLmem : ∀ k, treeElt pl LG k ∈ K := fun k =>
    treeElt_mem K pl (lettersG_mem K (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))) k
  let pos : X → ℕ := fun q => lk q.val.val
  have hpos : ∀ q : X, pos q < m ∧ pts (pos q) = q.val.val := fun q => hT.pos_spec q.property
  let t : X → K := fun q => ⟨treeElt pl LG (pos q), hLmem _⟩
  have ht : ∀ q, t q • x₀ = q := by
    intro q
    apply Subtype.ext
    apply smul_eq_of_idx
    rw [← (hpos q).2]
    exact hT.elt _ (hpos q).1
  have ht1 : t x₀ = 1 := by
    apply Subtype.ext
    show treeElt pl LG (lk r) = 1
    have : lk r = 0 := by rw [← hT.root, hT.lk_pts 0 hT.pos]
    rw [this, treeElt_zero]
  have hposa : ∀ q : X, pos (a' • q) = P₁ (pos q) := by
    intro q
    rw [hP₁ _ (hpos q).1, (hpos q).2]
    show lk ((g₁ • (q.val : Fin n)).val) = _
    rw [← idx_val]
  have hposb : ∀ q : X, pos (b' • q) = P₂ (pos q) := by
    intro q
    rw [hP₂ _ (hpos q).1, (hpos q).2]
    show lk ((g₂ • (q.val : Fin n)).val) = _
    rw [← idx_val]
  have hP₁lt : ∀ k < m, P₁ k < m := fun k hk => by rw [hP₁ k hk]; exact (hT.c1 k hk).1
  have hP₂lt : ∀ k < m, P₂ k < m := fun k hk => by rw [hP₂ k hk]; exact (hT.c2 k hk).1
  have hP₁pts : ∀ k < m, pts (P₁ k) = idx n g₁ (pts k) := fun k hk => by
    rw [hP₁ k hk]; exact (hT.c1 k hk).2
  have hP₂pts : ∀ k < m, pts (P₂ k) = idx n g₂ (pts k) := fun k hk => by
    rw [hP₂ k hk]; exact (hT.c2 k hk).2
  have hinv₁ : ∀ k < m, P₁ (P₁ k) = k := by
    intro k hk
    rw [hP₁ _ (hP₁lt k hk), hP₁pts k hk, ← idx_mul, ← pow_two, hg₁, idx_one, hT.lk_pts k hk]
  have hinv₂ : ∀ k < m, P₂ (P₂ (P₂ k)) = k := by
    intro k hk
    rw [hP₂ _ (hP₂lt _ (hP₂lt k hk)), hP₂pts _ (hP₂lt k hk), hP₂pts k hk, ← idx_mul, ← idx_mul,
      ← pow_three', hg₂, idx_one, hT.lk_pts k hk]
  let Ea : Set X := {q | reqTwo pl P₁ 1 (pos q) = true ∨ treeEdge pl 1 (pos q) (P₁ (pos q)) = true}
  let Eb : Set X :=
    {q | reqThree pl P₂ 2 (pos q) = true ∨ treeEdge pl 2 (pos q) (P₂ (pos q)) = true}
  have hEa : ∀ q ∈ Ea, (t (a' • q))⁻¹ * a' * t q ∈ K'.subgroupOf K := by
    intro q hq
    rw [Subgroup.mem_subgroupOf]
    show (treeElt pl LG (pos (a' • q)))⁻¹ * g₁ * treeElt pl LG (pos q) ∈ K'
    rw [hposa]
    rcases hq with hreq | htree
    · exact h₁ _ (hpos q).1 hreq
    · rw [treeElt_of_treeEdge pl LG htree
        (hT.lt_of_treeEdge (hP₁lt _ (hpos q).1) htree)]
      have : LG 1 = g₁ := by simp [LG, lettersG]
      rw [this, mul_inv_rev, mul_assoc, mul_assoc, inv_mul_cancel_left, inv_mul_cancel]
      exact K'.one_mem
  have hEb : ∀ q ∈ Eb, (t (b' • q))⁻¹ * b' * t q ∈ K'.subgroupOf K := by
    intro q hq
    rw [Subgroup.mem_subgroupOf]
    show (treeElt pl LG (pos (b' • q)))⁻¹ * g₂ * treeElt pl LG (pos q) ∈ K'
    rw [hposb]
    rcases hq with hreq | htree
    · exact h₂ _ (hpos q).1 hreq
    · rw [treeElt_of_treeEdge pl LG htree
        (hT.lt_of_treeEdge (hP₂lt _ (hpos q).1) htree)]
      have : LG 2 = g₂ := by simp [LG, lettersG]
      rw [this, mul_inv_rev, mul_assoc, mul_assoc, inv_mul_cancel_left, inv_mul_cancel]
      exact K'.one_mem
  have hca : ∀ q, q ∈ Ea ∨ (a' • q ≠ q ∧ a' • q ∈ Ea) := by
    intro q
    rcases reqTwo_cover pl P₁ 1 (pos q) (hinv₁ _ (hpos q).1) with h | ⟨hne, h⟩
    · exact Or.inl h
    · right
      refine ⟨fun heq => hne ?_, ?_⟩
      · rw [← hposa, heq]
      · show reqTwo pl P₁ 1 (pos (a' • q)) = true ∨
          treeEdge pl 1 (pos (a' • q)) (P₁ (pos (a' • q))) = true
        rw [hposa]
        exact h
  have hcb : ∀ q, q ∈ Eb ∨ (b' • q ≠ q ∧ b' • q ∈ Eb ∧ b' • (b' • q) ∈ Eb) := by
    intro q
    rcases reqThree_cover pl P₂ 2 (pos q) (hinv₂ _ (hpos q).1) with h | ⟨hne, h, h'⟩
    · exact Or.inl h
    · right
      refine ⟨fun heq => hne ?_, ?_, ?_⟩
      · rw [← hposb, heq]
      · show reqThree pl P₂ 2 (pos (b' • q)) = true ∨
          treeEdge pl 2 (pos (b' • q)) (P₂ (pos (b' • q))) = true
        rw [hposb]
        exact h
      · show reqThree pl P₂ 2 (pos (b' • (b' • q))) = true ∨
          treeEdge pl 2 (pos (b' • (b' • q))) (P₂ (pos (b' • (b' • q)))) = true
        rw [hposb, hposb]
        exact h'
  have ha' : a' ^ 2 = 1 := Subtype.ext (by simpa using hg₁)
  have hb' : b' ^ 3 = 1 := Subtype.ext (by simpa using hg₂)
  have hstab := stabilizer_le_of_schreier_two_three x₀ a' b' (closure_pair_subtype g₁ g₂) ha' hb'
    (K'.subgroupOf K) t ht ht1 Ea Eb hEa hEb hca hcb
  have hmem : (⟨g, hg⟩ : K) ∈ MulAction.stabilizer K x₀ := by
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    exact smul_eq_of_idx g r' r' hfix
  exact (Subgroup.mem_subgroupOf).1 (hstab hmem)

theorem TreeData.stab_eq_one (hT : TreeData n g₁ g₂ m r pts lk pl) {P : ℕ → ℕ → ℕ}
    (hP : ∀ s, ∀ k < m, P s k = lk (idx n (lettersG g₁ g₂ s) (pts k)))
    (h : ∀ k < m, ∀ s ∈ ({1, 2} : Finset ℕ),
      (treeElt pl (lettersG g₁ g₂) (P s k))⁻¹ * lettersG g₁ g₂ s *
        treeElt pl (lettersG g₁ g₂) k = 1) :
    ∀ g ∈ Subgroup.closure ({g₁, g₂} : Set G), idx n g r = r → g = 1 := by
  intro g hg hfix
  set K := Subgroup.closure ({g₁, g₂} : Set G) with hKdef
  set r' : Fin n := ⟨r, hT.r_lt⟩ with hr'
  let X := MulAction.orbit K r'
  let x₀ : X := ⟨r', MulAction.mem_orbit_self r'⟩
  let a' : K := ⟨g₁, Subgroup.subset_closure (Set.mem_insert _ _)⟩
  let b' : K := ⟨g₂, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩
  let LG := lettersG g₁ g₂
  have hLmem : ∀ k, treeElt pl LG k ∈ K := fun k =>
    treeElt_mem K pl (lettersG_mem K (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))) k
  let pos : X → ℕ := fun q => lk q.val.val
  have hpos : ∀ q : X, pos q < m ∧ pts (pos q) = q.val.val := fun q => hT.pos_spec q.property
  let t : X → K := fun q => ⟨treeElt pl LG (pos q), hLmem _⟩
  have ht : ∀ q, t q • x₀ = q := by
    intro q
    apply Subtype.ext
    apply smul_eq_of_idx
    rw [← (hpos q).2]
    exact hT.elt _ (hpos q).1
  have ht1 : t x₀ = 1 := by
    apply Subtype.ext
    show treeElt pl LG (lk r) = 1
    have : lk r = 0 := by rw [← hT.root, hT.lk_pts 0 hT.pos]
    rw [this, treeElt_zero]
  have hposs : ∀ (s : ℕ) (q : X), pos ((⟨LG s, lettersG_mem K (Subgroup.subset_closure
      (Set.mem_insert _ _)) (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) s⟩ : K) • q) =
      P s (pos q) := by
    intro s q
    rw [hP s _ (hpos q).1, (hpos q).2]
    show lk ((LG s • (q.val : Fin n)).val) = _
    rw [← idx_val]
  have hK : ∀ s' ∈ ({a', b'} : Set K), ∀ q : X, (t (s' • q))⁻¹ * s' * t q ∈ (⊥ : Subgroup K) := by
    intro s' hs' q
    rw [Subgroup.mem_bot]
    rcases hs' with rfl | rfl
    · have h1 : a' = (⟨LG 1, lettersG_mem K (Subgroup.subset_closure (Set.mem_insert _ _))
          (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) 1⟩ : K) :=
        Subtype.ext (by simp [LG, lettersG, a'])
      rw [h1]
      apply Subtype.ext
      show (treeElt pl LG (pos _))⁻¹ * LG 1 * treeElt pl LG (pos q) = 1
      rw [hposs 1 q]
      exact h _ (hpos q).1 1 (by simp)
    · have h2 : b' = (⟨LG 2, lettersG_mem K (Subgroup.subset_closure (Set.mem_insert _ _))
          (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) 2⟩ : K) :=
        Subtype.ext (by simp [LG, lettersG, b'])
      rw [h2]
      apply Subtype.ext
      show (treeElt pl LG (pos _))⁻¹ * LG 2 * treeElt pl LG (pos q) = 1
      rw [hposs 2 q]
      exact h _ (hpos q).1 2 (by simp)
  have hstab := stabilizer_le_of_schreier_mem x₀ (closure_pair_subtype g₁ g₂) ⊥ t ht ht1 hK
  have hmem : (⟨g, hg⟩ : K) ∈ MulAction.stabilizer K x₀ := by
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    exact smul_eq_of_idx g r' r' hfix
  have := hstab hmem
  rw [Subgroup.mem_bot] at this
  exact congrArg Subtype.val this

end Data

end TreeOrbit

section Reps

variable {c : ℕ} (hC : CertFacts c)
include hC

theorem nX_ge : 124 ≤ nX := by rw [hC.count]; norm_num

theorem nX_lt : nX < 2 ^ 32 := by rw [hC.count]; norm_num

end Reps

end CFSG.Sporadic.Th
