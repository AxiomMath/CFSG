module

public import CFSG.Sporadic.HNSchreier.ThreeSpec
public import Certificates.Certificate16025
public import Certificates.Certificate2096
public import Certificates.Certificate2097
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2105
public import Certificates.Certificate2109
public import Certificates.Certificate16041
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNSchreier

open CFSG.Blueprint.NativeSporadic CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.He.Native Matrix Equiv

theorem isChain_of_zip_tail : ∀ {L : List ℕ}, (∀ p ∈ L.zip L.tail, p.1 < p.2) →
    L.IsChain (· < ·)
  | [], _ => List.isChain_nil
  | [_], _ => List.isChain_singleton _
  | a :: b :: L, h => by
    rw [List.isChain_cons]
    refine ⟨fun y hy => ?_, isChain_of_zip_tail fun p hp => h p ?_⟩
    · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      exact h (a, b) (by simp)
    · rw [List.tail_cons, List.zip_cons_cons]
      exact List.mem_cons_of_mem _ hp

theorem card_filter_range_eq_countP (n : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ((Finset.range n).filter p).card = (List.range n).countP fun i => decide (p i) := by
  rw [Finset.card, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.coe_card, List.countP_eq_length_filter]

theorem fixListOK_spec {t : Array ℕ} {g : Perm X} {L : List ℕ} (hrep : PRep hnsData.n t g)
    (h : fixListOK hnsData.n t L = true) :
    (∀ x : X, g x = x ↔ x.val ∈ L) ∧
      (Finset.univ.filter fun x : X => g x = x).card = L.length := by
  unfold fixListOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hsort, hfix⟩, hcount⟩ := h
  have hnodup : L.Nodup :=
    ((isChain_of_zip_tail hsort).pairwise).imp fun h => ne_of_lt h
  have hfixed : ∀ x : X, g x = x ↔ t[x.val]! = x.val := by
    intro x
    rw [hrep x]
    exact ⟨fun e => by rw [e], fun e => Fin.ext e⟩
  set S := (Finset.range hnsData.n).filter fun i => t[i]! = i
  have hS : S.card = L.length := by
    rw [card_filter_range_eq_countP, ← hcount]
    congr 1
  have hsub : L.toFinset ⊆ S := by
    intro x hx
    rw [List.mem_toFinset] at hx
    obtain ⟨hxn, hxt⟩ := hfix x hx
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hxn, hxt⟩
  have hSL : S = L.toFinset := (Finset.eq_of_subset_of_card_le hsub (by
    rw [hS, List.toFinset_card_of_nodup hnodup])).symm
  have hmem : ∀ x : X, g x = x ↔ x.val ∈ L := by
    intro x
    rw [hfixed, ← List.mem_toFinset, ← hSL]
    simp [S, x.isLt]
  refine ⟨hmem, ?_⟩
  rw [← hS]
  refine Finset.card_bij (fun x _ => x.val) ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx
    rw [hSL, List.mem_toFinset]
    exact (hmem x).1 hx.2
  · intro x _ y _ hxy
    exact Fin.ext hxy
  · intro i hi
    have hi' := Finset.mem_filter.1 hi
    refine ⟨⟨i, Finset.mem_range.1 hi'.1⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (hfixed _).2 hi'.2⟩

theorem getElem!_map_lt {α β : Type*} [Inhabited α] [Inhabited β] (A : Array α) (f : α → β)
    {j : ℕ} (hj : j < A.size) : (A.map f)[j]! = f A[j]! := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_map, getElem!_pos A j hj]

theorem sJ_rep
    {k : ℕ} (hk : k < 4) : PRep hnsData.n
    (pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) FAData.sWords[k]!)
    (permJ (sJ k)) := prep_hWord (three_parts.1 k hk).1

theorem fixed_sJ
    {k : ℕ} (hk : k < 4) :
    (∀ x : X, sJ k • x = x ↔ x.val ∈ FAData.sFixed[k]!) ∧
      (Finset.univ.filter fun x : X => sJ k • x = x).card = (FAData.sFixed[k]!).length :=
  fixListOK_spec (sJ_rep hk) (three_parts.1 k hk).2

theorem c1J_rep
    {j : ℕ} (hj : j < 8) : PRep hnsData.n c1Arrs[j]! (permJ (c1J j)) := by
  have hs : j < FAData.c1Words.size := by rw [three_parts.2.1]; exact hj
  rw [c1Arrs_eq, getElem!_map_lt _ _ hs]
  exact prep_hWord (three_parts.2.2.2.1 j hj).1

theorem g3J_rep :
    PRep hnsData.n g3Arr (permJ g3J) := by
  obtain ⟨-, -, -, -, -, hg3H, hg3R, -⟩ := three_parts
  rw [g3Arr_eq, g3J, map_mul]
  refine prep_pcomp (prep_seedWordArr _ ?_) (prep_hWord hg3H)
  intro l hl
  have := List.all_eq_true.1 hg3R l hl
  simpa [beq_iff_eq] using this

theorem getElem!_push_size {α : Type*} [Inhabited α] (A : Array α) (x : α) :
    (A.push x)[A.size]! = x := by
  rw [getElem!_pos _ _ (by simp)]
  exact Array.getElem_push_eq

theorem c3J_rep
    {j : ℕ} (hj : j < 7) : PRep hnsData.n c3Arrs[j]! (permJ (c3J j)) := by
  have hsz : FAData.c3Words.size = 6 := three_parts.2.2.1
  rcases Nat.lt_or_ge j 6 with h6 | h6
  · have hs : j < (FAData.c3Words.map fun w =>
        pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) w).size := by simp [hsz, h6]
    rw [c3Arrs_eq, getElem!_pos _ j (by simp [hsz]; omega), Array.getElem_push_lt hs,
      ← getElem!_pos _ j hs, getElem!_map_lt _ _ (by rw [hsz]; exact h6), c3J, ite_eq_left h6]
    exact prep_hWord (three_parts.2.2.2.2.1 j h6)
  · have hj6 : j = 6 := by omega
    subst hj6
    have hs : (FAData.c3Words.map fun w =>
        pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) w).size = 6 := by simp [hsz]
    have e := getElem!_push_size (FAData.c3Words.map fun w =>
      pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) w) g3Arr
    rw [hs] at e
    rw [c3Arrs_eq, e, c3J, ite_eq_right (by norm_num)]
    exact g3J_rep

theorem comm_of_peq
    {t s : Array ℕ} {g h : JH} (ht : PRep hnsData.n t (permJ g))
    (hs : PRep hnsData.n s (permJ h))
    (hc : peq hnsData.n (pcomp hnsData.n t s) (pcomp hnsData.n s t) = true) : g * h = h * g := by
  apply permJ_injective
  rw [map_mul, map_mul]
  exact eq_of_peq (prep_pcomp ht hs) (prep_pcomp hs ht) hc

theorem c1J_comm
    {j : ℕ} (hj : j < 8) : c1J j * sJ 0 = sJ 0 * c1J j :=
  comm_of_peq (c1J_rep hj) (sJ_rep (by norm_num)) (three_parts.2.2.2.1 j hj).2

theorem c3J_comm
    {j : ℕ} (hj : j < 7) : c3J j * sJ 2 = sJ 2 * c3J j :=
  comm_of_peq (c3J_rep hj) (sJ_rep (by norm_num)) (three_parts.2.2.2.2.2.2.2.1 j hj)

theorem size_of_all {A : Array Table} (h : A.all (fun t => t.size == hnsData.n) = true) {l : ℕ}
    (hl : l < A.size) : A[l]!.size = hnsData.n := by
  rw [Array.all_eq_true] at h
  have := h l hl
  rw [getElem!_pos A l hl]
  simpa using this

theorem rep_letters1 :
    ∀ l ∈ Array.range (c1Arrs.map toTable).size,
    Rep hnsData.n (c1Arrs.map toTable)[l]! (permJ (c1J l)) := by
  obtain ⟨-, -, -, -, -, -, -, -, h8, -, h10, -⟩ := three_parts
  intro l hl
  rw [Array.mem_range, h8] at hl
  have hs : l < c1Arrs.size := by
    have : l < (c1Arrs.map toTable).size := by rw [h8]; exact hl
    simpa using this
  have hsz := size_of_all h10 (show l < (c1Arrs.map toTable).size by rw [h8]; exact hl)
  rw [getElem!_map_lt _ _ hs] at hsz ⊢
  refine rep_toTable (c1J_rep hl) hsz fun i hi => ?_
  rw [c1J_rep hl ⟨i, hi⟩]
  exact Fin.isLt _

theorem rep_letters3 :
    ∀ l ∈ Array.range (c3Arrs.map toTable).size,
    Rep hnsData.n (c3Arrs.map toTable)[l]! (permJ (c3J l)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h9, -, h11, -⟩ := three_parts
  intro l hl
  rw [Array.mem_range, h9] at hl
  have hs : l < c3Arrs.size := by
    have : l < (c3Arrs.map toTable).size := by rw [h9]; exact hl
    simpa using this
  have hsz := size_of_all h11 (show l < (c3Arrs.map toTable).size by rw [h9]; exact hl)
  rw [getElem!_map_lt _ _ hs] at hsz ⊢
  refine rep_toTable (c3J_rep hl) hsz fun i hi => ?_
  rw [c3J_rep hl ⟨i, hi⟩]
  exact Fin.isLt _

abbrev K1P : Subgroup (Perm X) :=
  lettersGroup (Array.range (c1Arrs.map toTable).size) fun l => permJ (c1J l)

abbrev K3P : Subgroup (Perm X) :=
  lettersGroup (Array.range (c3Arrs.map toTable).size) fun l => permJ (c3J l)

theorem tree0_facts :
    TreeFacts hnsData.n tree0 (Array.range (c1Arrs.map toTable).size)
    (fun l => permJ (c1J l)) 0 :=
  treeOK_facts rep_letters1 three_parts.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem tree1_facts :
    TreeFacts hnsData.n tree1 (Array.range (c1Arrs.map toTable).size)
    (fun l => permJ (c1J l)) 1047 :=
  treeOK_facts rep_letters1 three_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem tree2_facts :
    TreeFacts hnsData.n tree2 (Array.range (c1Arrs.map toTable).size)
    (fun l => permJ (c1J l)) 119497 :=
  treeOK_facts rep_letters1 three_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem tree3_facts :
    TreeFacts hnsData.n tree3 (Array.range (c3Arrs.map toTable).size)
    (fun l => permJ (c3J l)) 0 :=
  treeOK_facts rep_letters3 three_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

abbrev CJ (g : JH) : Subgroup JH := Subgroup.centralizer {g}

abbrev CJP (g : JH) : Subgroup (Perm X) := (CJ g).map permJ

theorem card_CJP (g : JH) : Nat.card (CJP g) = Nat.card (CJ g) :=
  Subgroup.card_map_of_injective permJ_injective

theorem card_CJ_dvd
    (g : JH) : Nat.card (CJ g) ∣ 273030912000000 :=
  card_JH ▸ Subgroup.card_subgroup_dvd_card _

theorem mem_CJ {g h : JH} : h ∈ CJ g ↔ g * h = h * g := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact eq_comm

theorem orbit_CJ_eq (g : JH) (y : X) :
    MulAction.orbit (CJ g) y = MulAction.orbit (CJP g) y := by
  ext z
  constructor
  · rintro ⟨⟨h, hh⟩, rfl⟩
    exact ⟨⟨permJ h, ⟨h, hh, rfl⟩⟩, rfl⟩
  · rintro ⟨⟨p, ⟨h, hh, rfl⟩⟩, rfl⟩
    exact ⟨⟨h, hh⟩, rfl⟩

theorem mem_CJP_comm {g : JH} {p : Perm X} (hp : p ∈ CJP g) : permJ g * p = p * permJ g := by
  obtain ⟨h, hh, rfl⟩ := hp
  rw [← map_mul, ← map_mul, mem_CJ.1 hh]

theorem CJP_maps_fix {g : JH} {p : Perm X} (hp : p ∈ CJP g) {y : X} (hy : permJ g y = y) :
    permJ g (p y) = p y := by
  have := congrArg (fun f : Perm X => f y) (mem_CJP_comm hp)
  simp only [Perm.mul_apply, hy] at this
  exact this

theorem orbit_CJP_fix
    {g : JH} (hg : g ∈ HJ) {y : X} (hy : y ∈ MulAction.orbit (CJP g) x0) :
    permJ g y = y := by
  obtain ⟨⟨p, hp⟩, rfl⟩ := hy
  exact CJP_maps_fix hp ((mem_HJ_iff_fix g).1 hg)

theorem orbit_sub_of_mem
    {G K : Subgroup (Perm X)} (hKG : K ≤ G) {x y r : X}
    (hy : y ∈ MulAction.orbit G x) (hyr : y ∈ MulAction.orbit K r) :
    MulAction.orbit K r ⊆ MulAction.orbit G x := by
  intro z hz
  rw [← MulAction.orbit_eq_iff.2 hyr] at hz
  obtain ⟨⟨k, hk⟩, rfl⟩ := hz
  rw [← MulAction.orbit_eq_iff.2 hy]
  exact ⟨⟨k, hKG hk⟩, rfl⟩

theorem K1P_le :
    K1P ≤ CJP (sJ 0) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨l, hl, rfl⟩
  rw [Array.mem_range, three_parts.2.2.2.2.2.2.2.2.1] at hl
  exact ⟨c1J l, mem_CJ.2 (c1J_comm hl).symm, rfl⟩

theorem K3P_le :
    K3P ≤ CJP (sJ 2) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨l, hl, rfl⟩
  rw [Array.mem_range, three_parts.2.2.2.2.2.2.2.2.2.1] at hl
  exact ⟨c3J l, mem_CJ.2 (c3J_comm hl).symm, rfl⟩

abbrev r1X :
    X := ⟨1047, tree1_facts.r_lt⟩

abbrev r2X :
    X := ⟨119497, tree2_facts.r_lt⟩

theorem orbit_K1P_x0 :
    MulAction.orbit K1P x0 = {x0} := by
  ext p
  rw [Set.mem_singleton_iff, show x0 = (⟨0, tree0_facts.r_lt⟩ : X) from rfl,
    tree0_facts.mem_orbit_iff]
  constructor
  · rintro ⟨k, hk, hkp⟩
    rw [three_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    exact Fin.ext (hkp.symm.trans tree0_facts.root)
  · rintro rfl
    exact ⟨0, tree0_facts.size_pos, tree0_facts.root⟩

theorem ncard_orbit_K1P_r1 :
    (MulAction.orbit K1P r1X).ncard = 560 := by
  rw [← Nat.card_coe_set_eq, tree1_facts.card_orbit,
    three_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]

theorem ncard_orbit_K1P_r2 :
    (MulAction.orbit K1P r2X).ncard = 84 := by
  rw [← Nat.card_coe_set_eq, tree2_facts.card_orbit,
    three_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]

theorem fix_s1_cover
    {y : X} (hy : permJ (sJ 0) y = y) :
    y ∈ MulAction.orbit K1P x0 ∨ y ∈ MulAction.orbit K1P r1X ∨ y ∈ MulAction.orbit K1P r2X := by
  have hy' : y.val ∈ FAData.sFixed[0]! := ((fixed_sJ (k := 0) (by norm_num)).1 y).1 hy
  have hall := List.all_eq_true.1 three_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ hy'
  simp only [Bool.or_eq_true, inTree, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hall
  rcases hall with (h | h) | h
  · left
    exact (tree0_facts.mem_orbit_iff y).2 ⟨_, h.1, h.2⟩
  · right; left
    exact (tree1_facts.mem_orbit_iff y).2 ⟨_, h.1, h.2⟩
  · right; right
    exact (tree2_facts.mem_orbit_iff y).2 ⟨_, h.1, h.2⟩

theorem orbit_inter_or
    {G : Subgroup (Perm X)} (hKG : K1P ≤ G) {x r : X} :
    MulAction.orbit G x ∩ MulAction.orbit K1P r = ∅ ∨
      MulAction.orbit K1P r ⊆ MulAction.orbit G x := by
  by_cases h : (MulAction.orbit G x ∩ MulAction.orbit K1P r).Nonempty
  · obtain ⟨y, hyG, hyK⟩ := h
    exact Or.inr (orbit_sub_of_mem hKG hyG hyK)
  · exact Or.inl (Set.not_nonempty_iff_eq_empty.1 h)

theorem x0_not_mem_r1 :
    x0 ∉ MulAction.orbit K1P r1X := by
  intro h
  have := ncard_orbit_K1P_r1
  rw [← MulAction.orbit_eq_iff.2 h, orbit_K1P_x0, Set.ncard_singleton] at this
  omega

theorem x0_not_mem_r2 :
    x0 ∉ MulAction.orbit K1P r2X := by
  intro h
  have := ncard_orbit_K1P_r2
  rw [← MulAction.orbit_eq_iff.2 h, orbit_K1P_x0, Set.ncard_singleton] at this
  omega

theorem disj_r1_r2 :
    Disjoint (MulAction.orbit K1P r1X) (MulAction.orbit K1P r2X) := by
  rw [Set.disjoint_left]
  intro y h1 h2
  have e1 := MulAction.orbit_eq_iff.2 h1
  have e2 := MulAction.orbit_eq_iff.2 h2
  have := ncard_orbit_K1P_r1
  rw [← e1, e2, ncard_orbit_K1P_r2] at this
  omega

theorem orbit_CJP_s1 :
    MulAction.orbit (CJP (sJ 0)) x0 = {x0} := by
  set O := MulAction.orbit (CJP (sJ 0)) x0
  have hsub : O ⊆ {x0} ∪ (O ∩ MulAction.orbit K1P r1X) ∪ (O ∩ MulAction.orbit K1P r2X) := by
    intro y hy
    rcases fix_s1_cover (orbit_CJP_fix (sJ_mem 0) hy) with h | h | h
    · left; left; rwa [orbit_K1P_x0] at h
    · left; right; exact ⟨hy, h⟩
    · right; exact ⟨hy, h⟩
  have hsup : {x0} ∪ (O ∩ MulAction.orbit K1P r1X) ∪ (O ∩ MulAction.orbit K1P r2X) ⊆ O := by
    rintro y ((rfl | ⟨h, -⟩) | ⟨h, -⟩)
    · exact MulAction.mem_orbit_self _
    · exact h
    · exact h
  have hO : O = {x0} ∪ (O ∩ MulAction.orbit K1P r1X) ∪ (O ∩ MulAction.orbit K1P r2X) :=
    le_antisymm hsub hsup
  have hd1 : Disjoint ({x0} : Set X) (O ∩ MulAction.orbit K1P r1X) :=
    Set.disjoint_singleton_left.2 fun h => x0_not_mem_r1 h.2
  have hd2 : Disjoint ({x0} ∪ (O ∩ MulAction.orbit K1P r1X)) (O ∩ MulAction.orbit K1P r2X) := by
    rw [Set.disjoint_union_left]
    exact ⟨Set.disjoint_singleton_left.2 fun h => x0_not_mem_r2 h.2,
      disj_r1_r2.mono Set.inter_subset_right Set.inter_subset_right⟩
  have hcard : O.ncard = 1 + (O ∩ MulAction.orbit K1P r1X).ncard +
      (O ∩ MulAction.orbit K1P r2X).ncard := by
    conv_lhs => rw [hO]
    rw [Set.ncard_union_eq hd2 (Set.toFinite _) (Set.toFinite _),
      Set.ncard_union_eq hd1 (Set.toFinite _) (Set.toFinite _), Set.ncard_singleton]
  have hdvd : O.ncard ∣ 273030912000000 := by
    rw [← MulAction.index_stabilizer]
    exact (Subgroup.index_dvd_card _).trans ((card_CJP _).symm ▸ card_CJ_dvd _)
  have ha : (O ∩ MulAction.orbit K1P r1X).ncard = 0 ∨
      (O ∩ MulAction.orbit K1P r1X).ncard = 560 := by
    rcases orbit_inter_or (G := CJP (sJ 0)) K1P_le (x := x0) (r := r1X) with h | h
    · left; rw [h, Set.ncard_empty]
    · right; rw [Set.inter_eq_right.2 h, ncard_orbit_K1P_r1]
  have hb : (O ∩ MulAction.orbit K1P r2X).ncard = 0 ∨ (O ∩ MulAction.orbit K1P r2X).ncard = 84 := by
    rcases orbit_inter_or (G := CJP (sJ 0)) K1P_le (x := x0) (r := r2X) with h | h
    · left; rw [h, Set.ncard_empty]
    · right; rw [Set.inter_eq_right.2 h, ncard_orbit_K1P_r2]
  have h1 : O.ncard = 1 := by
    rw [hcard] at hdvd ⊢
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp only [ha, hb] at hdvd ⊢ <;> omega
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h1
  have : x0 ∈ O := MulAction.mem_orbit_self _
  rw [ha, Set.mem_singleton_iff] at this
  rw [ha, this]

theorem CJ_s1_le :
    CJ (sJ 0) ≤ HJ := by
  intro h hh
  rw [mem_HJ_iff_fix, ← permJ_apply]
  have : permJ h x0 ∈ MulAction.orbit (CJP (sJ 0)) x0 := ⟨⟨permJ h, ⟨h, hh, rfl⟩⟩, rfl⟩
  rwa [orbit_CJP_s1, Set.mem_singleton_iff] at this

abbrev iotaA :
    alternatingGroup (Fin 12) →* JH :=
  HJ.subtype.comp (thetaJ.symm : alternatingGroup (Fin 12) →* HJ)

theorem iotaA_injective :
    Function.Injective iotaA :=
  Subtype.val_injective.comp thetaJ.symm.injective

theorem iotaA_theta
    (h : HJ) : iotaA (thetaJ h) = h := by
  show ((thetaJ.symm (thetaJ h) : HJ) : JH) = h
  rw [MulEquiv.symm_apply_apply]

theorem theta_sJ_eq
    {k : ℕ} (hk : k < 4) :
    thetaJ ⟨sJ k, sJ_mem k⟩ = ⟨tripleNat (k + 1), by
      rw [← thetaJ_sJ hk]; exact (thetaJ ⟨sJ k, sJ_mem k⟩).2⟩ :=
  Subtype.ext (thetaJ_sJ hk)

theorem theta_s1 :
    thetaJ ⟨sJ 0, sJ_mem 0⟩ = tri012A :=
  Subtype.ext ((thetaJ_sJ (k := 0) (by norm_num)).trans tripleNat_one)

theorem iotaA_tri012 :
    iotaA tri012A = sJ 0 := by
  rw [← theta_s1, iotaA_theta]

theorem CJ_eq_map
    {g : HJ} (hle : CJ g ≤ HJ) :
    CJ g = (Subgroup.centralizer {thetaJ g}).map iotaA := by
  ext x
  constructor
  · intro hx
    have hxH := hle hx
    refine ⟨thetaJ ⟨x, hxH⟩, ?_, iotaA_theta _⟩
    show thetaJ ⟨x, hxH⟩ ∈ Subgroup.centralizer {thetaJ g}
    have hc : g * ⟨x, hxH⟩ = ⟨x, hxH⟩ * g := Subtype.ext (mem_CJ.1 hx)
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hc]
  · rintro ⟨σ, hσ, rfl⟩
    rw [CJ, Subgroup.mem_centralizer_singleton_iff]
    have e : (g : JH) = iotaA (thetaJ g) := (iotaA_theta g).symm
    rw [e, ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hσ]

theorem CJ_s1_eq :
    CJ (sJ 0) = (Subgroup.centralizer {tri012A}).map iotaA := by
  have := CJ_eq_map (g := ⟨sJ 0, sJ_mem 0⟩) CJ_s1_le
  rw [theta_s1] at this
  exact this

abbrev L1J :
    Subgroup JH := alt3.map iotaA

theorem card_CJ_s1 :
    Nat.card (CJ (sJ 0)) = 544320 := by
  rw [CJ_s1_eq, Subgroup.card_map_of_injective iotaA_injective, card_centralizer_alt,
    tri012A_val, card_centralizer_tri012_alt]

theorem CJ_s1_structure :
    CJ (sJ 0) = Subgroup.zpowers (sJ 0) ⊔ L1J ∧
    Subgroup.zpowers (sJ 0) ⊓ L1J = ⊥ ∧ ∀ x ∈ L1J, x * sJ 0 = sJ 0 * x := by
  obtain ⟨hC, hinf, hcomm⟩ := centralizer_tri012
  refine ⟨?_, ?_, ?_⟩
  · rw [CJ_s1_eq, hC, Subgroup.map_sup, MonoidHom.map_zpowers, iotaA_tri012]
  · rw [← iotaA_tri012, ← MonoidHom.map_zpowers,
      ← Subgroup.map_inf_eq _ _ iotaA iotaA_injective, hinf, Subgroup.map_bot]
  · rintro _ ⟨σ, hσ, rfl⟩
    rw [← iotaA_tri012, ← map_mul, ← map_mul, hcomm σ hσ]

theorem commutator_CJ_s1 :
    ⁅CJ (sJ 0), CJ (sJ 0)⁆ = L1J := by
  rw [CJ_s1_eq, ← Subgroup.map_commutator, commutator_centralizer_tri012]

theorem CJP_preserves_fix
    {g : JH} {y : X} (hy : permJ g y = y) {z : X}
    (hz : z ∈ MulAction.orbit (CJP g) y) : permJ g z = z := by
  obtain ⟨⟨p, hp⟩, rfl⟩ := hz
  exact CJP_maps_fix hp hy

theorem card_CJP_s1 :
    Nat.card (CJP (sJ 0)) = 544320 := by rw [card_CJP, card_CJ_s1]

theorem orbit_dvd_544320
    (y : X) : (MulAction.orbit (CJP (sJ 0)) y).ncard ∣ 544320 := by
  rw [← MulAction.index_stabilizer, ← card_CJP_s1]
  exact Subgroup.index_dvd_card _

theorem fix_s1_of_K1P
    {y r : X} (hr : permJ (sJ 0) r = r) (hy : y ∈ MulAction.orbit K1P r) :
    permJ (sJ 0) y = y :=
  CJP_preserves_fix hr (orbit_sub_of_mem K1P_le (MulAction.mem_orbit_self r)
    (MulAction.mem_orbit_self r) hy)

theorem r1_fixed :
    permJ (sJ 0) r1X = r1X := by
  rw [permJ_apply, (fixed_sJ (k := 0) (by norm_num)).1]
  exact Certificates.certificate16025.1

theorem r2_fixed :
    permJ (sJ 0) r2X = r2X := by
  rw [permJ_apply, (fixed_sJ (k := 0) (by norm_num)).1]
  exact Certificates.certificate16025.2

theorem orbit_CJP_s1_eq
    {r r' : X} (hr : permJ (sJ 0) r = r)
    (hx0 : x0 ∉ MulAction.orbit K1P r)
    (hdisj : Disjoint (MulAction.orbit K1P r) (MulAction.orbit K1P r'))
    (hcov : ∀ y, permJ (sJ 0) y = y → y = x0 ∨ y ∈ MulAction.orbit K1P r ∨
      y ∈ MulAction.orbit K1P r')
    (hsum : ¬ ((MulAction.orbit K1P r).ncard + (MulAction.orbit K1P r').ncard) ∣ 544320) :
    MulAction.orbit (CJP (sJ 0)) r = MulAction.orbit K1P r := by
  set Q := MulAction.orbit (CJP (sJ 0)) r
  have hKQ : MulAction.orbit K1P r ⊆ Q := orbit_sub_of_mem K1P_le (MulAction.mem_orbit_self r)
    (MulAction.mem_orbit_self r)
  have hx0Q : x0 ∉ Q := by
    intro h
    have e : Q = {x0} := by rw [← orbit_CJP_s1]; exact (MulAction.orbit_eq_iff.2 h).symm
    have hr0 : r = x0 := Set.mem_singleton_iff.1 (e ▸ MulAction.mem_orbit_self r)
    exact hx0 (by rw [hr0]; exact MulAction.mem_orbit_self x0)
  rcases orbit_inter_or (G := CJP (sJ 0)) K1P_le (x := r) (r := r') with h | h
  · refine le_antisymm (fun y hy => ?_) hKQ
    rcases hcov y (CJP_preserves_fix hr hy) with rfl | h1 | h2
    · exact absurd hy hx0Q
    · exact h1
    · exact absurd (Set.mem_inter hy h2) (by rw [h]; exact Set.notMem_empty _)
  · exfalso
    have hQ : Q = MulAction.orbit K1P r ∪ MulAction.orbit K1P r' := by
      apply le_antisymm
      · intro y hy
        rcases hcov y (CJP_preserves_fix hr hy) with rfl | h1 | h2
        · exact absurd hy hx0Q
        · exact Or.inl h1
        · exact Or.inr h2
      · exact Set.union_subset hKQ h
    apply hsum
    rw [← Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), ← hQ]
    exact orbit_dvd_544320 r

theorem cover_s1
    (y : X) (hy : permJ (sJ 0) y = y) :
    y = x0 ∨ y ∈ MulAction.orbit K1P r1X ∨ y ∈ MulAction.orbit K1P r2X := by
  rcases fix_s1_cover hy with h | h | h
  · left; rwa [orbit_K1P_x0, Set.mem_singleton_iff] at h
  · right; left; exact h
  · right; right; exact h

theorem orbit_CJP_r1 :
    MulAction.orbit (CJP (sJ 0)) r1X = MulAction.orbit K1P r1X :=
  orbit_CJP_s1_eq r1_fixed x0_not_mem_r1 disj_r1_r2 cover_s1 (by
    rw [ncard_orbit_K1P_r1, ncard_orbit_K1P_r2]; norm_num)

theorem orbit_CJP_r2 :
    MulAction.orbit (CJP (sJ 0)) r2X = MulAction.orbit K1P r2X :=
  orbit_CJP_s1_eq r2_fixed x0_not_mem_r2 disj_r1_r2.symm (fun y hy => by
    rcases cover_s1 y hy with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)) (by rw [ncard_orbit_K1P_r1, ncard_orbit_K1P_r2]; norm_num)

theorem card_centralizer_equiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (g : G) :
    Nat.card (Subgroup.centralizer {g}) = Nat.card (Subgroup.centralizer {e g}) := by
  refine Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun x => ?_)
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  rw [← map_mul, ← map_mul, e.injective.eq_iff]

theorem card_CH_eq {g : HJ} :
    Nat.card (CJ g ⊓ HJ : Subgroup JH) = Nat.card (Subgroup.centralizer {g}) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨x.1, (Subgroup.mem_inf.1 x.2).2⟩,
        Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext
          (mem_CJ.1 (Subgroup.mem_inf.1 x.2).1).symm)⟩
      invFun := fun x => ⟨x.1.1, Subgroup.mem_inf.2 ⟨mem_CJ.2
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 x.2)).symm, x.1.2⟩⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }

theorem theta_s3 :
    (thetaJ ⟨sJ 2, sJ_mem 2⟩ : Perm (Fin 12)) = tri 0 1 2 * tri 3 4 5 * tri 6 7 8 :=
  (thetaJ_sJ (k := 2) (by norm_num)).trans tripleNat_three

theorem CH_eq_map
    (g : HJ) :
    (CJ g ⊓ HJ : Subgroup JH) = (Subgroup.centralizer {thetaJ g}).map iotaA := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxC, hxH⟩ := Subgroup.mem_inf.1 hx
    refine ⟨thetaJ ⟨x, hxH⟩, ?_, iotaA_theta _⟩
    show thetaJ ⟨x, hxH⟩ ∈ Subgroup.centralizer {thetaJ g}
    have hc : g * ⟨x, hxH⟩ = ⟨x, hxH⟩ * g := Subtype.ext (mem_CJ.1 hxC)
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hc]
  · rintro ⟨σ, hσ, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, (thetaJ.symm σ).2⟩
    rw [CJ, Subgroup.mem_centralizer_singleton_iff]
    have e : (g : JH) = iotaA (thetaJ g) := (iotaA_theta g).symm
    rw [e, ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hσ]

theorem tri3A_mem :
    tri 0 1 2 * tri 3 4 5 * tri 6 7 8 ∈ alternatingGroup (Fin 12) := by
  rw [← theta_s3]
  exact (thetaJ ⟨sJ 2, sJ_mem 2⟩).2

theorem card_CH_s3 :
    Nat.card (CJ (sJ 2) ⊓ HJ : Subgroup JH) = 486 := by
  have e : thetaJ ⟨sJ 2, sJ_mem 2⟩ = ⟨tri 0 1 2 * tri 3 4 5 * tri 6 7 8, tri3A_mem⟩ :=
    Subtype.ext theta_s3
  have := CH_eq_map ⟨sJ 2, sJ_mem 2⟩
  rw [e] at this
  rw [this, Subgroup.card_map_of_injective iotaA_injective, card_centralizer_alt]
  exact card_centralizer_tri3_alt

theorem fix_s3_card :
    (Finset.univ.filter fun x : X => sJ 2 • x = x).card = 60 := by
  have h := (fixed_sJ (k := 2) (by norm_num)).2
  rw [fa_data_sizes.1 2 (by norm_num)] at h
  exact h

theorem fix_s1_card :
    (Finset.univ.filter fun x : X => sJ 0 • x = x).card = 645 := by
  have h := (fixed_sJ (k := 0) (by norm_num)).2
  rw [fa_data_sizes.1 0 (by norm_num)] at h
  exact h

theorem fix_s3_set :
    {y : X | permJ (sJ 2) y = y}.ncard = 60 := by
  rw [← fix_s3_card, ← Set.ncard_coe_finset]
  congr 1
  ext y
  simp

theorem orbit_K3P_x0 :
    MulAction.orbit K3P x0 = {y | permJ (sJ 2) y = y} := by
  have hsub : MulAction.orbit K3P x0 ⊆ {y | permJ (sJ 2) y = y} := fun y hy =>
    orbit_CJP_fix (sJ_mem 2) (orbit_sub_of_mem K3P_le (MulAction.mem_orbit_self x0)
      (MulAction.mem_orbit_self x0) hy)
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  rw [fix_s3_set, ← Nat.card_coe_set_eq, show x0 = (⟨0, tree3_facts.r_lt⟩ : X) from rfl,
    tree3_facts.card_orbit, three_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]

abbrev C3gen : Subgroup JH := Subgroup.closure ((CJ (sJ 2) ⊓ HJ : Subgroup JH) ∪ {g3J})

theorem g3J_mem_CJ :
    g3J ∈ CJ (sJ 2) := by
  have h := c3J_comm (j := 6) (by norm_num)
  rw [c3J, ite_eq_right (by norm_num)] at h
  exact mem_CJ.2 h.symm

theorem C3gen_le :
    C3gen ≤ CJ (sJ 2) := by
  rw [Subgroup.closure_le]
  rintro x (hx | hx)
  · exact (Subgroup.mem_inf.1 hx).1
  · rw [Set.mem_singleton_iff.1 hx]
    exact g3J_mem_CJ

theorem c3J_mem_C3gen
    {l : ℕ} (hl : l < 7) : c3J l ∈ C3gen := by
  rcases Nat.lt_or_ge l 6 with h6 | h6
  · refine Subgroup.subset_closure (Or.inl (Subgroup.mem_inf.2 ⟨mem_CJ.2 (c3J_comm hl).symm, ?_⟩))
    rw [c3J, ite_eq_left h6]
    exact hWordJ_mem _
  · have : l = 6 := by omega
    subst this
    rw [c3J, ite_eq_right (by norm_num)]
    exact Subgroup.subset_closure (Or.inr rfl)

theorem K3P_le_C3gen :
    K3P ≤ C3gen.map permJ := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨l, hl, rfl⟩
  rw [Array.mem_range, three_parts.2.2.2.2.2.2.2.2.2.1] at hl
  exact ⟨c3J l, c3J_mem_C3gen hl, rfl⟩

theorem CJ_s3_eq :
    CJ (sJ 2) = C3gen := by
  refine le_antisymm (fun g hg => ?_) C3gen_le
  have hfix : permJ (sJ 2) (permJ g x0) = permJ g x0 :=
    orbit_CJP_fix (sJ_mem 2) ⟨⟨permJ g, ⟨g, hg, rfl⟩⟩, rfl⟩
  have hmem : permJ g x0 ∈ MulAction.orbit K3P x0 := by rw [orbit_K3P_x0]; exact hfix
  obtain ⟨⟨k, hk⟩, hkx⟩ := hmem
  obtain ⟨k', hk', rfl⟩ := K3P_le_C3gen hk
  have hstab : k'⁻¹ * g ∈ CJ (sJ 2) ⊓ HJ := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem (C3gen_le hk')) hg, ?_⟩
    rw [mem_HJ_iff_fix, mul_smul, ← permJ_apply g, ← hkx]
    show k'⁻¹ • (permJ k' x0) = x0
    rw [permJ_apply, inv_smul_smul]
  have : g = k' * (k'⁻¹ * g) := by group
  rw [this]
  exact mul_mem hk' (Subgroup.subset_closure (Or.inl hstab))

theorem orbit_CJ_s3 :
    MulAction.orbit (CJ (sJ 2)) x0 = {y | sJ 2 • y = y} := by
  rw [orbit_CJ_eq]
  apply le_antisymm
  · intro y hy
    exact orbit_CJP_fix (sJ_mem 2) hy
  · intro y hy
    have hy' : permJ (sJ 2) y = y := hy
    have hK : y ∈ MulAction.orbit K3P x0 := by rw [orbit_K3P_x0]; exact hy'
    exact orbit_sub_of_mem K3P_le (MulAction.mem_orbit_self x0) (MulAction.mem_orbit_self x0) hK

theorem card_CJ_s3 :
    Nat.card (CJ (sJ 2)) = 29160 := by
  have h := Subgroup.card_mul_index (MulAction.stabilizer (CJ (sJ 2)) x0)
  rw [MulAction.index_stabilizer, orbit_CJ_s3] at h
  have hstab : Nat.card (MulAction.stabilizer (CJ (sJ 2)) x0) = 486 := by
    rw [← card_CH_s3]
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, Subgroup.mem_inf.2 ⟨x.1.2, (mem_HJ_iff_fix _).2 x.2⟩⟩
        invFun := fun x => ⟨⟨x.1, (Subgroup.mem_inf.1 x.2).1⟩,
          (mem_HJ_iff_fix _).1 (Subgroup.mem_inf.1 x.2).2⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  have hfix : {y : X | sJ 2 • y = y}.ncard = 60 := by
    rw [← fix_s3_set]
    rfl
  rw [hstab, hfix] at h
  omega

theorem toMat_subId (M : Array (Array ℕ)) : toMat 5 133 (subId M) = toMat 5 133 M - 1 := by
  ext i j
  rw [Matrix.sub_apply, toMat_apply, toMat_apply, Matrix.one_apply]
  unfold subId
  rw [getElem!_ofFn _ i.isLt, getElem!_ofFn _ j.isLt, ZMod.natCast_mod]
  by_cases h : i = j
  · rw [ite_eq_left (congrArg Fin.val h), ite_eq_left h]
    push_cast
    have : (4 : ZMod 5) = -1 := by decide
    rw [this]
    exact (sub_eq_add_neg _ _).symm
  · rw [ite_eq_right (fun e => h (Fin.ext e)), ite_eq_right h, Nat.add_zero]
    exact (sub_zero _).symm

theorem toMat_diagR (r : ℕ) :
    toMat 5 133 (diagR r) = Matrix.diagonal fun i => if i.val < r then 1 else 0 := by
  ext i j
  rw [toMat_apply, Matrix.diagonal_apply]
  unfold diagR
  rw [getElem!_ofFn _ i.isLt, getElem!_ofFn _ j.isLt]
  by_cases h : i = j
  · subst h
    by_cases hr : i.val < r
    · simp [hr]
    · simp [hr]
  · have h' : ¬ i.val = j.val := fun e => h (Fin.ext e)
    simp [h, h']

theorem letters_of_plettersOK {w : List ℤ} (h : plettersOK 17 w = true) :
    ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 17 := by
  intro l hl
  have := List.all_eq_true.1 h l hl
  simpa [bne_iff_ne] using this

theorem rank_sJ
    {k : ℕ} (hk : k < 4) : (matJ (sJ k) - 1).rank = rankList[k]! := by
  have h := rank_cert
  unfold rankChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [← mRegs_eq, ← mH_eq, ← mHi_eq] at h
  have hk' := allBelowN_spec h.2 hk
  simp only [Bool.and_eq_true, beq_iff_eq] at hk'
  obtain ⟨⟨⟨⟨-, hlet⟩, hP⟩, hQ⟩, hE⟩ := hk'
  have hM : toMat 5 133 (subId (mword mH mHi FAData.sWords[k]!)) = matJ (sJ k) - 1 := by
    rw [toMat_subId, toMat_mword_hWord _ (letters_of_plettersOK hlet)]
    rfl
  have e := congrArg (toMat 5 133) hE
  rw [toMat_mulM, toMat_mulM, hM] at e
  have huP : IsUnit (toMat 5 133 (rankCertRows[k]!)[0]!).det :=
    Matrix.isUnit_det_of_right_inverse (by rw [← toMat_mulM, hP, toMat_idM])
  have huQ : IsUnit (toMat 5 133 (rankCertRows[k]!)[2]!).det :=
    Matrix.isUnit_det_of_right_inverse (by rw [← toMat_mulM, hQ, toMat_idM])
  rw [← Matrix.rank_mul_eq_right_of_isUnit_det _ _ huP,
    ← Matrix.rank_mul_eq_left_of_isUnit_det _ _ huQ, e, toMat_diagR, Matrix.rank_diagonal]
  interval_cases k <;> decide

theorem ctuc_hn_three_centralizers_exact :
    (Finset.univ.filter fun x : X => sJ 0 • x = x).card = 645 ∧
    CJ (sJ 0) ≤ HJ ∧ CJ (sJ 0) = (CJ (sJ 0) ⊓ HJ : Subgroup JH) ∧
    CJ (sJ 0) = Subgroup.zpowers (sJ 0) ⊔ L1J ∧ Subgroup.zpowers (sJ 0) ⊓ L1J = ⊥ ∧
    (∀ x ∈ L1J, x * sJ 0 = sJ 0 * x) ∧
    L1J = (alt3.comap (thetaJ : HJ →* alternatingGroup (Fin 12))).map HJ.subtype ∧
    Nat.card (CJ (sJ 0)) = 544320 ∧
    (MulAction.orbit (CJ (sJ 0)) x0).ncard = 1 ∧
    (MulAction.orbit (CJ (sJ 0)) r1X).ncard = 560 ∧
    (MulAction.orbit (CJ (sJ 0)) r2X).ncard = 84 ∧
    (∀ y : X, sJ 0 • y = y ↔ y ∈ MulAction.orbit (CJ (sJ 0)) x0 ∨
      y ∈ MulAction.orbit (CJ (sJ 0)) r1X ∨ y ∈ MulAction.orbit (CJ (sJ 0)) r2X) ∧
    (Finset.univ.filter fun x : X => sJ 2 • x = x).card = 60 ∧
    CJ (sJ 2) = Subgroup.closure ((CJ (sJ 2) ⊓ HJ : Subgroup JH) ∪ {g3J}) ∧
    Nat.card (CJ (sJ 2)) = 29160 ∧
    (∀ y : X, sJ 2 • y = y → ∃ g ∈ CJ (sJ 2), g • x0 = y) ∧
    (∀ k < 4, (matJ (sJ k) - 1).rank = [84, 84, 90, 84][k]!) ∧
    ⁅CJ (sJ 0), CJ (sJ 0)⁆ = L1J := by
  obtain ⟨hC, hinf, hcomm⟩ := CJ_s1_structure
  refine ⟨fix_s1_card, CJ_s1_le, (inf_eq_left.2 CJ_s1_le).symm, hC, hinf, hcomm, ?_, card_CJ_s1, ?_,
    ?_, ?_, ?_, fix_s3_card, CJ_s3_eq, card_CJ_s3, ?_, fun k hk => rank_sJ hk, commutator_CJ_s1⟩
  · ext x
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      refine ⟨thetaJ.symm σ, ?_, rfl⟩
      show thetaJ.symm σ ∈ alt3.comap (thetaJ : HJ →* alternatingGroup (Fin 12))
      rw [Subgroup.mem_comap]
      show thetaJ (thetaJ.symm σ) ∈ alt3
      rw [MulEquiv.apply_symm_apply]
      exact hσ
    · rintro ⟨h, hh, rfl⟩
      refine ⟨thetaJ h, hh, ?_⟩
      show ((thetaJ.symm (thetaJ h) : HJ) : JH) = h
      rw [MulEquiv.symm_apply_apply]
  · rw [orbit_CJ_eq, orbit_CJP_s1, Set.ncard_singleton]
  · rw [orbit_CJ_eq, orbit_CJP_r1, ncard_orbit_K1P_r1]
  · rw [orbit_CJ_eq, orbit_CJP_r2, ncard_orbit_K1P_r2]
  · intro y
    rw [orbit_CJ_eq, orbit_CJ_eq, orbit_CJ_eq, orbit_CJP_s1, orbit_CJP_r1, orbit_CJP_r2,
      Set.mem_singleton_iff, ← permJ_apply]
    constructor
    · exact cover_s1 y
    · rintro (rfl | h | h)
      · exact (mem_HJ_iff_fix _).1 (sJ_mem 0)
      · exact fix_s1_of_K1P r1_fixed h
      · exact fix_s1_of_K1P r2_fixed h
  · intro y hy
    have : y ∈ MulAction.orbit (CJ (sJ 2)) x0 := by rw [orbit_CJ_s3]; exact hy
    obtain ⟨⟨g, hg⟩, rfl⟩ := this
    exact ⟨g, hg, rfl⟩

end CFSG.Sporadic.HNSchreier
