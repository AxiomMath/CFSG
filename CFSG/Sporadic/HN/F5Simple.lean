module

public import CFSG.Sporadic.HN.F5Chain
public import CFSG.Sporadic.HN.ConjSimple

public section

namespace CFSG.Sporadic.F5

open Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.LevelChain CFSG.Sporadic.LevelChain.Native CFSG.Sporadic.Fi23
open CFSG.Sporadic.Fi23.Native
open CFSG.Sporadic.SmallF2.Native (labelsOf inTreeB ordOK)

theorem fold_ite_add_eq_sum (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℕ) :
    ∀ m, Nat.fold m (fun i _ acc => if P i then acc + f i else acc) 0 =
      ∑ i ∈ Finset.range m, if P i then f i else 0 := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.fold_succ, ih, Finset.sum_range_succ]
    split_ifs <;> simp

theorem testBit_sum_two_pow (s : Finset ℕ) (i : ℕ) :
    (∑ j ∈ s, 2 ^ j).testBit i = true ↔ i ∈ s := by
  rw [← Nat.mem_bitIndices]
  conv_rhs => rw [← Finset.toFinset_bitIndices_sum_two_pow s]
  rw [List.mem_toFinset]

theorem finset_of_divOK {n : ℕ} {sizes : List ℕ} (h : divOK n sizes = true) {k : ℕ}
    (hk : sizes.length = k + 1) :
    ∀ S : Finset (Fin (k + 1)), 0 ∈ S → (∑ i ∈ S, sizes[i.val]!) ∣ n →
      S = {0} ∨ S = Finset.univ := by
  intro S h0 hdvd
  obtain ⟨s, hs⟩ : ∃ s : Finset ℕ, s = S.map Fin.valEmbedding := ⟨_, rfl⟩
  obtain ⟨mask, hmask⟩ : ∃ mask : ℕ, mask = ∑ j ∈ s, 2 ^ j := ⟨_, rfl⟩
  have hbit : ∀ i, mask.testBit i = true ↔ i ∈ s := by
    intro i; rw [hmask]; exact testBit_sum_two_pow s i
  have hmem : ∀ i : Fin (k + 1), i.val ∈ s ↔ i ∈ S := by
    intro i; simp [hs, Fin.val_inj]
  have hs_lt : ∀ i ∈ s, i < k + 1 := by
    intro i hi
    simp only [hs, Finset.mem_map, Fin.valEmbedding_apply] at hi
    obtain ⟨j, -, rfl⟩ := hi
    exact j.isLt
  have hodd : mask.testBit 0 = true := (hbit 0).2 ((hmem 0).2 h0)
  have hmask_lt : mask < 2 ^ (k + 1) := by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    by_contra hc
    have := hs_lt i ((hbit i).1 (by simpa using hc))
    omega
  have hmask_eq : mask = 2 * (mask / 2) + 1 := by
    have := Nat.mod_two_eq_one_iff_testBit_zero.2 hodd
    omega
  have hm : mask / 2 < 2 ^ (sizes.length - 1) := by
    rw [hk, Nat.add_sub_cancel]
    rw [pow_succ] at hmask_lt
    omega
  have hcheck := (allIn_eq_true.1 h) (mask / 2) (Nat.zero_le _) hm
  rw [← hmask_eq] at hcheck
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, beq_iff_eq] at hcheck
  have hsum : maskSum sizes mask = ∑ i ∈ S, sizes[i.val]! := by
    unfold maskSum
    rw [fold_ite_add_eq_sum (fun i => mask.testBit i = true) (fun i => sizes[i]!), hk,
      ← Fin.sum_univ_eq_sum_range (fun i => if mask.testBit i = true then sizes[i]! else 0),
      ← Finset.sum_filter]
    congr 1
    ext i
    simp [hbit, hmem]
  rw [hsum] at hcheck
  rcases hcheck with (h1 | h1) | h1
  · exact absurd (Nat.mod_eq_zero_of_dvd hdvd) h1
  · left
    ext i
    rw [Finset.mem_singleton, ← hmem, ← hbit, show mask = 2 ^ 1 - 1 by omega,
      Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
    constructor
    · intro hi
      apply Fin.ext
      rw [Fin.val_zero]
      omega
    · rintro rfl
      rw [Fin.val_zero]
      omega
  · right
    ext i
    simp only [Finset.mem_univ, iff_true]
    rw [← hmem, ← hbit, h1, hk, Nat.testBit_two_pow_sub_one]
    simp only [decide_eq_true_eq]
    exact i.isLt

variable {D : F5Data} {c : ℕ} (hF : Facts D c)
include hF

theorem L_even : (L D).size % 2 = 0 := by
  rw [L_size hF]; omega

theorem rep_pairG_all : ∀ l < (L D).size, Rep D.n (L D)[l]! (pairG (gs D) l) := by
  obtain ⟨-, hinv, -⟩ := levelChainOK_parts hF.chain
  exact rep_pairG (rep_letters hF) (L_even hF) hinv

theorem lv1_lt {l : ℕ} (hl : l ∈ lv1 D) : l < (L D).size := by
  obtain ⟨hLsz, -, hsts, hmono, -⟩ := levelChainOK_parts hF.chain
  have hm := hF.base_two
  rw [lv1, mem_levelLv (hmono 1 (by omega))] at hl
  have := starts_mono hmono (1 + 1) D.base.size (by omega) le_rfl
  rw [hLsz]
  omega

theorem subTreeFacts {j : ℕ} (hj : j < D.subReps.size) :
    TreeFacts D.n (S D)[j]! (lv1 D) (pairG (gs D)) D.subReps[j]! :=
  treeOK_facts (fun l hl => rep_pairG_all hF l (lv1_lt hF hl)) (hF.subTrees j hj)

omit hF in
theorem lettersGroup_lv1 : lettersGroup (lv1 D) (pairG (gs D)) = lvl D 1 := rfl

omit hF in
theorem orbit_conj {H : Subgroup (J D)} {x p q : Fin D.n} (hp : p ∈ MulAction.orbit H x)
    (hq : q ∈ MulAction.orbit H x) : ∃ g ∈ H, g • p = q := by
  obtain ⟨⟨u, hu⟩, rfl⟩ := hp
  obtain ⟨⟨v, hv⟩, rfl⟩ := hq
  refine ⟨v * u⁻¹, H.mul_mem hv (H.inv_mem hu), ?_⟩
  show (v * u⁻¹) • (u • x) = v • x
  rw [mul_smul, inv_smul_smul]

omit hF in
theorem orbit_smul_mem' {H : Subgroup (J D)} {x p : Fin D.n} {g : J D} (hg : g ∈ H)
    (hp : p ∈ MulAction.orbit H x) : g • p ∈ MulAction.orbit H x := by
  obtain ⟨⟨u, hu⟩, rfl⟩ := hp
  refine ⟨⟨g * u, H.mul_mem hg hu⟩, ?_⟩
  show (g * u) • x = g • (u • x)
  exact mul_smul g u x

theorem mem_subTree_iff {j : ℕ} (hj : j < D.subReps.size) (p : Fin D.n) :
    (∃ t < (S D)[j]!.pts.size, ap (S D)[j]!.pts t = p.val) ↔
      p ∈ MulAction.orbit (lvl D 1) (⟨D.subReps[j]!, (subTreeFacts hF hj).r_lt⟩ : Fin D.n) :=
  ((subTreeFacts hF hj).mem_orbit_iff p).symm

theorem labs_iff {j : ℕ} (hj : j < D.subReps.size) (p : Fin D.n) :
    (labs D)[p.val]! = j ↔ ∃ t < (S D)[j]!.pts.size, ap (S D)[j]!.pts t = p.val := by
  constructor
  · intro h
    have hm := hF.labs_mem p.val p.isLt
    simp only [inTreeB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hm
    rw [h] at hm
    exact ⟨_, hm.1, hm.2⟩
  · rintro ⟨t, ht, hp⟩
    rw [← hp]
    exact hF.labs_pts j hj t ht

@[expose] noncomputable def subLab {k : ℕ} (hk : D.subReps.size = k + 1) (p : Fin D.n) :
    Fin (k + 1) :=
  ⟨(labs D)[p.val]!, by rw [← hk]; exact hF.labs_lt p.val p.isLt⟩

theorem subLab_orb {k : ℕ} (hk : D.subReps.size = k + 1) (p q : Fin D.n)
    (h : subLab hF hk p = subLab hF hk q) : ∃ g ∈ lvl D 1, g • p = q := by
  have hpq : (labs D)[p.val]! = (labs D)[q.val]! := congrArg Fin.val h
  have hjk : (labs D)[q.val]! < D.subReps.size := hF.labs_lt q.val q.isLt
  exact orbit_conj ((mem_subTree_iff hF hjk p).1 ((labs_iff hF hjk p).1 hpq))
    ((mem_subTree_iff hF hjk q).1 ((labs_iff hF hjk q).1 rfl))

theorem subLab_inv {k : ℕ} (hk : D.subReps.size = k + 1) :
    ∀ g ∈ lvl D 1, ∀ p : Fin D.n, subLab hF hk (g • p) = subLab hF hk p := by
  intro g hg p
  apply Fin.ext
  show (labs D)[(g • p).val]! = (labs D)[p.val]!
  have hjk : (labs D)[p.val]! < D.subReps.size := hF.labs_lt p.val p.isLt
  rw [labs_iff hF hjk, mem_subTree_iff hF hjk]
  exact orbit_smul_mem' hg ((mem_subTree_iff hF hjk p).1 ((labs_iff hF hjk p).1 rfl))

theorem card_subLab {k : ℕ} (hk : D.subReps.size = k + 1) (i : Fin (k + 1)) :
    (Finset.univ.filter (fun p : Fin D.n => subLab hF hk p = i)).card = D.subSizes[i.val]! := by
  classical
  have hik : i.val < D.subReps.size := by rw [hk]; exact i.isLt
  have hTF := subTreeFacts hF hik
  have hc := hTF.card_orbit
  have hset : MulAction.orbit (lettersGroup (lv1 D) (pairG (gs D)))
      (⟨D.subReps[i.val]!, hTF.r_lt⟩ : Fin D.n) =
      ↑(Finset.univ.filter (fun p : Fin D.n => subLab hF hk p = i)) := by
    ext p
    rw [Finset.mem_coe, Finset.mem_filter, hTF.mem_orbit_iff p, ← labs_iff hF hik p]
    simp only [Finset.mem_univ, true_and]
    exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset] at hc
  rw [hc]
  have h := congrArg (fun L : List ℕ => L[i.val]?) hF.subSizes
  have hi' : i.val < (S D).size := by rw [hF.S_size]; exact hik
  simp only [List.getElem?_map, Array.getElem?_toList, Array.getElem?_eq_getElem hi',
    Option.map_some] at h
  rw [getElem!_pos (S D) i.val hi', getElem!_def, ← h]

theorem subLab_root {k : ℕ} (hk : D.subReps.size = k + 1) : subLab hF hk (root hF) = 0 := by
  apply Fin.ext
  show (labs D)[0]! = 0
  have hTF := subTreeFacts hF hF.k_pos
  have h := hF.labs_pts 0 hF.k_pos 0 hTF.size_pos
  rwa [hTF.root, hF.rep0] at h

theorem subSizes_length {k : ℕ} (hk : D.subReps.size = k + 1) : D.subSizes.length = k + 1 := by
  rw [← hF.subSizes, List.length_map, Array.length_toList, hF.S_size, hk]

theorem isPreprimitive {k : ℕ} (hk : D.subReps.size = k + 1) :
    MulAction.IsPreprimitive (J D) (Fin D.n) := by
  have := isPretransitive hF
  apply isPreprimitive_of_suborbit_labels (root hF) (lvl D 1) (fun g hg => lvl_one_fix hF hg)
    (subLab hF hk) (subLab_inv hF hk) (subLab_orb hF hk)
  intro S' hS hdvd
  rw [subLab_root hF hk] at hS ⊢
  have hsum : (∑ i ∈ S', (Finset.univ.filter (fun p : Fin D.n => subLab hF hk p = i)).card) =
      ∑ i ∈ S', D.subSizes[i.val]! := Finset.sum_congr rfl fun i _ => card_subLab hF hk i
  rw [hsum, Fintype.card_fin] at hdvd
  exact finset_of_divOK hF.div (subSizes_length hF hk) S' hS hdvd

theorem tupleEq_Q_of_one {X : Table} (hX : Rep D.n X (1 : J D)) :
    tupleEq (apT X D.Q) D.Q = true := by
  simp only [tupleEq, Bool.and_eq_true, beq_iff_eq, apT_size, true_and]
  rw [allIn_eq_true]
  intro t _ ht
  rw [apT_get _ _ ht, hX _ (hF.Q_lt t ht), idx_one]
  simp

theorem eq_one_of_tupleEq {g : J D} {X : Table} (hX : Rep D.n X g)
    (h : tupleEq (apT X D.Q) D.Q = true) : g = 1 := by
  apply eq_one_of_fix_Q hF.toBaseFacts
  intro t ht
  simp only [tupleEq, Bool.and_eq_true, beq_iff_eq] at h
  have := (allIn_eq_true.1 h.2) t (Nat.zero_le _) ht
  simp only [beq_iff_eq] at this
  rw [apT_get _ _ ht, hX _ (hF.Q_lt t ht)] at this
  exact this

theorem orderOf_of_ordOK {g : J D} {X : Table} (hX : Rep D.n X g) {pe : ℕ × ℕ}
    (hp : pe.1.Prime) (h : ordOK D.n D.Q X pe = true) : orderOf g = pe.1 ^ pe.2 := by
  simp only [ordOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨he, h1⟩, h2⟩ := h
  have : Fact pe.1.Prime := ⟨hp⟩
  have hpow1 : g ^ pe.1 ^ (pe.2 - 1 + 1) = 1 := by
    rw [Nat.sub_add_cancel he]
    exact eq_one_of_tupleEq hF (Rep.powT (n_lt_two_pow hF) hX _) h1
  have hpow2 : ¬g ^ pe.1 ^ (pe.2 - 1) = 1 := by
    intro e
    have hR := Rep.powT (n_lt_two_pow hF) hX (pe.1 ^ (pe.2 - 1))
    rw [e] at hR
    rw [tupleEq_Q_of_one hF hR] at h2
    exact absurd h2 (by decide)
  have := orderOf_eq_prime_pow hpow2 hpow1
  rwa [Nat.sub_add_cancel he] at this

theorem orderOf_a (hp : D.ordA.1.Prime) : orderOf (a D) = D.ordA.1 ^ D.ordA.2 :=
  orderOf_of_ordOK hF (rep_a hF.toBaseFacts) hp hF.ordA

theorem orderOf_b (hp : D.ordB.1.Prime) : orderOf (b D) = D.ordB.1 ^ D.ordB.2 :=
  orderOf_of_ordOK hF (rep_b hF.toBaseFacts) hp hF.ordB

omit hF in
theorem genG_neg {z : ℤ} (hz : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) : genG D (-z) = (genG D z)⁻¹ := by
  unfold genG
  rcases hz with rfl | rfl | rfl | rfl <;> simp

omit hF in
theorem wordG_invWord {w : List ℤ} (hw : ∀ z ∈ w, z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) :
    wordG (genG D) (invWord w) = (wordG (genG D) w)⁻¹ := by
  induction w with
  | nil => simp [wordG, invWord]
  | cons z w ih =>
    have hz := hw z List.mem_cons_self
    have ih' := ih fun z' hz' => hw z' (List.mem_cons_of_mem _ hz')
    unfold invWord at ih' ⊢
    simp only [wordG, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one, mul_inv_rev] at ih' ⊢
    rw [ih', genG_neg hz]

@[expose] noncomputable def gConj (D : F5Data) : J D := wordG (genG D) D.gWord

theorem orderOf_c (hw : ∀ z ∈ D.gWord, z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) (hp : D.ordC.1.Prime) :
    orderOf (a D * ((gConj D)⁻¹ * b D * gConj D)) = D.ordC.1 ^ D.ordC.2 := by
  have hR := Rep.wordT (n_lt_two_pow hF) (cWordOf D.gWord) fun z _ => rep_genT hF z
  have he : wordG (genG D) (cWordOf D.gWord) = a D * ((gConj D)⁻¹ * b D * gConj D) := by
    unfold cWordOf
    simp only [wordG, List.map_append, List.prod_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
    have hi := wordG_invWord (D := D) hw
    unfold wordG at hi
    rw [hi]
    have hg1 : genG D 1 = a D := by simp [genG]
    have hg2 : genG D 2 = b D := by simp [genG]
    rw [hg1, hg2]
    simp only [gConj, wordG]
    group
  rw [← he]
  exact orderOf_of_ordOK hF hR hp hF.ordC

theorem T_pts_size {l : ℕ} (hl : l < D.base.size) : (T D)[l]!.pts.size = D.orbSizes[l]! := by
  have h := congrArg (fun L : List ℕ => L[l]?) hF.orbSizes
  have hT : (T D).size = D.base.size := by simp [T, levelTrees]
  have hl' : l < (T D).size := by rw [hT]; exact hl
  simp only [orbitSizes, List.getElem?_map, Array.getElem?_toList,
    Array.getElem?_eq_getElem hl', Option.map_some] at h
  rw [getElem!_pos (T D) l hl', getElem!_def, ← h]

theorem isSimpleGroup_J (hn2 : 2 ≤ D.n) {k : ℕ} (hk : D.subReps.size = k + 1)
    (hw : ∀ z ∈ D.gWord, z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2)
    (hpA : D.ordA.1.Prime) (hpB : D.ordB.1.Prime) (hpC : D.ordC.1.Prime)
    (hcop : Nat.Coprime (D.ordA.1 ^ D.ordA.2) (D.ordB.1 ^ D.ordB.2))
    (hprod : Nat.Coprime (D.ordC.1 ^ D.ordC.2)
      (∏ l ∈ Finset.Ico 1 D.base.size, D.orbSizes[l]!)) :
    IsSimpleGroup (J D) := by
  have := faithful hF.toBaseFacts
  have := isPreprimitive hF hk
  have : Finite (J D) := inferInstance
  refine isSimpleGroup_of_primitive_conj_product (Ω := Fin D.n) ?_ (a D) (b D) (gConj D)
    (closure_ab D) (root hF) ?_ ?_
  · rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn2
  · rw [orderOf_a hF hpA, orderOf_b hF hpB]; exact hcop
  · rw [orderOf_c hF hw hpC, card_stabilizer_root hF]
    rwa [Finset.prod_congr rfl fun l hl => T_pts_size hF (Finset.mem_Ico.1 hl).2]

theorem isSimpleGroup_seedUnits (hn2 : 2 ≤ D.n) {k : ℕ} (hk : D.subReps.size = k + 1)
    (hw : ∀ z ∈ D.gWord, z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2)
    (hpA : D.ordA.1.Prime) (hpB : D.ordB.1.Prime) (hpC : D.ordC.1.Prime)
    (hcop : Nat.Coprime (D.ordA.1 ^ D.ordA.2) (D.ordB.1 ^ D.ordB.2))
    (hprod : Nat.Coprime (D.ordC.1 ^ D.ordC.2)
      (∏ l ∈ Finset.Ico 1 D.base.size, D.orbSizes[l]!)) :
    IsSimpleGroup (CFSG.Blueprint.NativeSporadic.seedMonoid 5 D.d 1 D.seedA D.seedB)ˣ :=
  @MulEquiv.isSimpleGroup _ _ _ _
    (isSimpleGroup_J hF hn2 hk hw hpA hpB hpC hcop hprod) (seedEquiv hF.toBaseFacts)

theorem card_seedUnits :
    Nat.card (CFSG.Blueprint.NativeSporadic.seedMonoid 5 D.d 1 D.seedA D.seedB)ˣ =
      ∏ l ∈ Finset.Ico 0 D.base.size, D.orbSizes[l]! := by
  rw [Nat.card_congr (seedEquiv hF.toBaseFacts).toEquiv, card_J hF]
  exact Finset.prod_congr rfl fun l hl => T_pts_size hF (Finset.mem_Ico.1 hl).2

end CFSG.Sporadic.F5
