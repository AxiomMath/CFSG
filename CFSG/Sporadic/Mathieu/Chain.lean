module

public import Certificates.Data.CFSGNative.Mathieu.Check
public import CFSG.Perm.ChainSpec
public import CFSG.Sporadic.Fi23.SlpSpec
public import CFSG.Sporadic.Mathieu.Actions

public noncomputable section

namespace CFSG.Sporadic.Mathieu

open MulAction CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
  CFSG.Sporadic.Mathieu.Native

variable {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}

@[expose] def genABG (a b : G) (z : ℤ) : G :=
  if z = 1 then a else if z = -1 then a⁻¹ else if z = 2 then b else b⁻¹

@[expose] def gs (D : Data) (a b : G) (j : ℕ) : G :=
  CFSG.Sporadic.Fi23.slpG (genABG a b) D.words j

abbrev lvl (D : Data) (a b : G) (i : ℕ) : Subgroup G :=
  levelGroup (letters n D) D.base (pairG (gs D a b)) i

structure Hyp (G : Subgroup (Equiv.Perm (Fin n))) (D : Data) (a b : G) : Prop where
  lt : n < 2 ^ 32
  gen : Subgroup.closure ({a, b} : Set G) = ⊤
  repA : Rep n D.tA a
  repB : Rep n D.tB b
  cert : check n D = true

structure CheckFacts (n : ℕ) (D : Data) : Prop where
  invA : invOK n D.tA (invT n D.tA) = true
  invB : invOK n D.tB (invT n D.tB) = true
  slp_ok : CFSG.Sporadic.Fi23.Native.slpOK D.words = true
  slp_pure : CFSG.Sporadic.Fi23.Native.slpPure D.words = true
  two_le : 2 ≤ D.words.size
  chain : chainOK n (letters n D) D.base (Array.range n) D.base (trees n D) 0 = true
  sizes : orbitSizes (trees n D) = D.sizes
  sift_a : sift (trees n D) (letters n D) D.base (Array.range n) 0
    (apT D.tA (Array.range n)) = true
  sift_b : sift (trees n D) (letters n D) D.base (Array.range n) 0
    (apT D.tB (Array.range n)) = true
  k_le : D.k ≤ D.base.size
  cover : ∀ i < D.k, D.base[i]! = i ∧ levelCover n (trees n D) i = true
  ordX : orderOK n (letters n D)[0]! D.pX D.eX = true
  ordY : orderOK n (letters n D)[2]! D.pY D.eY = true
  ordXY : orderOK n (compT n (letters n D)[0]! (letters n D)[2]!) D.pXY D.eXY = true

theorem checkFacts {D : Data} (h : check n D = true) : CheckFacts n D := by
  unfold check at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, fun i hi => ?_, h12, h13, h14⟩
  have := (allIn_eq_true.1 h11) i (Nat.zero_le _) hi
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this

theorem range_get {t : ℕ} (ht : t < n) : (Array.range n)[t]! = t := by
  rw [getElem!_pos _ t (by simpa using ht), Array.getElem_range]

theorem eq_one_of_fix {g : G} (h : ∀ i < n, idx n g i = i) : g = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  apply Fin.ext
  have hi := h i.val i.isLt
  rw [idx_of_lt _ i.isLt] at hi
  exact hi

theorem sep (g : G)
    (hg : ∀ t < (Array.range n).size, idx n g (Array.range n)[t]! = (Array.range n)[t]!) :
    g = 1 :=
  eq_one_of_fix fun i hi => by
    have h := hg i (by simpa using hi)
    rwa [range_get hi] at h

theorem eq_one_of_isIdT {T : Table} {g : G} (hT : Rep n T g) (h : isIdT n T = true) : g = 1 :=
  eq_one_of_fix fun i hi => by
    have := (allIn_eq_true.1 h) i (Nat.zero_le _) hi
    rwa [beq_iff_eq, hT i hi] at this

theorem ne_one_of_isIdT {T : Table} {g : G} (hT : Rep n T g) (h : isIdT n T = false) : g ≠ 1 := by
  rintro rfl
  unfold isIdT at h
  rw [← Bool.not_eq_true, allIn_eq_true] at h
  apply h
  intro i _ hi
  rw [beq_iff_eq, hT i hi, idx_one]

theorem orderOf_of_orderOK (hn : n < 2 ^ 32) {T : Table} {g : G} (hT : Rep n T g) {p e : ℕ}
    (hp : p.Prime) (h : orderOK n T p e = true) : orderOf g = p ^ (e + 1) := by
  unfold orderOK at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  have : Fact p.Prime := ⟨hp⟩
  exact orderOf_eq_prime_pow (ne_one_of_isIdT (Rep.powT hn hT _) h.2)
    (eq_one_of_isIdT (Rep.powT hn hT _) h.1)

section Chain

variable {D : Data} {a b : G}

theorem rep_genAB (ha : Rep n D.tA a) (hb : Rep n D.tB b)
    (hia : invOK n D.tA (invT n D.tA) = true) (hib : invOK n D.tB (invT n D.tB) = true) (z : ℤ) :
    Rep n (genAB n D z) (genABG a b z) := by
  unfold genAB genABG
  split_ifs
  · exact ha
  · exact Rep.inv_of_invOK ha hia
  · exact hb
  · exact Rep.inv_of_invOK hb hib

theorem letters_size (h : CFSG.Sporadic.Fi23.Native.slpOK D.words = true) :
    (letters n D).size = 2 * D.words.size :=
  (CFSG.Sporadic.Fi23.slpInv_full (n := n) (gens := genAB n D) h).1

theorem rep_letters (H : Hyp G D a b) :
    ∀ j < (letters n D).size / 2, Rep n (letters n D)[2 * j]! (gs D a b j) := by
  intro j hj
  have hF := checkFacts H.cert
  rw [letters_size hF.slp_ok] at hj
  have hinv := (chainOK_parts hF.chain).2.1
  refine CFSG.Sporadic.Fi23.rep_slpLetters H.lt
    (rep_genAB H.repA H.repB hF.invA hF.invB) hF.slp_ok (fun i hi => ?_) j (by omega)
  exact hinv i (by rw [letters_size hF.slp_ok]; omega)

theorem chain (H : Hyp G D a b) :
    (∀ i < D.base.size, TreeFacts n (trees n D)[i]! (levelLetters (letters n D) D.base i)
      (pairG (gs D a b)) D.base[i]!) ∧
      (∀ i < D.base.size, ∀ g ∈ lvl D a b i,
        idx n g D.base[i]! = D.base[i]! ↔ g ∈ lvl D a b (i + 1)) ∧
      ∀ i ≤ D.base.size, Nat.card (lvl D a b i) =
        ∏ l ∈ Finset.Ico i D.base.size, (trees n D)[l]!.pts.size :=
  chain_facts (rep_letters H) sep (checkFacts H.cert).chain

theorem rep_pairG_all (H : Hyp G D a b) :
    ∀ l < (letters n D).size, Rep n (letters n D)[l]! (pairG (gs D a b) l) :=
  rep_pairG (rep_letters H) (by rw [letters_size (checkFacts H.cert).slp_ok]; omega)
    (chainOK_parts (checkFacts H.cert).chain).2.1

theorem walkFacts (H : Hyp G D a b) {i : ℕ} (hi : i < D.base.size) :
    WalkFacts n (trees n D)[i]! (letters n D) (pairG (gs D a b)) := by
  intro k hk hk0
  obtain ⟨hpar, hlab⟩ := ((chain H).1 i hi).par k hk hk0
  have hl := levelLetters_lt hlab
  refine ⟨hpar, rep_pairG_all H _ hl, ?_⟩
  rw [← pairG_invL]
  exact rep_pairG_all H _
    (invL_lt (by rw [letters_size (checkFacts H.cert).slp_ok]; omega) hl)

theorem mem_lvl_zero_of_sift (H : Hyp G D a b) {g : G} {img : Array ℕ}
    (hsz : img.size = (Array.range n).size)
    (himg : ∀ t < (Array.range n).size, img[t]! = idx n g (Array.range n)[t]!)
    (h : sift (trees n D) (letters n D) D.base (Array.range n) 0 img = true) :
    g ∈ lvl D a b 0 := by
  have htrees : (trees n D).size = D.base.size :=
    (chainOK_parts (checkFacts H.cert).chain).2.2.1
  refine sift_mem (letters := letters n D) (lG := pairG (gs D a b)) (qb := D.base) sep
    (fun t ht => by rw [range_get (by simpa using ht)]; simpa using ht) (lvl D a b 0)
    (trees n D).size 0 (by omega) ?_ g img hsz himg h
  intro l' hl' _
  have hl'' : l' < D.base.size := by rw [← htrees]; exact hl'
  exact ⟨walkFacts H hl'', fun k hk => levelGroup_anti (pairG (gs D a b)) (Nat.zero_le l')
    (((chain H).1 l' hl'').treeG_mem hk)⟩

theorem mem_lvl_zero_of_rep (H : Hyp G D a b) {T : Table} {g : G} (hT : Rep n T g)
    (h : sift (trees n D) (letters n D) D.base (Array.range n) 0 (apT T (Array.range n)) = true) :
    g ∈ lvl D a b 0 :=
  mem_lvl_zero_of_sift H (apT_size _ _) (fun t ht => by
    rw [apT_get _ _ ht, hT _ (by rw [range_get (by simpa using ht)]; simpa using ht)]) h

theorem lvl_zero (H : Hyp G D a b) : lvl D a b 0 = ⊤ := by
  rw [eq_top_iff, ← H.gen, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact mem_lvl_zero_of_rep H H.repA (checkFacts H.cert).sift_a
  · exact mem_lvl_zero_of_rep H H.repB (checkFacts H.cert).sift_b

theorem closure_gs (H : Hyp G D a b) :
    Subgroup.closure ({gs D a b 0, gs D a b 1} : Set G) = ⊤ := by
  rw [eq_top_iff, ← lvl_zero H]
  unfold lvl levelGroup lettersGroup
  rw [Subgroup.closure_le]
  rintro _ ⟨l, hl, rfl⟩
  have hF := checkFacts H.cert
  have hl' := levelLetters_lt hl
  rw [letters_size hF.slp_ok] at hl'
  have hmem := CFSG.Sporadic.Fi23.slpG_mem_closure (gensG := genABG a b) hF.slp_ok hF.slp_pure
    (l / 2) (by omega)
  unfold pairG
  split_ifs
  · exact hmem
  · exact Subgroup.inv_mem _ hmem

theorem prod_pts_size (T : Array Tree) :
    ∏ l ∈ Finset.Ico 0 T.size, T[l]!.pts.size = (orbitSizes T).prod := by
  rw [← Finset.range_eq_Ico, Finset.prod_range, orbitSizes, ← List.prod_ofFn]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_ofFn, List.getElem_map, Array.getElem_toList]
  rw [getElem!_pos T i (by simpa using h1)]

theorem card_eq (H : Hyp G D a b) : Nat.card G = D.sizes.prod := by
  have hF := checkFacts H.cert
  have htrees : (trees n D).size = D.base.size := (chainOK_parts hF.chain).2.2.1
  rw [← Subgroup.card_top (G := G), ← lvl_zero H, (chain H).2.2 0 (Nat.zero_le _), ← htrees,
    prod_pts_size, hF.sizes]

theorem rep_X (H : Hyp G D a b) : Rep n (letters n D)[0]! (gs D a b 0) := by
  have hF := checkFacts H.cert
  exact rep_letters H 0 (by rw [letters_size hF.slp_ok]; have := hF.two_le; omega)

theorem rep_Y (H : Hyp G D a b) : Rep n (letters n D)[2]! (gs D a b 1) := by
  have hF := checkFacts H.cert
  exact rep_letters H 1 (by rw [letters_size hF.slp_ok]; have := hF.two_le; omega)

theorem orderOf_X (H : Hyp G D a b) (hp : D.pX.Prime) : orderOf (gs D a b 0) = D.pX ^ (D.eX + 1) :=
  orderOf_of_orderOK H.lt (rep_X H) hp (checkFacts H.cert).ordX

theorem orderOf_Y (H : Hyp G D a b) (hp : D.pY.Prime) : orderOf (gs D a b 1) = D.pY ^ (D.eY + 1) :=
  orderOf_of_orderOK H.lt (rep_Y H) hp (checkFacts H.cert).ordY

theorem orderOf_XY (H : Hyp G D a b) (hp : D.pXY.Prime) :
    orderOf (gs D a b 0 * gs D a b 1) = D.pXY ^ (D.eXY + 1) :=
  orderOf_of_orderOK H.lt (Rep.compT (rep_X H) (rep_Y H)) hp (checkFacts H.cert).ordXY

theorem maps (H : Hyp G D a b) : ∀ k ≤ D.k, ∀ x : ℕ → Fin n, (∀ i < k, ∀ j < i, x i ≠ x j) →
    ∃ g : G, ∀ j < k, ∀ p : Fin n, p.val = j → g • p = x j := by
  have hF := checkFacts H.cert
  have hC := chain H
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · exact fun _ _ _ _ => ⟨1, fun _ _ p => p.elim0⟩
  have hkn : ∀ i < D.k, i < n := by
    intro i hi
    have := (hC.1 i (by have := hF.k_le; omega)).r_lt
    rwa [(hF.cover i hi).1] at this
  let pt : ℕ → Fin n := fun j => ⟨j % n, Nat.mod_lt _ hn0⟩
  have hb : ∀ i (hi : i < D.k), pt i = ⟨i, hkn i hi⟩ := by
    intro i hi
    exact Fin.ext (Nat.mod_eq_of_lt (hkn i hi))
  have hseq := exists_smul_eq_seq (lvl D a b) pt (fun i => levelGroup_anti _ (Nat.le_succ i)) D.k
    (by
      intro i hi g hg
      have hib : i < D.base.size := lt_of_lt_of_le hi hF.k_le
      have h1 := (hC.2.1 i hib g (levelGroup_anti _ (Nat.le_succ i) hg)).2 hg
      rw [(hF.cover i hi).1, idx_of_lt g (hkn i hi)] at h1
      rw [hb i hi]
      exact Fin.ext h1)
    (by
      intro i hi p hp
      have hib : i < D.base.size := lt_of_lt_of_le hi hF.k_le
      have hpi : i ≤ p.val := by
        by_contra hlt
        push Not at hlt
        apply hp p.val hlt
        rw [hb p.val (by omega)]
      have hcov := (allIn_eq_true.1 (hF.cover i hi).2) p.val (Nat.zero_le _) p.isLt
      simp only [Bool.or_eq_true, decide_eq_true_eq, inTreeB, Bool.and_eq_true,
        beq_iff_eq] at hcov
      rcases hcov with hlt | ⟨hk, hpts⟩
      · omega
      have hT := hC.1 i hib
      obtain ⟨⟨g, hg⟩, hgp⟩ := (hT.mem_orbit_iff p).2 ⟨_, hk, hpts⟩
      refine ⟨g, hg, ?_⟩
      have e : (⟨D.base[i]!, hT.r_lt⟩ : Fin n) = pt i := by
        rw [hb i hi]
        exact Fin.ext (hF.cover i hi).1
      rw [← e]
      exact hgp)
  intro k hk x hx
  obtain ⟨g, -, hg⟩ := hseq k hk x hx
  refine ⟨g, fun j hj p hp => ?_⟩
  have e : p = pt j := by
    rw [hb j (by omega)]
    exact Fin.ext hp
  rw [e]
  exact hg j hj

theorem exists_smul_eq_two (H : Hyp G D a b) (hk : 2 ≤ D.k) (hn : 2 ≤ n) (u v : Fin n)
    (huv : u ≠ v) : ∃ g : G, g • (⟨0, by omega⟩ : Fin n) = u ∧ g • (⟨1, by omega⟩ : Fin n) = v := by
  obtain ⟨g, hg⟩ := maps H 2 hk (fun j => if j = 0 then u else v) (by
    intro i hi j hj
    obtain rfl : i = 1 := by omega
    obtain rfl : j = 0 := by omega
    simpa using huv.symm)
  exact ⟨g, by simpa using hg 0 (by norm_num) _ rfl, by simpa using hg 1 (by norm_num) _ rfl⟩

theorem exists_smul_eq_three (H : Hyp G D a b) (hk : 3 ≤ D.k) (hn : 3 ≤ n) (u v w : Fin n)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    ∃ g : G, g • (⟨0, by omega⟩ : Fin n) = u ∧ g • (⟨1, by omega⟩ : Fin n) = v ∧
      g • (⟨2, by omega⟩ : Fin n) = w := by
  obtain ⟨g, hg⟩ := maps H 3 hk (fun j => if j = 0 then u else if j = 1 then v else w) (by
    intro i hi j hj
    interval_cases i <;> interval_cases j <;>
      simp [Ne.symm huv, Ne.symm huw, Ne.symm hvw])
  exact ⟨g, by simpa using hg 0 (by norm_num) _ rfl, by simpa using hg 1 (by norm_num) _ rfl,
    by simpa using hg 2 (by norm_num) _ rfl⟩

theorem exists_smul_eq_four (H : Hyp G D a b) (hk : 4 ≤ D.k) (hn : 4 ≤ n) (u v w z : Fin n)
    (huv : u ≠ v) (huw : u ≠ w) (huz : u ≠ z) (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z) :
    ∃ g : G, g • (⟨0, by omega⟩ : Fin n) = u ∧ g • (⟨1, by omega⟩ : Fin n) = v ∧
      g • (⟨2, by omega⟩ : Fin n) = w ∧ g • (⟨3, by omega⟩ : Fin n) = z := by
  obtain ⟨g, hg⟩ := maps H 4 hk
    (fun j => if j = 0 then u else if j = 1 then v else if j = 2 then w else z) (by
      intro i hi j hj
      interval_cases i <;> interval_cases j <;>
        simp [Ne.symm huv, Ne.symm huw, Ne.symm huz, Ne.symm hvw, Ne.symm hvz, Ne.symm hwz])
  exact ⟨g, by simpa using hg 0 (by norm_num) _ rfl, by simpa using hg 1 (by norm_num) _ rfl,
    by simpa using hg 2 (by norm_num) _ rfl, by simpa using hg 3 (by norm_num) _ rfl⟩

end Chain

end CFSG.Sporadic.Mathieu
