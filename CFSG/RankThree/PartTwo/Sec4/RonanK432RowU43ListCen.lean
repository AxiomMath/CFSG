module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43Class
public import CFSG.Permutation.FinPackWalk

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.RankThree.PartTwo.Sec4.Item434RemU43

@[expose] def u43CenOK (t : ℕ) : Bool :=
  (uGens.any fun g => !commutes4 (uAt t) g) || uAt t == one4 || uAt t == uAt uZ ||
    uAt t == sq4 (uAt uZ)

@[expose] def u43WitOK : Bool :=
  commutes4 (conjStep (wordPair [1, 1, 1]) (uAt uZ)) (uAt uZ) &&
    !(conjStep (wordPair [1, 1, 1]) (uAt uZ) == one4) &&
    !(conjStep (wordPair [1, 1, 1]) (uAt uZ) == uAt uZ) &&
    !(conjStep (wordPair [1, 1, 1]) (uAt uZ) == sq4 (uAt uZ))

@[noinline, expose] def u43Check : Bool :=
  (cube4 (uAt uZ) == one4) && u43WitOK && (List.range 729).all u43CenOK

namespace U43P

open CFSG.Permutation.FinPack

@[expose] noncomputable def pk (c : List ℕ) : ℕ := encF (fun i => c.getD i 0) 16

@[expose] def mulT : ℕ :=
  5107958271419843920193557880922165469200445146711473720438786334434434179969678641066430418649088

@[expose] def addT : ℕ :=
  8986690708024339884259668388453865091868182506470258411551265922896781674643265104972283578167824

@[expose] def mT (a b : ℕ) : ℕ := rd mulT (Nat.add (Nat.mul 9 a) b)

@[expose] def aT (a b : ℕ) : ℕ := rd addT (Nat.add (Nat.mul 9 a) b)

theorem mT_tab : ∀ a < 9, ∀ b < 9, mT a b = mulC a b := by
  decide +kernel

theorem aT_tab : ∀ a < 9, ∀ b < 9, aT a b = addC a b := by
  decide +kernel

@[expose] def entK (p q k : ℕ) : ℕ :=
  aT (aT (aT (mT (rd p (4 * (k / 4))) (rd q (k % 4)))
    (mT (rd p (4 * (k / 4) + 1)) (rd q (4 + k % 4))))
    (mT (rd p (4 * (k / 4) + 2)) (rd q (8 + k % 4))))
    (mT (rd p (4 * (k / 4) + 3)) (rd q (12 + k % 4)))

@[expose] noncomputable def mulP (p q : ℕ) : ℕ := encF (entK p q) 16

@[expose] def Good (c : List ℕ) : Prop := c.length = 16 ∧ ∀ i < 16, c.getD i 0 < 9

theorem addC_lt (a b : ℕ) : addC a b < 9 := by
  unfold addC
  have h1 := Nat.mod_lt ((a / 3 + b / 3)) (show 3 > 0 by norm_num)
  have h2 := Nat.mod_lt ((a % 3 + b % 3)) (show 3 > 0 by norm_num)
  omega

theorem arr_getD (l : List ℕ) (i d : ℕ) : l.toArray.getD i d = l.getD i d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem mul4_getD (a b : List ℕ) {k : ℕ} (hk : k < 16) : (mul4 a b).getD k 0 =
    addC (addC (addC (mulC (a.getD (4 * (k / 4)) 0) (b.getD (k % 4) 0))
      (mulC (a.getD (4 * (k / 4) + 1) 0) (b.getD (4 + k % 4) 0)))
      (mulC (a.getD (4 * (k / 4) + 2) 0) (b.getD (8 + k % 4) 0)))
      (mulC (a.getD (4 * (k / 4) + 3) 0) (b.getD (12 + k % 4) 0)) := by
  unfold mul4
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
    Option.map_some, Option.getD_some, arr_getD]

theorem length_mul4 (a b : List ℕ) : (mul4 a b).length = 16 := by
  unfold mul4
  simp

theorem good_mul4 (a b : List ℕ) : Good (mul4 a b) :=
  ⟨length_mul4 a b, fun i hi => by rw [mul4_getD a b hi]; exact addC_lt _ _⟩

theorem mulC_lt (a b : ℕ) : mulC a b < 9 := by
  unfold mulC
  have h1 := Nat.mod_lt (a / 3 * (b / 3) + 2 * (a % 3 * (b % 3))) (show 3 > 0 by norm_num)
  have h2 := Nat.mod_lt (a / 3 * (b % 3) + a % 3 * (b / 3)) (show 3 > 0 by norm_num)
  omega

theorem rd_lt (c i : ℕ) : rd c i < 16 := by
  rw [rd_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem entK_eq {p q k : ℕ} (hp : ∀ i < 16, rd p i < 9) (hq : ∀ i < 16, rd q i < 9) (hk : k < 16) :
    entK p q k = addC (addC (addC (mulC (rd p (4 * (k / 4))) (rd q (k % 4)))
      (mulC (rd p (4 * (k / 4) + 1)) (rd q (4 + k % 4))))
      (mulC (rd p (4 * (k / 4) + 2)) (rd q (8 + k % 4))))
      (mulC (rd p (4 * (k / 4) + 3)) (rd q (12 + k % 4))) := by
  unfold entK
  rw [mT_tab _ (hp _ (by omega)) _ (hq _ (by omega)),
    mT_tab _ (hp _ (by omega)) _ (hq _ (by omega)),
    mT_tab _ (hp _ (by omega)) _ (hq _ (by omega)), mT_tab _ (hp _ (by omega)) _ (hq _ (by omega)),
    aT_tab _ (mulC_lt _ _) _ (mulC_lt _ _), aT_tab _ (addC_lt _ _) _ (mulC_lt _ _),
    aT_tab _ (addC_lt _ _) _ (mulC_lt _ _)]

theorem good_one4 : Good one4 := ⟨rfl, by decide⟩

theorem good16 {c : List ℕ} (hc : Good c) : ∀ i < 16, c.getD i 0 < 16 :=
  fun i hi => lt_trans (hc.2 i hi) (by norm_num)

theorem rd_pk {c : List ℕ} (hc : Good c) {i : ℕ} (hi : i < 16) : rd (pk c) i = c.getD i 0 :=
  rd_encF (good16 hc) hi

theorem rd_pk_lt {c : List ℕ} (hc : Good c) : ∀ i < 16, rd (pk c) i < 9 :=
  fun i hi => (rd_pk hc hi) ▸ hc.2 i hi

theorem mulP_pk {a b : List ℕ} (ha : Good a) (hb : Good b) :
    mulP (pk a) (pk b) = pk (mul4 a b) := by
  unfold mulP
  conv_rhs => unfold pk
  refine encF_congr fun k hk => ?_
  have h1 : k / 4 < 4 := by omega
  have h2 : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
  rw [entK_eq (rd_pk_lt ha) (rd_pk_lt hb) hk, mul4_getD a b hk, rd_pk ha (by omega),
    rd_pk ha (by omega), rd_pk ha (by omega), rd_pk ha (by omega), rd_pk hb (by omega),
    rd_pk hb (by omega), rd_pk hb (by omega), rd_pk hb (by omega)]

theorem pk_inj {a b : List ℕ} (ha : Good a) (hb : Good b) (h : pk a = pk b) : a = b := by
  apply List.ext_getElem (ha.1.trans hb.1.symm)
  intro i hia hib
  have hi : i < 16 := ha.1 ▸ hia
  have e := congrArg (fun p => rd p i) h
  simp only [rd_pk ha hi, rd_pk hb hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hia,
    List.getElem?_eq_getElem hib, Option.getD_some] at e
  exact e

theorem beq_pk {a b : List ℕ} (ha : Good a) (hb : Good b) : (a == b) = (pk a == pk b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨congrArg pk, pk_inj ha hb⟩

@[expose] def oneP : ℕ := 3458767812358569987

@[expose] def letterP (l : ℕ) : ℕ :=
  if l = 0 then 2607710114383267106 else if l = 1 then 3839357440208500550 else
    if l = 2 then 1756493208096933649 else 3533147885621571622

@[expose] noncomputable def wordCodeP (w : List ℕ) : ℕ :=
  w.foldl (fun acc l => mulP acc (letterP l)) oneP

@[expose] noncomputable def gensP : List ℕ := uGenWords.map wordCodeP

@[expose] def rdW (c i : ℕ) : ℕ := Nat.land (Nat.shiftRight c (Nat.mul 64 i)) 18446744073709551615

@[expose] noncomputable def encW (a : ℕ → ℕ) (k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.add acc (Nat.shiftLeft (a i) (Nat.mul 64 i))) k

theorem encW_succ (a : ℕ → ℕ) (k : ℕ) : encW a (k + 1) = encW a k + a k * (2 ^ 64) ^ k := by
  change encW a k + a k <<< (64 * k) = _
  rw [Nat.shiftLeft_eq, pow_mul]

theorem rdW_eq (c i : ℕ) : rdW c i = c / (2 ^ 64) ^ i % 2 ^ 64 := by
  change (c >>> (64 * i)) &&& (2 ^ 64 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]

theorem encW_lt {a : ℕ → ℕ} {k : ℕ} (h : ∀ i < k, a i < 2 ^ 64) : encW a k < (2 ^ 64) ^ k := by
  induction k with
  | zero => exact Nat.one_pos
  | succ k ih =>
    rw [encW_succ, pow_succ (2 ^ 64) k]
    have h1 := ih fun i hi => h i (by omega)
    have h2 : a k * (2 ^ 64) ^ k ≤ (2 ^ 64 - 1) * (2 ^ 64) ^ k :=
      Nat.mul_le_mul_right _ (by have := h k (by omega); omega)
    omega

theorem rdW_encW {a : ℕ → ℕ} {k : ℕ} (h : ∀ i < k, a i < 2 ^ 64) {j : ℕ} (hj : j < k) :
    rdW (encW a k) j = a j := by
  rw [rdW_eq]
  induction k with
  | zero => omega
  | succ k ih =>
    rw [encW_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · have ih' := ih (fun i hi => h i (by omega)) hj
      have hk : a k * (2 ^ 64) ^ k = (2 ^ 64) ^ j * (2 ^ 64 * ((2 ^ 64) ^ (k - j - 1) * a k)) := by
        have e : (2 ^ 64) ^ k = (2 ^ 64) ^ j * (2 ^ 64) ^ (k - j - 1) * 2 ^ 64 := by
          rw [← pow_add, ← pow_succ]
          congr 1
          omega
        rw [e]
        ring
      rw [hk, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left, ih']
    · rw [mul_comm, Nat.add_mul_div_left _ _ (by positivity),
        Nat.div_eq_of_lt (encW_lt fun i hi => h i (by omega)), zero_add,
        Nat.mod_eq_of_lt (h j (by omega))]

theorem encW_congr {a b : ℕ → ℕ} {k : ℕ} (h : ∀ i < k, a i = b i) : encW a k = encW b k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [encW_succ, encW_succ, ih fun i hi => h i (by omega), h k (by omega)]

@[expose] noncomputable def stepW (st : ℕ × ℕ) (ps : ℕ × ℕ) : ℕ × ℕ :=
  (st.1 + 1, st.2 + Nat.shiftLeft
    (mulP (if ps.1 < st.1 then rdW st.2 ps.1 else oneP) (gensP.getD ps.2 oneP)) (64 * st.1))

@[expose] noncomputable def elemsW : ℕ × ℕ := uPar.foldl stepW (1, oneP)

theorem pk_facts : pk one4 = oneP ∧ pk matAc = 2607710114383267106 ∧
    pk matBc = 3839357440208500550 ∧ pk matAic = 1756493208096933649 ∧
    pk matBic = 3533147885621571622 ∧ pk [] = 0 := by
  decide +kernel

theorem good_letter (l : ℕ) : Good (letterCode l) := by
  unfold letterCode
  split_ifs
  · exact ⟨rfl, by decide⟩
  · exact ⟨rfl, by decide⟩
  · exact ⟨rfl, by decide⟩
  · exact ⟨rfl, by decide⟩

theorem pk_letter (l : ℕ) : pk (letterCode l) = letterP l := by
  obtain ⟨-, h0, h1, h2, h3, -⟩ := pk_facts
  unfold letterCode letterP
  split_ifs
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem wordCode_sim (w : List ℕ) : Good (wordCode w) ∧ pk (wordCode w) = wordCodeP w := by
  unfold wordCode wordCodeP
  have key : ∀ (w : List ℕ) (acc : List ℕ) (accP : ℕ), Good acc → pk acc = accP →
      Good (w.foldl (fun acc l => mul4 acc (letterCode l)) acc) ∧
        pk (w.foldl (fun acc l => mul4 acc (letterCode l)) acc) =
          w.foldl (fun acc l => mulP acc (letterP l)) accP := by
    intro w
    induction w with
    | nil => intro acc accP h1 h2; exact ⟨h1, h2⟩
    | cons l w ih =>
      intro acc accP h1 h2
      rw [List.foldl_cons, List.foldl_cons]
      refine ih _ _ (good_mul4 _ _) ?_
      rw [← mulP_pk h1 (good_letter l), h2, pk_letter]
  exact key w one4 oneP good_one4 pk_facts.1

theorem good_uGens : ∀ g ∈ uGens, Good g := by
  intro g hg
  unfold uGens at hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact (wordCode_sim w).1

theorem uGens_pk : uGens.map pk = gensP := by
  unfold uGens gensP
  rw [List.map_map]
  refine List.map_congr_left ?_
  intro w _
  rw [Function.comp_apply]
  exact (wordCode_sim w).2

theorem getD_good {l : List (List ℕ)} (hl : ∀ e ∈ l, Good e) (i : ℕ) : Good (l.getD i one4) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => exact good_one4
  | some e => exact hl e (List.mem_of_getElem? h)

theorem pk_getD (l : List (List ℕ)) (i : ℕ) (d : List ℕ) :
    pk (l.getD i d) = (l.map pk).getD i (pk d) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases l[i]? with _ | e
  · rw [Option.map_none, Option.getD_none, Option.getD_none]
  · rw [Option.map_some, Option.getD_some, Option.getD_some]

theorem arr_getD' (a : Array (List ℕ)) (i : ℕ) (d : List ℕ) : a.getD i d = a.toList.getD i d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem pk_lt {c : List ℕ} (hc : Good c) : pk c < 2 ^ 64 :=
  lt_of_lt_of_le (encF_lt (good16 hc)) (by norm_num)

theorem getD_append_lt (l : List (List ℕ)) (y : List ℕ) {i : ℕ} (hi : i < l.length) (d : List ℕ) :
    (l ++ [y]).getD i d = l.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_append_eq (l : List (List ℕ)) (y d : List ℕ) : (l ++ [y]).getD l.length d = y := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self]
  rfl

@[expose] def BuildInv (acc : Array (List ℕ)) (n E : ℕ) : Prop :=
  (∀ e ∈ acc.toList, Good e) ∧ n = acc.size ∧ E = encW (fun i => pk (acc.toList.getD i [])) acc.size

theorem shl_eq (a b : ℕ) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b

theorem lookup_eq {acc : Array (List ℕ)} {st : ℕ × ℕ} (h : BuildInv acc st.1 st.2) (i : ℕ) :
    pk (acc.getD i one4) = if i < st.1 then rdW st.2 i else oneP := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [arr_getD', h2]
  split_ifs with hi
  · rw [h3, rdW_encW (fun j hj => ?_) hi]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rwa [Array.length_toList]),
        Option.getD_some, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rwa [Array.length_toList]), Option.getD_some]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rwa [Array.length_toList]),
        Option.getD_some]
      exact pk_lt (h1 _ (List.getElem_mem _))
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [Array.length_toList]; omega),
      Option.getD_none, pk_facts.1]

theorem build_sim : ∀ (par : List (ℕ × ℕ)) (acc : Array (List ℕ)) (st : ℕ × ℕ),
    BuildInv acc st.1 st.2 →
    BuildInv
      (par.foldl (fun acc ps => acc.push (mul4 (acc.getD ps.1 one4) (uGens.getD ps.2 one4))) acc)
      (par.foldl stepW st).1 (par.foldl stepW st).2
  | [], _, _, h => h
  | ps :: par, acc, st, h => by
    rw [List.foldl_cons, List.foldl_cons]
    refine build_sim par _ _ ?_
    have hg1 : Good (acc.getD ps.1 one4) := by
      rw [arr_getD']
      exact getD_good h.1 ps.1
    have hg2 := getD_good good_uGens ps.2
    have hy : pk (mul4 (acc.getD ps.1 one4) (uGens.getD ps.2 one4)) =
        mulP (if ps.1 < st.1 then rdW st.2 ps.1 else oneP) (gensP.getD ps.2 oneP) := by
      rw [← lookup_eq h, ← pk_facts.1, ← uGens_pk, ← pk_getD, mulP_pk hg1 hg2]
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact h1 e he
      · exact good_mul4 _ _
    · rw [Array.size_push, ← h2]
      rfl
    · rw [Array.size_push, encW_succ, Array.toList_push]
      have hl : acc.toList.length = acc.size := Array.length_toList
      rw [← hl, getD_append_eq, hl,
        encW_congr (fun i hi => by rw [getD_append_lt _ _ (hl ▸ hi)]), ← h3,
        hy, h2]
      show st.2 + Nat.shiftLeft (mulP (if ps.1 < st.1 then rdW st.2 ps.1 else oneP)
        (gensP.getD ps.2 oneP)) (64 * st.1) = _
      rw [h2, shl_eq, pow_mul]

theorem uElems_inv : BuildInv uElems elemsW.1 elemsW.2 := by
  unfold uElems CFSG.Quasithin.G2U.build elemsW
  refine build_sim uPar _ _ ⟨?_, rfl, ?_⟩
  · intro e he
    rw [List.mem_singleton.1 he]
    exact good_one4
  · show oneP = encW (fun i => pk ([one4].getD i [])) 1
    rw [encW_succ]
    show oneP = 0 + pk one4 * (2 ^ 64) ^ 0
    rw [pk_facts.1, pow_zero, mul_one, zero_add]

@[expose] noncomputable def commP (x g : ℕ) : Bool :=
  allLtK (fun k => Nat.beq (entK x g k) (entK g x k)) 16

theorem entK_lt (p q k : ℕ) : entK p q k < 16 := rd_lt _ _

theorem commP_eq (x g : ℕ) : (mulP x g == mulP g x) = commP x g := by
  rw [Bool.eq_iff_iff, beq_iff_eq, commP, allLtK_iff]
  constructor
  · intro h k hk
    have e := congrArg (fun c => rd c k) h
    simp only [mulP, rd_encF (fun i _ => entK_lt _ _ i) hk] at e
    rw [e, Nat.beq_refl]
  · intro h
    exact encF_congr fun k hk => Nat.eq_of_beq_eq_true (h k hk)

@[expose] noncomputable def cenP (z z2 x : ℕ) : Bool :=
  (gensP.any fun g => !commP x g) || x == oneP || x == z || x == z2

@[expose] noncomputable def csP (z : ℕ) : ℕ :=
  mulP (mulP (wordCodeP [1, 1, 1]) z) (wordCodeP (invWord [1, 1, 1]))

@[expose] noncomputable def witP (z : ℕ) : Bool :=
  (mulP (csP z) z == mulP z (csP z)) && !(csP z == oneP) && !(csP z == z) && !(csP z == mulP z z)

@[expose] noncomputable def chkP (n E z : ℕ) : Bool :=
  (n == 729) && (mulP z (mulP z z) == oneP) && witP z &&
    allLtK (fun t => cenP z (mulP z z) (rdW E t)) 729

theorem chkP_true : chkP elemsW.1 elemsW.2 (rdW elemsW.2 uZ) = true := by
  decide +kernel

theorem any_congr_mem {l : List (List ℕ)} {f g : List ℕ → Bool} (h : ∀ a ∈ l, f a = g a) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.any_cons, List.any_cons, h a List.mem_cons_self,
      ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem all_range_eq {f : ℕ → Bool} {n : ℕ} : (List.range n).all f = allLtK f n := by
  rw [Bool.eq_iff_iff, List.all_eq_true, allLtK_iff]
  exact ⟨fun h j hj => h j (List.mem_range.2 hj), fun h j hj => h j (List.mem_range.1 hj)⟩

theorem uAt_sim {n E : ℕ} (hI : BuildInv uElems n E) (hn : n = 729) {t : ℕ} (ht : t < 729) :
    Good (uAt t) ∧ pk (uAt t) = rdW E t := by
  obtain ⟨h1, h2, h3⟩ := hI
  have hs : uElems.size = 729 := h2.symm.trans hn
  have hl : t < uElems.toList.length := by rw [Array.length_toList, hs]; exact ht
  have hget : uAt t = uElems.toList[t] := by
    unfold uAt
    rw [arr_getD', List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
  have hg : Good (uAt t) := hget ▸ h1 _ (List.getElem_mem hl)
  refine ⟨hg, ?_⟩
  rw [h3, rdW_encW (fun i hi => ?_) (by rw [hs]; exact ht)]
  · unfold uAt
    rw [arr_getD']
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rwa [Array.length_toList]),
      Option.getD_some]
    exact pk_lt (h1 _ (List.getElem_mem _))

theorem commutes4_pk {x g : List ℕ} (hx : Good x) (hg : Good g) :
    commutes4 x g = (mulP (pk x) (pk g) == mulP (pk g) (pk x)) := by
  unfold commutes4
  rw [beq_pk (good_mul4 _ _) (good_mul4 _ _), ← mulP_pk hx hg, ← mulP_pk hg hx]

theorem u43CenOK_eq {n E z : ℕ} (hI : BuildInv uElems n E) (hn : n = 729) (hz : rdW E uZ = z)
    {t : ℕ}
    (ht : t < 729) : u43CenOK t = cenP z (mulP z z) (rdW E t) := by
  obtain ⟨hg, hp⟩ := uAt_sim hI hn ht
  obtain ⟨hgz, hpz⟩ := uAt_sim hI hn (show uZ < 729 by decide)
  rw [hz] at hpz
  have hany : (uGens.any fun g => !commutes4 (uAt t) g) =
      gensP.any fun g => !commP (rdW E t) g := by
    rw [← uGens_pk, List.any_map]
    refine any_congr_mem fun g hgm => ?_
    simp only [Function.comp_apply, commutes4_pk hg (good_uGens g hgm), hp, commP_eq]
  unfold u43CenOK cenP sq4
  rw [hany, beq_pk hg good_one4, beq_pk hg hgz, beq_pk hg (good_mul4 _ _), ← mulP_pk hgz hgz, hp,
    hpz, pk_facts.1]

theorem u43Check_eq {n E z : ℕ} (hI : BuildInv uElems n E) (hn : n = 729) (hz : rdW E uZ = z) :
    u43Check = chkP n E z := by
  obtain ⟨hgz, hpz⟩ := uAt_sim hI hn (show uZ < 729 by decide)
  rw [hz] at hpz
  have hw := wordCode_sim [1, 1, 1]
  have hw' := wordCode_sim (invWord [1, 1, 1])
  have hcs : conjStep (wordPair [1, 1, 1]) (uAt uZ) =
      mul4 (mul4 (wordCode [1, 1, 1]) (uAt uZ)) (wordCode (invWord [1, 1, 1])) := by
    unfold conjStep wordPair
    rw [List.take_left' hw.1.1, List.drop_left' hw.1.1]
  have hgcs : Good (conjStep (wordPair [1, 1, 1]) (uAt uZ)) := by
    rw [hcs]
    exact good_mul4 _ _
  have hpcs : pk (conjStep (wordPair [1, 1, 1]) (uAt uZ)) = csP z := by
    rw [hcs, ← mulP_pk (good_mul4 _ _) hw'.1, ← mulP_pk hw.1 hgz, hw.2, hw'.2, hpz]
    rfl
  have hwit : u43WitOK = witP z := by
    unfold u43WitOK witP sq4
    rw [commutes4_pk hgcs hgz, beq_pk hgcs good_one4, beq_pk hgcs hgz, beq_pk hgcs (good_mul4 _ _),
      ← mulP_pk hgz hgz, hpcs, hpz, pk_facts.1]
  have hcube : (cube4 (uAt uZ) == one4) = (mulP z (mulP z z) == oneP) := by
    unfold cube4 sq4
    rw [beq_pk (good_mul4 _ _) good_one4, ← mulP_pk hgz (good_mul4 _ _), ← mulP_pk hgz hgz, hpz,
      pk_facts.1]
  have hall : (List.range 729).all u43CenOK =
      allLtK (fun t => cenP z (mulP z z) (rdW E t)) 729 := by
    rw [all_range_eq, Bool.eq_iff_iff, allLtK_iff, allLtK_iff]
    exact ⟨fun h j hj => (u43CenOK_eq hI hn hz hj) ▸ h j hj,
      fun h j hj => (u43CenOK_eq hI hn hz hj).symm ▸ h j hj⟩
  have hn' : (n == 729) = true := by rw [hn]; rfl
  unfold u43Check chkP
  rw [hcube, hwit, hall, hn', Bool.true_and]

end U43P

open U43P in
theorem u43Check_true : u43Check = true := by
  have hn : elemsW.1 = 729 := by
    have hc := chkP_true
    simp only [chkP, Bool.and_eq_true, beq_iff_eq] at hc
    exact hc.1.1.1
  rw [u43Check_eq uElems_inv hn rfl]
  exact chkP_true

theorem u43Check_parts : cube4 (uAt uZ) = one4 ∧ u43WitOK = true ∧
    (List.range 729).all u43CenOK = true := by
  have h := u43Check_true
  simp only [u43Check, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem uZ_lt : uZ < 729 := by decide

theorem u43WitOK_parts (h : u43WitOK = true) :
    commutes4 (conjStep (wordPair [1, 1, 1]) (uAt uZ)) (uAt uZ) = true ∧
      conjStep (wordPair [1, 1, 1]) (uAt uZ) ≠ one4 ∧
      conjStep (wordPair [1, 1, 1]) (uAt uZ) ≠ uAt uZ ∧
      conjStep (wordPair [1, 1, 1]) (uAt uZ) ≠ sq4 (uAt uZ) := by
  unfold u43WitOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hA, hB⟩, hC⟩, hD⟩ := h
  refine ⟨hA, fun e => ?_, fun e => ?_, fun e => ?_⟩
  · rw [e] at hB; simp at hB
  · rw [e] at hC; simp at hC
  · rw [e] at hD; simp at hD

theorem commutes_uGens_of_central (hsyl : uSylCheck = true) {t : ℕ} {s : SUg}
    (hst : dec4 (uAt t) = toMat s) (hc : ∀ g ∈ sylS, g * s = s * g) :
    ∀ g ∈ uGens, commutes4 (uAt t) g = true := by
  intro g hg
  unfold uGens at hg
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hg
  have hw4 : ∀ l ∈ w, l < 4 := (uSylCheck_parts hsyl).2.2.2.2 w hw
  have hmem : wordElem w ∈ sylS := Subgroup.subset_closure ⟨w, hw, rfl⟩
  have hm := congrArg toMat (hc (wordElem w) hmem)
  have hg' : toMat (wordElem w) = dec4 (wordCode w) := by
    rw [toMat_apply]
    exact coe_wordElem w hw4
  rw [map_mul, map_mul, hg', ← hst, ← dec4_mul4, ← dec4_mul4] at hm
  have h2 := dec4_injective (canon4_mul4 _ _) (canon4_mul4 _ _) hm
  unfold commutes4
  exact beq_iff_eq.mpr h2.symm

theorem sAt_uZ_pow_three (hsyl : uSylCheck = true) : sAt uZ ^ 3 = 1 :=
  pow_three_of_cube4 hsyl uZ_lt u43Check_parts.1

theorem inv_eq_mul_self_of_pow_three (x : SUg) (h : x ^ 3 = 1) : x⁻¹ = x * x :=
  inv_eq_of_mul_eq_one_right ((pow_three x).symm.trans h)

theorem inv_sAt_uZ (hsyl : uSylCheck = true) : (sAt uZ)⁻¹ = sAt uZ * sAt uZ :=
  inv_eq_mul_self_of_pow_three (sAt uZ) (sAt_uZ_pow_three hsyl)

theorem centre_sylS (hsyl : uSylCheck = true) {s : SUg} (hs : s ∈ sylS)
    (hc : ∀ g ∈ sylS, g * s = s * g) : s = 1 ∨ s = sAt uZ ∨ s = (sAt uZ)⁻¹ := by
  obtain ⟨hz3, -, hall⟩ := u43Check_parts
  obtain ⟨t, ht, hst⟩ := exists_code_sylS hsyl hs
  have hgen := commutes_uGens_of_central hsyl hst hc
  have hok : u43CenOK t = true := List.all_eq_true.mp hall t (List.mem_range.mpr ht)
  unfold u43CenOK at hok
  have hany : (uGens.any fun g => !commutes4 (uAt t) g) = false := by
    rw [Bool.eq_false_iff]
    intro h
    obtain ⟨g, hg, hg'⟩ := List.any_eq_true.mp h
    rw [hgen g hg] at hg'
    exact absurd hg' (by decide)
  rw [hany, Bool.false_or] at hok
  simp only [Bool.or_eq_true, beq_iff_eq] at hok
  rcases hok with (h1 | h2) | h3
  · left
    apply toMat_injective
    rw [map_one, ← hst, h1, dec4_one4]
  · right; left
    apply toMat_injective
    rw [← hst, h2, toMat_sAt hsyl uZ_lt]
  · right; right
    have hsq : s = sAt uZ * sAt uZ := by
      apply toMat_injective
      rw [map_mul, toMat_sAt hsyl uZ_lt, ← hst, h3, dec4_sq4]
    rw [hsq]
    exact (inv_sAt_uZ hsyl).symm

@[expose] noncomputable def u43X : SUg := wordElem [1, 1, 1] * sAt uZ * (wordElem [1, 1, 1])⁻¹

theorem toMat_u43X (hsyl : uSylCheck = true) :
    toMat u43X = dec4 (conjStep (wordPair [1, 1, 1]) (uAt uZ)) := by
  unfold u43X
  rw [dec4_conjStep [1, 1, 1] (by decide) (uAt uZ), map_mul, map_mul, toMat_sAt hsyl uZ_lt]
  rfl

theorem u43X_comm (hsyl : uSylCheck = true) : u43X * sAt uZ = sAt uZ * u43X := by
  have hc := (u43WitOK_parts u43Check_parts.2.1).1
  unfold commutes4 at hc
  apply toMat_injective
  rw [map_mul, map_mul, toMat_u43X hsyl, toMat_sAt hsyl uZ_lt, ← dec4_mul4, ← dec4_mul4]
  exact congrArg dec4 (beq_iff_eq.mp hc)

theorem u43X_ne_one (hsyl : uSylCheck = true) : u43X ≠ 1 := by
  have hne := (u43WitOK_parts u43Check_parts.2.1).2.1
  intro h
  apply hne
  have h1 : dec4 (conjStep (wordPair [1, 1, 1]) (uAt uZ)) = dec4 one4 := by
    rw [← toMat_u43X hsyl, h, map_one, dec4_one4]
  exact dec4_injective (by unfold conjStep; exact canon4_mul4 _ _) canon4_one4 h1

theorem u43X_ne_z (hsyl : uSylCheck = true) : u43X ≠ sAt uZ := by
  have hne := (u43WitOK_parts u43Check_parts.2.1).2.2.1
  intro h
  apply hne
  have h1 : dec4 (conjStep (wordPair [1, 1, 1]) (uAt uZ)) = dec4 (uAt uZ) := by
    rw [← toMat_u43X hsyl, h, toMat_sAt hsyl uZ_lt]
  exact dec4_injective (by unfold conjStep; exact canon4_mul4 _ _) (canon4_uAt hsyl uZ_lt) h1

theorem u43X_ne_inv (hsyl : uSylCheck = true) : u43X ≠ (sAt uZ)⁻¹ := by
  have hne := (u43WitOK_parts u43Check_parts.2.1).2.2.2
  intro h
  apply hne
  have h1 : dec4 (conjStep (wordPair [1, 1, 1]) (uAt uZ)) = dec4 (sq4 (uAt uZ)) := by
    rw [← toMat_u43X hsyl, h, inv_sAt_uZ hsyl, map_mul, toMat_sAt hsyl uZ_lt, dec4_sq4]
  exact dec4_injective (by unfold conjStep; exact canon4_mul4 _ _)
    (by unfold sq4; exact canon4_mul4 _ _) h1

end CFSG.RankThree.PartTwo.Sec4.RonanK432
