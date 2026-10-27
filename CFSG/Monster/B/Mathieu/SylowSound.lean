module

public import CFSG.Monster.B.Mathieu.SylowCore
public import CFSG.Monster.B.Mathieu.Order
public import CFSG.Certificates.NormalGeneration
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Monster.B.Mathieu

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

variable {n : ℕ}

theorem size_compA (t u : Array ℕ) : (compA n t u).size = n := by simp [compA]

theorem size_idA : (idA n).size = n := by simp [idA]

theorem size_powArr (t : Array ℕ) : ∀ k, (powArr n t k).size = n
  | 0 => size_idA
  | _ + 1 => size_compA _ _

theorem rep_powArr {t : Array ℕ} {g : Equiv.Perm (Fin n)} (h : Rep n t g) :
    ∀ k, Rep n (powArr n t k) (g ^ k)
  | 0 => by
    rw [pow_zero]
    exact rep_idA
  | k + 1 => by
    rw [powArr, pow_succ']
    exact rep_compA h (rep_powArr h k)

theorem rep_of_permArrOK {t : Array ℕ} (h : permArrOK n t = true) :
    t.size = n ∧ Rep n t (permOfArr n t) ∧ Rep n (invCand n t) (permOfArr n t)⁻¹ := by
  simp only [permArrOK, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1, rep_permOfArr h.2⟩

theorem toList_eq_imageList {t : Array ℕ} {g : Equiv.Perm (Fin n)} (hs : t.size = n)
    (h : Rep n t g) : t.toList = imageList g := by
  apply List.ext_getElem (by simp [hs, imageList])
  intro i h1 h2
  have hi : i < n := by simpa [imageList] using h2
  rw [Array.getElem_toList, ← getElem!_pos t i (by omega), h.apply hi]
  simp [imageList]

theorem imageList_injective : Function.Injective (imageList (n := n)) := by
  intro g h e
  have e' := List.ofFn_injective e
  exact Equiv.ext fun x => Fin.ext (congrFun e' x)

theorem eq_of_rep_of_size {a b : Array ℕ} {g : Equiv.Perm (Fin n)} (ha : a.size = n)
    (hb : b.size = n) (hra : Rep n a g) (hrb : Rep n b g) : a = b :=
  Array.toList_inj.1 ((toList_eq_imageList ha hra).trans (toList_eq_imageList hb hrb).symm)

theorem letterValue_def {G : Type*} [Group G] (gs : List G) (l : ℤ) :
    letterValue gs l = if 0 < l then gs.getD (l.natAbs - 1) 1 else (gs.getD (l.natAbs - 1) 1)⁻¹ :=
  rfl

theorem wordValue_cons {G : Type*} [Group G] (gs : List G) (l : ℤ) (w : List ℤ) :
    wordValue gs (l :: w) = letterValue gs l * wordValue gs w := by
  simp [wordValue]

theorem wordValue_mem {G : Type*} [Group G] (gs : List G) (H : Subgroup G)
    (hgs : ∀ g ∈ gs, g ∈ H) (w : List ℤ) : wordValue gs w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons l w ih =>
    rw [wordValue_cons]
    refine H.mul_mem ?_ ih
    have hg : gs.getD (l.natAbs - 1) 1 ∈ H := by
      rw [List.getD_eq_getElem?_getD]
      cases h : gs[l.natAbs - 1]? with
      | none => exact H.one_mem
      | some g => exact hgs g (List.mem_of_getElem? h)
    rw [letterValue_def]
    split
    · exact hg
    · exact H.inv_mem hg

theorem evalWord_toLetters {G : Type*} [Group G] (gs : List G) :
    ∀ w : List ℤ, lettersOK gs.length w = true →
      Quiver.SchreierGraph.evalWord (fun h : Fin gs.length => gs.getD h 1)
        (toLetters gs.length w) = wordValue gs w
  | [], _ => rfl
  | l :: w, hw => by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := hw
    have hw' : lettersOK gs.length w = true := by
      simpa [lettersOK, List.all_eq_true] using hw
    have hcons : toLetters gs.length (l :: w) = (⟨l.natAbs - 1, by omega⟩, decide (0 < l)) ::
        toLetters gs.length w := by
      simp [toLetters, hl0, hlj]
    rw [hcons, wordValue_cons, letterValue_def, ← evalWord_toLetters gs w hw']
    by_cases hpos : 0 < l
    · rw [decide_eq_true hpos, Quiver.SchreierGraph.evalWord_cons_true, ite_eq_left hpos]
    · rw [show decide (0 < l) = false by simpa using hpos,
        Quiver.SchreierGraph.evalWord_cons_false, ite_eq_right hpos]

theorem evalWord_toLetters' {G : Type*} [Group G] (gs : List G) (j : ℕ) (hj : j = gs.length)
    (w : List ℤ) (hw : lettersOK j w = true) :
    Quiver.SchreierGraph.evalWord (fun h : Fin j => gs.getD h 1) (toLetters j w) =
      wordValue gs w := by
  subst hj
  exact evalWord_toLetters gs w hw

@[expose] noncomputable def rootGroup (r : GroupRecord) (n : ℕ) :
    Subgroup (Equiv.Perm (Fin n)) :=
  Subgroup.closure {g | ∃ a ∈ r.chain.generators, arrPerm n a = g}

theorem closure_origArrs (c : ChainRecord) :
    Subgroup.closure {g | ∃ k < c.origArrs.size, permOfArr n c.origArrs[k]! = g} =
      Subgroup.closure {g | ∃ a ∈ c.generators, arrPerm n a = g} := by
  congr 1
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [c.origArrs_size] at hk
    exact ⟨c.generators[k], List.getElem_mem hk, by rw [arrPerm, c.origArrs_get hk]⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
    exact ⟨k, by rw [c.origArrs_size]; exact hk, by rw [arrPerm, c.origArrs_get hk]⟩

theorem rootGens_mem (r : GroupRecord) : ∀ g ∈ r.rootGens n, g ∈ rootGroup r n := by
  intro g hg
  rw [GroupRecord.rootGens, List.mem_map] at hg
  obtain ⟨a, ha, rfl⟩ := hg
  exact Subgroup.subset_closure ⟨a, ha, rfl⟩

theorem rootGens_getD (r : GroupRecord) {k : ℕ} (hk : k < r.chain.generators.length) :
    (r.rootGens n).getD k 1 = permOfArr n r.chain.origArrs[k]! := by
  rw [GroupRecord.rootGens, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
    arrPerm, r.chain.origArrs_get hk]

theorem rawInvs_get (O : Array (Array ℕ)) {k : ℕ} (hk : k < O.size) :
    (rawInvs n O)[k]! = invCand n O[k]! := by
  rw [rawInvs, getElem!_pos _ k (by simpa using hk), Array.getElem_map, getElem!_pos O k hk]

theorem root_facts {r : GroupRecord} (h : r.chain.check n = true) :
    (∀ k < r.chain.origArrs.size, Rep n r.chain.origArrs[k]! ((r.rootGens n).getD k 1) ∧
      Rep n (rawInvs n r.chain.origArrs)[k]! ((r.rootGens n).getD k 1)⁻¹) ∧
    Nat.card (rootGroup r n) = (r.chain.orbitSizes n).prod ∧
    ∀ (t : Array ℕ) (g : Equiv.Perm (Fin n)), Rep n t g →
      (siftA n (rawLevels n r.chain.strongArrs r.chain.baseArr) r.chain.baseArr 0 t = true ↔
        g ∈ rootGroup r n) := by
  have h' := h
  simp only [ChainRecord.check, Bool.and_eq_true, beq_iff_eq] at h'
  obtain ⟨⟨-, -⟩, hok⟩ := h'
  have hok' := hok
  simp only [arraysOK, Bool.and_eq_true, decide_eq_true_eq] at hok'
  obtain ⟨⟨⟨-, -⟩, hO⟩, -⟩ := hok'
  obtain ⟨Q, -, -, hsub, hcard, -, hsift⟩ := exists_valid_of_arraysOK hok
  rw [closure_origArrs] at hsub
  have hG : Q.originalSubgroup = rootGroup r n := hsub
  refine ⟨fun k hk => ?_, ?_, ?_⟩
  · have hk' : k < r.chain.generators.length := by rwa [r.chain.origArrs_size] at hk
    rw [rootGens_getD r hk', rawInvs_get _ hk]
    exact rep_permOfArr (allLt_spec hO hk)
  · rw [← hG, hcard]
    rfl
  · intro t g hg
    rw [hsift t g hg, hG]

theorem rep_wordA_root {r : GroupRecord} (h : r.chain.check n = true) {w : List ℤ}
    (hw : lettersOK r.chain.origArrs.size w = true) :
    Rep n (wordA n r.chain.origArrs (rawInvs n r.chain.origArrs) w)
      (wordValue (r.rootGens n) w) := by
  obtain ⟨hreps, -, -⟩ := root_facts h
  have hrep := rep_wordA (n := n) (gs := fun k => (r.rootGens n).getD k 1)
    (j := r.chain.origArrs.size) (fun k hk => (hreps k hk).1) (fun k hk => (hreps k hk).2) w hw
  have hlen : r.chain.origArrs.size = (r.rootGens n).length := by
    rw [r.chain.origArrs_size, GroupRecord.rootGens, List.length_map]
  rwa [evalWord_toLetters' (r.rootGens n) _ hlen w hw] at hrep

@[expose] noncomputable def SylowRecord.subgroup (s : SylowRecord) (n : ℕ) :
    Subgroup (Equiv.Perm (Fin n)) :=
  Subgroup.closure {g | ∃ a ∈ s.generators, arrPerm n a = g}

@[expose] noncomputable def SylowRecord.reps (s : SylowRecord) (n : ℕ) :
    List (Equiv.Perm (Fin n)) :=
  s.normalGeneration.map fun ng => arrPerm n ng.representative

@[expose] def SylowFacts (G : Subgroup (Equiv.Perm (Fin n))) (N : ℕ)
    (gs : List (Equiv.Perm (Fin n))) (s : SylowRecord) : Prop :=
  s.prime.Prime ∧ (∀ a ∈ s.generators, imageList (arrPerm n a) = a) ∧ s.subgroup n ≤ G ∧
    Nat.card (s.subgroup n) = s.prime ^ N.factorization s.prime ∧
    s.prime ^ N.factorization s.prime ∣ N ∧ ¬s.prime ^ (N.factorization s.prime + 1) ∣ N ∧
    (s.reps n).Nodup ∧
    (∀ x ∈ s.reps n, x ∈ s.subgroup n ∧ orderOf x = s.prime ∧
      ∀ y ∈ Subgroup.zpowers x, y ≠ 1 → imageList x ≤ imageList y) ∧
    (∀ Q : Subgroup (Equiv.Perm (Fin n)), Q ≤ s.subgroup n → Nat.card Q = s.prime →
      ∃! x, x ∈ s.reps n ∧ x ∈ Q) ∧
    (∀ ng ∈ s.normalGeneration, (∀ w ∈ ng.conjugators, ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ gs.length) ∧
      Subgroup.closure {g | g ∈ ng.conjugates gs} = G) ∧
    ∃ P : Sylow s.prime G, (P : Subgroup G).map G.subtype = s.subgroup n ∧
      ∀ Q : Subgroup G, Q ≤ P → Nat.card Q = s.prime → Subgroup.normalClosure (Q : Set G) = ⊤

theorem genArrs_size (s : SylowRecord) : s.genArrs.size = s.generators.length := by
  simp [SylowRecord.genArrs]

theorem genArrs_get (s : SylowRecord) {k : ℕ} (hk : k < s.generators.length) :
    s.genArrs[k]! = (s.generators[k]).toArray := by
  rw [getElem!_pos s.genArrs k (by rw [genArrs_size]; exact hk)]
  simp [SylowRecord.genArrs]

theorem all_genArrs {s : SylowRecord} {f : Array ℕ → Bool} (h : s.genArrs.all f = true) :
    ∀ a ∈ s.generators, f a.toArray = true := by
  rw [Array.all_eq_true_iff_forall_mem] at h
  intro a ha
  refine h _ ?_
  rw [SylowRecord.genArrs, List.mem_toArray, List.mem_map]
  exact ⟨a, ha, rfl⟩

theorem all_repArrs {s : SylowRecord} {f : Array ℕ → Bool} (h : s.repArrs.all f = true) :
    ∀ ng ∈ s.normalGeneration, f ng.representative.toArray = true := by
  rw [Array.all_eq_true_iff_forall_mem] at h
  intro ng hng
  refine h _ ?_
  rw [SylowRecord.repArrs, List.mem_toArray, List.mem_map]
  exact ⟨ng, hng, rfl⟩

theorem closure_genArrs (s : SylowRecord) :
    Subgroup.closure {g | ∃ k < s.genArrs.size, permOfArr n s.genArrs[k]! = g} = s.subgroup n := by
  unfold SylowRecord.subgroup
  congr 1
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [genArrs_size] at hk
    exact ⟨s.generators[k], List.getElem_mem hk, by rw [arrPerm, genArrs_get s hk]⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
    exact ⟨k, by rw [genArrs_size]; exact hk, by rw [arrPerm, genArrs_get s hk]⟩

theorem exists_index_of_card {G : Type*} [Group G] (P : Subgroup G) [Finite P] (f : ℕ → G)
    (m : ℕ) (hmem : ∀ i < m, f i ∈ P) (hinj : ∀ i < m, ∀ j < m, f i = f j → i = j)
    (hcard : Nat.card P = m) : ∀ x ∈ P, ∃ i < m, f i = x := by
  let F : Fin m → P := fun i => ⟨f i, hmem i i.2⟩
  have hF : Function.Injective F := fun i j h =>
    Fin.ext (hinj i i.2 j j.2 (congrArg Subtype.val h))
  have hb := hF.bijective_of_nat_card_le (by simp [hcard])
  intro x hx
  obtain ⟨i, hi⟩ := hb.2 ⟨x, hx⟩
  exact ⟨i, i.2, congrArg Subtype.val hi⟩

theorem factorization_eq_of_dvd {N p k : ℕ} (hp : p.Prime) (h1 : N % p ^ k = 0)
    (h2 : N % p ^ (k + 1) ≠ 0) : N.factorization p = k := by
  have hN : N ≠ 0 := by
    rintro rfl
    exact h2 (Nat.zero_mod _)
  have hle := (hp.pow_dvd_iff_le_factorization hN).1 (Nat.dvd_of_mod_eq_zero h1)
  have hlt : ¬k + 1 ≤ N.factorization p := fun h =>
    h2 (Nat.mod_eq_zero_of_dvd ((hp.pow_dvd_iff_le_factorization hN).2 h))
  omega

theorem strongArrs_get_elems (s : SylowRecord) (n N : ℕ) {i : ℕ} (hi : i < (s.elems n N).size) :
    (s.strongArrs n N)[s.genArrs.size + i]! = (s.elems n N)[i]! := by
  have hlt : s.genArrs.size + i < (s.strongArrs n N).size := by
    simp [SylowRecord.strongArrs, hi]
  rw [getElem!_pos (s.strongArrs n N) (s.genArrs.size + i) hlt,
    getElem!_pos (s.elems n N) i hi]
  simp only [SylowRecord.strongArrs]
  rw [Array.getElem_append_right (by omega)]
  simp

theorem sylow_enum_facts {s : SylowRecord} {n N : ℕ}
    (hok : arraysOK n s.genArrs (s.strongArrs n N) (fullBase n) (s.wordArrs n N) = true)
    (hsize : (rawOrbitSizes n (s.strongArrs n N) (fullBase n)).prod = (s.elems n N).size)
    (hvalid : ∀ i < (s.elems n N).size, permArrOK n (s.elems n N)[i]! = true)
    (hnd : ((s.elems n N).toList.map Array.toList).Nodup) :
    Nat.card (s.subgroup n) = (s.elems n N).size ∧
      (∀ i < (s.elems n N).size, permOfArr n (s.elems n N)[i]! ∈ s.subgroup n) ∧
      ∀ x ∈ s.subgroup n, ∃ i < (s.elems n N).size, permOfArr n (s.elems n N)[i]! = x := by
  obtain ⟨Q, -, -, hsub, hcard, hstrong, -⟩ := exists_valid_of_arraysOK hok
  rw [closure_genArrs] at hsub
  have hcardP : Nat.card (s.subgroup n) = (s.elems n N).size := by rw [← hsub, hcard, hsize]
  have hmem : ∀ i < (s.elems n N).size, permOfArr n (s.elems n N)[i]! ∈ s.subgroup n := by
    intro i hi
    have hj : s.genArrs.size + i < (s.strongArrs n N).size := by
      simp [SylowRecord.strongArrs, hi]
    have := hstrong _ hj
    rwa [strongArrs_get_elems s n N hi, hsub] at this
  have hinj : ∀ i < (s.elems n N).size, ∀ j < (s.elems n N).size,
      permOfArr n (s.elems n N)[i]! = permOfArr n (s.elems n N)[j]! → i = j := by
    intro i hi j hj e
    obtain ⟨hsi, hri, -⟩ := rep_of_permArrOK (hvalid i hi)
    obtain ⟨hsj, hrj, -⟩ := rep_of_permArrOK (hvalid j hj)
    rw [e] at hri
    have hij := eq_of_rep_of_size hsi hsj hri hrj
    have hlen : (s.elems n N).toList.length = (s.elems n N).size := by simp
    refine (List.Nodup.getElem_inj_iff hnd (i := i) (j := j)
      (hi := by simpa using hi) (hj := by simpa using hj)).1 ?_
    simp only [List.getElem_map, Array.getElem_toList]
    rw [← getElem!_pos (s.elems n N) i hi, ← getElem!_pos (s.elems n N) j hj, hij]
  exact ⟨hcardP, hmem, exists_index_of_card _ _ _ hmem hinj hcardP⟩

theorem rep_facts {p : ℕ} (hp : p.Prime) {elems : Array (Array ℕ)}
    {P : Subgroup (Equiv.Perm (Fin n))} (hmem : ∀ i < elems.size, permOfArr n elems[i]! ∈ P)
    (hvalid : ∀ i < elems.size, permArrOK n elems[i]! = true) {x : List ℕ}
    (h : repCheck n p elems x.toArray = true) :
    x.toArray.size = n ∧ Rep n x.toArray (arrPerm n x) ∧ arrPerm n x ∈ P ∧
      orderOf (arrPerm n x) = p ∧
      ∀ y ∈ Subgroup.zpowers (arrPerm n x), y ≠ 1 → imageList (arrPerm n x) ≤ imageList y := by
  simp only [repCheck, Bool.and_eq_true, Bool.not_eq_true', Array.any_eq_true,
    List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hok, ⟨i, hi, hix⟩⟩, hne⟩, hpow⟩, hlex⟩ := h
  obtain ⟨hsize, hrep, -⟩ := rep_of_permArrOK hok
  set X := arrPerm n x with hXdef
  have hX : Rep n x.toArray X := hrep
  have hXP : X ∈ P := by
    obtain ⟨-, hri, -⟩ := rep_of_permArrOK (hvalid i hi)
    have e := eq_of_eqA hri hX (by rwa [← getElem!_pos elems i hi] at hix)
    rw [← e]
    exact hmem i hi
  have hX1 : X ≠ 1 := fun e => by
    rw [e] at hX
    rw [(eqA_iff hX rep_idA).2 rfl] at hne
    exact Bool.false_ne_true hne.symm
  have hXp : X ^ p = 1 := eq_of_eqA (rep_powArr hX p) rep_idA hpow
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf X = p := orderOf_eq_prime hXp hX1
  refine ⟨hsize, hX, hXP, hord, fun y hy hy1 => ?_⟩
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hord, Finset.mem_image] at hy
  obtain ⟨j, hj, rfl⟩ := hy
  rw [Finset.mem_range] at hj
  rcases hlex j hj with h0 | hle
  · subst h0
    exact absurd (pow_zero X) hy1
  · rw [← toList_eq_imageList hsize hX,
      ← toList_eq_imageList (size_powArr _ j) (rep_powArr hX j)]
    exact hle

theorem eq_of_lex_least {p : ℕ} {x x' : Equiv.Perm (Fin n)} {Q : Subgroup (Equiv.Perm (Fin n))}
    (hp : p.Prime) (hx : orderOf x = p) (hx' : orderOf x' = p) (hQ : Nat.card Q = p)
    (hxQ : x ∈ Q) (hx'Q : x' ∈ Q)
    (hlx : ∀ y ∈ Subgroup.zpowers x, y ≠ 1 → imageList x ≤ imageList y)
    (hlx' : ∀ y ∈ Subgroup.zpowers x', y ≠ 1 → imageList x' ≤ imageList y) : x = x' := by
  have hz : ∀ {z : Equiv.Perm (Fin n)}, orderOf z = p → z ∈ Q → Subgroup.zpowers z = Q :=
    fun {z} hz hzQ => Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hzQ)
      (by rw [Nat.card_zpowers, hz, hQ])
  have hne : ∀ {z : Equiv.Perm (Fin n)}, orderOf z = p → z ≠ 1 := fun {z} hz e => by
    rw [e, orderOf_one] at hz
    exact hp.one_lt.ne hz
  have h1 := hlx x' (by rw [hz hx hxQ]; exact hx'Q) (hne hx')
  have h2 := hlx' x (by rw [hz hx' hx'Q]; exact hxQ) (hne hx)
  exact imageList_injective (le_antisymm h1 h2)

theorem cover_facts {p : ℕ} {elems reps : Array (Array ℕ)} {P : Subgroup (Equiv.Perm (Fin n))}
    (hexh : ∀ x ∈ P, ∃ i < elems.size, permOfArr n elems[i]! = x)
    (hvalid : ∀ i < elems.size, permArrOK n elems[i]! = true)
    (hcov : ∀ i < elems.size, coverCheck n p reps elems[i]! = true)
    (hrepvalid : ∀ j < reps.size, permArrOK n reps[j]! = true) (hp : 1 < p) :
    ∀ Q : Subgroup (Equiv.Perm (Fin n)), Q ≤ P → Nat.card Q = p →
      ∃ j < reps.size, permOfArr n reps[j]! ∈ Q := by
  intro Q hQP hQ
  have : Nontrivial Q := by
    rw [← Finite.one_lt_card_iff_nontrivial, hQ]
    exact hp
  obtain ⟨x, hxQ, hx1⟩ := Q.exists_ne_one_of_nontrivial
  obtain ⟨i, hi, rfl⟩ := hexh x (hQP hxQ)
  obtain ⟨-, hri, -⟩ := rep_of_permArrOK (hvalid i hi)
  have hxp : permOfArr n elems[i]! ^ p = 1 := by
    have := pow_card_eq_one' (G := Q) (x := ⟨_, hxQ⟩)
    rw [hQ] at this
    exact congrArg Subtype.val this
  have h := hcov i hi
  simp only [coverCheck, Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, List.mem_range,
    Bool.and_eq_true, bne_iff_ne, ne_eq, Array.any_eq_true] at h
  rcases h with (h1 | h2) | ⟨j, hj, hj0, idx, hidx, he⟩
  · exact absurd (eq_of_eqA hri rep_idA h1) hx1
  · rw [(eqA_iff (rep_powArr hri p) rep_idA).2 hxp] at h2
    exact absurd h2 (by decide)
  · obtain ⟨-, hrr, -⟩ := rep_of_permArrOK (hrepvalid idx hidx)
    have e := eq_of_eqA (rep_powArr hri j) hrr
      (by rwa [← getElem!_pos reps idx hidx] at he)
    refine ⟨idx, hidx, ?_⟩
    rw [← e]
    exact Q.pow_mem hxQ j

theorem lettersOK_spec {j : ℕ} {w : List ℤ} (h : lettersOK j w = true) :
    ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ j := by
  intro l hl
  simp only [lettersOK, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at h
  exact h l hl

theorem ChainRecord.rep_origArrs {c : ChainRecord} (h : c.check n = true) {k : ℕ}
    (hk : k < c.generators.length) :
    Rep n (c.generators[k]).toArray (arrPerm n c.generators[k]) := by
  simp only [ChainRecord.check, arraysOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨-, ⟨⟨-, hO⟩, -⟩⟩ := h
  have := allLt_spec hO (by rw [c.origArrs_size]; exact hk)
  rw [c.origArrs_get hk] at this
  exact (rep_permOfArr this).1

theorem normalGen_facts {r : GroupRecord} {N : ℕ} (hroot : r.chain.check n = true)
    (hN : (r.chain.orbitSizes n).prod = N) {ng : NormalGenRecord}
    (h : normalGenCheck n N r.chain.origArrs ng = true)
    (hrep : Rep n ng.representative.toArray (arrPerm n ng.representative))
    (hxG : arrPerm n ng.representative ∈ rootGroup r n) :
    (∀ w ∈ ng.conjugators, ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ (r.rootGens n).length) ∧
      Subgroup.closure {g | g ∈ ng.conjugates (r.rootGens n)} = rootGroup r n := by
  simp only [normalGenCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hlet, hchain⟩, hprod⟩, hlen⟩, hzip⟩ := h
  have hlenO : r.chain.origArrs.size = (r.rootGens n).length := by
    rw [r.chain.origArrs_size, GroupRecord.rootGens, List.length_map]
  refine ⟨fun w hw => by rw [← hlenO]; exact lettersOK_spec (hlet w hw), ?_⟩
  obtain ⟨Q, -, -, hsub, hcard⟩ := ChainRecord.exists_records_of_check hchain
  set X := arrPerm n ng.representative
  set gs := r.rootGens n
  have hgen : ∀ j (hj : j < ng.chain.generators.length) (hj' : j < ng.conjugators.length),
      arrPerm n ng.chain.generators[j] =
        (wordValue gs ng.conjugators[j])⁻¹ * X * wordValue gs ng.conjugators[j] := by
    intro j hj hj'
    have hz := hzip (ng.chain.generators[j], ng.conjugators[j])
      (List.mem_iff_getElem.2 ⟨j, by simp [hj, hj'], by simp⟩)
    simp only at hz
    obtain ⟨hinv, heq⟩ := hz
    have hg := rep_wordA_root hroot (hlet _ (List.getElem_mem hj'))
    have hconj := rep_compA (rep_inv_of_isInvA hg hinv) (rep_compA hrep hg)
    have e := eq_of_eqA (ChainRecord.rep_origArrs hchain hj) hconj heq
    rw [e, mul_assoc]
  have hset : {g | ∃ a ∈ ng.chain.generators, arrPerm n a = g} =
      {g | g ∈ ng.conjugates gs} := by
    ext g
    simp only [Set.mem_ofPred_eq, NormalGenRecord.conjugates, List.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
      exact ⟨ng.conjugators[j], List.getElem_mem (by omega), (hgen j hj (by omega)).symm⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
      exact ⟨ng.chain.generators[j], List.getElem_mem (by omega), hgen j (by omega) hj⟩
  rw [hset] at hsub
  have hle : Subgroup.closure {g | g ∈ ng.conjugates gs} ≤ rootGroup r n := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_ofPred_eq, NormalGenRecord.conjugates, List.mem_map] at hg
    obtain ⟨w, -, rfl⟩ := hg
    have hw := wordValue_mem gs (rootGroup r n) (rootGens_mem r) w
    exact (rootGroup r n).mul_mem ((rootGroup r n).mul_mem ((rootGroup r n).inv_mem hw) hxG) hw
  obtain ⟨-, hGcard, -⟩ := root_facts hroot
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hGcard, hN, ← hsub, hcard, hprod]

theorem normalClosure_eq_top_of_conjugates {G : Subgroup (Equiv.Perm (Fin n))}
    {x : Equiv.Perm (Fin n)} (hx : x ∈ G) (gs : List (Equiv.Perm (Fin n)))
    (hgs : ∀ g ∈ gs, g ∈ G)
    (hcl : Subgroup.closure {y | ∃ g ∈ gs, g⁻¹ * x * g = y} = G) :
    Subgroup.normalClosure ({⟨x, hx⟩} : Set G) = ⊤ := by
  let g : Fin gs.length → G := fun i => ⟨gs[i], hgs _ (List.getElem_mem i.2)⟩
  refine (full_order_conjugates_normally_generate (⟨x, hx⟩ : G) g ?_).2
  have hmap : (conjugateGenerated (⟨x, hx⟩ : G) g).map G.subtype = G := by
    rw [conjugateGenerated, MonoidHom.map_closure]
    refine Eq.trans ?_ hcl
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨gs[i], List.getElem_mem i.2, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hh
      exact ⟨_, ⟨⟨i, hi⟩, rfl⟩, rfl⟩
  rw [← Subgroup.card_map_of_injective (f := G.subtype) G.subtype_injective, hmap]

theorem repArrs_size (s : SylowRecord) : s.repArrs.size = s.normalGeneration.length := by
  simp [SylowRecord.repArrs]

theorem repArrs_get (s : SylowRecord) {j : ℕ} (hj : j < s.normalGeneration.length) :
    s.repArrs[j]! = (s.normalGeneration[j]).representative.toArray := by
  rw [getElem!_pos s.repArrs j (by rw [repArrs_size]; exact hj)]
  simp [SylowRecord.repArrs]

theorem sylowFacts_of_check {r : GroupRecord} {N : ℕ} (hroot : r.chain.check n = true)
    (hN : (r.chain.orbitSizes n).prod = N) {s : SylowRecord}
    (hs : sylowCheck n N r.chain s = true) (hp : s.prime.Prime) :
    SylowFacts (rootGroup r n) N (r.rootGens n) s := by
  simp only [sylowCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hgens, hok⟩, hsize⟩, hpts⟩, hvalid⟩, hnd⟩, hdiv⟩, hndiv⟩, hrnd⟩, hreps⟩,
    hcov⟩, hngall⟩ := hs
  set p := s.prime
  set k := s.exponent N
  set G := rootGroup r n
  have hfact : N.factorization p = k := factorization_eq_of_dvd hp hdiv hndiv
  obtain ⟨-, -, hsift⟩ := root_facts hroot
  obtain ⟨-, hGcard, -⟩ := root_facts hroot
  have hgen := all_genArrs hgens
  have hgenrep : ∀ a ∈ s.generators, a.toArray.size = n ∧ Rep n a.toArray (arrPerm n a) := by
    intro a ha
    simp only [Bool.and_eq_true] at hgen
    obtain ⟨hs1, hr1, -⟩ := rep_of_permArrOK (hgen a ha).1
    exact ⟨hs1, hr1⟩
  have hgenG : ∀ a ∈ s.generators, arrPerm n a ∈ G := by
    intro a ha
    simp only [Bool.and_eq_true] at hgen
    exact (hsift _ _ (hgenrep a ha).2).1 (hgen a ha).2
  have hPG : s.subgroup n ≤ G := by
    rw [SylowRecord.subgroup, Subgroup.closure_le]
    rintro _ ⟨a, ha, rfl⟩
    exact hgenG a ha
  have hvalid' : ∀ i < (s.elems n N).size, permArrOK n (s.elems n N)[i]! = true := by
    intro i hi
    rw [Array.all_eq_true] at hvalid
    rw [getElem!_pos (s.elems n N) i hi]
    exact hvalid i hi
  obtain ⟨hPcard, hmem, hexh⟩ := sylow_enum_facts hok (by rw [hsize, hpts]) hvalid' hnd
  rw [hpts] at hPcard
  have hrep := all_repArrs hreps
  have hrepf := fun ng hng => rep_facts hp hmem hvalid' (hrep ng hng)
  have hcovf : ∀ Q : Subgroup (Equiv.Perm (Fin n)), Q ≤ s.subgroup n → Nat.card Q = p →
      ∃ x ∈ s.reps n, x ∈ Q := by
    intro Q hQP hQ
    have hcov' : ∀ i < (s.elems n N).size, coverCheck n p s.repArrs (s.elems n N)[i]! = true := by
      intro i hi
      rw [Array.all_eq_true] at hcov
      rw [getElem!_pos (s.elems n N) i hi]
      exact hcov i hi
    have hrv : ∀ j < s.repArrs.size, permArrOK n s.repArrs[j]! = true := by
      intro j hj
      rw [repArrs_size] at hj
      rw [repArrs_get s hj]
      have := hrep _ (List.getElem_mem hj)
      simp only [repCheck, Bool.and_eq_true] at this
      exact this.1.1.1.1
    obtain ⟨j, hj, hjQ⟩ := cover_facts hexh hvalid' hcov' hrv hp.one_lt Q hQP hQ
    rw [repArrs_size] at hj
    rw [repArrs_get s hj] at hjQ
    exact ⟨_, List.mem_map.2 ⟨_, List.getElem_mem hj, rfl⟩, hjQ⟩
  have hrepsfacts : ∀ x ∈ s.reps n, x ∈ s.subgroup n ∧ orderOf x = p ∧
      ∀ y ∈ Subgroup.zpowers x, y ≠ 1 → imageList x ≤ imageList y := by
    intro x hx
    obtain ⟨ng, hng, rfl⟩ := List.mem_map.1 hx
    obtain ⟨-, -, h1, h2, h3⟩ := hrepf ng hng
    exact ⟨h1, h2, h3⟩
  have hngf : ∀ ng ∈ s.normalGeneration,
      (∀ w ∈ ng.conjugators, ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ (r.rootGens n).length) ∧
        Subgroup.closure {g | g ∈ ng.conjugates (r.rootGens n)} = G := by
    intro ng hng
    obtain ⟨-, hr, hP, -, -⟩ := hrepf ng hng
    rw [List.all_eq_true] at hngall
    exact normalGen_facts hroot hN (hngall ng hng) hr (hPG hP)
  have hc1 : Nat.card (s.subgroup n) = p ^ N.factorization p := by rw [hPcard, hfact]
  have hc2 : p ^ N.factorization p ∣ N := by
    rw [hfact]
    exact Nat.dvd_of_mod_eq_zero hdiv
  have hc3 : ¬p ^ (N.factorization p + 1) ∣ N := by
    rw [hfact]
    exact fun h => hndiv (Nat.mod_eq_zero_of_dvd h)
  refine ⟨hp, fun a ha => ?_, hPG, hc1, hc2, hc3, ?_, hrepsfacts, ?_, hngf, ?_⟩
  · obtain ⟨hs1, hr1⟩ := hgenrep a ha
    rw [← toList_eq_imageList hs1 hr1]
  ·
    have hinj : ∀ ng ∈ s.normalGeneration, ∀ ng' ∈ s.normalGeneration,
        arrPerm n ng.representative = arrPerm n ng'.representative →
          ng.representative = ng'.representative := by
      intro ng hng ng' hng' e
      obtain ⟨hs1, hr1, -⟩ := hrepf ng hng
      obtain ⟨hs2, hr2, -⟩ := hrepf ng' hng'
      rw [e] at hr1
      have := eq_of_rep_of_size hs1 hs2 hr1 hr2
      simpa using congrArg Array.toList this
    have hnd' : (s.normalGeneration.map fun ng => ng.representative).Nodup := by
      have : (s.repArrs.toList.map Array.toList) =
          s.normalGeneration.map fun ng => ng.representative := by
        simp [SylowRecord.repArrs]
      rwa [this] at hrnd
    rw [SylowRecord.reps]
    have e : (s.normalGeneration.map fun ng => arrPerm n ng.representative) =
        (s.normalGeneration.map fun ng => ng.representative).map (arrPerm n) := by
      simp
    rw [e]
    refine hnd'.map_on ?_
    intro a ha b hb hab
    obtain ⟨ng, hng, rfl⟩ := List.mem_map.1 ha
    obtain ⟨ng', hng', rfl⟩ := List.mem_map.1 hb
    exact hinj ng hng ng' hng' hab
  ·
    intro Q hQP hQ
    obtain ⟨x, hx, hxQ⟩ := hcovf Q hQP hQ
    refine ⟨x, ⟨hx, hxQ⟩, fun x' ⟨hx', hx'Q⟩ => ?_⟩
    obtain ⟨-, ho, hl⟩ := hrepsfacts x hx
    obtain ⟨-, ho', hl'⟩ := hrepsfacts x' hx'
    exact (eq_of_lex_least hp ho ho' hQ hxQ hx'Q hl hl').symm
  ·
    have : Fact p.Prime := ⟨hp⟩
    have hcardP' : Nat.card ((s.subgroup n).subgroupOf G) =
        p ^ (Nat.card G).factorization p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPG).toEquiv, hPcard, hGcard, hN, hfact]
    refine ⟨Sylow.ofCard _ hcardP', by
      rw [Sylow.coe_ofCard, Subgroup.map_subgroupOf_eq_of_le hPG], fun Q hQ hQcard => ?_⟩
    rw [Sylow.coe_ofCard] at hQ
    have hQ1 : Q.map G.subtype ≤ s.subgroup n := by
      have := Subgroup.map_mono (f := G.subtype) hQ
      rwa [Subgroup.map_subgroupOf_eq_of_le hPG] at this
    have hQ1card : Nat.card (Q.map G.subtype) = p := by
      rw [Subgroup.card_map_of_injective G.subtype_injective, hQcard]
    obtain ⟨x, hx, hxQ⟩ := hcovf _ hQ1 hQ1card
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hxQ
    obtain ⟨ng, hng, hngx⟩ := List.mem_map.1 hx
    obtain ⟨-, hcl⟩ := hngf ng hng
    have hqx : (q : Equiv.Perm (Fin n)) = arrPerm n ng.representative := hngx.symm
    have hcl' : Subgroup.closure {y | ∃ g ∈ ng.conjugators.map (wordValue (r.rootGens n)),
        g⁻¹ * (q : Equiv.Perm (Fin n)) * g = y} = G := by
      refine Eq.trans ?_ hcl
      congr 1
      ext y
      simp only [Set.mem_ofPred_eq, List.mem_map, NormalGenRecord.conjugates,
        exists_exists_and_eq_and]
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w, hw, by rw [hqx]⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w, hw, by rw [hqx]⟩
    have hgsG : ∀ g ∈ ng.conjugators.map (wordValue (r.rootGens n)), g ∈ G := by
      intro g hg
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
      exact wordValue_mem _ G (rootGens_mem r) w
    have htop := normalClosure_eq_top_of_conjugates q.2 _ hgsG hcl'
    refine top_le_iff.1 ?_
    rw [← htop]
    refine Subgroup.normalClosure_mono ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hq

theorem rootGroup_eq_closure {r : GroupRecord} {a b : Equiv.Perm (Fin n)}
    (h : r.chain.generators = [imageList a, imageList b]) :
    rootGroup r n = Subgroup.closure {a, b} := by
  unfold rootGroup
  congr 1
  ext g
  rw [h]
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
    arrPerm_imageList, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩

theorem rootGens_eq {r : GroupRecord} {a b : Equiv.Perm (Fin n)}
    (h : r.chain.generators = [imageList a, imageList b]) : r.rootGens n = [a, b] := by
  rw [GroupRecord.rootGens, h]
  simp [arrPerm_imageList]

theorem prime_dvd_iff_mem {N : ℕ} {ps l : List ℕ} (hN : N ≠ 0) (hl : N.primeFactorsList = l)
    (hps : ∀ p, p ∈ l ↔ p ∈ ps) : ∀ p : ℕ, p.Prime → (p ∣ N ↔ p ∈ ps) := by
  intro p hp
  rw [← hps, ← hl, Nat.mem_primeFactorsList hN]
  exact ⟨fun h => ⟨hp, h⟩, fun h => h.2⟩

end CFSG.Monster.B.Mathieu
