module

public import CFSG.Monster.B.Mathieu.CertData

public section

namespace CFSG.Monster.B.Mathieu

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def arraysOK (n : ℕ) (O S : Array (Array ℕ)) (base : Array ℕ) (W : Array (List ℤ)) :
    Bool :=
  decide (1 ≤ n) && decide base.toList.Nodup &&
    allLt O.size (fun k => isInvA n O[k]! (invCand n O[k]!)) && rawChainOK n O S base W 1

@[expose] noncomputable def rawOfArrays (n : ℕ) (O S : Array (Array ℕ)) (base : Array ℕ)
    (W : Array (List ℤ)) (hn : 1 ≤ n) (hle : O.size ≤ S.size)
    (hlt : ∀ i < base.size, base[i]! < n) (hnd : base.toList.Nodup) : RawSchreierDatum n where
  degree_pos := hn
  originalCount := O.size
  strongCount := S.size
  baseCount := base.size
  originalCount_le := hle
  original := Vector.ofFn fun k : Fin O.size => permOfArr n O[(k : ℕ)]!
  strong := Vector.ofFn fun j : Fin S.size => permOfArr n S[(j : ℕ)]!
  base := Vector.ofFn fun i : Fin base.size => ⟨base[(i : ℕ)]!, hlt i i.2⟩
  base_distinct := by
    rw [Vector.toList_ofFn]
    refine List.Nodup.of_map Fin.val ?_
    have e : (List.ofFn fun i : Fin base.size => (⟨base[(i : ℕ)]!, hlt i i.2⟩ : Fin n)).map
        Fin.val = base.toList := by
      apply List.ext_getElem (by simp)
      intro k h1 h2
      simp only [List.getElem_map, List.getElem_ofFn, Array.getElem_toList]
      exact getElem!_pos base k (by simpa using h2)
    rw [e]
    exact hnd
  derivation j _ := toLetters j.val W[(j : ℕ)]!

theorem rawOfArrays_original_get {n : ℕ} {O S : Array (Array ℕ)} {base : Array ℕ}
    {W : Array (List ℤ)} {hn : 1 ≤ n} {hle : O.size ≤ S.size}
    {hlt : ∀ i < base.size, base[i]! < n} {hnd : base.toList.Nodup}
    (k : Fin (rawOfArrays n O S base W hn hle hlt hnd).originalCount) :
    (rawOfArrays n O S base W hn hle hlt hnd).original.get k = permOfArr n O[(k : ℕ)]! := by
  change (Vector.ofFn fun k : Fin O.size => permOfArr n O[(k : ℕ)]!).get k = _
  simp only [Vector.get, Vector.ofFn, Array.getElem_ofFn]
  rfl

theorem rawOfArrays_strong_get {n : ℕ} {O S : Array (Array ℕ)} {base : Array ℕ}
    {W : Array (List ℤ)} {hn : 1 ≤ n} {hle : O.size ≤ S.size}
    {hlt : ∀ i < base.size, base[i]! < n} {hnd : base.toList.Nodup}
    (j : Fin (rawOfArrays n O S base W hn hle hlt hnd).strongCount) :
    (rawOfArrays n O S base W hn hle hlt hnd).strong.get j = permOfArr n S[(j : ℕ)]! := by
  change (Vector.ofFn fun j : Fin S.size => permOfArr n S[(j : ℕ)]!).get j = _
  simp only [Vector.get, Vector.ofFn, Array.getElem_ofFn]
  rfl

theorem rawOfArrays_base_get {n : ℕ} {O S : Array (Array ℕ)} {base : Array ℕ}
    {W : Array (List ℤ)} {hn : 1 ≤ n} {hle : O.size ≤ S.size}
    {hlt : ∀ i < base.size, base[i]! < n} {hnd : base.toList.Nodup}
    (i : Fin (rawOfArrays n O S base W hn hle hlt hnd).baseCount) :
    (((rawOfArrays n O S base W hn hle hlt hnd).base.get i : Fin n) : ℕ) = base[(i : ℕ)]! := by
  change (((Vector.ofFn fun i : Fin base.size =>
    (⟨base[(i : ℕ)]!, hlt i i.2⟩ : Fin n)).get i : Fin n) : ℕ) = _
  simp only [Vector.get, Vector.ofFn, Array.getElem_ofFn]
  rfl

theorem original_toList_rawOfArrays {n : ℕ} {O S : Array (Array ℕ)} {base : Array ℕ}
    {W : Array (List ℤ)} {hn : 1 ≤ n} {hle : O.size ≤ S.size}
    {hlt : ∀ i < base.size, base[i]! < n} {hnd : base.toList.Nodup} (g : Equiv.Perm (Fin n)) :
    g ∈ (rawOfArrays n O S base W hn hle hlt hnd).original.toList ↔
      ∃ k < O.size, permOfArr n O[k]! = g := by
  change g ∈ (Vector.ofFn fun k : Fin O.size => permOfArr n O[(k : ℕ)]!).toList ↔ _
  rw [Vector.toList_ofFn, List.mem_ofFn]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, k.2, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩

theorem exists_valid_of_arraysOK {n : ℕ} {O S : Array (Array ℕ)} {base : Array ℕ}
    {W : Array (List ℤ)} (h : arraysOK n O S base W = true) :
    ∃ Q : RawSchreierDatum n, ChainArrays Q O S base W ∧ ValidSchreier Q ∧
      Q.originalSubgroup = Subgroup.closure {g | ∃ k < O.size, permOfArr n O[k]! = g} ∧
      Nat.card Q.originalSubgroup = (rawOrbitSizes n S base).prod ∧
      (∀ j < S.size, permOfArr n S[j]! ∈ Q.originalSubgroup) ∧
      ∀ (t : Array ℕ) (g : Equiv.Perm (Fin n)), Rep n t g →
        (siftA n (rawLevels n S base) base 0 t = true ↔ g ∈ Q.originalSubgroup) := by
  simp only [arraysOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hn, hnd⟩, hO⟩, hchain⟩ := h
  have hF := chainCheckFacts hchain
  let Q := rawOfArrays n O S base W hn hF.orig_le hF.base_lt hnd
  have hA : ChainArrays Q O S base W :=
    { orig_size := rfl
      strong_size := rfl
      base_size := rfl
      orig := fun k => by
        rw [rawOfArrays_original_get]
        exact (rep_permOfArr (allLt_spec hO k.2)).1
      strong := fun j => by
        rw [rawOfArrays_strong_get]
        exact (rep_permOfArr (hF.strong_inv j j.2)).1
      base_val := fun i => rawOfArrays_base_get i
      deriv := fun _ _ => rfl }
  obtain ⟨hQ, hsizes⟩ := validSchreier_of_chainOK hA Nat.one_pos hchain
  refine ⟨Q, hA, hQ, ?_, ?_, ?_, ?_⟩
  · change Subgroup.closure {g | g ∈ Q.original.toList} = _
    congr 1
    ext g
    exact original_toList_rawOfArrays g
  · rw [← RawSchreierDatum.orderCertificate_eq_card Q hQ, RawSchreierDatum.orderCertificate,
      rawOrbitSizes]
    congr 1
    apply List.ext_getElem (by simp [ChainArrays.chainLevels_size]; rfl)
    intro k h1 h2
    simp only [List.getElem_map, List.getElem_finRange, Array.getElem_toList]
    rw [hsizes]
    change (rawLevels n S base)[k]!.pts.size = _
    rw [getElem!_pos (rawLevels n S base) k (by simpa using h2)]
  · intro j hj
    have := Q.strong_get_mem_originalSubgroup hQ ⟨j, hj⟩
    rwa [rawOfArrays_strong_get] at this
  · intro t g hg
    have hsift := hA.siftA_eq hF base.size 0 (by simp; rfl) t g hg
    rw [hsift, ← Q.sift_eq_true_iff_mem_original hQ g]
    rfl

@[expose] def ChainRecord.check (c : ChainRecord) (n : ℕ) : Bool :=
  c.degree == n && c.generators.length + c.derivations.length == c.strongGenerators.length &&
    arraysOK n c.origArrs c.strongArrs c.baseArr c.wordArrs

@[expose] def ChainRecord.orbitSizes (c : ChainRecord) (n : ℕ) : List ℕ :=
  rawOrbitSizes n c.strongArrs c.baseArr

theorem ChainRecord.origArrs_size (c : ChainRecord) : c.origArrs.size = c.generators.length := by
  simp [ChainRecord.origArrs]

theorem ChainRecord.origArrs_get (c : ChainRecord) {k : ℕ} (hk : k < c.generators.length) :
    c.origArrs[k]! = (c.generators[k]).toArray := by
  rw [getElem!_pos c.origArrs k (by rw [c.origArrs_size]; exact hk)]
  simp [ChainRecord.origArrs]

theorem ChainRecord.exists_records_of_check {c : ChainRecord} {n : ℕ} (h : c.check n = true) :
    ∃ Q : RawSchreierDatum n, c.Records Q ∧ ValidSchreier Q ∧
      Q.originalSubgroup = Subgroup.closure {g | ∃ a ∈ c.generators, arrPerm n a = g} ∧
      Nat.card Q.originalSubgroup = (c.orbitSizes n).prod := by
  simp only [ChainRecord.check, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hdeg, hlen⟩, hok⟩ := h
  obtain ⟨Q, hA, hQ, hsub, hcard, -, -⟩ := exists_valid_of_arraysOK hok
  refine ⟨Q, ⟨hdeg, hlen, hA⟩, hQ, ?_, hcard⟩
  rw [hsub]
  congr 1
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [c.origArrs_size] at hk
    exact ⟨c.generators[k], List.getElem_mem hk, by rw [arrPerm, c.origArrs_get hk]⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
    exact ⟨k, by rw [c.origArrs_size]; exact hk, by rw [arrPerm, c.origArrs_get hk]⟩

end CFSG.Monster.B.Mathieu
