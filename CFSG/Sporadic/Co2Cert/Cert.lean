module

public import CFSG.Sporadic.Co2Cert.Check
public import CFSG.Monster.B.Mathieu.ChainCheck
public import Mathlib.Data.List.GetD

public section

namespace CFSG.Sporadic.Co2Cert

open CFSG.Certificates CFSG.Monster.B.Mathieu CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Binary.Native

structure ChainShape (c : ChainRecord) (n k r : ℕ) (base : List ℕ) : Prop where
  degree : c.degree = n
  gens_length : c.generators.length = k
  strong_length : c.strongGenerators.length = r
  derivs_length : c.derivations.length = r - k
  gens_perm : ∀ a ∈ c.generators, isPermList n a = true
  strong_perm : ∀ a ∈ c.strongGenerators, isPermList n a = true
  base_eq : c.base = base
  letters : ∀ j < r - k, lettersOK (j + k) (c.derivations.getD j []) = true

theorem chainShape_of {c : ChainRecord} {n k r : ℕ} {base : List ℕ}
    (h : chainShapeOK c n k r base = true) : ChainShape c n k r base := by
  simp only [chainShapeOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

structure Co2Shape : Prop where
  schema : co2Rec.schemaVersion = 1
  group : co2Rec.group = "Co2"
  prime : co2Rec.prime = 2
  dimension : co2Rec.dimension = 22
  vectors_length : co2Rec.vectors.length = 2300
  vectors : ∀ v ∈ co2Rec.vectors, v.length = 22 ∧ ∀ x ∈ v, x < 2
  basis : co2Rec.basisIndices = co2BasisList
  chain : ChainShape co2Rec.chain 2300 2 11 [0, 1, 2, 3, 5, 4]
  coprimeChain : ChainShape co2Rec.coprimeChain 2300 2 17 [0, 1, 3, 2, 5, 4]
  conjugator : co2Rec.coprimeConjugator = [-1, 2, 2, 1, 2, -1]
  point : co2Rec.point = 0
  stabIdx : co2Rec.stabilizerGeneratorIndices = [0, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  orbit_lengths : co2Rec.stabilizerOrbits.map List.length = [1, 1408, 891]
  orbits : ∀ o ∈ co2Rec.stabilizerOrbits, increasingBelow 2300 o = true
  merge_reps : co2Rec.merges.map (·.representative) = [1, 3]
  merge_lengths : co2Rec.merges.map (·.instructions.length) = [2298, 2298]
  merge_triples : ∀ m ∈ co2Rec.merges, ∀ t ∈ m.instructions, tripleOK t = true

theorem co2Shape : Co2Shape := by
  have h := co2ShapeOK_eq_true
  simp only [co2ShapeOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩, h16⟩, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, chainShape_of h8, chainShape_of h9, h10, h11, h12, h13,
    h14, h15, h16, h17⟩

theorem isPermList_spec {n : ℕ} {l : List ℕ} (h : isPermList n l = true) :
    l.length = n ∧ isInvA n l.toArray (invCand n l.toArray) = true := by
  simp only [isPermList, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem rep_of_isPermList {n : ℕ} {l : List ℕ} (h : isPermList n l = true) :
    Rep n l.toArray (permOfArr n l.toArray) :=
  (rep_permOfArr (isPermList_spec h).2).1

theorem strongArrs_size_eq (c : ChainRecord) : c.strongArrs.size = c.strongGenerators.length := by
  simp [ChainRecord.strongArrs]

theorem strongArrs_get_eq (c : ChainRecord) {j : ℕ} (hj : j < c.strongGenerators.length) :
    c.strongArrs[j]! = (c.strongGenerators[j]).toArray := by
  rw [getElem!_pos c.strongArrs j (by rw [strongArrs_size_eq]; exact hj)]
  simp [ChainRecord.strongArrs]

theorem baseArr_eq (c : ChainRecord) : c.baseArr = c.base.toArray := rfl

theorem ChainShape.orig_inv {c : ChainRecord} {n k r : ℕ} {base : List ℕ}
    (hc : ChainShape c n k r base) {i : ℕ} (hi : i < k) :
    isInvA n c.origArrs[i]! (invCand n c.origArrs[i]!) = true := by
  have hi' : i < c.generators.length := by rw [hc.gens_length]; exact hi
  rw [c.origArrs_get hi']
  exact (isPermList_spec (hc.gens_perm _ (List.getElem_mem hi'))).2

theorem ChainShape.strong_inv {c : ChainRecord} {n k r : ℕ} {base : List ℕ}
    (hc : ChainShape c n k r base) {j : ℕ} (hj : j < r) :
    isInvA n c.strongArrs[j]! (invCand n c.strongArrs[j]!) = true := by
  have hj' : j < c.strongGenerators.length := by rw [hc.strong_length]; exact hj
  rw [strongArrs_get_eq c hj']
  exact (isPermList_spec (hc.strong_perm _ (List.getElem_mem hj'))).2

theorem ChainShape.origArrs_size {c : ChainRecord} {n k r : ℕ} {base : List ℕ}
    (hc : ChainShape c n k r base) : c.origArrs.size = k := by
  rw [c.origArrs_size, hc.gens_length]

theorem ChainShape.strongArrs_size {c : ChainRecord} {n k r : ℕ} {base : List ℕ}
    (hc : ChainShape c n k r base) : c.strongArrs.size = r := by
  rw [strongArrs_size_eq, hc.strong_length]

@[expose] def co2Vec (i : ℕ) : Fin 22 → ZMod 2 :=
  fun j => (((co2Rec.vectors.getD i []).getD j 0 : ℕ) : ZMod 2)

@[expose] def co2X : Set (Fin 22 → ZMod 2) := {v | ∃ i < 2300, co2Vec i = v}

theorem co2OrigArrs_size :
    co2OrigArrs.size = 2 := co2Shape.chain.origArrs_size

theorem co2StrongArrs_size :
    co2StrongArrs.size = 11 := co2Shape.chain.strongArrs_size

theorem co2BaseArr_eq : co2BaseArr = #[0, 1, 2, 3, 5, 4] := by
  rw [co2BaseArr, baseArr_eq, co2Shape.chain.base_eq]

theorem co2BaseArr_lt :
    ∀ i < co2BaseArr.size, co2BaseArr[i]! < 2300 := by
  rw [co2BaseArr_eq]
  decide

theorem co2BaseArr_nodup : co2BaseArr.toList.Nodup := by
  rw [co2BaseArr_eq]
  decide

theorem co2cOrigArrs_size :
    co2cOrigArrs.size = 2 := co2Shape.coprimeChain.origArrs_size

theorem co2cStrongArrs_size :
    co2cStrongArrs.size = 17 := co2Shape.coprimeChain.strongArrs_size

theorem co2cBaseArr_eq : co2cBaseArr = #[0, 1, 3, 2, 5, 4] := by
  rw [co2cBaseArr, baseArr_eq, co2Shape.coprimeChain.base_eq]

theorem co2cBaseArr_lt :
    ∀ i < co2cBaseArr.size, co2cBaseArr[i]! < 2300 := by
  rw [co2cBaseArr_eq]
  decide

theorem co2cBaseArr_nodup : co2cBaseArr.toList.Nodup := by
  rw [co2cBaseArr_eq]
  decide

@[expose] noncomputable def co2Q : RawSchreierDatum 2300 :=
  rawOfArrays 2300 co2OrigArrs co2StrongArrs co2BaseArr co2WordArrs (by norm_num)
    (by rw [co2OrigArrs_size, co2StrongArrs_size]; norm_num) co2BaseArr_lt co2BaseArr_nodup

@[expose] noncomputable def co2Qc : RawSchreierDatum 2300 :=
  rawOfArrays 2300 co2cOrigArrs co2cStrongArrs co2cBaseArr co2cWordArrs (by norm_num)
    (by rw [co2cOrigArrs_size, co2cStrongArrs_size]; norm_num) co2cBaseArr_lt co2cBaseArr_nodup

theorem records_rawOfArrays {c : ChainRecord} {k r : ℕ} {base : List ℕ}
    (hc : ChainShape c 2300 k r base) (hle : c.origArrs.size ≤ c.strongArrs.size)
    (hlt : ∀ i < c.baseArr.size, c.baseArr[i]! < 2300) (hnd : c.baseArr.toList.Nodup)
    (hkr : k + (r - k) = r) :
    c.Records (rawOfArrays 2300 c.origArrs c.strongArrs c.baseArr c.wordArrs (by norm_num) hle
      hlt hnd) := by
  have hlen : c.generators.length + c.derivations.length = c.strongGenerators.length := by
    rw [hc.gens_length, hc.derivs_length, hc.strong_length, hkr]
  refine ⟨hc.degree, hlen, ?_⟩
  exact
    { orig_size := rfl
      strong_size := rfl
      base_size := rfl
      orig := fun i => by
        rw [rawOfArrays_original_get]
        have hi : (i : ℕ) < k := by
          have := i.2
          change (i : ℕ) < c.origArrs.size at this
          rwa [hc.origArrs_size] at this
        exact (rep_permOfArr (hc.orig_inv hi)).1
      strong := fun j => by
        rw [rawOfArrays_strong_get]
        have hj : (j : ℕ) < r := by
          have := j.2
          change (j : ℕ) < c.strongArrs.size at this
          rwa [hc.strongArrs_size] at this
        exact (rep_permOfArr (hc.strong_inv hj)).1
      base_val := fun i => rawOfArrays_base_get i
      deriv := fun _ _ => rfl }

theorem co2Q_records : co2Rec.chain.Records co2Q :=
  records_rawOfArrays co2Shape.chain _ _ _ (by norm_num)

theorem co2Qc_records : co2Rec.coprimeChain.Records co2Qc :=
  records_rawOfArrays co2Shape.coprimeChain _ _ _ (by norm_num)

@[expose] noncomputable def co2Gen (k : ℕ) : Equiv.Perm (Fin 2300) :=
  permOfArr 2300 co2OrigArrs[k]!

@[expose] noncomputable def co2Strong (j : ℕ) : Equiv.Perm (Fin 2300) :=
  permOfArr 2300 co2StrongArrs[j]!

@[expose] noncomputable def co2cGen (k : ℕ) : Equiv.Perm (Fin 2300) :=
  permOfArr 2300 co2cOrigArrs[k]!

@[expose] noncomputable def co2cStrong (j : ℕ) : Equiv.Perm (Fin 2300) :=
  permOfArr 2300 co2cStrongArrs[j]!

@[expose] noncomputable def co2P : Subgroup (Equiv.Perm (Fin 2300)) :=
  Subgroup.closure {co2Gen 0, co2Gen 1}

@[expose] noncomputable def co2Pc : Subgroup (Equiv.Perm (Fin 2300)) :=
  Subgroup.closure {co2cGen 0, co2cGen 1}

@[expose] noncomputable def co2W : Equiv.Perm (Fin 2300) :=
  wordValue [co2Gen 0, co2Gen 1] co2Rec.coprimeConjugator

@[expose] def co2Pt (x : ℕ) : Fin 2300 := ⟨x % 2300, Nat.mod_lt _ (by norm_num)⟩

@[expose] def co2Point : Fin 2300 := co2Pt co2Rec.point

@[expose] def co2StabIdx : List ℕ := co2Rec.stabilizerGeneratorIndices

@[expose] noncomputable def co2H0 : Subgroup (Equiv.Perm (Fin 2300)) :=
  Subgroup.closure {g | ∃ j ∈ co2StabIdx, co2Strong j = g}

@[expose] def co2StabOrbit (t : ℕ) : Set (Fin 2300) :=
  {x | (x : ℕ) ∈ co2Rec.stabilizerOrbits.getD t []}

@[expose] def co2Triple (t : List ℕ) : Fin 2 × Fin 2300 × Fin 2300 :=
  (⟨t.getD 0 0 % 2, Nat.mod_lt _ (by norm_num)⟩, co2Pt (t.getD 1 0), co2Pt (t.getD 2 0))

@[expose] def co2Merges : List (Fin 2300 × List (Fin 2 × Fin 2300 × Fin 2300)) :=
  co2Rec.merges.map fun m => (co2Pt m.representative, m.instructions.map co2Triple)

@[expose] noncomputable def co2MergeGens : Fin 2 → Equiv.Perm (Fin 2300) := fun i => co2Gen i

theorem co2Q_original_get
    (k : Fin co2Q.originalCount) : co2Q.original.get k = co2Gen k :=
  rawOfArrays_original_get k

theorem co2Q_strong_get
    (j : Fin co2Q.strongCount) : co2Q.strong.get j = co2Strong j :=
  rawOfArrays_strong_get j

theorem co2Qc_original_get
    (k : Fin co2Qc.originalCount) : co2Qc.original.get k = co2cGen k :=
  rawOfArrays_original_get k

theorem co2Qc_strong_get
    (j : Fin co2Qc.strongCount) : co2Qc.strong.get j = co2cStrong j :=
  rawOfArrays_strong_get j

theorem co2Q_originalCount :
    co2Q.originalCount = 2 := co2OrigArrs_size

theorem co2Q_strongCount :
    co2Q.strongCount = 11 := co2StrongArrs_size

theorem co2Qc_originalCount :
    co2Qc.originalCount = 2 := co2cOrigArrs_size

theorem co2Qc_strongCount :
    co2Qc.strongCount = 17 := co2cStrongArrs_size

theorem rep_co2Gen
    {k : ℕ} (hk : k < 2) : Rep 2300 co2OrigArrs[k]! (co2Gen k) :=
  (rep_permOfArr (co2Shape.chain.orig_inv hk)).1

theorem rep_co2Strong
    {j : ℕ} (hj : j < 11) : Rep 2300 co2StrongArrs[j]! (co2Strong j) :=
  (rep_permOfArr (co2Shape.chain.strong_inv hj)).1

theorem rep_co2cGen
    {k : ℕ} (hk : k < 2) : Rep 2300 co2cOrigArrs[k]! (co2cGen k) :=
  (rep_permOfArr (co2Shape.coprimeChain.orig_inv hk)).1

theorem rep_co2cStrong
    {j : ℕ} (hj : j < 17) : Rep 2300 co2cStrongArrs[j]! (co2cStrong j) :=
  (rep_permOfArr (co2Shape.coprimeChain.strong_inv hj)).1

theorem originalSubgroup_rawOfArrays_two {O S : Array (Array ℕ)} {base : Array ℕ}
    {W : Array (List ℤ)} {hn : 1 ≤ 2300} {hle : O.size ≤ S.size}
    {hlt : ∀ i < base.size, base[i]! < 2300} {hnd : base.toList.Nodup} (hO : O.size = 2) :
    (rawOfArrays 2300 O S base W hn hle hlt hnd).originalSubgroup =
      Subgroup.closure {permOfArr 2300 O[0]!, permOfArr 2300 O[1]!} := by
  rw [RawSchreierDatum.originalSubgroup]
  congr 1
  ext g
  rw [Set.mem_ofPred_eq, original_toList_rawOfArrays, hO]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · left; rfl
    · right; rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩

theorem co2Q_originalSubgroup : co2Q.originalSubgroup = co2P :=
  originalSubgroup_rawOfArrays_two co2OrigArrs_size

theorem co2Qc_originalSubgroup : co2Qc.originalSubgroup = co2Pc :=
  originalSubgroup_rawOfArrays_two co2cOrigArrs_size

theorem wordValue_conj {G : Type*} [Group G] (a b : G) :
    wordValue [a, b] [-1, 2, 2, 1, 2, -1] = a⁻¹ * b * b * a * b * a⁻¹ := by
  simp [wordValue, letterValue, mul_assoc]

theorem co2W_eq :
    co2W = (co2Gen 0)⁻¹ * co2Gen 1 * co2Gen 1 * co2Gen 0 * co2Gen 1 * (co2Gen 0)⁻¹ := by
  rw [co2W, co2Shape.conjugator]
  exact wordValue_conj _ _

theorem co2Point_eq : co2Point = 0 := by
  rw [co2Point, co2Pt, co2Shape.point]
  rfl

theorem co2StabIdx_eq :
    co2StabIdx = [0, 2, 3, 4, 5, 6, 7, 8, 9, 10] := co2Shape.stabIdx

theorem co2StabOrbits_length :
    co2Rec.stabilizerOrbits.length = 3 := by
  have h := congrArg List.length co2Shape.orbit_lengths
  simpa using h

theorem co2StabOrbit_list {t : ℕ} (ht : t < 3) :
    (∀ x ∈ co2Rec.stabilizerOrbits.getD t [], x < 2300) ∧
      ∀ k, k + 1 < (co2Rec.stabilizerOrbits.getD t []).length →
        (co2Rec.stabilizerOrbits.getD t []).getD k 0 <
          (co2Rec.stabilizerOrbits.getD t []).getD (k + 1) 0 := by
  have ht' : t < co2Rec.stabilizerOrbits.length := by rw [co2StabOrbits_length]; exact ht
  have h := co2Shape.orbits _ (List.getElem_mem ht')
  rw [List.getD_eq_getElem _ _ ht']
  simp only [increasingBelow, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    List.mem_range] at h
  exact ⟨h.1, fun k hk => h.2 k (by omega)⟩

theorem co2StabOrbit_lengths :
    ((List.range 3).map fun t => (co2Rec.stabilizerOrbits.getD t []).length) = [1, 1408, 891] := by
  rw [← co2Shape.orbit_lengths]
  apply List.ext_getElem (by simp [co2StabOrbits_length])
  intro k h1 h2
  have hk : k < 3 := by simpa using h1
  have hk' : k < co2Rec.stabilizerOrbits.length := by rw [co2StabOrbits_length]; exact hk
  simp [List.getElem?_eq_getElem hk']

theorem co2Merges_reps :
    co2Merges.map (fun m => (m.1 : ℕ)) = [1, 3] := by
  have h := co2Shape.merge_reps
  rw [co2Merges, List.map_map]
  have hlen : co2Rec.merges.length = 2 := by simpa using congrArg List.length h
  apply List.ext_getElem (by simp [hlen])
  intro k h1 h2
  have := congrArg (fun l => l[k]?) h
  simp only [List.getElem?_map] at this
  simp only [List.getElem_map, Function.comp_apply, co2Pt]
  have hk : k < co2Rec.merges.length := by simpa using h1
  rw [List.getElem?_eq_getElem hk] at this
  have hk2 : k < 2 := by omega
  interval_cases k <;> simp_all

theorem co2Merges_lengths :
    co2Merges.map (fun m => m.2.length) = [2298, 2298] := by
  rw [co2Merges, List.map_map, ← co2Shape.merge_lengths]
  simp [Function.comp_def]

theorem co2Merges_triples :
    ∀ m ∈ co2Rec.merges, ∀ t ∈ m.instructions, t.length = 3 ∧ t.getD 0 0 < 2 ∧
      t.getD 1 0 < 2300 ∧ t.getD 2 0 < 2300 := by
  intro m hm t ht
  have h := co2Shape.merge_triples m hm t ht
  simp only [tripleOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem co2_image_lists :
    ∀ a ∈ co2Rec.chain.generators ++ co2Rec.chain.strongGenerators ++
      co2Rec.coprimeChain.generators ++ co2Rec.coprimeChain.strongGenerators,
      a.length = 2300 ∧ ∃ σ : Equiv.Perm (Fin 2300), ∀ x : Fin 2300, a.getD x 0 = σ x := by
  intro a ha
  have hp : isPermList 2300 a = true := by
    simp only [List.mem_append] at ha
    rcases ha with ((h | h) | h) | h
    · exact co2Shape.chain.gens_perm a h
    · exact co2Shape.chain.strong_perm a h
    · exact co2Shape.coprimeChain.gens_perm a h
    · exact co2Shape.coprimeChain.strong_perm a h
  refine ⟨(isPermList_spec hp).1, permOfArr 2300 a.toArray, fun x => ?_⟩
  have h := rep_of_isPermList hp x
  rw [← h]
  have hx : (x : ℕ) < a.length := by rw [(isPermList_spec hp).1]; exact x.2
  rw [List.getD_eq_getElem _ _ hx, getElem!_pos a.toArray (x : ℕ) (by simpa using hx)]
  simp

end CFSG.Sporadic.Co2Cert
