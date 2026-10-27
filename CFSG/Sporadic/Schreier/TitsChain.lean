module

public import CFSG.Sporadic.Schreier.TitsBasic
public import CFSG.Certificates.NativeSchreierCard

public section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

variable {n : ℕ} [NeZero n] {hn : 1 ≤ n} {S : Array (Array ℕ)} {k : ℕ} {hk : k ≤ S.size}
  {b : List ℕ} {hb : (finList n b).Nodup} {W : Array (List ℤ)} {chunks : ℕ}

omit [NeZero n] in
theorem rawInvs_get (hP : allPermsOK n S = true) {j : ℕ} (hj : j < S.size) :
    isInvA n S[j]! (rawInvs n S)[j]! = true := by
  rw [rawInvs, getElem!_map_of_lt hj]
  exact isInvA_of_allPermsOK hP hj

theorem baseArr_eq (b : List ℕ) : baseArr n b = ((finList n b).map Fin.val).toArray := rfl

theorem chainArrays_ofArrays' (hP : allPermsOK n S = true) :
    ChainArrays (RawSchreierDatum.ofArrays n hn S k hk (finList n b) hb W) (S.extract 0 k) S
      (baseArr n b) W :=
  chainArrays_ofArrays fun _ hj => rawInvs_get hP hj

theorem valid_ofArrays (hP : allPermsOK n S = true) (hc : 0 < chunks)
    (h : rawChainOK n (S.extract 0 k) S (baseArr n b) W chunks = true) :
    ValidSchreier (RawSchreierDatum.ofArrays n hn S k hk (finList n b) hb W) ∧
      ∀ i, (RawSchreierDatum.ofArrays n hn S k hk (finList n b) hb W).orbitSize i =
        ((rawLevels n S (baseArr n b))[(i : ℕ)]!).pts.size :=
  validSchreier_of_chainOK (chainArrays_ofArrays' hP) hc h

theorem originalSubgroup_ofArrays :
    (RawSchreierDatum.ofArrays n hn S k hk (finList n b) hb W).originalSubgroup =
      Subgroup.closure (Set.range fun i : Fin k => permOfArr n S[(i : ℕ)]!) := by
  rw [RawSchreierDatum.originalSubgroup]
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  rw [RawSchreierDatum.mem_ofArrays_original]
  exact ⟨fun ⟨i, hi, e⟩ => ⟨⟨i, hi⟩, e⟩, fun ⟨i, e⟩ => ⟨i, i.2, e⟩⟩

theorem card_ofArrays (hP : allPermsOK n S = true) (hc : 0 < chunks)
    (h : rawChainOK n (S.extract 0 k) S (baseArr n b) W chunks = true) :
    Nat.card (RawSchreierDatum.ofArrays n hn S k hk (finList n b) hb W).originalSubgroup =
      (rawOrbitSizes n S (baseArr n b)).prod :=
  card_originalSubgroup_of_chainOK (chainArrays_ofArrays' hP) hc h

theorem siftA_iff_mem_ofArrays (hP : allPermsOK n S = true) (hc : 0 < chunks)
    (h : rawChainOK n (S.extract 0 k) S (baseArr n b) W chunks = true) {g : Array ℕ}
    {G : Equiv.Perm (Fin n)} (hG : Rep n g G) :
    siftA n (rawLevels n S (baseArr n b)) (baseArr n b) 0 g = true ↔
      G ∈ (RawSchreierDatum.ofArrays n hn S k hk (finList n b) hb W).originalSubgroup :=
  siftA_iff_mem_originalSubgroup (chainArrays_ofArrays' hP) hc h hG

theorem strong_mem_ofArrays (hP : allPermsOK n S = true) (hc : 0 < chunks)
    (h : rawChainOK n (S.extract 0 k) S (baseArr n b) W chunks = true) {j : ℕ}
    (hj : j < S.size) :
    permOfArr n S[j]! ∈
      (RawSchreierDatum.ofArrays n hn S k hk (finList n b) hb W).originalSubgroup := by
  have hQ := (valid_ofArrays (hn := hn) (hk := hk) (hb := hb) hP hc h).1
  have := RawSchreierDatum.strong_get_mem_originalSubgroup _ hQ ⟨j, hj⟩
  rwa [RawSchreierDatum.ofArrays_strong_get] at this

theorem wordsArr_get {s : ℕ} {D : List (List ℤ)} {j : ℕ} (hkj : k ≤ j) (hj : j < s) :
    (wordsArr k s D)[j]! = D.getD (j - k) [] := by
  rw [wordsArr, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  simp only [show ¬ j < k by omega, ↓reduceIte]

theorem strong_eq_strongOf {D : List (List ℤ)} (hk : k ≤ S.size) (hP : allPermsOK n S = true)
    (h : rawChainOK n (S.extract 0 k) S (baseArr n b) (wordsArr k S.size D) chunks = true) :
    ∀ j < S.size, permOfArr n S[j]! = strongOf k (fun i => permOfArr n S[i]!) D j := by
  have hF := chainCheckFacts h
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    by_cases hjk : j < k
    · rw [strongOf_of_lt hjk]
    · have hext : (S.extract 0 k).size = k := by simp [Nat.min_eq_left hk]
      have hw := hF.words j hj (by rw [hext]; omega)
      rw [wordsArr_get (by omega) hj] at hw
      have hrep : Rep n (wordA n S (rawInvs n S) (D.getD (j - k) []))
          (wordIn j (fun i => permOfArr n S[i]!) (D.getD (j - k) [])) :=
        rep_wordA (fun i hi => rep_of_allPermsOK hP (by omega))
          (fun i hi => (rep_permOfArr (rawInvs_get hP (by omega))).2) _ hw.1
      rw [eq_of_eqA (rep_of_allPermsOK hP hj) hrep hw.2, strongOf_of_le (by omega)]
      exact wordIn_congr (fun i hi => ih i hi (by omega)) _

omit [NeZero n] in
theorem size_rawLevels (S : Array (Array ℕ)) (base : Array ℕ) :
    (rawLevels n S base).size = base.size := by
  simp [rawLevels]

omit [NeZero n] in
theorem levelSize_of_orbitSizes {S : Array (Array ℕ)} {base : Array ℕ} {l : List ℕ}
    (h : rawOrbitSizes n S base = l) {i : ℕ} (hi : i < l.length) :
    ((rawLevels n S base)[i]!).pts.size = l[i] := by
  subst h
  have hi' : i < (rawLevels n S base).size := by simpa [rawOrbitSizes] using hi
  rw [getElem!_pos _ i hi']
  simp [rawOrbitSizes]

theorem orbitSizes_ofArrays (hP : allPermsOK n S = true) (hc : 0 < chunks)
    (h : rawChainOK n (S.extract 0 k) S (baseArr n b) W chunks = true) :
    List.ofFn (RawSchreierDatum.ofArrays n hn S k hk (finList n b) hb W).orbitSize =
      rawOrbitSizes n S (baseArr n b) := by
  have hsz := (valid_ofArrays (hn := hn) (hk := hk) (hb := hb) hP hc h).2
  have hlen : (rawLevels n S (baseArr n b)).size = b.length := by
    rw [size_rawLevels]
    simp [baseArr, finList]
  apply List.ext_getElem
  · simp only [List.length_ofFn, rawOrbitSizes, List.length_map, Array.length_toList, hlen]
    show (finList n b).length = b.length
    simp [finList]
  · intro i h1 h2
    rw [List.getElem_ofFn, hsz]
    simp only [rawOrbitSizes, List.getElem_map, Array.getElem_toList]
    rw [getElem!_pos _ i (by simp only [rawOrbitSizes, List.length_map,
      Array.length_toList] at h2; exact h2)]

theorem exists_mem_ofArrays_apply_base (hP : allPermsOK n S = true) (hc : 0 < chunks)
    (h : rawChainOK n (S.extract 0 k) S (baseArr n b) W chunks = true)
    (h0 : 0 < (RawSchreierDatum.ofArrays n hn S k hk (finList n b) hb W).baseCount)
    (hfull : ((rawLevels n S (baseArr n b))[0]!).pts.size = n) (x : Fin n) :
    ∃ g ∈ (RawSchreierDatum.ofArrays n hn S k hk (finList n b) hb W).originalSubgroup,
      g ((RawSchreierDatum.ofArrays n hn S k hk (finList n b) hb W).base.get ⟨0, h0⟩) = x := by
  set Q := RawSchreierDatum.ofArrays n hn S k hk (finList n b) hb W
  obtain ⟨hQ, hsz⟩ := valid_ofArrays (hn := hn) (hk := hk) (hb := hb) hP hc h
  have hcard : Nat.card (Q.orbitPoints ⟨0, h0⟩) = n := by
    rw [← Q.orbitSize_eq_card, hsz]
    exact hfull
  have huniv : Q.orbitPoints ⟨0, h0⟩ = Set.univ := by
    rw [Set.eq_univ_iff_ncard, ← Nat.card_coe_set_eq, hcard, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hx : x ∈ Q.orbitPoints ⟨0, h0⟩ := huniv ▸ Set.mem_univ x
  obtain ⟨-, hmem, happ⟩ := Q.transversal_getD_spec ⟨0, h0⟩ x hx
  refine ⟨_, ?_, happ⟩
  rw [← Q.levelSubgroup_zero_eq_original hQ]
  exact hmem

end CFSG.Sporadic.Schreier.Tits
