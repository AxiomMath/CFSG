module

public import CFSG.Monster.B.Co2.Data
public import CFSG.Monster.B.Co2.ChainCert

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Co2

open Native CFSG.Certificates CFSG.Certificates.SchreierOrbitState

attribute [local irreducible] Native.chainStrong Native.strongInv Native.chainLevels
  Native.chainWords Native.pairPerms

structure ChainFacts : Prop where
  pair_size : pairPerms.size = 2
  strong_size : chainStrong.size = 20
  words_size : chainWords.size = 20
  base_size : chainBase.size = 10
  levels_size : chainLevels.size = 10
  strong_inv : ∀ j < 20, isInvA 2300 chainStrong[j]! strongInv[j]! = true
  strong_zero : eqA 2300 chainStrong[0]! pairPerms[0]! = true
  strong_one : eqA 2300 chainStrong[1]! pairPerms[1]! = true
  words : ∀ j < 20, 2 ≤ j → lettersOK j chainWords[j]! = true ∧
    eqA 2300 chainStrong[j]! (wordA 2300 chainStrong strongInv chainWords[j]!) = true
  terminal : ∀ j < 20, fixesFirst chainBase chainStrong[j]! 10 = true →
    eqA 2300 chainStrong[j]! (idA 2300) = true
  base_lt : ∀ i < 10, chainBase[i]! < 2300
  level : ∀ i < 10, levelOK 2300 chainBase[i]! (chainSteps i) chainLevels[i]! = true ∧
    chainLevels[i]!.pts.size = orbitLengths[i]!
  schreier : ∀ i < 10,
    schreierOK 2300 chainLevels chainBase i (chainSteps i) chainLevels[i]! 8 = true

theorem chainFacts : ChainFacts := by
  have h := co2ChainCertOK_eq_true
  simp only [co2ChainCertOK, chainCheck, Bool.and_eq_true, beq_iff_eq, deg] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, -⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, -⟩ := h
  have hS : chainStrong.size = 20 := by rw [h2]; rfl
  refine ⟨h1, hS, by rw [h3]; rfl, h4, h5, fun j hj => allLt_spec h7 (by rwa [hS]), h8, h9,
    fun j hj hj2 => ?_, fun j hj hf => ?_, fun i hi => ?_, fun i hi => ?_,
    fun i hi => allLt_spec h14 hi⟩
  · have := allLt_spec h10 (by rwa [hS] : j < chainStrong.size)
    simpa [show ¬ j < 2 by omega] using this
  · have := allLt_spec h11 (by rwa [hS] : j < chainStrong.size)
    simpa [hf] using this
  · exact of_decide_eq_true (allLt_spec h12 hi)
  · have := allLt_spec h13 hi
    simpa only [Bool.and_eq_true, beq_iff_eq] using this

theorem rep_strong
    {j : ℕ} (hj : j < 20) : Rep 2300 chainStrong[j]! (strongPerm j) :=
  (rep_permOfArr (chainFacts.strong_inv j hj)).1

theorem rep_strongInv
    {j : ℕ} (hj : j < 20) : Rep 2300 strongInv[j]! (strongPerm j)⁻¹ :=
  (rep_permOfArr (chainFacts.strong_inv j hj)).2

theorem chainQ_strong_get (j : Fin 20) : chainQ.strong.get j = strongPerm j := by
  change (Vector.ofFn fun j : Fin 20 => strongPerm j).get j = strongPerm j
  simp only [Vector.get, Vector.ofFn, Array.getElem_ofFn]
  rfl

theorem chainQ_strong_toList : chainQ.strong.toList = (List.range 20).map strongPerm := by
  change (Vector.ofFn fun j : Fin 20 => strongPerm j).toList = _
  rw [Vector.toList_ofFn, List.ofFn_eq_map,
    show (fun j : Fin 20 => strongPerm j) = strongPerm ∘ (fun j : Fin 20 => (j : ℕ)) from rfl,
    ← List.map_map, List.map_coe_finRange_eq_range]

@[expose] def toFin (x : ℕ) : Fin 2300 := ⟨x % 2300, Nat.mod_lt _ (by norm_num)⟩

theorem toFin_val {x : ℕ} (hx : x < 2300) : ((toFin x : Fin 2300) : ℕ) = x := Nat.mod_eq_of_lt hx

theorem toFin_eq {x : ℕ} (hx : x < 2300) : toFin x = ⟨x, hx⟩ := Fin.ext (toFin_val hx)

theorem chainQ_base_toList : chainQ.base.toList = (List.range 10).map fun k => toFin chainBase[k]! := by
  decide +kernel

theorem chainQ_base_val (i : Fin chainQ.baseCount) :
    ((chainQ.base.get i : Fin 2300) : ℕ) = chainBase[i.val]! := by
  revert i
  decide +kernel

theorem fixes_iff (j : ℕ) (hj : j < 20) {i : ℕ} (hi : i ≤ 10) :
    ((chainQ.base.toList.take i).all fun b => decide (strongPerm j b = b)) =
      fixesFirst chainBase chainStrong[j]! i := by
  rw [chainQ_base_toList, List.map_take.symm, List.take_range, Nat.min_eq_left hi,
    Bool.eq_iff_iff, List.all_map, List.all_eq_true, fixesFirst, allLt_iff]
  simp only [List.mem_range, Function.comp_apply, decide_eq_true_eq, beq_iff_eq]
  refine forall_congr' fun k => imp_congr_right fun hk => ?_
  have hb := chainFacts.base_lt k (by omega)
  rw [toFin_eq hb, (rep_strong hj).apply hb, Fin.ext_iff]

theorem levelGenerators_eq {i : ℕ} (hi : i ≤ 10) :
    chainQ.levelGenerators i = (levelIdx chainStrong chainBase i).map strongPerm := by
  rw [RawSchreierDatum.levelGenerators, chainQ_strong_toList, List.filter_map, levelIdx,
    chainFacts.strong_size]
  congr 1
  apply List.filter_congr
  intro j hj
  exact fixes_iff j (List.mem_range.1 hj) hi

theorem levelIdx_lt
    {i j : ℕ} (hj : j ∈ levelIdx chainStrong chainBase i) : j < 20 := by
  rw [levelIdx, chainFacts.strong_size] at hj
  exact List.mem_range.1 (List.mem_filter.1 hj).1

theorem chainQ_levelSteps_eq {i : ℕ} (hi : i ≤ 10) :
    chainQ.levelSteps i = (levelIdx chainStrong chainBase i).map strongPerm ++
      (levelIdx chainStrong chainBase i).map fun j => (strongPerm j)⁻¹ := by
  rw [RawSchreierDatum.levelSteps, levelGenerators_eq hi, List.map_map]
  rfl

theorem chainSteps_size {i : ℕ} (hi : i ≤ 10) :
    (chainSteps i).size = (chainQ.levelSteps i).length := by
  rw [chainQ_levelSteps_eq hi, chainSteps, levelSteps]
  simp

theorem rep_chainSteps
    {i : ℕ} (hi : i ≤ 10) {j : ℕ} (hj : j < (chainQ.levelSteps i).length) :
    Rep 2300 (chainSteps i)[j]! ((chainQ.levelSteps i)[j]) := by
  have hj' := hj
  rw [chainQ_levelSteps_eq hi] at hj'
  set idx := levelIdx chainStrong chainBase i with hidx
  have hsz : j < (chainSteps i).size := by rw [chainSteps_size hi]; exact hj
  rw [getElem!_pos (chainSteps i) j hsz]
  simp only [List.length_append, List.length_map] at hj'
  have e1 : ∀ h : j < (chainQ.levelSteps i).length, (chainQ.levelSteps i)[j] =
      (idx.map strongPerm ++ idx.map fun j => (strongPerm j)⁻¹)[j]'(by
        simpa [chainQ_levelSteps_eq hi] using h) := by
    intro h
    simp only [chainQ_levelSteps_eq hi, idx]
  rw [e1 hj]
  by_cases hlt : j < idx.length
  · rw [List.getElem_append_left (by simpa using hlt)]
    simp only [List.getElem_map]
    have : (chainSteps i)[j] = chainStrong[idx[j]]! := by
      simp only [chainSteps, levelSteps, ← hidx]
      rw [Array.getElem_append_left (by simpa using hlt)]
      simp
    rw [this]
    exact rep_strong (levelIdx_lt (List.getElem_mem hlt))
  · have hle : idx.length ≤ j := by omega
    rw [List.getElem_append_right (by simpa using hle)]
    simp only [List.getElem_map, List.length_map]
    have hk : j - idx.length < idx.length := by omega
    have : (chainSteps i)[j] = strongInv[idx[j - idx.length]]! := by
      simp only [chainSteps, levelSteps, ← hidx]
      rw [Array.getElem_append_right (by simpa using hle)]
      simp
    rw [this]
    exact rep_strongInv (levelIdx_lt (List.getElem_mem hk))

@[expose] def lev (i : ℕ) : Level := chainLevels[i]!

@[expose] def levPts (i k : ℕ) : Fin 2300 := toFin (lev i).pts[k]!

@[expose] def levT (i k : ℕ) : Equiv.Perm (Fin 2300) := permOfArr 2300 (lev i).tr[k]!

structure LevelFacts (root : ℕ) (steps : Array (Array ℕ)) (L : Level) : Prop where
  pos : 0 < L.pts.size
  le : L.pts.size ≤ 2300
  root : L.pts[0]! = root
  pts_lt : ∀ k < L.pts.size, L.pts[k]! < 2300
  pos_pts : ∀ k < L.pts.size, L.pos[L.pts[k]!]! = k
  pts_pos : ∀ z < 2300, L.pos[z]! < L.pts.size → L.pts[L.pos[z]!]! = z
  par_lt : ∀ k < L.pts.size, 0 < k → L.par[k]! < k
  lab_lt : ∀ k < L.pts.size, 0 < k → L.lab[k]! < steps.size
  edge : ∀ k < L.pts.size, 0 < k → (steps[L.lab[k]!]!)[L.pts[L.par[k]!]!]! = L.pts[k]!
  mono : ∀ k < L.pts.size, 0 < k → k + 1 < L.pts.size →
    lexLt L.par[k]! L.lab[k]! L.par[k + 1]! L.lab[k + 1]! = true
  closed : ∀ h < L.pts.size, ∀ j < steps.size,
    L.pos[(steps[j]!)[L.pts[h]!]!]! < L.pts.size ∧
      (L.pos[(steps[j]!)[L.pts[h]!]!]! = 0 ∨
        lexLt h j L.par[L.pos[(steps[j]!)[L.pts[h]!]!]!]! L.lab[L.pos[(steps[j]!)[L.pts[h]!]!]!]! =
          false)
  tr_zero : eqA 2300 L.tr[0]! (idA 2300) = true
  tr_step : ∀ k < L.pts.size, 0 < k →
    eqA 2300 L.tr[k]! (compA 2300 steps[L.lab[k]!]! L.tr[L.par[k]!]!) = true
  tr_inv : ∀ k < L.pts.size, isInvA 2300 L.tr[k]! L.trInv[k]! = true

theorem levelFacts_of_levelOK {root : ℕ} {steps : Array (Array ℕ)} {L : Level}
    (h : levelOK 2300 root steps L = true) : LevelFacts root steps L := by
  simp only [levelOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  refine ⟨h1, h2, h3, fun k hk => ?_, fun k hk => ?_, fun z hz hzm => ?_, fun k hk hk0 => ?_,
    fun k hk hk0 => ?_, fun k hk hk0 => ?_, fun k hk hk0 hk1 => ?_, fun h hh j hj => ?_, h9,
    fun k hk hk0 => ?_, fun k hk => allLt_spec h11 hk⟩
  · exact (by simpa [Bool.and_eq_true] using allLt_spec h4 hk : _ ∧ _).1
  · exact (by simpa [Bool.and_eq_true] using allLt_spec h4 hk : _ ∧ _).2
  · have := allLt_spec h5 hz
    simpa [hzm] using this
  · have := allLt_spec h6 hk
    simp only [show k ≠ 0 by omega, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
      decide_eq_true_eq, false_or] at this
    exact this.1.1
  · have := allLt_spec h6 hk
    simp only [show k ≠ 0 by omega, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
      decide_eq_true_eq, false_or] at this
    exact this.1.2
  · have := allLt_spec h6 hk
    simp only [show k ≠ 0 by omega, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
      decide_eq_true_eq, false_or] at this
    exact this.2
  · have := allLt_spec h7 hk
    simpa [show k ≠ 0 by omega, hk1] using this
  · have := allLt_spec (allLt_spec h8 hh) hj
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq,
      Bool.not_eq_true'] at this
    exact this
  · have := allLt_spec h10 hk
    simpa [show k ≠ 0 by omega] using this

theorem levelFacts {i : ℕ} (hi : i < 10) :
    LevelFacts chainBase[i]! (chainSteps i) (lev i) :=
  levelFacts_of_levelOK (chainFacts.level i hi).1

theorem lev_size
    {i : ℕ} (hi : i < 10) : (lev i).pts.size = orbitLengths[i]! :=
  (chainFacts.level i hi).2

theorem levPts_val
    {i k : ℕ} (hi : i < 10) (hk : k < (lev i).pts.size) :
    ((levPts i k : Fin 2300) : ℕ) = (lev i).pts[k]! :=
  toFin_val ((levelFacts hi).pts_lt k hk)

theorem rep_levT
    {i k : ℕ} (hi : i < 10) (hk : k < (lev i).pts.size) :
    Rep 2300 (lev i).tr[k]! (levT i k) :=
  (rep_permOfArr ((levelFacts hi).tr_inv k hk)).1

theorem rep_levTInv
    {i k : ℕ} (hi : i < 10) (hk : k < (lev i).pts.size) :
    Rep 2300 (lev i).trInv[k]! (levT i k)⁻¹ :=
  (rep_permOfArr ((levelFacts hi).tr_inv k hk)).2

theorem bfsCert {i : ℕ} (hi : i < 10) :
    BFSCert (chainQ.levelSteps i) (chainQ.base.get ⟨i, hi⟩) (lev i).pts.size (levPts i)
      (fun k => (lev i).par[k]!) (fun k => (lev i).lab[k]!) (levT i) := by
  have F := levelFacts hi
  have hsz := chainSteps_size (Nat.le_of_lt hi)
  have hlab : ∀ k, 0 < k → k < (lev i).pts.size → (lev i).lab[k]! < (chainQ.levelSteps i).length :=
    fun k hk0 hk => hsz ▸ F.lab_lt k hk hk0
  have hedge : ∀ k (hk0 : 0 < k) (hk : k < (lev i).pts.size),
      ((chainQ.levelSteps i)[(lev i).lab[k]!]'(hlab k hk0 hk)) (levPts i ((lev i).par[k]!)) =
        levPts i k := by
    intro k hk0 hk
    have hp := F.par_lt k hk hk0
    apply Fin.ext
    rw [levPts_val hi hk, ← F.edge k hk hk0,
      (rep_chainSteps (Nat.le_of_lt hi) (hlab k hk0 hk)).apply ((levelFacts hi).pts_lt _ (by omega))]
    congr 2
    exact Fin.ext (levPts_val hi (by omega))
  refine ⟨F.pos, ?_, ?_, ?_, fun k hk0 hk => F.par_lt k hk hk0, hlab, hedge, ?_, ?_, ?_⟩
  · apply Fin.ext
    rw [levPts_val hi F.pos, F.root, chainQ_base_val ⟨i, hi⟩]
  · exact (eqA_iff (rep_levT hi F.pos) rep_idA).1 F.tr_zero
  · intro a ha b hb hab
    have h1 := congrArg Fin.val hab
    rw [levPts_val hi ha, levPts_val hi hb] at h1
    rw [← F.pos_pts a ha, ← F.pos_pts b hb, h1]
  · intro k hk0 hk
    have hp := F.par_lt k hk hk0
    have hrep := rep_compA (rep_chainSteps (Nat.le_of_lt hi) (hlab k hk0 hk))
      (rep_levT hi (by omega : (lev i).par[k]! < (lev i).pts.size))
    exact (eqA_iff (rep_levT hi hk) hrep).1 (F.tr_step k hk hk0)
  · intro k hk0 hk1
    have := F.mono k (by omega) hk0 hk1
    simp only [lexLt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at this
    exact this
  · intro h hh j hj
    have hj' : j < (chainSteps i).size := by rw [hsz]; exact hj
    obtain ⟨hk, hle⟩ := F.closed h hh j hj'
    set z := ((chainSteps i)[j]!)[(lev i).pts[h]!]! with hz
    have hz2300 : z < 2300 := by
      rw [hz, (rep_chainSteps (Nat.le_of_lt hi) hj).apply (F.pts_lt h hh)]
      exact Fin.isLt _
    refine ⟨(lev i).pos[z]!, hk, ?_, ?_⟩
    · apply Fin.ext
      rw [levPts_val hi hk, F.pts_pos z hz2300 hk, hz,
        (rep_chainSteps (Nat.le_of_lt hi) hj).apply (F.pts_lt h hh)]
      congr 2
      exact Fin.ext (levPts_val hi hh).symm
    · rcases hle with h0 | hl
      · exact Or.inl h0
      · right
        intro hlex
        simp only [lexLt, Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.and_eq_false_iff,
          beq_eq_false_iff_ne, ne_eq] at hl
        unfold LexLt at hlex
        omega

theorem orbitSearch_eq {i : ℕ} (hi : i < 10) :
    chainQ.orbitSearch ⟨i, hi⟩ =
      ⟨(List.range (lev i).pts.size).map fun k => (levPts i k, levT i k), []⟩ :=
  (bfsCert hi).run_initial_eq

theorem transversal_of_lt
    {i : ℕ} (hi : i < 10) {k : ℕ} (hk : k < (lev i).pts.size) :
    (chainQ.orbitSearch ⟨i, hi⟩).transversal? (levPts i k) = some (levT i k) := by
  rw [orbitSearch_eq hi]
  exact (bfsCert hi).lookup_recs_of_lt le_rfl hk

theorem transversal_eq_none {i : ℕ} (hi : i < 10) {z : Fin 2300}
    (hz : ¬ (lev i).pos[(z : ℕ)]! < (lev i).pts.size) :
    (chainQ.orbitSearch ⟨i, hi⟩).transversal? z = none := by
  rw [orbitSearch_eq hi]
  change List.lookup z ((List.range (lev i).pts.size).map fun k => (levPts i k, levT i k)) = none
  rw [List.lookup_eq_none_iff]
  intro p hp
  simp only [List.mem_map, List.mem_range] at hp
  obtain ⟨k, hk, rfl⟩ := hp
  rw [bne_iff_ne]
  intro he
  apply hz
  rw [he, levPts_val hi hk, (levelFacts hi).pos_pts k hk]
  exact hk

theorem schreierSiftSucceeds_cons_some {n : ℕ} (b : Fin n) (q : SchreierOrbitState n)
    (levels : List (Fin n × SchreierOrbitState n)) (h t : Equiv.Perm (Fin n))
    (ht : q.transversal? (h b) = some t) :
    schreierSiftSucceeds ((b, q) :: levels) h = schreierSiftSucceeds levels (t⁻¹ * h) := by
  unfold schreierSiftSucceeds
  rw [schreierSiftResidual_available b q levels h t ht]

theorem schreierSiftSucceeds_cons_none {n : ℕ} (b : Fin n) (q : SchreierOrbitState n)
    (levels : List (Fin n × SchreierOrbitState n)) (h : Equiv.Perm (Fin n))
    (ht : q.transversal? (h b) = none) : schreierSiftSucceeds ((b, q) :: levels) h = false := by
  unfold schreierSiftSucceeds
  rw [schreierSiftResidual_unavailable b q levels h ht]

theorem chainLevels_getElem {l : ℕ} (hl : l < chainLevels.size) : chainLevels[l] = lev l := by
  rw [lev, getElem!_pos chainLevels l hl]

theorem siftA_eq :
    ∀ d l, l + d = 10 → ∀ (g : Array ℕ) (G : Equiv.Perm (Fin 2300)),
    Rep 2300 g G → siftA 2300 chainLevels chainBase l g =
      schreierSiftSucceeds (chainQ.siftLevels chainQ.orbitTables l) G := by
  intro d
  induction d with
  | zero =>
    intro l hl g G hG
    have hl10 : l = 10 := by omega
    subst hl10
    rw [siftA, dite_eq_right (by rw [chainFacts.levels_size]; omega)]
    have hnil : chainQ.siftLevels chainQ.orbitTables 10 = [] := by
      simp [RawSchreierDatum.siftLevels, chainQ]
    rw [hnil]
    rw [Bool.eq_iff_iff, eqA_iff hG rep_idA, schreierSiftSucceeds_nil]
  | succ d ih =>
    intro l hl g G hG
    have hl10 : l < 10 := by omega
    have hls : l < chainLevels.size := by rw [chainFacts.levels_size]; exact hl10
    rw [siftA, dite_eq_left hls, chainLevels_getElem hls]
    have hcons := chainQ.siftLevels_cons chainQ.orbitTables ⟨l, hl10⟩
    simp only at hcons
    rw [hcons, RawSchreierDatum.orbitTables_get]
    set b := chainQ.base.get ⟨l, hl10⟩ with hb
    have hbv : (b : ℕ) = chainBase[l]! := chainQ_base_val ⟨l, hl10⟩
    have hgb : g[chainBase[l]!]! = (G b : ℕ) := by
      rw [← hbv]
      exact hG b
    rw [hgb]
    by_cases hk : (lev l).pos[(G b : ℕ)]! < (lev l).pts.size
    · have hpts : levPts l ((lev l).pos[(G b : ℕ)]!) = G b := by
        apply Fin.ext
        rw [levPts_val hl10 hk, (levelFacts hl10).pts_pos _ (G b).2 hk]
      have ht := transversal_of_lt hl10 hk
      rw [hpts] at ht
      rw [schreierSiftSucceeds_cons_some _ _ _ _ _ ht]
      simp only [hk, decide_true, Bool.true_and]
      exact ih (l + 1) (by omega) _ _ (rep_compA (rep_levTInv hl10 hk) hG)
    · rw [schreierSiftSucceeds_cons_none _ _ _ _ (transversal_eq_none hl10 hk)]
      simp [hk]

theorem chainQ_original_get_zero : chainQ.original.get ⟨0, by decide⟩ = pa := rfl

theorem chainQ_original_get_one : chainQ.original.get ⟨1, by decide⟩ = pb := rfl

theorem strongPerm_zero :
    strongPerm 0 = pa :=
  (eqA_iff (rep_strong (by norm_num)) rep_pa).1 chainFacts.strong_zero

theorem strongPerm_one :
    strongPerm 1 = pb :=
  (eqA_iff (rep_strong (by norm_num)) rep_pb).1 chainFacts.strong_one

theorem chainQ_initial :
    ∀ j : Fin chainQ.originalCount,
    chainQ.strong.get (Fin.castLE chainQ.originalCount_le j) = chainQ.original.get j := by
  intro j
  change Fin 2 at j
  fin_cases j
  · exact (chainQ_strong_get ⟨0, by norm_num⟩).trans strongPerm_zero
  · exact (chainQ_strong_get ⟨1, by norm_num⟩).trans strongPerm_one

theorem chainQ_words :
    ∀ (j : Fin chainQ.strongCount) (hj : chainQ.originalCount ≤ j.val),
    chainQ.strong.get j = chainQ.derivationValue j hj := by
  intro j hj
  change Fin 20 at j
  change 2 ≤ j.val at hj
  obtain ⟨hl, he⟩ := chainFacts.words j j.2 hj
  have hrep := rep_wordA (gs := strongPerm) (j := j.val)
    (fun h hh => rep_strong (by omega)) (fun h hh => rep_strongInv (by omega)) _ hl
  rw [chainQ_strong_get]
  refine (eqA_iff (rep_strong j.2) hrep).1 he |>.trans ?_
  unfold RawSchreierDatum.derivationValue schreierWordValue
  congr 1
  funext h
  exact (chainQ_strong_get ⟨h.val, by omega⟩).symm

theorem chainQ_terminal :
    ∀ s ∈ chainQ.levelGenerators chainQ.baseCount, s = 1 := by
  intro s hs
  change s ∈ chainQ.levelGenerators 10 at hs
  rw [levelGenerators_eq le_rfl, List.mem_map] at hs
  obtain ⟨j, hj, rfl⟩ := hs
  have hj20 := levelIdx_lt hj
  have hfix : fixesFirst chainBase chainStrong[j]! 10 = true := by
    rw [levelIdx, List.mem_filter] at hj
    exact hj.2
  exact (eqA_iff (rep_strong hj20) rep_idA).1 (chainFacts.terminal j hj20 hfix)

theorem chainQ_schreier :
    ∀ (i : Fin chainQ.baseCount) (x : Fin 2300) (tx : Equiv.Perm (Fin 2300)),
    (chainQ.orbitSearch i).transversal? x = some tx →
    ∀ s ∈ chainQ.levelSteps i.val, ∃ ty : Equiv.Perm (Fin 2300),
      (chainQ.orbitSearch i).transversal? (s x) = some ty ∧
      schreierSiftSucceeds (chainQ.siftLevels chainQ.orbitTables (i.val + 1))
        (ty⁻¹ * s * tx) = true := by
  rintro ⟨i, hi⟩ x tx htx s hs
  change i < 10 at hi
  rw [orbitSearch_eq hi] at htx
  change List.lookup x ((List.range (lev i).pts.size).map fun k => (levPts i k, levT i k)) =
    some tx at htx
  obtain ⟨before, after, heq, -⟩ := List.lookup_eq_some_iff.1 htx
  have hmem : (x, tx) ∈ (List.range (lev i).pts.size).map fun k => (levPts i k, levT i k) := by
    rw [heq]
    simp
  simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at hmem
  obtain ⟨h, hh, rfl, rfl⟩ := hmem
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
  have F := levelFacts hi
  have hsz := chainSteps_size (Nat.le_of_lt hi)
  have hj' : j < (chainSteps i).size := by rw [hsz]; exact hj
  have hrs := rep_chainSteps (Nat.le_of_lt hi) hj
  have htest : allLt (chainSteps i).size (fun j =>
      decide ((lev i).pos[((chainSteps i)[j]!)[(lev i).pts[h]!]!]! < (lev i).pts.size) &&
        siftA 2300 chainLevels chainBase (i + 1)
          (compA 2300 (lev i).trInv[(lev i).pos[((chainSteps i)[j]!)[(lev i).pts[h]!]!]!]!
            (compA 2300 (chainSteps i)[j]! (lev i).tr[h]!))) = true :=
    parLt_spec (by norm_num) (chainFacts.schreier i hi) h hh
  have htest' := allLt_spec htest hj'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at htest'
  obtain ⟨hk, hsift⟩ := htest'
  have hzv : ((chainSteps i)[j]!)[(lev i).pts[h]!]! =
      ((chainQ.levelSteps i)[j] (levPts i h) : ℕ) := by
    rw [hrs.apply (F.pts_lt h hh)]
    congr 2
    exact Fin.ext (levPts_val hi hh).symm
  have hpts : levPts i ((lev i).pos[((chainSteps i)[j]!)[(lev i).pts[h]!]!]!) =
      (chainQ.levelSteps i)[j] (levPts i h) := by
    apply Fin.ext
    rw [levPts_val hi hk, F.pts_pos _ (by rw [hzv]; exact Fin.isLt _) hk, hzv]
  refine ⟨levT i ((lev i).pos[((chainSteps i)[j]!)[(lev i).pts[h]!]!]!), ?_, ?_⟩
  · rw [← hpts]
    exact transversal_of_lt hi hk
  · have hrep := rep_compA (rep_levTInv hi hk) (rep_compA hrs (rep_levT hi hh))
    rw [mul_assoc, ← siftA_eq (10 - (i + 1)) (i + 1) (by omega) _ _ hrep]
    exact hsift

theorem validSchreier_chainQ :
    ValidSchreier chainQ := by
  rw [validSchreier_iff]
  exact ⟨chainQ_initial, chainQ_words, chainQ_terminal, chainQ_schreier⟩

theorem orbitSize_eq {i : ℕ} (hi : i < 10) :
    chainQ.orbitSize ⟨i, hi⟩ = orbitLengths[i]! := by
  rw [RawSchreierDatum.orbitSize, orbitSearch_eq hi, ← lev_size hi]
  simp [SchreierOrbitState.keys]

theorem card_orbitPoints {i : ℕ} (hi : i < 10) :
    Nat.card (chainQ.orbitPoints ⟨i, hi⟩) = orbitLengths[i]! := by
  rw [← chainQ.orbitSize_eq_card, orbitSize_eq hi]

end CFSG.Monster.B.Co2
