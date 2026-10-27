module

public import CFSG.Sporadic.Schreier.ONCompactSpec
public import CFSG.Sporadic.Schreier.ONWordDatum
public import CFSG.Certificates.SchreierPointSiftSoundness
public import CFSG.Certificates.SchreierSift

public noncomputable section

namespace CFSG.ONSchreier

open CFSG.ONSchreier.Native CFSG.Certificates CFSG.Certificates.RawSchreierDatum

variable {n : ℕ}

theorem pwords_eq (n : ℕ) (S Sinv : Array (Array ℕ)) (ws : Array (List ℤ)) :
    pwords n S Sinv ws = ws.map (pword n S Sinv) := by
  simp only [pwords, Id.run]
  rw [Array.forIn_pure_yield_eq_foldl, Array.mkEmpty_eq, Array.map_eq_foldl]
  rfl

theorem conjAll_eq (n : ℕ) (c ci : Array ℕ) (g : Array (Array ℕ)) :
    conjAll n c ci g = g.map fun x => pcomp n c (pcomp n x ci) := by
  simp only [conjAll, Id.run]
  rw [Array.forIn_pure_yield_eq_foldl, Array.mkEmpty_eq, Array.map_eq_foldl]
  rfl

@[expose] def commArr (n : ℕ) (g : Array (Array ℕ)) (s : ℕ × ℕ × ℕ) : Array ℕ :=
  if s.2.2 == 0 then
    pcomp n g[s.2.1 - 1]! (pcomp n g[s.1 - 1]!
      (pcomp n (pinvCand n g[s.2.1 - 1]!) (pinvCand n g[s.1 - 1]!)))
  else pcomp n g[s.2.2 - 1]! (pcomp n (pcomp n g[s.2.1 - 1]! (pcomp n g[s.1 - 1]!
      (pcomp n (pinvCand n g[s.2.1 - 1]!) (pinvCand n g[s.1 - 1]!))))
    (pinvCand n g[s.2.2 - 1]!))

theorem commGens_eq (n : ℕ) (g : Array (Array ℕ)) (specs : Array (ℕ × ℕ × ℕ)) :
    commGens n g specs = specs.map (commArr n g) := by
  simp only [commGens, Id.run]
  rw [Array.forIn_pure_yield_eq_foldl, Array.mkEmpty_eq, Array.map_eq_foldl]
  rfl

@[expose] def listComm {G : Type*} [Group G] (g : List G) (a b : ℕ) : G :=
  g.getD (b - 1) 1 * g.getD (a - 1) 1 * (g.getD (b - 1) 1)⁻¹ * (g.getD (a - 1) 1)⁻¹

@[expose] def commSpec {G : Type*} [Group G] (g : List G) (s : ℕ × ℕ × ℕ) : G :=
  if s.2.2 = 0 then listComm g s.1 s.2.1
  else g.getD (s.2.2 - 1) 1 * listComm g s.1 s.2.1 * (g.getD (s.2.2 - 1) 1)⁻¹

theorem prep_getD {g : Array (Array ℕ)} {gl : List (Equiv.Perm (Fin n))}
    (hg : ∀ j (hj : j < gl.length), PRep n g[j]! gl[j]) {j : ℕ} (hj : j < gl.length) :
    PRep n g[j]! (gl.getD j 1) := by
  rw [List.getD_eq_getElem _ _ hj]
  exact hg j hj

theorem prep_commArr {g : Array (Array ℕ)} {gl : List (Equiv.Perm (Fin n))}
    (hg : ∀ j (hj : j < gl.length), PRep n g[j]! gl[j])
    (hinv : ∀ j < gl.length, pisInv n g[j]! (pinvCand n g[j]!) = true) {s : ℕ × ℕ × ℕ}
    (ha : 1 ≤ s.1 ∧ s.1 ≤ gl.length) (hb : 1 ≤ s.2.1 ∧ s.2.1 ≤ gl.length)
    (hk : s.2.2 ≤ gl.length) : PRep n (commArr n g s) (commSpec gl s) := by
  have pa := prep_getD hg (j := s.1 - 1) (by omega)
  have pb := prep_getD hg (j := s.2.1 - 1) (by omega)
  have pai := prep_inv_of_pisInv pa (hinv _ (by omega))
  have pbi := prep_inv_of_pisInv pb (hinv _ (by omega))
  have pc := prep_pcomp pb (prep_pcomp pa (prep_pcomp pbi pai))
  have ec : gl.getD (s.2.1 - 1) 1 * (gl.getD (s.1 - 1) 1 * ((gl.getD (s.2.1 - 1) 1)⁻¹ *
      (gl.getD (s.1 - 1) 1)⁻¹)) = listComm gl s.1 s.2.1 := by
    simp only [listComm, mul_assoc]
  rw [ec] at pc
  unfold commArr commSpec
  by_cases h0 : s.2.2 = 0
  · rw [ite_eq_left (by simpa using h0), ite_eq_left h0]
    exact pc
  · rw [ite_eq_right (by simpa using h0), ite_eq_right h0]
    have pk := prep_getD hg (j := s.2.2 - 1) (by omega)
    have pki := prep_inv_of_pisInv pk (hinv _ (by omega))
    have := prep_pcomp pk (prep_pcomp pc pki)
    rwa [← mul_assoc] at this

theorem base_getElem! {base : List (Fin n)} {baseArr : Array ℕ}
    (hbase : base.map Fin.val = baseArr.toList) {i : ℕ} (hi : i < base.length) :
    baseArr[i]! = (base[i] : ℕ) := by
  have hlen : baseArr.size = base.length := by
    have := congrArg List.length hbase
    simpa using this.symm
  rw [getElem!_pos baseArr i (by omega)]
  have := List.getElem_of_eq hbase (by simpa using hi)
  rw [List.getElem_map, Array.getElem_toList] at this
  exact this.symm

theorem ofWords_arrays {hn : 1 ≤ n} {orig : List (Equiv.Perm (Fin n))} {W : Array (List ℤ)}
    {hk : orig.length ≤ W.size} {base : List (Fin n)} {hb : base.Nodup} {S : Array (Array ℕ)}
    {baseArr : Array ℕ} (hsize : S.size = W.size)
    (horig : ∀ j (hj : j < orig.length), PRep n S[j]! orig[j])
    (hbase : base.map Fin.val = baseArr.toList) :
    CArrays (RawSchreierDatum.ofWords n hn orig W hk base hb) orig.length S baseArr W := by
  have hlen : baseArr.size = base.length := by
    have := congrArg List.length hbase
    simpa using this.symm
  refine ⟨rfl, hsize, hlen, fun j hj => ?_, fun i => ?_, fun _ _ => rfl, ofWords_initial,
    ofWords_words⟩
  · rw [ofWords_strong_get, wordStrong_of_lt _ _ hj]
    exact horig j hj
  · rw [ofWords_base_get]
    exact (base_getElem! hbase _).symm

@[expose] def RawSchreierDatum.ofArrays (n : ℕ) (hn : 1 ≤ n) (gens strong : Array (Array ℕ))
    (hk : gens.size ≤ strong.size) (base : List (Fin n)) (hb : base.Nodup)
    (D : Array (List ℤ)) : RawSchreierDatum n where
  degree_pos := hn
  originalCount := gens.size
  strongCount := strong.size
  baseCount := base.length
  originalCount_le := hk
  original := Vector.ofFn fun j => permOfArr n gens[j.val]!
  strong := Vector.ofFn fun j => permOfArr n strong[j.val]!
  base := ⟨base.toArray, by simp⟩
  base_distinct := by simpa using hb
  derivation j _ := ptoLetters j.val D[j.val - gens.size]!

section OfArrays

variable {hn : 1 ≤ n} {gens strong : Array (Array ℕ)} {hk : gens.size ≤ strong.size}
  {base : List (Fin n)} {hb : base.Nodup} {D : Array (List ℤ)}

theorem ofArrays_strong_get
    (j : Fin (RawSchreierDatum.ofArrays n hn gens strong hk base hb D).strongCount) :
    (RawSchreierDatum.ofArrays n hn gens strong hk base hb D).strong.get j =
      permOfArr n strong[j.val]! := by
  simp only [RawSchreierDatum.ofArrays, Vector.get, Vector.toArray_ofFn, Array.getElem_ofFn]
  rfl

theorem ofArrays_original_get
    (j : Fin (RawSchreierDatum.ofArrays n hn gens strong hk base hb D).originalCount) :
    (RawSchreierDatum.ofArrays n hn gens strong hk base hb D).original.get j =
      permOfArr n gens[j.val]! := by
  simp only [RawSchreierDatum.ofArrays, Vector.get, Vector.toArray_ofFn, Array.getElem_ofFn]
  rfl

theorem ofArrays_base_get
    (i : Fin (RawSchreierDatum.ofArrays n hn gens strong hk base hb D).baseCount) :
    (RawSchreierDatum.ofArrays n hn gens strong hk base hb D).base.get i =
      base[i.val]'(by simpa [RawSchreierDatum.ofArrays] using i.isLt) := by
  simp only [RawSchreierDatum.ofArrays, Vector.get, List.getElem_toArray]
  rfl

theorem ofArrays_base_toList :
    (RawSchreierDatum.ofArrays n hn gens strong hk base hb D).base.toList = base := by
  simp [RawSchreierDatum.ofArrays]

theorem ofArrays_originalSubgroup :
    (RawSchreierDatum.ofArrays n hn gens strong hk base hb D).originalSubgroup =
      Subgroup.closure (Set.range fun j : Fin gens.size => permOfArr n gens[j.val]!) := by
  rw [RawSchreierDatum.originalSubgroup]
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  rw [schreier_vector_mem_toList_iff_get]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j, (ofArrays_original_get j).symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, ofArrays_original_get j⟩

theorem getElem!_replicate_append {α : Type*} [Inhabited α] (m : ℕ) (a : α) (E : Array α)
    {j : ℕ} (hj : m ≤ j) : (Array.replicate m a ++ E)[j]! = E[j - m]! := by
  by_cases h : j - m < E.size
  · rw [getElem!_pos _ j (by simp; omega), getElem!_pos E (j - m) h,
      Array.getElem_append_right (by simp; omega)]
    simp
  · rw [getElem!_neg _ j (by simp; omega), getElem!_neg E (j - m) h]

theorem ofArrays_arrays {baseArr : Array ℕ} {pts bidx : Array ℕ} {full : Bool} {chunks : ℕ}
    (hbase : base.map Fin.val = baseArr.toList)
    (hgens : ∀ j < gens.size,
      peq n gens[j]! strong[j]! = true ∧ pisInv n gens[j]! (pinvCand n gens[j]!) = true)
    (hchain : chainOK n gens.size strong baseArr (Array.replicate gens.size [] ++ D) pts bidx
      full chunks = true) :
    CArrays (RawSchreierDatum.ofArrays n hn gens strong hk base hb D) gens.size strong baseArr
      (Array.replicate gens.size [] ++ D) := by
  have hF := chainFacts hchain
  have hlen : baseArr.size = base.length := by
    have := congrArg List.length hbase
    simpa using this.symm
  have hrep : ∀ j < strong.size, PRep n strong[j]! (permOfArr n strong[j]!) ∧
      PRep n (pinvs n strong)[j]! (permOfArr n strong[j]!)⁻¹ :=
    fun j hj => prep_permOfArr (hF.strong_inv j hj)
  refine ⟨rfl, rfl, hlen, fun j _ => ?_, fun i => ?_, fun j hj => ?_, fun j => ?_,
    fun j hj => ?_⟩
  · rw [ofArrays_strong_get]
    exact (hrep j j.isLt).1
  · rw [ofArrays_base_get]
    exact (base_getElem! hbase _).symm
  · change ptoLetters j.val D[j.val - gens.size]! = _
    rw [getElem!_replicate_append gens.size [] D (j := j.val) hj]
  · rw [ofArrays_strong_get, ofArrays_original_get]
    have hj : j.val < gens.size := j.isLt
    obtain ⟨hpeq, hinv⟩ := hgens j hj
    have h1 := (prep_permOfArr hinv).1
    have h2 := prep_of_peq hpeq (hrep j (by omega)).1
    exact h2.unique h1
  · have hjs : (j : ℕ) < strong.size := j.isLt
    rw [ofArrays_strong_get, RawSchreierDatum.derivationValue, schreierWordValue]
    obtain ⟨hl, hw⟩ := hF.words j hjs hj
    have hp := prep_pword (gs := fun h => permOfArr n strong[h]!) (j := j.val)
      (fun h hh => (hrep h (by omega)).1) (fun h hh => (hrep h (by omega)).2) _ hl
    have h2 := prep_of_peq hw hp
    have e := (hrep j hjs).1.unique h2
    rw [e]
    change _ = Quiver.SchreierGraph.evalWord _ (ptoLetters j.val D[j.val - gens.size]!)
    rw [← getElem!_replicate_append gens.size ([] : List ℤ) D hj]
    congr 1
    funext h
    rw [ofArrays_strong_get]

end OfArrays

theorem mem_of_pointSift (Q : RawSchreierDatum n) (hQ : ValidPointSchreier Q)
    {H : Subgroup (Equiv.Perm (Fin n))} (hle : Q.originalSubgroup ≤ H)
    (hstab : H ⊓ fixingSubgroup (Equiv.Perm (Fin n)) {b | b ∈ Q.base.toList} = ⊥)
    {h : Equiv.Perm (Fin n)} (hH : h ∈ H) (hpt : Q.pointSift h 0 = true) :
    h ∈ Q.originalSubgroup := by
  obtain ⟨r, hr⟩ := (schreierPointSiftSucceeds_eq_true_iff _ h).1 hpt
  have go : ∀ d i, i + d = Q.baseCount → ∀ h : Equiv.Perm (Fin n), h ∈ H →
      (∀ b ∈ Q.base.toList.take i, h b = b) →
      schreierSiftResidual (Q.siftLevels Q.orbitTables i) h = some r →
        h ∈ Q.originalSubgroup := by
    intro d
    induction d with
    | zero =>
      intro i hi h hH hfix _
      have hi' : i = Q.baseCount := by omega
      subst i
      have hmem : h ∈ H ⊓ fixingSubgroup (Equiv.Perm (Fin n)) {b | b ∈ Q.base.toList} := by
        refine Subgroup.mem_inf.2 ⟨hH,
          (mem_fixingSubgroup_iff (Equiv.Perm (Fin n))).2 fun b hb => ?_⟩
        rw [Equiv.Perm.smul_def]
        exact hfix b (Q.base_take_baseCount.symm ▸ hb)
      rw [hstab, Subgroup.mem_bot] at hmem
      rw [hmem]
      exact one_mem _
    | succ d ih =>
      intro i hi h hH hfix hr
      let j : Fin Q.baseCount := ⟨i, by omega⟩
      rw [Q.siftLevels_cons Q.orbitTables j] at hr
      cases ht : (Q.orbitTables.get j).transversal? (h (Q.base.get j)) with
      | none =>
        rw [schreierSiftResidual_unavailable _ _ _ _ ht] at hr
        exact absurd hr (by simp)
      | some t =>
        rw [schreierSiftResidual_available _ _ _ _ _ ht] at hr
        have ht' : Q.transversal? j (h (Q.base.get j)) = some t := by
          simpa only [orbitTables_get, RawSchreierDatum.transversal?] using ht
        obtain ⟨htL, htfix, htb⟩ := Q.transversal_sound j _ t ht'
        have htP := Q.levelSubgroup_le_originalSubgroup_of_point hQ i htL
        have hfix' : ∀ b ∈ Q.base.toList.take (i + 1), (t⁻¹ * h) b = b := by
          intro b hb
          rcases (Q.mem_base_take_succ (i := j)).1 hb with hb | hb
          · rw [Equiv.Perm.mul_apply, hfix b hb, Equiv.Perm.inv_eq_iff_eq, htfix b hb]
          · rw [hb, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq, htb]
        have hrest := ih (i + 1) (by omega) (t⁻¹ * h) (mul_mem (inv_mem (hle htP)) hH) hfix' hr
        have e : h = t * (t⁻¹ * h) := by rw [mul_inv_cancel_left]
        rw [e]
        exact mul_mem htP hrest
  exact go Q.baseCount 0 (by omega) h hH (by simp) hr

theorem mem_of_sift (Q : RawSchreierDatum n) (hQ : ValidPointSchreier Q)
    {h : Equiv.Perm (Fin n)} (hs : Q.sift h 0 = true) : h ∈ Q.originalSubgroup :=
  Q.permutation_sift_membership 0 (Nat.zero_le _) h Q.originalSubgroup
    (fun j _ x _ t ht => Q.levelSubgroup_le_originalSubgroup_of_point hQ _
      (Q.transversal_sound j x t ht).1) hs

section Native

variable {Q : RawSchreierDatum n} {m : ℕ} {S : Array (Array ℕ)} {base : Array ℕ}
  {W : Array (List ℤ)} {chunks : ℕ}

theorem pointSift_of_memPoint (hA : CArrays Q m S base W)
    (hchain : pointChainOK n m S base W chunks = true) {g : Array ℕ}
    {G : Equiv.Perm (Fin n)} (hg : PRep n g G)
    (h : memPoint (levelsOf n S base) (invsOf n S base) base g = true) :
    Q.pointSift G 0 = true := by
  have hF := chainFacts hchain
  refine (hA.psift_sound hF (by simp) Q.baseCount 0 (by omega) (base.map fun b => g[b]!) G
    (by simp) (fun t ht => ?_) h).1
  rw [getElem!_map' _ _ ht]
  exact hg ⟨base[t]!, hF.pts_lt t ht⟩

theorem sift_of_memFull (hA : CArrays Q m S base W)
    (hchain : fullChainOK n m S base W chunks = true) {g : Array ℕ}
    {G : Equiv.Perm (Fin n)} (hg : PRep n g G)
    (h : memFull n (levelsOf n S base) (invsOf n S base) base g = true) :
    Q.sift G 0 = true := by
  have hF := chainFacts hchain
  have hcover : true = true → ∀ x : Fin n, ∃ t < (pid n).size, (pid n)[t]! = x := by
    intro _ x
    exact ⟨x, by simp [pid], by rw [pid_get x.2]⟩
  refine (hA.psift_sound hF hcover Q.baseCount 0 (by omega)
    (Array.ofFn (n := n) fun i => g[i.val]!) G (by simp [pid]) (fun t ht => ?_) h).2 rfl
  have ht' : t < n := by simpa [pid] using ht
  have e : (⟨(pid n)[t]!, hF.pts_lt t ht⟩ : Fin n) = ⟨t, ht'⟩ := Fin.ext (pid_get ht')
  rw [e, getElem!_ofFn_nat _ ht']
  exact hg ⟨t, ht'⟩

theorem mem_of_memPoint (hA : CArrays Q m S base W)
    (hchain : pointChainOK n m S base W chunks = true) (hQ : ValidPointSchreier Q)
    {H : Subgroup (Equiv.Perm (Fin n))} (hle : Q.originalSubgroup ≤ H)
    (hstab : H ⊓ fixingSubgroup (Equiv.Perm (Fin n)) {b | b ∈ Q.base.toList} = ⊥)
    {g : Array ℕ} {G : Equiv.Perm (Fin n)} (hg : PRep n g G) (hG : G ∈ H)
    (h : memPoint (levelsOf n S base) (invsOf n S base) base g = true) :
    G ∈ Q.originalSubgroup :=
  mem_of_pointSift Q hQ hle hstab hG (pointSift_of_memPoint hA hchain hg h)

theorem mem_of_memFull (hA : CArrays Q m S base W)
    (hchain : fullChainOK n m S base W chunks = true) (hQ : ValidPointSchreier Q)
    {g : Array ℕ} {G : Equiv.Perm (Fin n)} (hg : PRep n g G)
    (h : memFull n (levelsOf n S base) (invsOf n S base) base g = true) :
    G ∈ Q.originalSubgroup :=
  mem_of_sift Q hQ (sift_of_memFull hA hchain hg h)

end Native

theorem orbit_sizes_eq {Q : RawSchreierDatum n} {S : Array (Array ℕ)} {base : Array ℕ}
    (hsize : base.size = Q.baseCount)
    (horb : ∀ i : Fin Q.baseCount, Q.orbitSize i = (CArrays.lev n S base i).pts.size) :
    (List.finRange Q.baseCount).map (fun i => Nat.card (Q.orbitPoints i)) =
      cOrbitSizes n S base := by
  rw [cOrbitSizes]
  apply List.ext_getElem (by simp [cLevels, hsize])
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_finRange, Array.getElem_toList]
  rw [← Q.orbitSize_eq_card, horb]
  simp only [CArrays.lev, Fin.val_cast]
  rw [getElem!_pos _ k (by simpa [cLevels, hsize] using h1)]

theorem card_eq_prod_cOrbitSizes {Q : RawSchreierDatum n} (hQ : ValidSchreier Q)
    {S : Array (Array ℕ)} {base : Array ℕ} (hsize : base.size = Q.baseCount)
    (horb : ∀ i : Fin Q.baseCount, Q.orbitSize i = (CArrays.lev n S base i).pts.size) :
    Nat.card Q.originalSubgroup = (cOrbitSizes n S base).prod := by
  rw [Q.original_card_eq_orbit_product hQ, Fin.prod_univ_def, orbit_sizes_eq hsize horb]

end CFSG.ONSchreier
