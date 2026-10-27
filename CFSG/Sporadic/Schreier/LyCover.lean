
module

public import CFSG.Sporadic.Schreier.LyData
public import CFSG.Sporadic.Schreier.LyChain11
public import CFSG.Sporadic.Schreier.LyCoverCertificate
public import CFSG.Sporadic.Th.TableSpec

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.He.Native Matrix
open CFSG.Sporadic.SchreierLemmas
open CFSG.Sporadic.Th (allIn_eq_true)

@[expose] def RepM [LySeed] (X : Mat) (g : J) : Prop := toMat 5 111 X = mat g

theorem RepM.mul [LySeed]
    {X Y : Mat} {g h : J} (hX : RepM X g) (hY : RepM Y h) :
    RepM (mulM 5 111 X Y) (g * h) := by
  unfold RepM at *
  rw [toMat_mulM, hX, hY, mat_mul]

theorem repM_id [LySeed] : RepM (idM 111) 1 := by
  unfold RepM
  rw [toMat_idM, mat_one]

theorem RepM.inv_of_check [LySeed]
    {X Y : Mat} {g : J} (hX : RepM X g) (h : mulM 5 111 X Y = idM 111) :
    RepM Y g⁻¹ := by
  have e := congrArg (toMat 5 111) h
  rw [toMat_mulM, toMat_idM, hX] at e
  have hinv : mat g⁻¹ * mat g = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]
  unfold RepM
  calc toMat 5 111 Y = (mat g⁻¹ * mat g) * toMat 5 111 Y := by rw [hinv, Matrix.one_mul]
    _ = mat g⁻¹ * (mat g * toMat 5 111 Y) := Matrix.mul_assoc _ _ _
    _ = mat g⁻¹ := by rw [e, Matrix.mul_one]

theorem RepM.unique [LySeed]
    {X : Mat} {g h : J} (hg : RepM X g) (hh : RepM X h) : g = h :=
  mat_injective (hg.symm.trans hh)

theorem repM_matA [LySeed] : RepM matA a := by
  unfold RepM
  rw [toMat_matA, mat_a]

theorem repM_matB [LySeed] : RepM matB b := by
  unfold RepM
  rw [toMat_matB, mat_b]

theorem b_inv' [LySeed] : b⁻¹ = b ^ 4 := by
  rw [inv_eq_iff_mul_eq_one, ← pow_succ']
  apply mat_injective
  rw [mat_one]
  show (mat b) ^ 5 = 1
  rw [mat_b, mB_pow]

theorem mat_pow' [LySeed] (g : J) (n : ℕ) : mat (g ^ n) = mat g ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, mat_one]
  | succ n ih => rw [pow_succ, pow_succ, mat_mul, ih]

theorem repM_b4 [LySeed] : RepM (powM 5 111 matB 4) b⁻¹ := by
  unfold RepM
  rw [toMat_powM, toMat_matB, b_inv', mat_pow', mat_b]

theorem repM_letter [LySeed]
    {g gi : ℕ → Mat} {gJ : ℕ → J} (hg : ∀ k, RepM (g k) (gJ k))
    (hgi : ∀ k, RepM (gi k) (gJ k)⁻¹) (l : ℤ) : RepM (letterM g gi l) (letterVal gJ l) := by
  unfold letterM letterVal
  split_ifs
  · exact hg _
  · exact hgi _

theorem repM_wordFrom [LySeed]
    {g gi : ℕ → Mat} {gJ : ℕ → J} (hg : ∀ k, RepM (g k) (gJ k))
    (hgi : ∀ k, RepM (gi k) (gJ k)⁻¹) (w : List ℤ) {X : Mat} {x : J} (hX : RepM X x) :
    RepM (wordFromM g gi X w) (x * evalWord gJ w) := by
  induction w generalizing X x with
  | nil => simpa [wordFromM, evalWord] using hX
  | cons l w ih =>
    have e : wordFromM g gi X (l :: w) = wordFromM g gi (mulM 5 111 X (letterM g gi l)) w := by
      simp only [wordFromM, List.foldl_cons]
    rw [e, evalWord_cons, ← mul_assoc]
    exact ih (hX.mul (repM_letter hg hgi l))

theorem repM_evalWordM [LySeed]
    {g gi : ℕ → Mat} {gJ : ℕ → J} (hg : ∀ k, RepM (g k) (gJ k))
    (hgi : ∀ k, RepM (gi k) (gJ k)⁻¹) (w : List ℤ) :
    RepM (evalWordM g gi w) (evalWord gJ w) := by
  have := repM_wordFrom hg hgi w repM_id
  rwa [one_mul] at this

theorem repM_seedM [LySeed] (k : ℕ) : RepM (seedM k) (seedFam k) := by
  by_cases hk : k = 0
  · simp only [seedM, seedFam, hk, ↓reduceIte]
    exact repM_matA
  · simp only [seedM, seedFam, hk, ↓reduceIte]
    exact repM_matB

theorem a_inv' [LySeed] : a⁻¹ = a := by
  rw [inv_eq_iff_mul_eq_one]
  apply mat_injective
  rw [mat_mul, mat_one, mat_a, mA_sq]

theorem repM_seedMInv [LySeed]
    (k : ℕ) : RepM (seedMInv (powM 5 111 matB 4) k) (seedFam k)⁻¹ := by
  by_cases hk : k = 0
  · simp only [seedMInv, seedFam, hk, ↓reduceIte]
    rw [a_inv']; exact repM_matA
  · simp only [seedMInv, seedFam, hk, ↓reduceIte]
    exact repM_b4

theorem repM_cSeed [LySeed] (j : ℕ) :
    RepM (evalWordM seedM (seedMInv (powM 5 111 matB 4)) (seedWord j)) (cSeed j) :=
  repM_evalWordM repM_seedM repM_seedMInv _

theorem pairAt_push_lt {acc : Array (Mat × Mat)} {p : Mat × Mat} {j : ℕ} (hj : j < acc.size) :
    pairAt (acc.push p) j = pairAt acc j := by
  simp [pairAt, Array.getD_eq_getD_getElem?, Array.getElem?_push, hj.ne]

theorem pairAt_push_size (acc : Array (Mat × Mat)) (p : Mat × Mat) :
    pairAt (acc.push p) acc.size = p := by
  simp [pairAt, Array.getD_eq_getD_getElem?]

theorem getD_append_length {α : Type*} (l : List α) (x d : α) :
    (l ++ [x]).getD l.length d = x := by
  simp [List.getD_eq_getElem?_getD]

theorem extendM_prefix (ws : List (List ℤ)) (acc : Array (Mat × Mat)) {j : ℕ}
    (hj : j < acc.size) : pairAt (extendM acc ws) j = pairAt acc j := by
  induction ws generalizing acc with
  | nil => rfl
  | cons w ws ih =>
    have e : extendM acc (w :: ws) = extendM (acc.push
        (evalWordM (fun i => (pairAt acc i).1) (fun i => (pairAt acc i).2) w,
          invM 5 111 (evalWordM (fun i => (pairAt acc i).1) (fun i => (pairAt acc i).2) w)))
          ws := by
      simp only [extendM, List.foldl_cons]
    rw [e, ih _ (by simp; omega), pairAt_push_lt hj]

theorem extendM_size (ws : List (List ℤ)) (acc : Array (Mat × Mat)) :
    (extendM acc ws).size = acc.size + ws.length := by
  induction ws generalizing acc with
  | nil => rfl
  | cons w ws ih =>
    have e : extendM acc (w :: ws) = extendM (acc.push
        (evalWordM (fun i => (pairAt acc i).1) (fun i => (pairAt acc i).2) w,
          invM 5 111 (evalWordM (fun i => (pairAt acc i).1) (fun i => (pairAt acc i).2) w)))
          ws := by
      simp only [extendM, List.foldl_cons]
    rw [e, ih]
    simp
    omega

theorem pairAt_of_ge {acc : Array (Mat × Mat)} {j : ℕ} (hj : acc.size ≤ j) :
    pairAt acc j = (idM 111, idM 111) := by
  simp [pairAt, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hj]

theorem invPairsOK_spec {cs : Array (Mat × Mat)} (h : invPairsOK cs = true) {j : ℕ}
    (hj : j < cs.size) : mulM 5 111 (pairAt cs j).1 (pairAt cs j).2 = idM 111 := by
  unfold invPairsOK at h
  rw [Array.all_eq_true] at h
  have := h j hj
  rw [beq_iff_eq] at this
  simpa [pairAt, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj] using this

theorem getD_of_ge [LySeed]
    {l : List J} {j : ℕ} (hj : l.length ≤ j) : l.getD j 1 = 1 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hj, Option.getD_none]

theorem repM_extendM [LySeed]
    (ws : List (List ℤ)) (acc : Array (Mat × Mat)) (l : List J)
    (hsize : acc.size = l.length) (hrep : ∀ j < acc.size, RepM (pairAt acc j).1 (l.getD j 1))
    (hinv : invPairsOK (extendM acc ws) = true) :
    ∀ j, RepM (pairAt (extendM acc ws) j).1 ((extendByWords l ws).getD j 1) ∧
      RepM (pairAt (extendM acc ws) j).2 ((extendByWords l ws).getD j 1)⁻¹ := by
  have first : ∀ (ws : List (List ℤ)) (acc : Array (Mat × Mat)) (l : List J),
      acc.size = l.length → (∀ j < acc.size, RepM (pairAt acc j).1 (l.getD j 1)) →
      invPairsOK (extendM acc ws) = true →
      ∀ j < (extendM acc ws).size,
        RepM (pairAt (extendM acc ws) j).1 ((extendByWords l ws).getD j 1) := by
    intro ws
    induction ws with
    | nil => intro acc l _ hrep _; exact hrep
    | cons w ws ih =>
      intro acc l hsize hrep hinv
      set X := evalWordM (fun i => (pairAt acc i).1) (fun i => (pairAt acc i).2) w with hXdef
      have e : extendM acc (w :: ws) = extendM (acc.push (X, invM 5 111 X)) ws := by
        simp only [extendM, List.foldl_cons, hXdef]
      rw [e] at hinv ⊢
      rw [extendByWords_cons]
      have hall : ∀ k, RepM (pairAt acc k).1 (l.getD k 1) ∧
          RepM (pairAt acc k).2 (l.getD k 1)⁻¹ := by
        intro k
        by_cases hk : k < acc.size
        · have h1 := hrep k hk
          refine ⟨h1, h1.inv_of_check ?_⟩
          have hk' : k < (extendM (acc.push (X, invM 5 111 X)) ws).size := by
            rw [extendM_size]; simp; omega
          have := invPairsOK_spec hinv hk'
          rwa [extendM_prefix _ _ (by simp; omega), pairAt_push_lt hk] at this
        · push Not at hk
          rw [pairAt_of_ge hk, getD_of_ge (by omega), inv_one]
          exact ⟨repM_id, repM_id⟩
      have hX : RepM X (evalWord (fun i => l.getD i 1) w) :=
        repM_evalWordM (fun k => (hall k).1) (fun k => (hall k).2) w
      apply ih _ _ (by simp [hsize]) _ hinv
      intro j hj
      rw [Array.size_push] at hj
      rcases Nat.lt_or_ge j acc.size with hlt | hge
      · rw [pairAt_push_lt hlt, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
        exact hrep j hlt
      · have hj' : j = acc.size := by omega
        subst hj'
        rw [pairAt_push_size, hsize, getD_append_length]
        exact hX
  intro j
  have hlen : (extendByWords l ws).length = (extendM acc ws).size := by
    rw [extendByWords_length, extendM_size, hsize]
  by_cases hj : j < (extendM acc ws).size
  · have h1 := first ws acc l hsize hrep hinv j hj
    exact ⟨h1, h1.inv_of_check (invPairsOK_spec hinv hj)⟩
  · push Not at hj
    rw [pairAt_of_ge hj, getD_of_ge (by omega), inv_one]
    exact ⟨repM_id, repM_id⟩

@[expose, irreducible] def csArr : Array (Mat × Mat) := cStarArr (powM 5 111 matB 4)

theorem csArr_def : csArr = cStarArr (powM 5 111 matB 4) := by unfold csArr; rfl

@[expose, irreducible] def tTab : Array (Array (Mat × Mat)) := transTab csArr

theorem tTab_def : tTab = transTab csArr := by unfold tTab; rfl

theorem cover_parts : csArr.size = 12 ∧ invPairsOK csArr = true ∧
    mulM 5 111 matA (pairAt csArr 0).1 = mulM 5 111 (pairAt csArr 0).1 matA ∧
    mulM 5 111 matA (pairAt csArr 1).1 = mulM 5 111 (pairAt csArr 1).1 matA ∧
    diffMod5 (pairAt csArr 0).1 (idM 111) = true ∧ diffMod5 (pairAt csArr 0).1 matA = true ∧
    transInvOK = true ∧ relOK csArr tTab = true ∧ (relResidue csArr tTab 0 1 0).2 = matA := by
  have h := ly_cover_certificate
  unfold coverCertificate at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [← csArr_def, ← tTab_def] at h
  obtain ⟨h, h10⟩ := h
  obtain ⟨h, h9⟩ := h
  obtain ⟨h, h8⟩ := h
  obtain ⟨h, h7⟩ := h
  obtain ⟨h, h6⟩ := h
  obtain ⟨h, h5⟩ := h
  obtain ⟨h, h4⟩ := h
  obtain ⟨h, h3⟩ := h
  obtain ⟨-, h2⟩ := h
  exact ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem toMat_ne_of_diffMod5 {X Y : Mat} (h : diffMod5 X Y = true) :
    toMat 5 111 X ≠ toMat 5 111 Y := by
  unfold diffMod5 at h
  simp only [List.any_eq_true, List.mem_range, bne_iff_ne, ne_eq] at h
  obtain ⟨r, hr, c, hc, hne⟩ := h
  intro e
  have := congrFun (congrFun e ⟨r, hr⟩) ⟨c, hc⟩
  rw [toMat_apply, toMat_apply] at this
  exact hne ((ZMod.natCast_eq_natCast_iff' _ _ 5).1 this)

theorem repM_csArr [LySeed]
    (j : ℕ) : RepM (pairAt csArr j).1 (cStar j) ∧
    RepM (pairAt csArr j).2 (cStar j)⁻¹ := by
  set c0 := evalWordM seedM (seedMInv (powM 5 111 matB 4)) seedWord0 with hc0
  set c1 := evalWordM seedM (seedMInv (powM 5 111 matB 4)) seedWord1 with hc1
  have hcs : csArr = extendM #[(c0, invM 5 111 c0), (c1, invM 5 111 c1)] cDerivations.toList := by
    rw [csArr_def]; rfl
  have hstart : ∀ j < (#[(c0, invM 5 111 c0), (c1, invM 5 111 c1)] : Array (Mat × Mat)).size,
      RepM (pairAt #[(c0, invM 5 111 c0), (c1, invM 5 111 c1)] j).1
        ([cSeed 0, cSeed 1].getD j 1) := by
    intro j hj
    have hj2 : j < 2 := by simpa using hj
    interval_cases j
    · exact repM_cSeed 0
    · exact repM_cSeed 1
  have hinv := cover_parts.2.1
  rw [hcs] at hinv ⊢
  exact repM_extendM _ _ [cSeed 0, cSeed 1] rfl hstart hinv j

theorem cSeed_mem [LySeed] (i : Fin 2) : cSeed i ∈ lyC := by
  fin_cases i
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] def cC [LySeed] (i : Fin 2) : lyC := ⟨cSeed i, cSeed_mem i⟩

theorem closure_cC [LySeed] : Subgroup.closure (Set.range cC) = ⊤ := by
  have h : Set.range cC = ((↑) : lyC → J) ⁻¹' {cSeed 0, cSeed 1} := by
    ext x
    simp only [Set.mem_range, Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · left; rfl
      · right; rfl
    · rintro (h | h)
      · exact ⟨0, Subtype.ext h.symm⟩
      · exact ⟨1, Subtype.ext h.symm⟩
  rw [h]
  exact Subgroup.closure_closure_coe_preimage

theorem lift_cC_strongF [LySeed]
    (j : ℕ) : ((FreeGroup.lift cC (strongF j) : lyC) : J) = cStar j := by
  rw [strongF, strongList, map_getD_extendByWords]
  have := map_getD_extendByWords lyC.subtype [FreeGroup.lift cC (FreeGroup.of 0),
    FreeGroup.lift cC (FreeGroup.of 1)] cDerivations.toList j
  simp only [List.map_cons, List.map_nil, FreeGroup.lift_apply_of] at this ⊢
  rw [Subgroup.coe_subtype] at this
  exact this

theorem cStar_mem [LySeed] (j : ℕ) : cStar j ∈ lyC := by
  rw [← lift_cC_strongF]
  exact (FreeGroup.lift cC (strongF j)).2

theorem coe_lift_cC_transversal [LySeed]
    (i : Fin lyChain.baseCount) (x : Fin 11) :
    ((FreeGroup.lift cC (lyChain.transversal i x) : lyC) : J) = ((twWord i x).map cStar).prod := by
  change ((FreeGroup.lift cC ((twWord i x).map strongF).prod : lyC) : J) = _
  rw [map_list_prod, ← Subgroup.coe_subtype, map_list_prod, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  exact lift_cC_strongF j

theorem repM_foldl_fst [LySeed]
    (L : List ℕ) {X : Mat} {x : J} (hX : RepM X x) :
    RepM (L.foldl (fun X j => mulM 5 111 X (pairAt csArr j).1) X) (x * (L.map cStar).prod) := by
  induction L generalizing X x with
  | nil => simpa using hX
  | cons j L ih =>
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    exact ih (hX.mul (repM_csArr j).1)

theorem repM_foldl_snd [LySeed]
    (L : List ℕ) {X : Mat} {x : J} (hX : RepM X x) :
    RepM (L.foldl (fun X j => mulM 5 111 X (pairAt csArr j).2) X)
      (x * (L.map fun j => (cStar j)⁻¹).prod) := by
  induction L generalizing X x with
  | nil => simpa using hX
  | cons j L ih =>
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    exact ih (hX.mul (repM_csArr j).2)

theorem tabAt_tTab {i x : ℕ} (hi : i < 11) (hx : x < 11) : tabAt tTab i x =
    ((twWord i x).foldl (fun X j => mulM 5 111 X (pairAt csArr j).1) (idM 111),
      (twWord i x).reverse.foldl (fun X j => mulM 5 111 X (pairAt csArr j).2) (idM 111)) := by
  simp only [tabAt, tTab, transTab, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hi, hx,
    dite_true, Option.getD_some]

theorem repM_tabAt [LySeed] (i x : Fin 11) :
    RepM (tabAt tTab i x).1 ((FreeGroup.lift cC (lyChain.transversal i x) : lyC) : J) ∧
    RepM (tabAt tTab i x).2 ((FreeGroup.lift cC (lyChain.transversal i x) : lyC) : J)⁻¹ := by
  rw [tabAt_tTab i.isLt x.isLt, coe_lift_cC_transversal i x]
  refine ⟨by simpa using repM_foldl_fst (twWord i x) repM_id, ?_⟩
  have := repM_foldl_snd (twWord i x).reverse repM_id
  rw [one_mul, List.prod_inv_reverse] at *
  simpa [List.map_reverse, Function.comp_def] using this

theorem chainOrbits_lt : ∀ i : Fin 11, ∀ n ∈ chainOrbits[i.val]!, n < 11 := by decide +kernel

theorem mem_chainOrbit {i : Fin 11} {x : Fin 11} (hx : x ∈ chainOrbit i) :
    x.val ∈ chainOrbits[i.val]! := by
  unfold chainOrbit at hx
  rw [List.mem_toFinset, List.mem_map] at hx
  obtain ⟨n, hn, rfl⟩ := hx
  simpa [Nat.mod_eq_of_lt (chainOrbits_lt i n hn)] using hn

theorem transInv_parts (i x : Fin 11) :
    compP (tPArr i x) (invP (tPArr i x)) = id11 ∧
      ∀ y : Fin 11, (invP (tPArr i x))[y.val]! < 11 := by
  have h := cover_parts.2.2.2.2.2.2.1
  unfold transInvOK at h
  have := (allIn_eq_true.1 ((allIn_eq_true.1 h) i (Nat.zero_le _) i.isLt)) x (Nat.zero_le _)
    x.isLt
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq] at this
  refine ⟨this.1, fun y => ?_⟩
  have hsz : (invP (tPArr i x)).size = 11 := by simp [invP]
  have := this.2 y.val (by rw [hsz]; exact y.isLt)
  rwa [getElem!_pos _ y.val (by rw [hsz]; exact y.isLt)]

theorem repP_invP
    (i x : Fin 11) : RepP (invP (tPArr i x)) (twPerm i x)⁻¹ :=
  (repP_tPArr i x).inv_of_check (transInv_parts i x).1 (transInv_parts i x).2

@[expose] def RepW [LySeed]
    (st : Array ℕ × Mat) (v : FreeGroup (Fin 2)) : Prop :=
  RepP st.1 (FreeGroup.lift pGen v) ∧ RepM st.2 ((FreeGroup.lift cC v : lyC) : J)

theorem repW_strip [LySeed]
    (st : Array ℕ × Mat) (v : FreeGroup (Fin 2)) (h : RepW st v) (l : Fin 11) :
    RepW (stripStep tTab st l)
      ((lyChain.transversal l (FreeGroup.lift pGen v (lyChain.base l)))⁻¹ * v) := by
  obtain ⟨hP, hX⟩ := h
  set y := FreeGroup.lift pGen v l with hy
  have hyv : st.1[l.val]! = y.val := hP l
  have hb : lyChain.base l = l := rfl
  refine ⟨?_, ?_⟩
  · simp only [stripStep, hyv, map_mul, map_inv, hb]
    rw [lift_transversal (i := l) (x := y)]
    exact (repP_invP l y).comp hP
  · simp only [stripStep, hyv, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hb]
    exact (repM_tabAt l y).2.mul hX

theorem residue_levels (i : ℕ) :
    ((List.finRange lyChain.baseCount).filter fun l => decide (i < l.val)).map Fin.val =
      (List.range 11).filter fun l => decide (i < l) := by
  change ((List.finRange 11).filter fun l => decide (i < l.val)).map Fin.val = _
  rw [← List.map_coe_finRange_eq_range, List.filter_map]
  rfl

theorem repW_residue [LySeed]
    (i : ℕ) (st : Array ℕ × Mat) (u : FreeGroup (Fin 2)) (h : RepW st u) :
    RepW (((List.range 11).filter fun l => decide (i < l)).foldl (stripStep tTab) st)
      (lyChain.residue pGen i u) := by
  rw [← residue_levels, List.foldl_map]
  unfold SchreierWordChain.residue
  generalize ((List.finRange lyChain.baseCount).filter fun l => decide (i < l.val)) = L
  induction L generalizing st u with
  | nil => exact h
  | cons l L ih =>
    rw [List.foldl_cons, List.foldl_cons]
    exact ih _ _ (repW_strip st u h l)

theorem repW_relResidue [LySeed]
    (i : Fin 11) (x : Fin 11) (j : Fin 12) :
    RepW (relResidue csArr tTab i x j)
      (lyChain.residue pGen i (lyChain.schreierElement pGen i x j)) := by
  unfold relResidue
  apply repW_residue
  have hpj : (pArr j)[x.val]! = (pPerm j x).val := repP_pArr j.isLt x
  have hs : FreeGroup.lift pGen (lyChain.strong j) x = pPerm j x := by rw [lift_strong j]
  refine ⟨?_, ?_⟩
  · simp only [hpj, SchreierWordChain.schreierElement, map_mul, map_inv,
      lift_transversal (i := i), lift_strong j]
    rw [mul_assoc]
    exact (repP_invP i (pPerm j x)).comp ((repP_pArr j.isLt).comp (repP_tPArr i x))
  · simp only [hpj, SchreierWordChain.schreierElement, map_mul, map_inv, hs,
      Subgroup.coe_mul, Subgroup.coe_inv]
    change RepM _ (((FreeGroup.lift cC (lyChain.transversal i (pPerm j x)) : lyC) : J)⁻¹ *
      ((FreeGroup.lift cC (strongF j) : lyC) : J) *
      ((FreeGroup.lift cC (lyChain.transversal i x) : lyC) : J))
    rw [lift_cC_strongF, mul_assoc]
    exact (repM_tabAt i (pPerm j x)).2.mul ((repM_csArr j).1.mul (repM_tabAt i x).1)

theorem fixesBelow_iff (j : Fin 12) (i : ℕ) (hi : i ≤ 11) :
    fixesBelow j i = true ↔ ∀ l : Fin 11, l.val < i → pPerm j l = l := by
  unfold fixesBelow
  rw [allIn_eq_true]
  constructor
  · intro h l hl
    have := h l.val (Nat.zero_le _) hl
    rw [beq_iff_eq, repP_pArr j.isLt l] at this
    exact Fin.ext this
  · intro h l _ hl
    rw [beq_iff_eq, repP_pArr j.isLt ⟨l, by omega⟩, h ⟨l, by omega⟩ hl]

theorem rel_parts
    (i : Fin 11) (x : Fin 11) (hx : x ∈ chainOrbit i) (j : Fin 12)
    (hj : ∀ l : Fin 11, l.val < i.val → pPerm j l = l) :
    (relResidue csArr tTab i x j).1 = id11 ∧
      ((relResidue csArr tTab i x j).2 = idM 111 ∨ (relResidue csArr tTab i x j).2 = matA) := by
  have h := cover_parts.2.2.2.2.2.2.2.1
  unfold relOK at h
  have h1 := (allIn_eq_true.1 h) i (Nat.zero_le _) i.isLt
  rw [List.all_eq_true] at h1
  have h2 := h1 x.val (mem_chainOrbit hx)
  have h3 := (allIn_eq_true.1 h2) j (Nat.zero_le _) j.isLt
  rw [(fixesBelow_iff j i (by omega)).2 hj] at h3
  simpa [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] using h3

end CFSG.Sporadic.LySchreier
