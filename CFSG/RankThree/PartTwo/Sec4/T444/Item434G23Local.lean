module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G23Words
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CoverFinal
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Gen
public import CFSG.Certificates.Kernel.ThDemp.Sound
public import CFSG.Permutation.AlternatingAutomorphism

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434RemG23

open CFSG.RankThree.PartTwo.Census.Carrier.G2Three CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec4.Item434Cover
open CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest

local notation "M14" => Matrix (Fin 14) (Fin 14) (ZMod 3)
local notation "GL14" => GL (Fin 14) (ZMod 3)

attribute [local irreducible] tArr tCodes zCodes pathsArr

theorem sylWord_lt : ∀ l ∈ sylWord, l < 8 := by decide

theorem zOK_of_k2Check (h : k2Check = true) : zOK = true := by
  simp only [k2Check, Bool.and_eq_true] at h
  exact h.1.1

theorem wordsOK_of_coverCheck (h : coverCheck = true) : wordsOK = true := by
  simp only [coverCheck, Bool.and_eq_true] at h
  exact h.1.1.1

theorem eq_of_code {g g' : GL14} {c : List ℕ} (h : (g : M14) = dec14 c)
    (h' : (g' : M14) = dec14 c) : g = g' :=
  Units.ext (h.trans h'.symm)

theorem coe_pow14 {g : GL14} {c : List ℕ} (h : (g : M14) = dec14 c) {k : ℕ} (hk : k < 3) :
    ((g ^ k : GL14) : M14) = dec14 (pow14 c k) := by
  unfold pow14
  interval_cases k
  · simp [dec14_one14]
  · simpa using h
  · simpa using coe_sq h

theorem coe_cube14 {g : GL14} {c : List ℕ} (h : (g : M14) = dec14 c) :
    ((g ^ 3 : GL14) : M14) = dec14 (cube14 c) := by
  have h2 := coe_sq h
  have := coe_mul h (show ((g ^ 2 : GL14) : M14) = dec14 (sq14 c) from h2)
  rw [cube14]
  rw [show g ^ 3 = g * g ^ 2 by group]
  exact this

theorem cube14_eq_one {g : GL14} {c : List ℕ} (h : (g : M14) = dec14 c) (h3 : g ^ 3 = 1) :
    cube14 c = one14 := by
  have h1 := coe_cube14 h
  rw [h3, Units.val_one] at h1
  exact dec14_injective (canon14_mul14 _ _) canon14_one14 (by rw [← h1, dec14_one14])

theorem pow_three_of_cube14 {g : GL14} {c : List ℕ} (h : (g : M14) = dec14 c)
    (hc : cube14 c = one14) : g ^ 3 = 1 := by
  refine Units.ext ?_
  rw [coe_cube14 h, hc, dec14_one14, Units.val_one]

theorem mul14_assoc (a b c : List ℕ) : mul14 (mul14 a b) c = mul14 a (mul14 b c) :=
  dec14_injective (canon14_mul14 _ _) (canon14_mul14 _ _) (by
    rw [dec14_mul14, dec14_mul14, dec14_mul14, dec14_mul14, mul_assoc])

theorem mul14_one {x : List ℕ} (hx : canon14 x = true) : mul14 x one14 = x :=
  dec14_injective (canon14_mul14 _ _) hx (by rw [dec14_mul14, dec14_one14, mul_one])

theorem sylAt_def (t : ℕ) : sylAt t = sylElems.getD t [] := rfl

attribute [local irreducible] sylAt

theorem sylCheck_parts (h : sylCheck = true) :
    sylElems.size = 729 ∧ closedCheck mul14 sylGens sylElems = true ∧
      distinctCheck sylElems = true ∧ allCheck canon14 sylElems = true ∧ RootCubes := by
  simp only [sylCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, h4, fun l hl => ?_⟩
  have := h5 (rootCode l) (by
    unfold rootCode
    interval_cases l <;> simp)
  simpa using this

theorem wordsOK_parts (h : wordsOK = true) :
    (∀ l ∈ sylWord, l < 8) ∧ (∀ w ∈ conjWords, ∀ l ∈ w, l < 8) ∧
      (∀ w ∈ liftG, ∀ l ∈ w, l < 8) := by
  simp only [wordsOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem zOK_parts (h : zOK = true) :
    (∀ i ∈ sylZ, i < 729 ∧ ∀ c ∈ sylGens, commutes (sylAt i) c = true) := by
  simp only [zOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact fun i hi => h.1.1.1.1 i hi

theorem canon14_sylAt (hsyl : sylCheck = true) {t : ℕ} (ht : t < 729) :
    canon14 (sylAt t) = true := by
  obtain ⟨hsize, -, -, hcanon, -⟩ := sylCheck_parts hsyl
  have h := allCheck_spec (p := canon14) (es := sylElems) hcanon (t := t) (ht.trans_eq hsize.symm)
  rw [sylAt_def]
  exact h

theorem sylAt_inj (hsyl : sylCheck = true) {t t' : ℕ} (ht : t < 729) (ht' : t' < 729)
    (h : sylAt t = sylAt t') : t = t' := by
  obtain ⟨hsize, -, hdist, -⟩ := sylCheck_parts hsyl
  rw [sylAt_def, sylAt_def] at h
  exact distinctCheck_spec hdist (ht.trans_eq hsize.symm) (ht'.trans_eq hsize.symm) h

theorem sylAt_zero : sylAt 0 = one14 := by
  rw [sylAt_def]
  unfold sylElems
  exact build_getD_zero one14 mul14 sylGens sylPar

attribute [local irreducible] rtTab

def pathProd (path : List ℕ) (x : List ℕ) : List ℕ :=
  path.foldl (fun c s => mul14 c (sylGens.getD s one14)) x

theorem pathProd_mul (path : List ℕ) : ∀ x y : List ℕ,
    pathProd path (mul14 x y) = mul14 x (pathProd path y) := by
  induction path with
  | nil => intro x y; rfl
  | cons s path ih =>
    intro x y
    simp only [pathProd, List.foldl_cons] at ih ⊢
    rw [mul14_assoc, ih x (mul14 y (sylGens.getD s one14))]

theorem rtStep_spec (hsyl : sylCheck = true) {m : Std.HashMap (List ℕ) ℕ}
    (hrt : rtOK m = true) {i s : ℕ} (hi : i < 729) (hs : s < 3) :
    rtStep (rtTab m) i s < 729 ∧
      sylAt (rtStep (rtTab m) i s) = mul14 (sylAt i) (sylGens.getD s one14) := by
  obtain ⟨hsize, -⟩ := sylCheck_parts hsyl
  have hstep : rtStep (rtTab m) i s = rtIdx m i s := by
    simp [rtStep, rtTab, Array.getD_eq_getD_getElem?, hi, hs]
  have hf := (List.all_eq_true.1 (List.all_eq_true.1 hrt i (List.mem_range.2 hi)) s
    (List.mem_range.2 hs))
  rw [hstep]
  unfold found at hf
  unfold rtIdx
  cases hget : m.get? (mul14 (sylAt i) (sylGens.getD s one14)) with
  | none => rw [hget] at hf; exact absurd hf Bool.false_ne_true
  | some t =>
    rw [hget] at hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
    refine ⟨?_, ?_⟩
    · simpa using hf.1.trans_eq hsize
    · simp only [Option.getD_some]
      rw [sylAt_def]
      exact hf.2

theorem foldl_rtStep_spec (hsyl : sylCheck = true) {m : Std.HashMap (List ℕ) ℕ}
    (hrt : rtOK m = true) :
    ∀ (path : List ℕ), (∀ s ∈ path, s < 3) → ∀ i < 729,
      path.foldl (rtStep (rtTab m)) i < 729 ∧
        sylAt (path.foldl (rtStep (rtTab m)) i) = pathProd path (sylAt i) := by
  intro path
  induction path with
  | nil => intro _ i hi; exact ⟨hi, rfl⟩
  | cons s path ih =>
    intro hpath i hi
    obtain ⟨h1, h2⟩ := rtStep_spec hsyl hrt hi (hpath s (List.mem_cons_self ..))
    have h3 := ih (fun s' hs' => hpath s' (List.mem_cons_of_mem _ hs')) _ h1
    rw [List.foldl_cons]
    refine ⟨h3.1, ?_⟩
    rw [h3.2, h2]
    rfl

theorem mulIdx_spec (hsyl : sylCheck = true) {m : Std.HashMap (List ℕ) ℕ}
    (hrt : rtOK m = true) (hpath : pathOK (rtTab m) = true)
    {a b : ℕ} (ha : a < 729) (hb : b < 729) :
    mulIdx (rtTab m) a b < 729 ∧
      sylAt (mulIdx (rtTab m) a b) = mul14 (sylAt a) (sylAt b) := by
  have hp := List.all_eq_true.1 hpath b (List.mem_range.2 hb)
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
  obtain ⟨hp3, hp0⟩ := hp
  have h0 := foldl_rtStep_spec hsyl hrt (pathsArr.getD b []) hp3 0 (by norm_num)
  have h1 := foldl_rtStep_spec hsyl hrt (pathsArr.getD b []) hp3 a ha
  rw [hp0, sylAt_zero] at h0
  refine ⟨h1.1, ?_⟩
  have h2 := pathProd_mul (pathsArr.getD b []) (sylAt a) one14
  rw [mul14_one (canon14_sylAt hsyl ha)] at h2
  unfold mulIdx
  rw [h1.2, h0.2, h2]

theorem mulIdx_main (hsyl : sylCheck = true) (hrt : rtOK (indexMap sylElems) = true)
    (hpath : pathOK rtMain = true) {a b : ℕ} (ha : a < 729) (hb : b < 729) :
    mulIdx rtMain a b < 729 ∧ sylAt (mulIdx rtMain a b) = mul14 (sylAt a) (sylAt b) :=
  mulIdx_spec hsyl hrt hpath ha hb

theorem nArr_getD {ia : ℕ} (h : ia < 729) : nArr.getD ia false = isN ia := by
  simp [nArr, Array.getD_eq_getD_getElem?, h]

theorem coverCheck_parts (h : coverCheck = true) :
    wordsOK = true ∧ rtOK (indexMap sylElems) = true ∧ pathOK rtMain = true ∧
      ∀ ia < 729, isN ia = true → ∀ ib < 729, isN ib = true →
        ib = ia ∨ ib = mulIdx rtMain ia ia ∨ mulIdx rtMain ia ib ≠ mulIdx rtMain ib ia ∨
          tArr.getD (mulIdx rtMain ia ib) false = true ∨
          tArr.getD (mulIdx rtMain (mulIdx rtMain ia ib) ib) false = true := by
  simp only [coverCheck, coverLoop, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hw, hrt⟩, hpath⟩, hall⟩ := h
  refine ⟨hw, hrt, hpath, fun ia hia hNa ib hib hNb => ?_⟩
  have h1 := List.all_eq_true.1 hall ia (List.mem_range.2 hia)
  rw [nArr_getD hia, hNa] at h1
  simp only [Bool.not_true, Bool.false_or] at h1
  have h2 := List.all_eq_true.1 h1 ib (List.mem_range.2 hib)
  rw [nArr_getD hib, hNb] at h2
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq, or_assoc] at h2
  exact h2

def prodElem4 {Y : Type*} [Group Y] (e : Fin 4 → Y) (u : ℕ) : Y :=
  e 0 ^ (u % 3) * e 1 ^ (u / 3 % 3) * e 2 ^ (u / 9 % 3) * e 3 ^ (u / 27 % 3)

theorem coe_prodElem4 {e : Fin 4 → GL14} {cs : Fin 4 → List ℕ}
    (h : ∀ j, (e j : M14) = dec14 (cs j)) (u : ℕ) :
    ((prodElem4 e u : GL14) : M14) =
      dec14 (mul14 (mul14 (mul14 (pow14 (cs 0) (u % 3)) (pow14 (cs 1) (u / 3 % 3)))
        (pow14 (cs 2) (u / 9 % 3))) (pow14 (cs 3) (u / 27 % 3))) := by
  unfold prodElem4
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_pow14 (h 0) (Nat.mod_lt _ (by norm_num)),
    coe_pow14 (h 1) (Nat.mod_lt _ (by norm_num)), coe_pow14 (h 2) (Nat.mod_lt _ (by norm_num)),
    coe_pow14 (h 3) (Nat.mod_lt _ (by norm_num)), dec14_mul14, dec14_mul14, dec14_mul14]

theorem prodElem4_mem {e : Fin 4 → GL14} (u : ℕ) :
    prodElem4 e u ∈ Subgroup.closure (Set.range e) :=
  mul_mem (mul_mem (mul_mem (pow_mem (Subgroup.subset_closure (Set.mem_range_self 0)) _)
    (pow_mem (Subgroup.subset_closure (Set.mem_range_self 1)) _))
    (pow_mem (Subgroup.subset_closure (Set.mem_range_self 2)) _))
    (pow_mem (Subgroup.subset_closure (Set.mem_range_self 3)) _)

theorem dArr_getD (D : List ℕ) {u : ℕ} (hu : u < 81) : (dArr D).getD u [] = dProd D u := by
  simp [dArr, Array.getD_eq_getD_getElem?, hu]

def prodElem3 {Y : Type*} [Group Y] (e : Fin 3 → Y) (u : ℕ) : Y :=
  e 0 ^ (u % 3) * e 1 ^ (u / 3 % 3) * e 2 ^ (u / 9 % 3)

theorem coe_prodElem3 {e : Fin 3 → GL14} {c0 c1 c2 : List ℕ} (h0 : (e 0 : M14) = dec14 c0)
    (h1 : (e 1 : M14) = dec14 c1) (h2 : (e 2 : M14) = dec14 c2) (u : ℕ) :
    ((prodElem3 e u : GL14) : M14) =
      dec14 (mul14 (mul14 (pow14 c0 (u % 3)) (pow14 c1 (u / 3 % 3))) (pow14 c2 (u / 9 % 3))) := by
  unfold prodElem3
  rw [Units.val_mul, Units.val_mul, coe_pow14 h0 (Nat.mod_lt _ (by norm_num)),
    coe_pow14 h1 (Nat.mod_lt _ (by norm_num)), coe_pow14 h2 (Nat.mod_lt _ (by norm_num)),
    dec14_mul14, dec14_mul14]

theorem liftCheck_parts (h : liftCheck = true) :
    liftW.length = 3 ∧ (∀ i ∈ liftW, i < 729) ∧ liftG.length = 2 ∧ liftM.length = 2 ∧
      (∀ a < 3, ∀ b < 3, commutes (liftEl a) (liftEl b) = true) ∧
      (∀ a < 3, cube14 (liftEl a) = one14) ∧
      distinctCheck ((List.range 27).map liftProd).toArray = true ∧
      (∀ j < 2, ∀ k < 3, ∀ i < 3, liftMat j k i < 3) ∧
      (∀ j < 2, ∀ i < 3, conjStep (wordPair (liftG.getD j [])) (liftEl i) = liftRhs j i) := by
  simp only [liftCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

section Sylow


noncomputable def sylow : Subgroup GL14 :=
  Subgroup.closure {gX 0, gX 1, wordElem sylWord}

theorem image_gens_sylow (hc : RootCubes) (hw : ∀ l ∈ sylWord, l < 8) :
    (Units.coeHom M14) '' {gX 0, gX 1, wordElem sylWord} =
      {y | ∃ c ∈ sylGens, dec14 c = y} := by
  ext y
  simp only [Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_ofPred_eq, sylGens, List.mem_cons, List.not_mem_nil,
    or_false, exists_eq_or_imp, exists_eq_left, Units.coeHom_apply, coe_gX0, coe_gX1,
    coe_wordElem hc sylWord hw, @eq_comm _ (dec14 _) y]

theorem sylow_le_R3 (hw : ∀ l ∈ sylWord, l < 8) : sylow ≤ R3 := by
  rw [sylow, Subgroup.closure_le]
  rintro g (rfl | rfl | rfl)
  · exact gX_mem 0
  · exact gX_mem 1
  · exact wordElem_mem _ hw

theorem image_sylow (hsyl : sylCheck = true) (hw : ∀ l ∈ sylWord, l < 8) :
    (Units.coeHom M14) '' (sylow : Set GL14) =
      {y | ∃ t < sylElems.size, dec14 (sylElems.getD t []) = y} := by
  obtain ⟨-, hclosed, -, -, hc⟩ := sylCheck_parts hsyl
  exact image_closure_eq dec14 one14 mul14 sylGens (Units.coeHom M14) dec14_one14 dec14_mul14 _
    (image_gens_sylow hc hw) sylPar hclosed

theorem card_sylow (hsyl : sylCheck = true) (hw : ∀ l ∈ sylWord, l < 8) :
    Nat.card sylow = 729 := by
  obtain ⟨hsize, hclosed, hdist, hcanon, hc⟩ := sylCheck_parts hsyl
  refine (card_closure_eq dec14 one14 mul14 sylGens (Units.coeHom M14) Units.val_injective
    dec14_one14 dec14_mul14 _ (image_gens_sylow hc hw) sylPar hclosed hdist
    fun t ht t' ht' e => ?_).trans hsize
  exact dec14_injective (allCheck_spec hcanon ht) (allCheck_spec hcanon ht') e

theorem exists_code_sylow (hsyl : sylCheck = true) (hw : ∀ l ∈ sylWord, l < 8) {g : GL14}
    (hg : g ∈ sylow) : ∃ t < 729, dec14 (sylAt t) = (g : M14) := by
  have h : (Units.coeHom M14) g ∈ (Units.coeHom M14) '' (sylow : Set GL14) := ⟨g, hg, rfl⟩
  rw [image_sylow hsyl hw] at h
  obtain ⟨t, ht, e⟩ := h
  obtain ⟨hsize, -⟩ := sylCheck_parts hsyl
  refine ⟨t, ht.trans_eq hsize, ?_⟩
  rw [sylAt_def]
  exact e

theorem exists_elem_of_code (hsyl : sylCheck = true) (hw : ∀ l ∈ sylWord, l < 8) {t : ℕ}
    (ht : t < 729) : ∃ g ∈ sylow, dec14 (sylAt t) = (g : M14) := by
  have h : dec14 (sylElems.getD t []) ∈
      {y | ∃ t < sylElems.size, dec14 (sylElems.getD t []) = y} := by
    obtain ⟨hsize, -⟩ := sylCheck_parts hsyl
    exact ⟨t, ht.trans_eq hsize.symm, rfl⟩
  rw [← image_sylow hsyl hw] at h
  obtain ⟨g, hg, e⟩ := h
  refine ⟨g, hg, ?_⟩
  rw [sylAt_def]
  exact e.symm

theorem central_of_commutes (hc : RootCubes) (hw : ∀ l ∈ sylWord, l < 8) {z : GL14}
    {cz : List ℕ} (hz : (z : M14) = dec14 cz) (h : ∀ c ∈ sylGens, commutes cz c = true) :
    ∀ q ∈ sylow, q * z = z * q := by
  have hle : sylow ≤ Subgroup.centralizer ({z} : Set GL14) := by
    rw [sylow, Subgroup.closure_le]
    rintro g (rfl | rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (commute_of_commutes hz coe_gX0 (h x0c (by simp [sylGens]))).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (commute_of_commutes hz coe_gX1 (h x1c (by simp [sylGens]))).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (commute_of_commutes hz (coe_wordElem hc sylWord hw) (h _ (by simp [sylGens]))).symm
  exact fun q hq => Subgroup.mem_centralizer_singleton_iff.mp (hle hq)

theorem exists_z (hsyl : sylCheck = true) (hz : zOK = true) (hw : ∀ l ∈ sylWord, l < 8) :
    ∃ z ∈ sylow, dec14 (sylAt sylZIdx) = (z : M14) ∧ z ^ 3 = 1 ∧ z ≠ 1 ∧
      ∀ q ∈ sylow, q * z = z * q := by
  obtain ⟨-, -, -, -, hc⟩ := sylCheck_parts hsyl
  simp only [zOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hz
  obtain ⟨⟨⟨⟨-, hidx⟩, hcomm⟩, hcube⟩, hne⟩ := hz
  obtain ⟨z, hzS, hzc⟩ := exists_elem_of_code hsyl hw hidx
  refine ⟨z, hzS, hzc, pow_three_of_cube14 hzc.symm hcube, fun h1 => hne ?_,
    central_of_commutes hc hw hzc.symm hcomm⟩
  have : (z : M14) = dec14 one14 := by rw [h1, Units.val_one, dec14_one14]
  exact dec14_injective (canon14_sylAt hsyl hidx) canon14_one14 (hzc.trans this)

theorem exists_E (hsyl : sylCheck = true) (hw : ∀ l ∈ sylWord, l < 8) {z : GL14}
    (hzc : dec14 (sylAt sylZIdx) = (z : M14)) (D : List ℕ) (hD : dOK D = true) :
    ∃ E : Subgroup GL14, E ≤ sylow ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧
      z ∈ E ∧ ∀ u < 81, ∃ g ∈ E, dec14 (dProd D u) = (g : M14) := by
  obtain ⟨-, -, -, -, hc⟩ := sylCheck_parts hsyl
  simp only [dOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    beq_iff_eq] at hD
  obtain ⟨⟨⟨⟨⟨hlen, hlt⟩, hcomm⟩, hcube⟩, hdist⟩, hfound⟩ := hD
  have hlt4 : ∀ j : Fin 4, D.getD j 0 < 729 := fun j => by
    have hj : (j : ℕ) < D.length := by omega
    rw [List.getD_eq_getElem _ _ hj]
    exact hlt _ (List.getElem_mem hj)
  choose e he hec using fun j : Fin 4 => exists_elem_of_code hsyl hw (hlt4 j)
  have hecode : ∀ j : Fin 4, (e j : M14) = dec14 (dEl D j) := fun j => (hec j).symm
  have hcan : ∀ j : Fin 4, canon14 (dEl D j) = true := fun j => canon14_sylAt hsyl (hlt4 j)
  have hprod : ∀ u : ℕ, ((prodElem4 e u : GL14) : M14) = dec14 (dProd D u) := fun u =>
    coe_prodElem4 (cs := fun j => dEl D j) (fun j => hecode j) u
  have hprodmem := fun u => prodElem4_mem (e := e) u
  refine ⟨Subgroup.closure (Set.range e), ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact he j
  · refine Item434SporE81.isElemAbelian_closure_of_comm ?_ ?_
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      exact commute_of_commutes (hecode a) (hecode b) (hcomm a a.2 b b.2)
    · rintro _ ⟨a, rfl⟩
      exact pow_three_of_cube14 (hecode a) (hcube a a.2)
  · have hinj : Function.Injective
        (fun u : Fin 81 => (⟨prodElem4 e u, hprodmem u⟩ : Subgroup.closure (Set.range e))) := by
      intro u u' h
      have h1 : prodElem4 e u = prodElem4 e u' := congrArg Subtype.val h
      have h2 : dProd D u = dProd D u' := by
        refine dec14_injective (canon14_mul14 _ _) (canon14_mul14 _ _) ?_
        rw [← hprod, ← hprod, h1]
      have h3 := distinctCheck_spec hdist (t := u) (t' := u') (by simp [dArr])
        (by simp [dArr]) (by rw [dArr_getD D u.2, dArr_getD D u'.2, h2])
      exact Fin.ext h3
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  · obtain ⟨t, ht, ht'⟩ := found_spec hfound
    have ht81 : t < 81 := by simpa [dArr] using ht
    rw [dArr_getD D ht81] at ht'
    have : prodElem4 e t = z := by
      refine eq_of_code (hprod t) ?_
      rw [ht', hzc]
    rw [← this]
    exact hprodmem t
  · intro u hu
    exact ⟨prodElem4 e u, hprodmem u, (hprod u).symm⟩

theorem exists_hgood (hsyl : sylCheck = true) (hk2 : k2Check = true) (hw : ∀ l ∈ sylWord, l < 8) :
    ∃ z ∈ sylow, z ^ 3 = 1 ∧ z ≠ 1 ∧ (∀ q ∈ sylow, q * z = z * q) ∧
      ∀ s ∈ sylow, s ^ 3 = 1 → s ∉ Subgroup.zpowers z →
        ∃ E : Subgroup GL14, E ≤ R3 ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧
          s ∈ E ∧ z ∈ E := by
  simp only [k2Check, Bool.and_eq_true] at hk2
  obtain ⟨⟨hz, hD⟩, hcover⟩ := hk2
  obtain ⟨z, hzS, hzc, hz3, hz1, hzcen⟩ := exists_z hsyl hz hw
  refine ⟨z, hzS, hz3, hz1, hzcen, fun s hs hs3 hsz => ?_⟩
  obtain ⟨t, ht, hts⟩ := exists_code_sylow hsyl hw hs
  have hcan : canon14 (sylAt t) = true := canon14_sylAt hsyl ht
  simp only [coverK2, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    Bool.not_eq_true', List.any_eq_true] at hcover
  have h := hcover t ht
  rcases h with (h | h) | ⟨p, hp, hfp⟩
  · exfalso
    apply hsz
    have : s = 1 := by
      refine Units.ext ?_
      rw [← hts, h, dec14_one14, Units.val_one]
    rw [this]
    exact Subgroup.one_mem _
  · exfalso
    have := cube14_eq_one hts.symm hs3
    simp [this] at h
  · obtain ⟨D, hD', rfl⟩ := List.mem_map.1 hp
    have hdok : dOK D = true := List.all_eq_true.1 hD D hD'
    obtain ⟨E, hES, hEe, hE81, hzE, hEp⟩ := exists_E hsyl hw hzc D hdok
    obtain ⟨k, hk, hk'⟩ := found_spec hfp
    have hk81 : k < 81 := by simpa [dArr] using hk
    rw [dArr_getD D hk81] at hk'
    obtain ⟨g, hgE, hg⟩ := hEp k hk81
    have hsg : s = g := by
      apply eq_of_code (c := dProd D k)
      · rw [hk']
        exact hts.symm
      · exact hg.symm
    exact ⟨E, hES.trans (sylow_le_R3 hw), hEe, hE81, hsg ▸ hgE, hzE⟩

theorem isT_spec (hsyl : sylCheck = true) (hz : zOK = true) (hwords : wordsOK = true)
    (hw : ∀ l ∈ sylWord, l < 8) {t : ℕ} (ht : t < 729) (hT : tArr.getD t false = true)
    {s : GL14} (hs : dec14 (sylAt t) = (s : M14)) :
    ∃ h ∈ R3, ∃ z' ∈ sylow, (∀ q ∈ sylow, q * z' = z' * q) ∧ h * s * h⁻¹ = z' := by
  obtain ⟨-, -, -, -, hc⟩ := sylCheck_parts hsyl
  obtain ⟨-, hconj, -⟩ := wordsOK_parts hwords
  have hT' : tCodes.contains (sylAt t) = true := by
    simpa [tArr, isTIdx, Array.getD_eq_getD_getElem?, ht] using hT
  have hmem : sylAt t ∈ tCodes := List.contains_iff_mem.mp hT'
  simp only [tCodes, List.mem_flatMap, List.mem_map] at hmem
  obtain ⟨w, hwc, zc, hzc, hzeq⟩ := hmem
  simp only [zCodes, List.mem_map] at hzc
  obtain ⟨i, hi, rfl⟩ := hzc
  obtain ⟨hi729, hicomm⟩ := zOK_parts hz i hi
  obtain ⟨z', hz'S, hz'c⟩ := exists_elem_of_code hsyl hw hi729
  have hwl : ∀ l ∈ w, l < 8 := hconj w hwc
  refine ⟨wordElem w, wordElem_mem w hwl, z', hz'S,
    central_of_commutes hc hw hz'c.symm hicomm, ?_⟩
  have hsEq : s = (wordElem w)⁻¹ * z' * wordElem w := by
    refine Units.ext ?_
    rw [← hs, ← hzeq, dec14_conjStep hc (invWord w) (invWord_lt w hwl), wordElem_invWord w hwl,
      inv_inv, hz'c, Units.val_mul, Units.val_mul]
  rw [hsEq]
  group

theorem exists_isT (hsyl : sylCheck = true) (hz : zOK = true) (hcov : coverCheck = true)
    (hw : ∀ l ∈ sylWord, l < 8) :
    ∀ a ∈ sylow, ∀ b ∈ sylow, a ≠ 1 → a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a →
      b ∉ Subgroup.zpowers a → ∃ t ∈ ({a, b, a * b, a * b ^ 2} : Set GL14), ∃ h ∈ R3,
        ∃ z' ∈ sylow, (∀ q ∈ sylow, q * z' = z' * q) ∧ h * t * h⁻¹ = z' := by
  intro a ha b hb ha1 ha3 hb3 hab hbz
  obtain ⟨hwords, hrt, hpath, hall⟩ := coverCheck_parts hcov
  obtain ⟨ia, hia, hiac⟩ := exists_code_sylow hsyl hw ha
  obtain ⟨ib, hib, hibc⟩ := exists_code_sylow hsyl hw hb
  have key : ∀ (s : GL14) (t : ℕ), t < 729 → tArr.getD t false = true →
      dec14 (sylAt t) = (s : M14) →
      ∃ h ∈ R3, ∃ z' ∈ sylow, (∀ q ∈ sylow, q * z' = z' * q) ∧ h * s * h⁻¹ = z' :=
    fun s t ht hT hs => isT_spec hsyl hz hwords hw ht hT hs
  have hN : ∀ (g : GL14) (t : ℕ), dec14 (sylAt t) = (g : M14) → g ≠ 1 → g ^ 3 = 1 →
      isN t = false → tArr.getD t false = true := by
    intro g t hg hg1 hg3 h
    have h1 : (sylAt t == one14) = false := by
      rw [beq_eq_false_iff_ne]
      intro e
      apply hg1
      refine Units.ext ?_
      rw [← hg, e, dec14_one14, Units.val_one]
    have h2 : cube14 (sylAt t) = one14 := cube14_eq_one hg.symm hg3
    unfold isN at h
    simpa [h1, h2] using h
  have hb1 : b ≠ 1 := fun h => hbz (by rw [h]; exact Subgroup.one_mem _)
  by_cases hNa : isN ia = true
  · by_cases hNb : isN ib = true
    · rcases hall ia hia hNa ib hib hNb with h | h | h | h | h
      · exfalso
        apply hbz
        have : b = a := Units.ext (by rw [← hibc, ← hiac, h])
        rw [this]
        exact Subgroup.mem_zpowers a
      · exfalso
        apply hbz
        obtain ⟨-, hmul⟩ := mulIdx_main hsyl hrt hpath hia hia
        have : b = a ^ 2 := Units.ext (by
          rw [← hibc, h, hmul, dec14_mul14, hiac, pow_two, Units.val_mul])
        rw [this]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers a) 2
      · exfalso
        apply h
        obtain ⟨hlt1, hm1⟩ := mulIdx_main hsyl hrt hpath hia hib
        obtain ⟨hlt2, hm2⟩ := mulIdx_main hsyl hrt hpath hib hia
        have hcomm : mul14 (sylAt ia) (sylAt ib) = mul14 (sylAt ib) (sylAt ia) := by
          refine dec14_injective (canon14_mul14 _ _) (canon14_mul14 _ _) ?_
          rw [dec14_mul14, dec14_mul14, hiac, hibc, ← Units.val_mul, ← Units.val_mul, hab]
        exact sylAt_inj hsyl hlt1 hlt2 (by rw [hm1, hm2, hcomm])
      · obtain ⟨hlt, hm1⟩ := mulIdx_main hsyl hrt hpath hia hib
        refine ⟨a * b, by simp, ?_⟩
        exact key (a * b) _ hlt h (by rw [hm1, dec14_mul14, hiac, hibc, Units.val_mul])
      · obtain ⟨hlt, hm1⟩ := mulIdx_main hsyl hrt hpath hia hib
        obtain ⟨hlt2, hm2⟩ := mulIdx_main hsyl hrt hpath hlt hib
        refine ⟨a * b ^ 2, by simp, ?_⟩
        have := key (a * b * b) _ hlt2 h (by
          rw [hm2, dec14_mul14, hm1, dec14_mul14, hiac, hibc, Units.val_mul, Units.val_mul])
        rwa [show a * b * b = a * b ^ 2 by rw [pow_two, mul_assoc]] at this
    · have hNb' : isN ib = false := by simpa using hNb
      exact ⟨b, by simp, key b ib hib (hN b ib hibc hb1 hb3 hNb') hibc⟩
  · have hNa' : isN ia = false := by simpa using hNa
    exact ⟨a, by simp, key a ia hia (hN a ia hiac ha1 ha3 hNa') hiac⟩

theorem exists_liftData (hsyl : sylCheck = true) (hlift : liftCheck = true)
    (hwords : wordsOK = true) (hw : ∀ l ∈ sylWord, l < 8) :
    ∃ d : LiftData R3, ∀ i, ((d.x i : R3) : GL14) ∈ sylow := by
  obtain ⟨hWlen, hWlt, hGlen, hMlen, hcomm, hcube, hdist, hMlt, hrel⟩ := liftCheck_parts hlift
  obtain ⟨-, -, hliftG⟩ := wordsOK_parts hwords
  obtain ⟨-, -, -, -, hc⟩ := sylCheck_parts hsyl
  have hW3 : ∀ i : Fin 3, liftW.getD i 0 < 729 := fun i => by
    have hi : (i : ℕ) < liftW.length := by omega
    rw [List.getD_eq_getElem _ _ hi]
    exact hWlt _ (List.getElem_mem hi)
  choose xs hxsS hxsc using fun i : Fin 3 => exists_elem_of_code hsyl hw (hW3 i)
  have hxsc' : ∀ i : Fin 3, (xs i : M14) = dec14 (liftEl i) := fun i => (hxsc i).symm
  have hG : ∀ j : Fin 2, ∀ l ∈ liftG.getD j [], l < 8 := fun j => by
    have hj : (j : ℕ) < liftG.length := by omega
    rw [List.getD_eq_getElem _ _ hj]
    exact hliftG _ (List.getElem_mem hj)
  let x : Fin 3 → R3 := fun i => ⟨xs i, sylow_le_R3 hw (hxsS i)⟩
  let g : Fin 2 → R3 := fun j => ⟨wordElem (liftG.getD j []), wordElem_mem _ (hG j)⟩
  have hx3 : ∀ i, x i ^ 3 = 1 := fun i =>
    Subtype.ext (pow_three_of_cube14 (hxsc' i) (hcube i i.2))
  have hxc : ∀ i j, x i * x j = x j * x i := fun i j =>
    Subtype.ext (commute_of_commutes (hxsc' i) (hxsc' j) (hcomm i i.2 j j.2))
  have hrel' : ∀ (j : Fin 2) (i : Fin 3), g j * x i * (g j)⁻¹ =
      (List.ofFn fun k : Fin 3 => x k ^ liftMat j k i).prod := by
    intro j i
    have hl := hG j
    have hr := hrel j j.2 i i.2
    have hL := dec14_conjStep hc (liftG.getD j []) hl (liftEl i)
    rw [← hxsc' i] at hL
    have hlt0 := hMlt j j.2 0 (by norm_num) i i.2
    have hlt1 := hMlt j j.2 1 (by norm_num) i i.2
    have hlt2 := hMlt j j.2 2 (by norm_num) i i.2
    have hof : ∀ f : Fin 3 → R3, (List.ofFn f).prod = f 0 * (f 1 * (f 2 * 1)) := fun f => by
      simp [List.ofFn_succ]
    rw [hof]
    refine Subtype.ext (Units.ext ?_)
    change ((wordElem (liftG.getD j []) * xs i * (wordElem (liftG.getD j []))⁻¹ : GL14) : M14) =
      ((xs 0 ^ liftMat j 0 i * (xs 1 ^ liftMat j 1 i * (xs 2 ^ liftMat j 2 i * 1)) : GL14) : M14)
    rw [Units.val_mul, Units.val_mul, ← hL, hr, liftRhs, Units.val_mul, Units.val_mul,
      Units.val_mul, Units.val_one, coe_pow14 (hxsc' 0) hlt0, coe_pow14 (hxsc' 1) hlt1,
      coe_pow14 (hxsc' 2) hlt2, dec14_mul14, dec14_mul14, dec14_mul14, dec14_one14]
    rfl
  have hx27 : 27 ≤ Nat.card (Subgroup.closure (Set.range x)) := by
    have hmem : ∀ u : ℕ, prodElem3 x u ∈ Subgroup.closure (Set.range x) := fun u =>
      mul_mem (mul_mem (pow_mem (Subgroup.subset_closure (Set.mem_range_self 0)) _)
        (pow_mem (Subgroup.subset_closure (Set.mem_range_self 1)) _))
        (pow_mem (Subgroup.subset_closure (Set.mem_range_self 2)) _)
    have hinj : Function.Injective
        (fun u : Fin 27 => (⟨prodElem3 x u, hmem u⟩ : Subgroup.closure (Set.range x))) := by
      intro u u' h
      have h1 : prodElem3 x u = prodElem3 x u' := congrArg Subtype.val h
      have h2 : liftProd u = liftProd u' := by
        have c0 : ((xs 0 : GL14) : M14) = dec14 (liftEl 0) := hxsc' 0
        have c1 : ((xs 1 : GL14) : M14) = dec14 (liftEl 1) := hxsc' 1
        have c2 : ((xs 2 : GL14) : M14) = dec14 (liftEl 2) := hxsc' 2
        have e1 := coe_prodElem3 (e := fun i => ((x i : R3) : GL14)) c0 c1 c2 u
        have e2 := coe_prodElem3 (e := fun i => ((x i : R3) : GL14)) c0 c1 c2 u'
        refine dec14_injective (canon14_mul14 _ _) (canon14_mul14 _ _) ?_
        have h1' : ((prodElem3 (fun i => ((x i : R3) : GL14)) u : GL14) : M14) =
            ((prodElem3 (fun i => ((x i : R3) : GL14)) u' : GL14) : M14) := by
          have := congrArg (fun y : R3 => ((y : R3) : GL14)) h1
          simpa [prodElem3] using congrArg (fun y : GL14 => (y : M14)) this
        rw [liftProd, liftProd, ← e1, ← e2, h1']
      have h3 := distinctCheck_spec hdist (t := u) (t' := u') (by simp) (by simp)
        (by simpa [Array.getD_eq_getD_getElem?] using h2)
      exact Fin.ext h3
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  refine ⟨⟨3, 2, x, g, fun j k i => liftMat j k i, 0, 0,
    fun k l => (liftCs.getD k []).getD l [], fun i => liftCs'.getD i [], hx3, hxc, hrel', ?_, ?_,
    hx27⟩, fun i => hxsS i⟩
  · decide +kernel
  · decide +kernel

end Sylow

end CFSG.RankThree.PartTwo.Sec4.Item434RemG23
