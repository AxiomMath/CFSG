module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CenterCheckFastPart3
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CenterCheckFastPart4

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.CenterCheckFast
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
variable (L : Type) [Field L]
variable {L}

def stepOk2 (lam : ℕ → ℤ) (D : List ℕ) (u : ℕ) (e : List (ℕ × ℤ)) : Bool :=
  (e.all fun vc => vc.1 == u || vc.2 % 2 == 0 || D.contains vc.1) &&
    (formCoeff u e % 2 != 0) && (formLam lam e % 2 == 0)

theorem eq_of_stepOk2 [CharP L 2] {lam : ℕ → ℤ} {D : List ℕ} {u : ℕ} {e : List (ℕ × ℤ)}
    (x : ℕ → L) (h : stepOk2 lam D u e = true) (hD : ∀ v ∈ D, x v = (lam v : L) * x 0)
    (he : formEval x e = 0) : x u = (lam u : L) * x 0 := by
  simp only [stepOk2, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
    List.contains_iff_mem, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨hall, hu⟩, hlam⟩ := h
  have hcast : ∀ z : ℤ, z % 2 = 0 → (z : L) = 0 := fun z hz =>
    (CharP.intCast_eq_zero_iff L 2 z).2 (Int.dvd_of_emod_eq_zero hz)
  rw [formEval_eq x lam u e fun vc hvc => by
    rcases hall vc hvc with (h1 | h1) | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl (hcast _ h1))
    · exact Or.inr (Or.inr (hD _ h1))] at he
  have hu0 : (formCoeff u e : L) ≠ 0 := fun h0 =>
    hu (Int.emod_eq_zero_of_dvd ((CharP.intCast_eq_zero_iff L 2 _).1 h0))
  push_cast at he
  rw [hcast _ hlam] at he
  refine mul_left_cancel₀ hu0 ?_
  linear_combination he

def stepsOk2 (lam : ℕ → ℤ) (form : ℕ → ℕ → ℕ → List (ℕ × ℤ)) (n : ℕ) :
    List ℕ → List (ℕ × ℕ × ℕ × ℕ) → Bool
  | D, [] => (List.range n).all fun u => D.contains u
  | D, (u, g, p, q) :: rest =>
    decide (g < 8 ∧ p < 52 ∧ q < 52) && stepOk2 lam D u (form g p q) &&
      stepsOk2 lam form n (u :: D) rest

theorem stepsOk2_sound [CharP L 2] {lam : ℕ → ℤ} {form : ℕ → ℕ → ℕ → List (ℕ × ℤ)} {n : ℕ}
    (x : ℕ → L) (hform : ∀ g p q, g < 8 → p < 52 → q < 52 → formEval x (form g p q) = 0) :
    ∀ (D : List ℕ) (steps : List (ℕ × ℕ × ℕ × ℕ)), stepsOk2 lam form n D steps = true →
      (∀ v ∈ D, x v = (lam v : L) * x 0) → ∀ u < n, x u = (lam u : L) * x 0
  | D, [], h, hD => fun u hu => by
    simp only [stepsOk2, List.all_eq_true, List.mem_range, List.contains_iff_mem] at h
    exact hD u (h u hu)
  | D, (u, g, p, q) :: rest, h, hD => by
    simp only [stepsOk2, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hg, hp, hq⟩, hs⟩, hrest⟩ := h
    have hu := eq_of_stepOk2 x hs hD (hform g p q hg hp hq)
    refine stepsOk2_sound x hform (u :: D) rest hrest fun v hv => ?_
    rcases List.mem_cons.1 hv with rfl | hv
    · exact hu
    · exact hD v hv

private def maskOfList : List ℕ → ℕ
  | [] => 0
  | a :: l => 2 ^ a ||| maskOfList l

private theorem maskOfList_testBit (l : List ℕ) (i : ℕ) :
    (maskOfList l).testBit i = true ↔ i ∈ l := by
  induction l with
  | nil => simp [maskOfList]
  | cons a l ih =>
    rw [maskOfList, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq, ih,
      List.mem_cons]
    constructor <;> rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h
    · exact Or.inl h.symm
    · exact Or.inr h

private theorem maskOfList_eq_contains (l : List ℕ) (i : ℕ) :
    (maskOfList l).testBit i = l.contains i := by
  rw [Bool.eq_iff_iff, maskOfList_testBit, List.contains_iff_mem]

private def stepOk2Mask (lam : ℕ → ℤ) (M : ℕ) (u : ℕ) (e : List (ℕ × ℤ)) : Bool :=
  (e.all fun vc => vc.1 == u || vc.2 % 2 == 0 || M.testBit vc.1) &&
    (formCoeff u e % 2 != 0) && (formLam lam e % 2 == 0)

private def runSteps (lam : ℕ → ℤ) (form : ℕ → ℕ → ℕ → List (ℕ × ℤ)) :
    ℕ → List (ℕ × ℕ × ℕ × ℕ) → Bool × ℕ
  | M, [] => (true, M)
  | M, (u, g, p, q) :: rest =>
      let b := decide (g < 8 ∧ p < 52 ∧ q < 52) && stepOk2Mask lam M u (form g p q)
      let r := runSteps lam form (M ||| 2 ^ u) rest
      (b && r.1, r.2)

private def fastStepsOk2 (lam : ℕ → ℤ) (form : ℕ → ℕ → ℕ → List (ℕ × ℤ)) (n : ℕ)
    (M : ℕ) (steps : List (ℕ × ℕ × ℕ × ℕ)) : Bool :=
  let r := runSteps lam form M steps
  r.1 && (List.range n).all fun u => r.2.testBit u

private theorem fastStepsOk2_eq (lam : ℕ → ℤ) (form : ℕ → ℕ → ℕ → List (ℕ × ℤ)) (n : ℕ) :
    ∀ (steps : List (ℕ × ℕ × ℕ × ℕ)) (M : ℕ) (D : List ℕ),
      (∀ i, M.testBit i = D.contains i) →
      stepsOk2 lam form n D steps = fastStepsOk2 lam form n M steps := by
  intro steps
  induction steps with
  | nil =>
    intro M D h
    simp only [stepsOk2, fastStepsOk2, runSteps, Bool.true_and]
    congr 1
    funext u
    exact (h u).symm
  | cons step rest ih =>
    intro M D h
    obtain ⟨u, g, p, q⟩ := step
    have h1 : stepOk2Mask lam M u (form g p q) = stepOk2 lam D u (form g p q) := by
      simp only [stepOk2Mask, stepOk2, h]
    have h2 : ∀ i, (M ||| 2 ^ u).testBit i = (u :: D).contains i := by
      intro i
      rw [Nat.testBit_or, Nat.testBit_two_pow, h i, List.contains_cons,
        Bool.or_comm (D.contains i) (decide (u = i))]
      congr 1
      rw [Bool.eq_iff_iff, decide_eq_true_eq, beq_iff_eq]
      exact eq_comm
    have h3 := ih (M ||| 2 ^ u) (u :: D) h2
    simp only [stepsOk2, fastStepsOk2, runSteps, h1, h3, Bool.and_assoc]

private def f4NilRowData : List (List (List (ℕ × ℤ))) :=
[
  [[(8, 1)], [], [], [], [(0, 2), (1, 1), (8, 1)], [], [], [], [], [(5, 1)], [(16, 1)], [], [], [],
    [], [], [], [(11, 1)], [(24, 1)], [], [(12, 1)], [], [(30, 1)], [], [], [], [(19, 1)],
    [(33, 1)], [(21, 1)], [], [], [(36, 1)], [], [], [], [(29, 1)], [], [(41, 1)], [], [], [], [],
    [], [], [], [], [(50, 1)], [(43, 1)], [], [], [], []],
  [[(4, 1)], [], [], [], [], [(9, 1)], [], [], [(0, 2), (1, 1), (4, 1)], [], [], [(17, 1)],
    [(20, 1)], [], [], [], [(10, 1)], [], [], [(26, 1)], [], [(28, 1)], [], [], [(18, 1)], [], [],
    [], [], [(35, 1)], [(22, 1)], [], [], [(27, 1)], [], [], [(31, 1)], [], [], [], [], [(37, 1)],
    [], [(47, 1)], [], [], [], [], [], [], [(46, 1)], []],
  [[], [(10, 1)], [], [], [], [(0, 1), (1, 2), (2, 2), (10, 1)], [], [], [(16, 1)], [(4, 1)], [],
    [], [(6, 1)], [(22, 1)], [], [], [], [], [], [], [], [(14, 1)], [], [(31, 1)], [(32, 1)],
    [(17, 1)], [], [], [], [], [], [], [], [(38, 1)], [(26, 1)], [], [], [], [], [], [(35, 1)],
    [(45, 1)], [(46, 1)], [(39, 1)], [], [], [], [], [], [], [], []],
  [[], [(5, 1)], [], [], [(9, 1)], [], [(12, 1)], [], [], [], [(0, 1), (1, 2), (2, 2), (5, 1)], [],
    [], [], [(21, 1)], [], [(8, 1)], [(25, 1)], [], [], [], [], [(13, 1)], [], [], [], [(34, 1)],
    [], [], [], [], [(23, 1)], [(24, 1)], [], [], [(40, 1)], [], [], [(33, 1)], [(43, 1)], [], [],
    [], [], [], [(41, 1)], [(42, 1)], [], [], [], [], []],
  [[], [], [(13, 1)], [], [], [], [(1, 1), (2, 2), (3, 1), (13, 1)], [], [], [], [(18, 1), (22, 2)],
    [(5, 1), (12, 2)], [(5, 1)], [], [(7, 1)], [(23, 1)], [(24, 1), (30, 2)], [(9, 1), (20, 2)], [],
    [], [(9, 1)], [], [(18, 1)], [], [], [], [], [], [], [(21, 1)], [(24, 1)], [(37, 1)], [], [],
    [], [(28, 1)], [(41, 1)], [], [(42, 1), (51, 2)], [(34, 1), (48, 2)], [], [], [], [], [(40, 1)],
    [(49, 1)], [], [], [(34, 1)], [], [], [(42, 1)]],
  [[], [], [(6, 1)], [], [], [(11, 1), (12, 2)], [], [(14, 1)], [], [(17, 1), (20, 2)], [], [],
    [(11, 1)], [(1, 1), (2, 2), (3, 1), (6, 1)], [], [], [], [], [(10, 1), (22, 2)], [], [(17, 1)],
    [(29, 1)], [(10, 1)], [(15, 1)], [(16, 1), (30, 2)], [], [], [], [(35, 1)], [], [(16, 1)], [],
    [], [], [(39, 1), (48, 2)], [], [], [(31, 1)], [], [], [(44, 1)], [(36, 1)], [(38, 1), (51, 2)],
    [], [], [], [], [], [(39, 1)], [(45, 1)], [], [(38, 1)]],
  [[], [], [], [(15, 1)], [], [], [], [(2, 1), (3, 2), (15, 1)], [], [], [], [], [], [(23, 1)],
    [(6, 1)], [], [], [], [(27, 1), (37, 2)], [(11, 1), (29, 2)], [], [(12, 1)], [(31, 1)], [],
    [(33, 1), (41, 2)], [], [(17, 1), (35, 2)], [], [(20, 1)], [(11, 1)], [(36, 1)], [],
    [(38, 1), (45, 2)], [], [(25, 1), (40, 2)], [(17, 1)], [], [(27, 1)], [], [], [(25, 1)],
    [(33, 1)], [], [], [], [(38, 1)], [], [], [(44, 1)], [(51, 1)], [], []],
  [[], [], [], [(7, 1)], [], [], [(14, 1)], [], [], [], [], [(19, 1), (29, 2)], [(21, 1)], [], [],
    [(2, 1), (3, 2), (7, 1)], [], [(26, 1), (35, 2)], [], [], [(28, 1)], [], [], [(13, 1)], [],
    [(34, 1), (40, 2)], [], [(18, 1), (37, 2)], [], [(19, 1)], [], [(22, 1)], [],
    [(24, 1), (41, 2)], [], [(26, 1)], [(30, 1)], [(18, 1)], [(32, 1), (45, 2)], [], [(34, 1)],
    [(24, 1)], [], [], [(48, 1)], [(32, 1)], [], [], [], [], [], [(49, 1)]]
]

private def f4NilRow (g p : ℕ) : List (ℕ × ℤ) :=
  (f4NilRowData.getD g []).getD p []

private theorem f4NilRow_eq_fin : ∀ g : Fin 8, ∀ p : Fin 52,
    ((((List.range 52).map fun r => (r, coefAt p (f4NilCol g r))).filter
      fun rz => rz.2 != 0) == f4NilRow g p) = true := by
  decide +kernel

private def f4FormS (g p q : ℕ) : List (ℕ × ℤ) :=
  (f4NilCol g q).map (fun rz => (52 * p + rz.1, rz.2)) ++
    (f4NilRow g p).map fun rz => (52 * rz.1 + q, -rz.2)

private theorem sum_map_filter_nz (f : ℕ × ℤ → ℤ) (hf : ∀ vc : ℕ × ℤ, vc.2 = 0 → f vc = 0)
    (e : List (ℕ × ℤ)) : ((e.filter fun vc => vc.2 != 0).map f).sum = (e.map f).sum := by
  induction e with
  | nil => rfl
  | cons a e ih =>
    by_cases h : a.2 = 0
    · rw [List.filter_cons_of_neg (by simp [h]), ih, List.map_cons, List.sum_cons, hf a h,
        zero_add]
    · rw [List.filter_cons_of_pos (by simp [h]), List.map_cons, List.sum_cons, ih, List.map_cons,
        List.sum_cons]

private theorem all_filter_nz (t : ℕ × ℤ → Bool) (ht : ∀ vc : ℕ × ℤ, vc.2 = 0 → t vc = true)
    (e : List (ℕ × ℤ)) : (e.filter fun vc => vc.2 != 0).all t = e.all t := by
  induction e with
  | nil => rfl
  | cons a e ih =>
    by_cases h : a.2 = 0
    · rw [List.filter_cons_of_neg (by simp [h]), ih, List.all_cons, ht a h, Bool.true_and]
    · rw [List.filter_cons_of_pos (by simp [h]), List.all_cons, List.all_cons, ih]

private theorem stepOk2Mask_filter (lam : ℕ → ℤ) (M u : ℕ) (e : List (ℕ × ℤ)) :
    stepOk2Mask lam M u (e.filter fun vc => vc.2 != 0) = stepOk2Mask lam M u e := by
  have h1 := all_filter_nz (fun vc => vc.1 == u || vc.2 % 2 == 0 || M.testBit vc.1)
    (fun vc h => by simp [h]) e
  have h2 : formCoeff u (e.filter fun vc => vc.2 != 0) = formCoeff u e :=
    sum_map_filter_nz _ (fun vc h => by simp [h]) e
  have h3 : formLam lam (e.filter fun vc => vc.2 != 0) = formLam lam e :=
    sum_map_filter_nz _ (fun vc h => by simp [h]) e
  unfold stepOk2Mask
  rw [h1, h2, h3]

private theorem f4Form_filter (g p q : ℕ) (hg : g < 8) (hp : p < 52) :
    ((f4Form g p q).filter fun vc => vc.2 != 0) = ((f4FormS g p q).filter fun vc => vc.2 != 0) := by
  have hR : (((List.range 52).map fun r => (r, coefAt p (f4NilCol g r))).filter
      fun rz => rz.2 != 0) = f4NilRow g p := beq_iff_eq.1 (f4NilRow_eq_fin ⟨g, hg⟩ ⟨p, hp⟩)
  have hB : ((List.range 52).map fun r => (52 * r + q, -coefAt p (f4NilCol g r))) =
      ((List.range 52).map fun r => (r, coefAt p (f4NilCol g r))).map
        fun rz => (52 * rz.1 + q, -rz.2) := by
    rw [List.map_map]
    rfl
  have hφ : ∀ l : List (ℕ × ℤ), ((l.map fun rz => (52 * rz.1 + q, -rz.2)).filter
      fun vc => vc.2 != 0) = (l.filter fun vc => vc.2 != 0).map fun rz => (52 * rz.1 + q, -rz.2) := by
    intro l
    rw [List.filter_map]
    congr 2
    funext rz
    change (-rz.2 != 0) = (rz.2 != 0)
    by_cases h : rz.2 = 0
    · simp [h]
    · have h' : -rz.2 ≠ 0 := neg_ne_zero.2 h
      rw [bne_iff_ne.2 h', bne_iff_ne.2 h]
  unfold f4Form f4FormS
  rw [List.filter_append, List.filter_append, hB, hφ, hφ, ← hR, List.filter_filter]
  simp only [Bool.and_self]

private theorem runSteps_congr (lam : ℕ → ℤ) (F F' : ℕ → ℕ → ℕ → List (ℕ × ℤ))
    (h : ∀ M u g p q, g < 8 → p < 52 → q < 52 →
      stepOk2Mask lam M u (F g p q) = stepOk2Mask lam M u (F' g p q)) :
    ∀ (steps : List (ℕ × ℕ × ℕ × ℕ)) (M : ℕ),
      runSteps lam F M steps = runSteps lam F' M steps := by
  intro steps
  induction steps with
  | nil => intro M; rfl
  | cons step rest ih =>
    intro M
    obtain ⟨u, g, p, q⟩ := step
    simp only [runSteps, ih]
    by_cases hb : g < 8 ∧ p < 52 ∧ q < 52
    · rw [h M u g p q hb.1 hb.2.1 hb.2.2]
    · rw [decide_eq_false hb]
      simp only [Bool.false_and]

private theorem fastStepsOk2_f4FormS (n M : ℕ) (steps : List (ℕ × ℕ × ℕ × ℕ)) :
    fastStepsOk2 f4Lam f4Form n M steps = fastStepsOk2 f4Lam f4FormS n M steps := by
  unfold fastStepsOk2
  rw [runSteps_congr f4Lam f4Form f4FormS (fun M u g p q hg hp _ => by
    rw [← stepOk2Mask_filter, f4Form_filter g p q hg hp, stepOk2Mask_filter])]

theorem stepsOk2_f4Steps : stepsOk2 f4Lam f4Form 2704 [0] f4Steps = true := by
  rw [fastStepsOk2_eq f4Lam f4Form 2704 f4Steps (maskOfList [0]) [0]
    (by intro i; rw [maskOfList_eq_contains]), fastStepsOk2_f4FormS]
  decide +kernel

theorem eq_smul_one_of_commute_f4Gen
    [CharP L 2] (M : Module.End L (RootModule Tag.F4 L))
    (hM : ∀ g, g < 8 → Commute M (f4Gen L g)) :
    M = f4Entries M 0 • (1 : Module.End L (RootModule Tag.F4 L)) := by
  have hsol := stepsOk2_sound (f4Entries M)
    (fun g p q hg hp hq => formEval_f4Form M hg (hM g hg) hp hq)
    [0] f4Steps stepsOk2_f4Steps (fun v hv => by
      rw [List.mem_singleton.1 hv]
      simp [f4Lam])
  refine ext_posVec fun q hq => ?_
  have hq' : q < 52 := hq
  rw [eq_sum_posCoord_smul_posVec (M (posVec Tag.F4 L q))]
  rw [LinearMap.smul_apply, Module.End.one_apply]
  rw [Finset.sum_eq_single q]
  · have h := hsol (52 * q + q) (by omega)
    rw [f4Entries_apply M hq'] at h
    rw [h]
    simp only [f4Lam, show (52 * q + q) / 52 = q by omega, show (52 * q + q) % 52 = q by omega,
      ↓reduceIte, Int.cast_one, one_mul]
  · intro p hp hpq
    have h := hsol (52 * p + q) (by have := Finset.mem_range.1 hp; omega)
    rw [f4Entries_apply M hq'] at h
    rw [h]
    simp only [f4Lam, show (52 * p + q) / 52 = p by omega, show (52 * p + q) % 52 = q by omega,
      hpq, ↓reduceIte, Int.cast_zero, zero_mul, zero_smul]
  · exact fun h => absurd (Finset.mem_range.2 hq) h

variable {K : Type} [Field K] [CharP K 2]

def f4EntriesData : List (List (List Entry)) :=
[[[(0, 4, 2), (1, 4, 1), (5, 9, 1), (8, 0, 1), (11, 17, 1), (12, 20, 1), (16, 10, 1), (19, 26,
        1), (21, 28, 1), (24, 18, 1), (29, 35, 1), (30, 22, 1), (33, 27, 1), (36, 31, 1), (41, 37,
            1), (43, 47, 1), (50, 46, 1)],
    [(8, 4, 1)],
    [],
  ],
  [[(0, 8, 2), (1, 8, 1), (4, 0, 1), (9, 5, 1), (10, 16, 1), (17, 11, 1), (18, 24, 1), (20, 12,
        1), (22, 30, 1), (26, 19, 1), (27, 33, 1), (28, 21, 1), (31, 36, 1), (35, 29, 1), (37, 41,
            1), (46, 50, 1), (47, 43, 1)],
    [(4, 8, 1)],
    [],
  ],
  [[(0, 5, 1), (1, 5, 2), (2, 5, 2), (4, 9, 1), (6, 12, 1), (10, 1, 1), (14, 21, 1), (16, 8, 1),
        (17, 25, 1), (22, 13, 1), (26, 34, 1), (31, 23, 1), (32, 24, 1), (35, 40, 1), (38, 33, 1),
            (39, 43, 1), (45, 41, 1), (46, 42, 1)],
    [(10, 5, 1)],
    [],
  ],
  [[(0, 10, 1), (1, 10, 2), (2, 10, 2), (5, 1, 1), (8, 16, 1), (9, 4, 1), (12, 6, 1), (13, 22, 1),
        (21, 14, 1), (23, 31, 1), (24, 32, 1), (25, 17, 1), (33, 38, 1), (34, 26, 1), (40, 35, 1),
            (41, 45, 1), (42, 46, 1), (43, 39, 1)],
    [(5, 10, 1)],
    [],
  ],
  [[(1, 6, 1), (2, 6, 2), (3, 6, 1), (5, 12, 1), (7, 14, 1), (9, 20, 1), (12, 11, 2), (13, 2, 1),
        (18, 22, 1), (20, 17, 2), (21, 29, 1), (22, 10, 2), (23, 15, 1), (24, 30, 1), (28, 35, 1),
            (30, 16, 2), (34, 48, 1), (37, 31, 1), (40, 44, 1), (41, 36, 1), (42, 51, 1), (48, 39,
                2), (49, 45, 1), (51, 38, 2)],
    [(5, 11, 1), (9, 17, 1), (13, 6, 1), (18, 10, 1), (24, 16, 1), (34, 39, 1), (42, 38, 1)],
    [],
  ],
  [[(1, 13, 1), (2, 13, 2), (3, 13, 1), (6, 2, 1), (10, 22, 1), (11, 12, 1), (12, 5, 2), (14, 7,
        1), (15, 23, 1), (16, 30, 1), (17, 20, 1), (20, 9, 2), (22, 18, 2), (29, 21, 1), (30, 24,
            2), (31, 37, 1), (35, 28, 1), (36, 41, 1), (38, 51, 1), (39, 48, 1), (44, 40, 1), (45,
                49, 1), (48, 34, 2), (51, 42, 2)],
    [(6, 13, 1), (10, 18, 1), (11, 5, 1), (16, 24, 1), (17, 9, 1), (38, 42, 1), (39, 34, 1)],
    [],
  ],
  [[(2, 7, 1), (3, 7, 2), (6, 14, 1), (11, 29, 1), (12, 21, 1), (15, 3, 1), (17, 35, 1), (20, 28,
        1), (23, 13, 1), (25, 40, 1), (27, 37, 1), (29, 19, 2), (31, 22, 1), (33, 41, 1), (35, 26,
            2), (36, 30, 1), (37, 18, 2), (38, 45, 1), (40, 34, 2), (41, 24, 2), (44, 48, 1), (45,
                32, 2), (51, 49, 1)],
    [(11, 19, 1), (15, 7, 1), (17, 26, 1), (25, 34, 1), (27, 18, 1), (33, 24, 1), (38, 32, 1)],
    [],
  ],
  [[(2, 15, 1), (3, 15, 2), (7, 3, 1), (13, 23, 1), (14, 6, 1), (18, 37, 1), (19, 29, 1), (21, 12,
        1), (22, 31, 1), (24, 41, 1), (26, 35, 1), (28, 20, 1), (29, 11, 2), (30, 36, 1), (32, 45,
            1), (34, 40, 1), (35, 17, 2), (37, 27, 2), (40, 25, 2), (41, 33, 2), (45, 38, 2), (48,
                44, 1), (49, 51, 1)],
    [(7, 15, 1), (18, 27, 1), (19, 11, 1), (24, 33, 1), (26, 17, 1), (32, 38, 1), (34, 25, 1)],
    [],
  ],
]

def f4EntriesOfData (g k : ℕ) : List Entry :=
  (f4EntriesData.getD g []).getD k []

def f4ColData (g k p : ℕ) : List (ℕ × ℤ) :=
  if k = 0 then [(p, 1)] else colOf (f4EntriesOfData g (k - 1)) p

theorem entries_f4_eq_data_fin :
    ∀ g : Fin 8, ∀ k : Fin 3,
      entries .F4 (simplePos .F4 (f4GenY (g : ℕ)) (f4GenI (g : ℕ))) ((k : ℕ) + 1)
        = f4EntriesOfData (g : ℕ) (k : ℕ) := by
  decide +kernel

theorem entries_f4_eq_data (g : ℕ) (hg : g < 8) (k : ℕ) (hk : 1 ≤ k) (hk3 : k ≤ 3) :
    entries .F4 (simplePos .F4 (f4GenY g) (f4GenI g)) k = f4EntriesOfData g (k - 1) := by
  have h := entries_f4_eq_data_fin ⟨g, hg⟩ ⟨k - 1, by omega⟩
  rwa [Nat.sub_add_cancel hk] at h

theorem f4ColData_of_ne_zero (g k p : ℕ) (hk : k ≠ 0) :
    f4ColData g k p = colOf (f4EntriesOfData g (k - 1)) p := by
  simp [f4ColData, hk]

theorem f4ColData_eq_coeffVec (g : ℕ) (hg : g < 8) (k : ℕ) (hk : k ≤ 3) (p : ℕ) :
    coeffVec .F4 (f4GenY g) (f4GenI g) k [(p, 1)] = f4ColData g k p := by
  by_cases h0 : k = 0
  · subst h0; simp [coeffVec, f4ColData]
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 h0
    rw [coeffVec_of_ne_zero _ _ h0, applyL_singleton, f4ColData_of_ne_zero g k p h0,
      entries_f4_eq_data g hg k hk1 hk]

theorem validVec_f4ColData
    (g : ℕ) (hg : g < 8) (k : ℕ) (hk : k ≤ 3) (p : ℕ) (hp : p < 52) :
    ValidVec Tag.F4 (f4ColData g k p) := by
  by_cases h0 : k = 0
  · subst h0; simp only [f4ColData, ↓reduceIte]
    exact validVec_single (show p < dim Tag.F4 from hp)
  · have hk4 : k < 4 := by omega
    have hvalid := (coeffOp_vecOf (k := k) simpleRow_F4 f4_allValid ℤ (f4GenY g) (f4GenI g)
      hk4 (validVec_single (show p < dim Tag.F4 from hp))).2
    rwa [f4ColData_eq_coeffVec g hg k hk p] at hvalid

def f4GramPairs : List (ℕ × ℕ) :=
  [(0, 1), (4, 8), (5, 10), (9, 16), (11, 18), (17, 24), (19, 27), (25, 32), (26, 33),
    (34, 38), (39, 42), (43, 46), (47, 50)]

def gramZ (p q : ℕ) : ℤ :=
  if f4GramPairs.contains (p, q) || f4GramPairs.contains (q, p) then 1 else 0

def sparseB (u v : List (ℕ × ℤ)) : ℤ :=
  (u.map fun x => x.2 * (v.map fun y => gramZ x.1 y.1 * y.2).sum).sum

theorem sparseB_cons (x : ℕ × ℤ) (u v : List (ℕ × ℤ)) :
    sparseB (x :: u) v = (x.2 : ℤ) * sparseB [(x.1, 1)] v + sparseB u v := by
  simp only [sparseB, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, add_zero,
    one_mul]

def polyCoeff (g p q d : ℕ) : ℤ :=
  ∑ a ∈ Finset.range 4, ∑ b ∈ Finset.range 4,
    if a + b = d then sparseB (f4ColData g a p) (f4ColData g b q) else 0

private theorem colOf_entriesData_two (g : Fin 8) (p : ℕ) :
    colOf (f4EntriesOfData (g : ℕ) 2) p = [] := by
  fin_cases g <;> simp [f4EntriesOfData, f4EntriesData, colOf]

private def polyCoeffFast (g p q d : ℕ) : ℤ :=
  let c1p := f4ColData g 1 p
  let c2p := f4ColData g 2 p
  let c1q := f4ColData g 1 q
  let c2q := f4ColData g 2 q
  match d with
  | 0 => gramZ p q
  | 1 => sparseB [(p, 1)] c1q + sparseB c1p [(q, 1)]
  | 2 => sparseB [(p, 1)] c2q + sparseB c1p c1q + sparseB c2p [(q, 1)]
  | 3 => sparseB c1p c2q + sparseB c2p c1q
  | 4 => sparseB c2p c2q
  | _ => 0

private theorem polyCoeffFast_eq_polyCoeff_fin :
    ∀ g : Fin 8, ∀ p : Fin 52, ∀ q : Fin 52, ∀ d : Fin 7,
      polyCoeffFast (g : ℕ) (p : ℕ) (q : ℕ) (d : ℕ) =
        polyCoeff (g : ℕ) (p : ℕ) (q : ℕ) (d : ℕ) := by
  intro g p q d
  have h3p := colOf_entriesData_two g (p : ℕ)
  have h3q := colOf_entriesData_two g (q : ℕ)
  fin_cases d <;>
    simp [polyCoeffFast, polyCoeff, Finset.sum_range_succ,
      h3p, h3q, sparseB, gramZ, f4ColData]

private def f4GramMask : ℕ := 67049959916263298876552884825273703787545873740547050830503521944171674816020659894447546822729233301062077353291527201137938491330487463614977123877128070677279714466659373590653012142620348043879860947661692187067677429494026334673400952445399009555675927326551566201699009975901784518329601805405021066175076284956223752647815114614268906186732467423633200158057906523418865581309471083468270911594890117589528404917320361398765211702007537974866133528661596655887520576968319988868719195085437040155785698972725381980564627324333847842033197784499305352750544451447079890898607887947888988970384487457206174283097680525387447222507977887952348887477653038746035956245726535559488643140290207196244466194398924691156857720433137548665439506563151168861909613902634763989846181141531713649770498

private def f4GramF (p q : ℕ) : ℤ :=
  Bool.rec (motive := fun _ => ℤ) 0 1 (Nat.blt p 52 && Nat.blt q 52 &&
    Nat.blt 0 (Nat.land f4GramMask (Nat.shiftLeft 1 (Nat.add (Nat.mul 52 p) q))))

private theorem gramZ_eq_f4GramF_fin : ∀ p : Fin 52, ∀ q : Fin 52,
    gramZ (p : ℕ) (q : ℕ) = f4GramF (p : ℕ) (q : ℕ) := by
  decide +kernel

private theorem gramZ_of_not_lt {p q : ℕ} (h : ¬ (p < 52 ∧ q < 52)) : gramZ p q = 0 := by
  have h1 : f4GramPairs.contains (p, q) = false := by
    rw [Bool.eq_false_iff]
    intro hc
    rw [List.contains_iff_mem] at hc
    simp only [f4GramPairs, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hc
    omega
  have h2 : f4GramPairs.contains (q, p) = false := by
    rw [Bool.eq_false_iff]
    intro hc
    rw [List.contains_iff_mem] at hc
    simp only [f4GramPairs, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hc
    omega
  unfold gramZ
  rw [h1, h2]
  rfl

private theorem f4GramF_of_not_lt {p q : ℕ} (h : ¬ (p < 52 ∧ q < 52)) : f4GramF p q = 0 := by
  have hb : (Nat.blt p 52 && Nat.blt q 52) = false := by
    rw [Bool.eq_false_iff]
    intro hc
    simp only [Bool.and_eq_true, Nat.blt_eq] at hc
    exact h hc
  simp only [f4GramF, hb, Bool.false_and]

private theorem gramZ_eq_f4GramF : gramZ = f4GramF := by
  funext p q
  by_cases h : p < 52 ∧ q < 52
  · exact gramZ_eq_f4GramF_fin ⟨p, h.1⟩ ⟨q, h.2⟩
  · rw [gramZ_of_not_lt h, f4GramF_of_not_lt h]

private def f4SparseG (G : ℕ → ℕ → ℤ) (u v : List (ℕ × ℤ)) : ℤ :=
  (u.map fun x => x.2 * (v.map fun y => G x.1 y.1 * y.2).sum).sum

private def f4PolyB (G : ℕ → ℕ → ℤ) (g p q : ℕ) : Bool :=
  ((f4SparseG G [(p, 1)] (f4ColData g 1 q) + f4SparseG G (f4ColData g 1 p) [(q, 1)]) % 2 == 0) &&
  ((f4SparseG G [(p, 1)] (f4ColData g 2 q) + f4SparseG G (f4ColData g 1 p) (f4ColData g 1 q) +
    f4SparseG G (f4ColData g 2 p) [(q, 1)]) % 2 == 0) &&
  ((f4SparseG G (f4ColData g 1 p) (f4ColData g 2 q) +
    f4SparseG G (f4ColData g 2 p) (f4ColData g 1 q)) % 2 == 0) &&
  (f4SparseG G (f4ColData g 2 p) (f4ColData g 2 q) % 2 == 0)

private theorem f4PolyB_0 : ∀ p : Fin 52, ∀ q : Fin 52, f4PolyB f4GramF 0 p q = true := by
  decide +kernel
private theorem f4PolyB_1 : ∀ p : Fin 52, ∀ q : Fin 52, f4PolyB f4GramF 1 p q = true := by
  decide +kernel
private theorem f4PolyB_2 : ∀ p : Fin 52, ∀ q : Fin 52, f4PolyB f4GramF 2 p q = true := by
  decide +kernel
private theorem f4PolyB_3 : ∀ p : Fin 52, ∀ q : Fin 52, f4PolyB f4GramF 3 p q = true := by
  decide +kernel
private theorem f4PolyB_4 : ∀ p : Fin 52, ∀ q : Fin 52, f4PolyB f4GramF 4 p q = true := by
  decide +kernel
private theorem f4PolyB_5 : ∀ p : Fin 52, ∀ q : Fin 52, f4PolyB f4GramF 5 p q = true := by
  decide +kernel
private theorem f4PolyB_6 : ∀ p : Fin 52, ∀ q : Fin 52, f4PolyB f4GramF 6 p q = true := by
  decide +kernel
private theorem f4PolyB_7 : ∀ p : Fin 52, ∀ q : Fin 52, f4PolyB f4GramF 7 p q = true := by
  decide +kernel

private theorem f4PolyB_all (g : Fin 8) (p q : Fin 52) :
    f4PolyB gramZ (g : ℕ) (p : ℕ) (q : ℕ) = true := by
  rw [gramZ_eq_f4GramF]
  obtain ⟨g, hg⟩ := g
  match g, hg with
  | 0, _ => exact f4PolyB_0 p q
  | 1, _ => exact f4PolyB_1 p q
  | 2, _ => exact f4PolyB_2 p q
  | 3, _ => exact f4PolyB_3 p q
  | 4, _ => exact f4PolyB_4 p q
  | 5, _ => exact f4PolyB_5 p q
  | 6, _ => exact f4PolyB_6 p q
  | 7, _ => exact f4PolyB_7 p q

private theorem polyCoeffFast_spec : ∀ g : Fin 8, ∀ d : Fin 7, ∀ p : Fin 52, ∀ q : Fin 52,
    polyCoeffFast (g : ℕ) (p : ℕ) (q : ℕ) (d : ℕ) % 2 =
      (if (d : ℕ) = 0 then gramZ (p : ℕ) (q : ℕ) else 0) % 2 := by
  intro g d p q
  have h := f4PolyB_all g p q
  simp only [f4PolyB, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  obtain ⟨d, hd⟩ := d
  match d, hd with
  | 0, _ => rfl
  | 1, _ => exact h1.trans rfl
  | 2, _ => exact h2.trans rfl
  | 3, _ => exact h3.trans rfl
  | 4, _ => exact h4.trans rfl
  | 5, _ => rfl
  | 6, _ => rfl

theorem polyCoeff_spec :
    ∀ g : Fin 8, ∀ p : Fin 52, ∀ q : Fin 52, ∀ d : Fin 7,
      polyCoeff (g : ℕ) (p : ℕ) (q : ℕ) (d : ℕ) % 2 =
        (if (d : ℕ) = 0 then gramZ (p : ℕ) (q : ℕ) else 0) % 2 := by
  intro g p q d
  rw [← polyCoeffFast_eq_polyCoeff_fin g p q d]
  exact polyCoeffFast_spec g d p q

theorem gramZ_zero_one : gramZ 0 1 = 1 := by decide

end CFSG.StandardType.F4ExplicitPos.CenterCheckFast

end

end
