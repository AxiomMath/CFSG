module

public import CFSG.LieType.Chevalley.LangRootArithmeticG2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CenterCheckFastPart1
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CenterCheckFastPart2

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.CenterCheckFast
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
variable (L : Type) [Field L]

def f4NilCol (g q : ℕ) : List (ℕ × ℤ) :=
  (f4NilColData.getD g []).getD q []

def f4NilEntriesActual (g : ℕ) : List Entry :=
  entries .F4 (simplePos .F4 (f4GenY g) (f4GenI g)) 1 ++
    entries .F4 (simplePos .F4 (f4GenY g) (f4GenI g)) 2 ++
    entries .F4 (simplePos .F4 (f4GenY g) (f4GenI g)) 3

def f4NilEntriesData : List (List Entry) :=
[[(0, 4, 2), (1, 4, 1), (5, 9, 1), (8, 0, 1), (11, 17, 1), (12, 20, 1), (16, 10, 1),
    (19, 26, 1), (21, 28, 1), (24, 18, 1), (29, 35, 1), (30, 22, 1), (33, 27, 1),
    (36, 31, 1), (41, 37, 1), (43, 47, 1), (50, 46, 1), (8, 4, 1)
  ],
  [(0, 8, 2), (1, 8, 1), (4, 0, 1), (9, 5, 1), (10, 16, 1), (17, 11, 1), (18, 24, 1),
    (20, 12, 1), (22, 30, 1), (26, 19, 1), (27, 33, 1), (28, 21, 1), (31, 36, 1),
    (35, 29, 1), (37, 41, 1), (46, 50, 1), (47, 43, 1), (4, 8, 1)
  ],
  [(0, 5, 1), (1, 5, 2), (2, 5, 2), (4, 9, 1), (6, 12, 1), (10, 1, 1), (14, 21, 1),
    (16, 8, 1), (17, 25, 1), (22, 13, 1), (26, 34, 1), (31, 23, 1), (32, 24, 1), (35, 40, 1),
    (38, 33, 1), (39, 43, 1), (45, 41, 1), (46, 42, 1), (10, 5, 1)
  ],
  [(0, 10, 1), (1, 10, 2), (2, 10, 2), (5, 1, 1), (8, 16, 1), (9, 4, 1), (12, 6, 1),
    (13, 22, 1), (21, 14, 1), (23, 31, 1), (24, 32, 1), (25, 17, 1), (33, 38, 1),
    (34, 26, 1), (40, 35, 1), (41, 45, 1), (42, 46, 1), (43, 39, 1), (5, 10, 1)
  ],
  [(1, 6, 1), (2, 6, 2), (3, 6, 1), (5, 12, 1), (7, 14, 1), (9, 20, 1), (12, 11, 2),
    (13, 2, 1), (18, 22, 1), (20, 17, 2), (21, 29, 1), (22, 10, 2), (23, 15, 1), (24, 30, 1),
    (28, 35, 1), (30, 16, 2), (34, 48, 1), (37, 31, 1), (40, 44, 1), (41, 36, 1),
    (42, 51, 1), (48, 39, 2), (49, 45, 1), (51, 38, 2), (5, 11, 1), (9, 17, 1), (13, 6, 1),
    (18, 10, 1), (24, 16, 1), (34, 39, 1), (42, 38, 1)
  ],
  [(1, 13, 1), (2, 13, 2), (3, 13, 1), (6, 2, 1), (10, 22, 1), (11, 12, 1), (12, 5, 2),
    (14, 7, 1), (15, 23, 1), (16, 30, 1), (17, 20, 1), (20, 9, 2), (22, 18, 2), (29, 21, 1),
    (30, 24, 2), (31, 37, 1), (35, 28, 1), (36, 41, 1), (38, 51, 1), (39, 48, 1),
    (44, 40, 1), (45, 49, 1), (48, 34, 2), (51, 42, 2), (6, 13, 1), (10, 18, 1), (11, 5, 1),
    (16, 24, 1), (17, 9, 1), (38, 42, 1), (39, 34, 1)
  ],
  [(2, 7, 1), (3, 7, 2), (6, 14, 1), (11, 29, 1), (12, 21, 1), (15, 3, 1), (17, 35, 1),
    (20, 28, 1), (23, 13, 1), (25, 40, 1), (27, 37, 1), (29, 19, 2), (31, 22, 1),
    (33, 41, 1), (35, 26, 2), (36, 30, 1), (37, 18, 2), (38, 45, 1), (40, 34, 2),
    (41, 24, 2), (44, 48, 1), (45, 32, 2), (51, 49, 1), (11, 19, 1), (15, 7, 1), (17, 26, 1),
    (25, 34, 1), (27, 18, 1), (33, 24, 1), (38, 32, 1)
  ],
  [(2, 15, 1), (3, 15, 2), (7, 3, 1), (13, 23, 1), (14, 6, 1), (18, 37, 1), (19, 29, 1),
    (21, 12, 1), (22, 31, 1), (24, 41, 1), (26, 35, 1), (28, 20, 1), (29, 11, 2),
    (30, 36, 1), (32, 45, 1), (34, 40, 1), (35, 17, 2), (37, 27, 2), (40, 25, 2),
    (41, 33, 2), (45, 38, 2), (48, 44, 1), (49, 51, 1), (7, 15, 1), (18, 27, 1), (19, 11, 1),
    (24, 33, 1), (26, 17, 1), (32, 38, 1), (34, 25, 1)
  ]
]

def f4NilEntries (g : ℕ) : List Entry :=
  f4NilEntriesData.getD g []

theorem f4NilEntries_eq_actual_fin :
    ∀ g : Fin 8, f4NilEntries g = f4NilEntriesActual g := by
  decide +kernel

theorem colOf_append (A B : List Entry) (q : ℕ) :
    colOf (A ++ B) q = colOf A q ++ colOf B q := by
  simp [colOf]

theorem applyL_singleton (A : List Entry) (q : ℕ) :
    applyL A [(q, 1)] = colOf A q := by
  simp [applyL, colOf]

theorem coeffVec_of_ne_zero {τ : Tag} (y : Bool) (i : Fin τ.rank) {k : ℕ} (hk : k ≠ 0)
    (v : List (ℕ × ℤ)) :
    coeffVec τ y i k v = applyL (entries τ (simplePos τ y i) k) v := by
  simp [coeffVec, hk]

theorem f4NilColActual_eq_colOf (g q : ℕ) :
    f4NilColActual g q = colOf (f4NilEntriesActual g) q := by
  have h3 : f4NilColActual g q =
      coeffVec .F4 (f4GenY g) (f4GenI g) 1 [(q, 1)] ++
        (coeffVec .F4 (f4GenY g) (f4GenI g) 2 [(q, 1)] ++
          coeffVec .F4 (f4GenY g) (f4GenI g) 3 [(q, 1)]) := by
    unfold f4NilColActual
    rw [show List.range 3 = [0, 1, 2] from by decide]
    simp
  rw [h3, f4NilEntriesActual]
  rw [coeffVec_of_ne_zero (f4GenY g) (f4GenI g) (by norm_num : (1 : ℕ) ≠ 0),
    coeffVec_of_ne_zero (f4GenY g) (f4GenI g) (by norm_num : (2 : ℕ) ≠ 0),
    coeffVec_of_ne_zero (f4GenY g) (f4GenI g) (by norm_num : (3 : ℕ) ≠ 0)]
  rw [applyL_singleton, applyL_singleton, applyL_singleton]
  rw [← colOf_append, ← colOf_append, List.append_assoc]

theorem f4NilCol_eq_normalize_literal_fin :
    ∀ g : Fin 8, ∀ q : Fin 52,
      f4NilCol g q = normalize (colOf (f4NilEntries g) q) := by
  decide +kernel

theorem f4NilCol_eq_normalize_actual_fin :
    ∀ g : Fin 8, ∀ q : Fin 52,
      f4NilCol g q = normalize (f4NilColActual g q) := by
  intro g q
  rw [f4NilColActual_eq_colOf, ← f4NilEntries_eq_actual_fin g]
  exact f4NilCol_eq_normalize_literal_fin g q

theorem f4NilCol_eq_normalize_actual (g : ℕ) (hg : g < 8) (q : ℕ) (hq : q < 52) :
    f4NilCol g q = normalize (f4NilColActual g q) :=
  f4NilCol_eq_normalize_actual_fin ⟨g, hg⟩ ⟨q, hq⟩

theorem f4NilCol_all_valid :
    ∀ g : Fin 8, ∀ q : Fin 52, (f4NilCol g q).all (fun x => decide (x.1 < 52)) = true := by
  decide +kernel

theorem validVec_f4NilCol_fin :
    ∀ g : Fin 8, ∀ q : Fin 52, ValidVec Tag.F4 (f4NilCol g q) := by
  intro g q x hx
  have h := (List.all_eq_true.1 (f4NilCol_all_valid g q)) x hx
  simpa [dim_F4] using h

theorem validVec_f4NilCol (g : ℕ) (hg : g < 8) {q : ℕ} (hq : q < dim Tag.F4) :
    ValidVec Tag.F4 (f4NilCol g q) :=
  validVec_f4NilCol_fin ⟨g, hg⟩ ⟨q, by rw [dim_F4] at hq; exact hq⟩

theorem f4Gen_eq_sum (g : ℕ) :
    f4Gen L g = ∑ k ∈ Finset.range 4, coeffOp Tag.F4 L (f4GenY g) (f4GenI g) k := by
  unfold f4Gen coeffOp
  cases f4GenY g
  · simp only [Bool.false_eq_true, ↓reduceIte, xOp_eq_sum_xCoeff, one_pow, one_smul]
  · simp only [↓reduceIte, yOp_eq_sum_yCoeff, one_pow, one_smul]

theorem coeffOp_zero_f4
    (y : Bool) (i : Fin Tag.F4.rank) : coeffOp Tag.F4 L y i 0 = 1 := by
  cases y
  · exact xCoeff_zero i
  · exact yCoeff_zero i

theorem f4Gen_posVec
    (g : ℕ) (hg : g < 8) {q : ℕ} (hq : q < dim Tag.F4) :
    f4Gen L g (posVec Tag.F4 L q) = posVec Tag.F4 L q + vecOf Tag.F4 L (f4NilCol g q) := by
  have hnorm : vecOf Tag.F4 L (f4NilCol g q) = vecOf Tag.F4 L (f4NilColActual g q) := by
    rw [f4NilCol_eq_normalize_actual g hg q (by rw [dim_F4] at hq; omega),
      vecOf_normalize]
  rw [f4Gen_eq_sum, LinearMap.sum_apply, Finset.sum_range_succ', coeffOp_zero_f4,
      Module.End.one_apply,
    add_comm, hnorm, f4NilColActual, vecOf_flatMap_range]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [posVec_eq_vecOf_single]
  exact (coeffOp_vecOf (k := k + 1) simpleRow_F4 f4_allValid L _ _
    (by have := Finset.mem_range.1 hk; omega) (validVec_single hq)).1

def f4Form (g p q : ℕ) : List (ℕ × ℤ) :=
  (f4NilCol g q).map (fun rz => (52 * p + rz.1, rz.2)) ++
    (List.range 52).map fun r => (52 * r + q, -coefAt p (f4NilCol g r))

variable {L}

theorem posCoord_vecOf
    (p : ℕ) {v : List (ℕ × ℤ)} (hv : ValidVec Tag.F4 v) :
    posCoord Tag.F4 L p (vecOf Tag.F4 L v) = (coefAt p v : L) := by
  induction v with
  | nil => simp [coefAt]
  | cons x v ih =>
    rw [vecOf_cons, map_add, map_smul, posCoord_posVec (hv x List.mem_cons_self),
      ih fun y hy => hv y (List.mem_cons_of_mem _ hy)]
    simp only [coefAt, List.map_cons, List.sum_cons, smul_eq_mul]
    split_ifs with h1 h2 h2
    · push_cast; ring
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · push_cast; ring

theorem map_vecOf
    (M : Module.End L (RootModule Tag.F4 L)) (v : List (ℕ × ℤ)) :
    M (vecOf Tag.F4 L v) = (v.map fun x => (x.2 : L) • M (posVec Tag.F4 L x.1)).sum := by
  induction v with
  | nil => simp
  | cons x v ih => rw [vecOf_cons, map_add, map_smul, ih, List.map_cons, List.sum_cons]

theorem eq_sum_posCoord_smul_posVec
    (w : RootModule Tag.F4 L) :
    w = ∑ p ∈ Finset.range 52, posCoord Tag.F4 L p w • posVec Tag.F4 L p := by
  rw [← dim_F4]
  ext b
  obtain ⟨p0, hp0, rfl⟩ := posLabel_surjective b
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single p0]
  · rw [Finsupp.smul_apply, posVec_eq_single hp0, Finsupp.single_eq_same, smul_eq_mul, mul_one]
    simp only [posCoord, hp0, ↓reduceDIte, Finsupp.lapply_apply]
  · intro p hp hne
    rw [Finsupp.smul_apply, posVec_eq_single (Finset.mem_range.1 hp),
      Finsupp.single_eq_of_ne' fun h => hne (posLabel_injective _ _ h), smul_zero]
  · exact fun h => absurd (Finset.mem_range.2 hp0) h

def f4Entries
    (M : Module.End L (RootModule Tag.F4 L)) (u : ℕ) : L :=
  posCoord Tag.F4 L (u / 52) (M (posVec Tag.F4 L (u % 52)))

theorem f4Entries_apply
    (M : Module.End L (RootModule Tag.F4 L)) {a b : ℕ} (hb : b < 52) :
    f4Entries M (52 * a + b) = posCoord Tag.F4 L a (M (posVec Tag.F4 L b)) := by
  have h1 : (52 * a + b) / 52 = a := by omega
  have h2 : (52 * a + b) % 52 = b := by omega
  simp only [f4Entries, h1, h2]

private theorem mul_posCoord_f4Gen_posVec
    (z : L) (g p r : ℕ) (hg : g < 8) (hr : r < dim Tag.F4) :
    z * posCoord Tag.F4 L p (f4Gen L g (posVec Tag.F4 L r)) =
      z * (if p = r then 1 else 0) + z * (coefAt p (f4NilCol g r) : L) := by
  rw [f4Gen_posVec L g hg hr, map_add, posCoord_vecOf p (validVec_f4NilCol g hg hr),
    posCoord_posVec hr, mul_add]

theorem formEval_f4Form
    (M : Module.End L (RootModule Tag.F4 L)) {g : ℕ} (hg : g < 8)
    (hM : Commute M (f4Gen L g)) {p q : ℕ} (hp : p < 52) (hq : q < 52) :
    formEval (f4Entries M) (f4Form g p q) = 0 := by
  have hq' : q < dim Tag.F4 := hq
  set c : ℕ → L := fun r => posCoord Tag.F4 L r (M (posVec Tag.F4 L q)) with hc
  have hL : posCoord Tag.F4 L p (M (f4Gen L g (posVec Tag.F4 L q))) =
      c p + formEval (f4Entries M) ((f4NilCol g q).map fun rz => (52 * p + rz.1, rz.2)) := by
    rw [f4Gen_posVec L g hg hq', map_add, map_add, map_vecOf, map_list_sum, formEval, List.map_map,
      List.map_map]
    congr 1
    refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
    simp only [Function.comp_apply, map_smul, smul_eq_mul]
    rw [f4Entries_apply M (validVec_f4NilCol g hg hq' x hx)]
  have hR : posCoord Tag.F4 L p (f4Gen L g (M (posVec Tag.F4 L q))) =
      c p + ∑ r ∈ Finset.range 52, c r * (coefAt p (f4NilCol g r) : L) := by
    conv_lhs => rw [eq_sum_posCoord_smul_posVec (M (posVec Tag.F4 L q))]
    rw [map_sum, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [Finset.sum_congr rfl fun r hr => by
      rw [mul_posCoord_f4Gen_posVec ((posCoord Tag.F4 L r) (M (posVec Tag.F4 L q)))
        g p r hg (Finset.mem_range.1 hr)],
      Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single p (fun r _ hr => by simp [Ne.symm hr])
      (fun h => absurd (Finset.mem_range.2 hp) h)]
    simp [hc]
  have h2 : formEval (f4Entries M) ((List.range 52).map fun r =>
      (52 * r + q, -coefAt p (f4NilCol g r))) =
      -∑ r ∈ Finset.range 52, c r * (coefAt p (f4NilCol g r) : L) := by
    rw [← Finset.sum_neg_distrib, sum_range_eq_list_sum, formEval, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun r _ => ?_)
    simp only [Function.comp_apply]
    rw [f4Entries_apply M hq]
    push_cast
    ring
  have hcomm := congrArg (fun A : Module.End L (RootModule Tag.F4 L) =>
    posCoord Tag.F4 L p (A (posVec Tag.F4 L q))) hM.eq
  simp only [Module.End.mul_apply] at hcomm
  rw [hL, hR] at hcomm
  rw [f4Form, formEval_append, h2]
  linear_combination hcomm

def f4Lam (u : ℕ) : ℤ :=
  if u / 52 = u % 52 then 1 else 0

end CFSG.StandardType.F4ExplicitPos.CenterCheckFast
end

end
