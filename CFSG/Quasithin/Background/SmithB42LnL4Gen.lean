module

public import CFSG.Quasithin.Background.SmithB42LnL4Models

public section

namespace CFSG.Quasithin.B42Ln

open Matrix

local notation "𝕄₄" => Matrix (Fin 4) (Fin 4) (ZMod 2)

@[expose] def toM4 (r : Fin 4 → ℕ) : 𝕄₄ := Matrix.of fun i j => if (r i).testBit j then 1 else 0

@[expose] def ofMI (M M' : 𝕄₄) (h : M * M' = 1) : G4 := ⟨M, det_eq_one_of_mul4 h⟩

theorem coe_ofMI (M M' : 𝕄₄) (h : M * M' = 1) : ((ofMI M M' h : G4) : 𝕄₄) = M := rfl

theorem coe_ofMI_inv {M M' : 𝕄₄} (h : M * M' = 1) : (((ofMI M M' h)⁻¹ : G4) : 𝕄₄) = M' := by
  have h' : M' * M = 1 := (mul_eq_one_comm_of_card_eq (Fin 4) (Fin 4) (ZMod 2) rfl).mp h
  have : (ofMI M M' h)⁻¹ = ofMI M' M h' := inv_eq_of_mul_eq_one_right (Subtype.ext h)
  rw [this]
  rfl

theorem coe_list_prod (l : List G4) :
    ((l.prod : G4) : 𝕄₄) = (l.map fun g : G4 => (g : 𝕄₄)).prod := by
  induction l with
  | nil => rfl
  | cons g l ih => rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih]; rfl

@[expose] def loWord4 (i j : Fin 4) : List (Fin 3) := (upWord4 j i).reverse

theorem loWord4_spec : ∀ i j : Fin 4, j < i →
    Matrix.transvection i j (1 : ZMod 2) = ((loWord4 i j).map yM4).prod := by
  decide

theorem prod_mem_closure_xy (l : List (Fin 3)) (f : Fin 3 → G4) (hf : ∀ s, f s ∈
    Subgroup.closure (Set.range x4 ∪ Set.range y4)) :
    (l.map f).prod ∈ Subgroup.closure (Set.range x4 ∪ Set.range y4) := by
  induction l with
  | nil => exact Subgroup.one_mem _
  | cons s l ih =>
    rw [List.map_cons, List.prod_cons]
    exact Subgroup.mul_mem _ (hf s) ih

theorem prod_y4_coe (l : List (Fin 3)) : (((l.map y4).prod : G4) : 𝕄₄) = (l.map yM4).prod := by
  rw [coe_list_prod, List.map_map]
  rfl

theorem closure_xy4 : Subgroup.closure (Set.range x4 ∪ Set.range y4) = ⊤ := by
  refine JonesParshall.closure_eq_top_of_transvection fun t => ?_
  obtain ⟨i, j, hij, c⟩ := t
  rcases zmod2_eq c with rfl | rfl
  · rw [TransvectionStruct.toSpecialLinearGroup_mk, SpecialLinearGroup.transvection_coeff_zero]
    exact Subgroup.one_mem _
  · rw [TransvectionStruct.toSpecialLinearGroup_mk]
    rcases lt_or_gt_of_ne hij with h | h
    · have e : SpecialLinearGroup.transvection hij (1 : ZMod 2) = ((upWord4 i j).map x4).prod :=
        Subtype.ext (by rw [prod_x4_coe]; exact upWord4_spec i j h)
      rw [e]
      exact prod_mem_closure_xy _ _ fun s => Subgroup.subset_closure (Or.inl ⟨s, rfl⟩)
    · have e : SpecialLinearGroup.transvection hij (1 : ZMod 2) = ((loWord4 i j).map y4).prod :=
        Subtype.ext (by rw [prod_y4_coe]; exact loWord4_spec i j h)
      rw [e]
      exact prod_mem_closure_xy _ _ fun s => Subgroup.subset_closure (Or.inr ⟨s, rfl⟩)

@[expose] def upWordC : Fin 64 → List (Fin 3) :=
  ![[], [0], [0, 1, 0, 1], [1, 0, 1], [0, 1, 2, 1, 0, 1, 2, 1], [1, 2, 1, 0, 1, 2, 1],
    [0, 2, 1, 0, 1, 2], [2, 1, 0, 1, 2], [1], [1, 0], [0, 1, 0], [0, 1],
    [0, 1, 2, 1, 0, 1, 2], [2, 1, 0, 1, 2, 1], [0, 2, 1, 0, 1, 2, 1], [1, 2, 1, 0, 1, 2],
    [1, 2, 1, 2], [1, 2, 1, 0, 2], [0, 1, 0, 2, 1, 2], [2, 1, 0, 2, 1], [0, 1, 2, 1, 0, 2],
    [0, 1, 2, 1, 2], [0, 2, 1, 0, 2, 1], [1, 0, 2, 1, 2], [2, 1, 2], [2, 1, 0, 2],
    [0, 1, 0, 1, 2, 1, 2], [1, 2, 1, 0, 2, 1], [0, 1, 2, 1, 0, 2, 1], [1, 0, 1, 2, 1, 2],
    [0, 2, 1, 0, 2], [0, 2, 1, 2], [2], [0, 2], [0, 2, 1, 0, 1], [2, 1, 0, 1],
    [1, 0, 1, 2, 1, 0, 1], [0, 1, 0, 1, 2, 1, 0, 1], [0, 1, 0, 1, 2], [1, 0, 1, 2], [2, 1],
    [2, 1, 0], [0, 2, 1, 0], [0, 2, 1], [1, 0, 1, 2, 1, 0], [1, 0, 1, 2, 1],
    [0, 1, 0, 1, 2, 1], [0, 1, 0, 1, 2, 1, 0], [1, 2, 1], [1, 2, 1, 0], [1, 0, 2, 1, 0],
    [1, 0, 2, 1], [0, 1, 2, 1, 0], [0, 1, 2, 1], [0, 1, 0, 2, 1], [0, 1, 0, 2, 1, 0], [1, 2],
    [1, 0, 2], [1, 0, 2, 1, 0, 1], [1, 2, 1, 0, 1], [0, 1, 2, 1, 0, 1],
    [0, 1, 0, 2, 1, 0, 1], [0, 1, 0, 2], [0, 1, 2]]

theorem upWordC_spec : ∀ c : Fin 64, ((upWordC c).map xM4).prod = up4 c := by
  decide

theorem mem_of_x4_mem {K : Subgroup G4} (hK : ∀ s, x4 s ∈ K) {u : G4} (hu : u ∈ U4) : u ∈ K := by
  have e : u = ((upWordC (code4 (u : 𝕄₄))).map x4).prod :=
    Subtype.ext (by rw [prod_x4_coe, upWordC_spec, up4_code4 hu])
  rw [e]
  induction (upWordC (code4 (u : 𝕄₄))) with
  | nil => exact K.one_mem
  | cons s l ih =>
    rw [List.map_cons, List.prod_cons]
    exact K.mul_mem (hK s) ih

structure GenEntry4 (k m : ℕ) where
  cs : Fin k → Fin 4 → ℕ
  ci : Fin k → Fin 4 → ℕ
  fc : Fin m → Fin 64
  wx : Fin 3 → List (Fin k × Fin m)
  wy : Fin 3 → List (Fin k × Fin m)

variable {k m : ℕ}

@[expose] def GenEntry4.letter (E : GenEntry4 k m) (p : Fin k × Fin m) : 𝕄₄ :=
  toM4 (E.cs p.1) * up4 (E.fc p.2) * toM4 (E.ci p.1)

@[expose] def GenEntry4.Ok (E : GenEntry4 k m) : Prop :=
  (∀ i, toM4 (E.cs i) * toM4 (E.ci i) = 1) ∧
    (∀ s, ((E.wx s).map E.letter).prod = xM4 s) ∧ (∀ s, ((E.wy s).map E.letter).prod = yM4 s)

instance (E : GenEntry4 k m) : Decidable E.Ok := by
  unfold GenEntry4.Ok
  infer_instance

@[expose] def GenEntry4.conj (E : GenEntry4 k m) (hE : E.Ok) (i : Fin k) : G4 :=
  ofMI (toM4 (E.cs i)) (toM4 (E.ci i)) (hE.1 i)

@[expose] def GenEntry4.gens (E : GenEntry4 k m) (hE : E.Ok) : Set G4 :=
  {x | ∃ i j, x = E.conj hE i * uOf (E.fc j) * (E.conj hE i)⁻¹}

theorem GenEntry4.closure_eq_top (E : GenEntry4 k m) (hE : E.Ok) :
    Subgroup.closure (E.gens hE) = ⊤ := by
  set L : Fin k × Fin m → G4 :=
    fun p => E.conj hE p.1 * uOf (E.fc p.2) * (E.conj hE p.1)⁻¹ with hL
  have hLc : ∀ p, ((L p : G4) : 𝕄₄) = E.letter p := fun p => by
    rw [hL]
    show ((E.conj hE p.1 : G4) : 𝕄₄) * up4 (E.fc p.2) * (((E.conj hE p.1)⁻¹ : G4) : 𝕄₄) = _
    rw [GenEntry4.conj, coe_ofMI, coe_ofMI_inv]
    rfl
  have hw : ∀ w : List (Fin k × Fin m), (w.map L).prod ∈ Subgroup.closure (E.gens hE) := by
    intro w
    induction w with
    | nil => exact Subgroup.one_mem _
    | cons p w ih =>
      rw [List.map_cons, List.prod_cons]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨p.1, p.2, rfl⟩) ih
  have hcoe : ∀ w : List (Fin k × Fin m), (((w.map L).prod : G4) : 𝕄₄) = (w.map E.letter).prod :=
    fun w => by
      rw [coe_list_prod, List.map_map]
      exact congrArg List.prod (List.map_congr_left fun p _ => hLc p)
  rw [eq_top_iff, ← closure_xy4, Subgroup.closure_le]
  rintro _ (⟨s, rfl⟩ | ⟨s, rfl⟩)
  · have e : x4 s = ((E.wx s).map L).prod := Subtype.ext (by rw [hcoe, hE.2.1 s]; rfl)
    rw [e]
    exact hw _
  · have e : y4 s = ((E.wy s).map L).prod := Subtype.ext (by rw [hcoe, hE.2.2 s]; rfl)
    rw [e]
    exact hw _

@[expose] def E_t0 : GenEntry4 4 1 where
  cs := ![![1, 2, 4, 8], ![11, 3, 13, 1], ![3, 1, 9, 4], ![10, 3, 2, 6]]
  ci := ![![1, 2, 4, 8], ![8, 10, 15, 3], ![2, 3, 8, 6], ![6, 4, 12, 5]]
  fc := ![1]
  wx := ![
    [(0, 0)],
    [(3, 0)],
    [(3, 0), (2, 0), (1, 0), (0, 0), (1, 0), (2, 0), (3, 0)]]
  wy := ![
    [(0, 0), (2, 0), (0, 0), (3, 0), (0, 0), (2, 0), (0, 0), (3, 0)],
    [(2, 0), (3, 0), (0, 0), (2, 0), (0, 0), (3, 0), (2, 0)],
    [(2, 0), (3, 0), (1, 0), (2, 0), (1, 0), (3, 0), (2, 0)]]

@[expose] def E_s0 : GenEntry4 4 1 where
  cs := ![![1, 2, 4, 8], ![1, 12, 5, 10], ![15, 10, 4, 3], ![5, 11, 1, 3]]
  ci := ![![1, 2, 4, 8], ![1, 15, 5, 7], ![7, 15, 4, 13], ![4, 12, 5, 10]]
  fc := ![18]
  wx := ![
    [(1, 0), (0, 0), (3, 0), (0, 0), (3, 0), (2, 0), (3, 0), (1, 0)],
    [(1, 0), (3, 0), (0, 0), (3, 0), (1, 0), (0, 0), (1, 0), (3, 0)],
    [(3, 0), (0, 0), (1, 0), (3, 0), (2, 0), (0, 0), (1, 0), (3, 0), (2, 0), (3, 0)]]
  wy := ![
    [(1, 0), (0, 0), (3, 0), (1, 0), (0, 0), (3, 0)],
    [(0, 0), (1, 0), (2, 0), (3, 0), (1, 0), (0, 0), (1, 0), (2, 0), (3, 0), (1, 0)],
    [(0, 0), (1, 0), (3, 0), (0, 0), (1, 0), (3, 0)]]

@[expose] def E_R1 : GenEntry4 2 2 where
  cs := ![![1, 2, 4, 8], ![5, 4, 7, 10]]
  ci := ![![1, 2, 4, 8], ![3, 5, 2, 13]]
  fc := ![2, 12]
  wx := ![
    [(0, 0), (1, 0), (0, 0), (1, 0)],
    [(1, 0), (0, 1), (1, 0), (0, 1), (1, 0)],
    [(1, 0), (1, 1), (0, 1), (1, 0), (0, 0), (0, 1), (1, 0), (0, 1), (1, 1)]]
  wy := ![
    [(1, 0), (0, 0), (0, 1), (1, 1), (0, 0), (1, 1), (0, 0), (0, 1), (1, 0)],
    [(0, 0), (1, 0), (0, 0)],
    [(1, 0), (0, 0), (0, 1), (1, 1), (0, 0), (1, 1), (0, 0), (1, 1), (0, 1), (1, 0)]]

@[expose] def E_R2 : GenEntry4 2 2 where
  cs := ![![1, 2, 4, 8], ![9, 6, 14, 11]]
  ci := ![![1, 2, 4, 8], ![7, 9, 11, 6]]
  fc := ![1, 33]
  wx := ![
    [(0, 0)],
    [(0, 0), (1, 1), (0, 1), (1, 0), (0, 0), (1, 0), (0, 1), (1, 1), (0, 0)],
    [(0, 0), (0, 1)]]
  wy := ![
    [(1, 1), (0, 0), (0, 1), (1, 1)],
    [(0, 0), (1, 0), (0, 1), (1, 0), (0, 0), (1, 0), (0, 1), (1, 0)],
    [(1, 1), (0, 0), (1, 1)]]

@[expose] def E_R3 : GenEntry4 3 2 where
  cs := ![![1, 2, 4, 8], ![10, 14, 13, 11], ![9, 3, 1, 15]]
  ci := ![![1, 2, 4, 8], ![9, 15, 3, 14], ![4, 6, 15, 5]]
  fc := ![12, 22]
  wx := ![
    [(2, 1), (0, 0), (2, 0), (0, 0), (1, 1), (2, 1)],
    [(0, 0), (0, 1), (1, 0), (2, 0), (1, 0)],
    [(0, 0), (2, 0), (0, 1), (2, 1), (1, 1), (2, 0), (0, 0), (1, 0)]]
  wy := ![
    [(0, 0), (1, 0), (0, 0), (2, 1), (1, 1), (2, 0), (0, 1), (2, 1)],
    [(0, 0), (1, 0), (0, 1), (2, 0), (1, 0), (1, 1)],
    [(2, 1), (0, 0), (2, 0), (0, 0), (1, 0), (1, 1), (2, 1)]]

@[expose] def E_R4 : GenEntry4 3 2 where
  cs := ![![1, 2, 4, 8], ![13, 9, 7, 2], ![3, 8, 9, 4]]
  ci := ![![1, 2, 4, 8], ![15, 8, 3, 13], ![6, 7, 8, 2]]
  fc := ![18, 33]
  wx := ![
    [(0, 1), (1, 1), (0, 1), (2, 0), (1, 1)],
    [(0, 0), (1, 0), (1, 1), (2, 1), (1, 0), (1, 1)],
    [(1, 1), (0, 1), (2, 0), (1, 1)]]
  wy := ![
    [(0, 0), (1, 1), (0, 0), (1, 0), (2, 1), (1, 0)],
    [(0, 1), (1, 1), (2, 0), (1, 1), (2, 0)],
    [(1, 0), (2, 0), (2, 1), (0, 1), (2, 1), (1, 0)]]

theorem entries_ok : E_t0.Ok ∧ E_s0.Ok ∧ E_R1.Ok ∧ E_R2.Ok ∧ E_R3.Ok ∧ E_R4.Ok := by
  decide

@[expose] def tvL : List (Fin 64) := [1, 2, 3, 4, 5, 6, 7, 8, 10, 16, 20, 24, 30, 32, 36, 48, 52]

@[expose] def ntvL : List (Fin 64) := [12, 14, 18, 22, 26, 28, 33, 37, 51, 55]

set_option maxRecDepth 100000 in
theorem invol_cases : ∀ c : Fin 64, up4 c * up4 c = 1 → c ≠ 0 → c ∈ tvL ∨ c ∈ ntvL := by
  decide +kernel

@[expose] def invTab4 : List (Fin 64 × (Fin 4 → ℕ) × (Fin 4 → ℕ)) :=
  [(1, ![1, 2, 4, 8], ![1, 2, 4, 8]), (2, ![1, 4, 2, 8], ![1, 4, 2, 8]),
    (3, ![1, 6, 2, 8], ![1, 4, 6, 8]), (4, ![1, 8, 2, 4], ![1, 4, 8, 2]),
    (5, ![1, 10, 2, 4], ![1, 4, 8, 6]), (6, ![1, 12, 2, 4], ![1, 4, 8, 10]),
    (7, ![1, 14, 2, 4], ![1, 4, 8, 14]), (8, ![2, 4, 1, 8], ![4, 1, 2, 8]),
    (10, ![1, 4, 3, 8], ![1, 5, 2, 8]), (12, ![1, 2, 8, 4], ![1, 2, 8, 4]),
    (14, ![1, 2, 12, 4], ![1, 2, 8, 12]), (16, ![2, 8, 1, 4], ![4, 1, 8, 2]),
    (18, ![1, 2, 4, 8], ![1, 2, 4, 8]), (20, ![1, 8, 3, 4], ![1, 5, 8, 2]),
    (22, ![1, 2, 12, 8], ![1, 2, 12, 8]), (24, ![2, 12, 1, 4], ![4, 1, 8, 10]),
    (26, ![1, 2, 4, 12], ![1, 2, 4, 12]), (28, ![1, 2, 8, 12], ![1, 2, 12, 4]),
    (30, ![1, 12, 3, 4], ![1, 5, 8, 10]), (32, ![4, 8, 1, 2], ![4, 8, 1, 2]),
    (33, ![1, 4, 2, 8], ![1, 4, 2, 8]), (36, ![1, 8, 2, 5], ![1, 4, 9, 2]),
    (37, ![1, 4, 10, 8], ![1, 12, 2, 8]), (48, ![2, 8, 1, 6], ![4, 1, 9, 2]),
    (51, ![1, 2, 6, 8], ![1, 2, 6, 8]), (52, ![1, 8, 3, 5], ![1, 5, 9, 2]),
    (55, ![1, 2, 14, 8], ![1, 2, 14, 8])]

@[expose] def InvGood4 (c : Fin 64) : Prop :=
  match invTab4.find? (fun t => t.1 = c) with
  | some t => toM4 t.2.1 * toM4 t.2.2 = 1 ∧
      (c ∈ tvL → toM4 t.2.1 * up4 c * toM4 t.2.2 = up4 1) ∧
      (c ∈ ntvL → toM4 t.2.1 * up4 c * toM4 t.2.2 = up4 18)
  | none => False

instance (c : Fin 64) : Decidable (InvGood4 c) := by
  unfold InvGood4
  split <;> infer_instance

theorem invTab4_spec : ∀ c : Fin 64, c ∈ tvL ∨ c ∈ ntvL → InvGood4 c := by
  decide

@[expose] def pairTab4 : List (Fin 64 × Fin 64 × (Fin 4 → ℕ) × (Fin 4 → ℕ) × Fin 2) :=
  [(1, 33, ![1, 2, 4, 8], ![1, 2, 4, 8], 1), (1, 37, ![5, 2, 4, 8], ![5, 2, 4, 8], 1),
    (2, 12, ![1, 2, 4, 8], ![1, 2, 4, 8], 0), (2, 14, ![1, 2, 4, 12], ![1, 2, 4, 12], 0),
    (2, 18, ![1, 4, 2, 8], ![1, 4, 2, 8], 1), (2, 22, ![3, 4, 2, 8], ![5, 4, 2, 8], 1),
    (2, 26, ![1, 4, 2, 12], ![1, 4, 2, 10], 1), (2, 28, ![3, 4, 2, 12], ![5, 4, 2, 10], 1),
    (3, 51, ![1, 6, 2, 8], ![1, 4, 6, 8], 1), (3, 55, ![3, 6, 2, 8], ![5, 4, 6, 8], 1),
    (4, 12, ![1, 8, 2, 4], ![1, 4, 8, 2], 1), (4, 14, ![3, 8, 2, 4], ![5, 4, 8, 2], 1),
    (4, 18, ![1, 2, 8, 4], ![1, 2, 8, 4], 0), (4, 22, ![1, 2, 8, 12], ![1, 2, 12, 4], 0),
    (4, 26, ![3, 8, 2, 12], ![5, 4, 10, 2], 1), (4, 28, ![1, 8, 2, 12], ![1, 4, 10, 2], 1),
    (4, 33, ![1, 4, 8, 2], ![1, 8, 2, 4], 0), (4, 37, ![1, 4, 8, 10], ![1, 12, 2, 4], 0),
    (4, 51, ![1, 2, 8, 6], ![1, 2, 10, 4], 0), (4, 55, ![1, 2, 8, 14], ![1, 2, 14, 4], 0),
    (5, 33, ![5, 10, 4, 8], ![5, 10, 4, 8], 1), (5, 37, ![1, 10, 4, 8], ![1, 10, 4, 8], 1),
    (6, 12, ![3, 12, 2, 4], ![5, 4, 8, 10], 1), (6, 14, ![1, 12, 2, 4], ![1, 4, 8, 10], 1),
    (6, 18, ![3, 12, 2, 8], ![5, 4, 10, 8], 1), (6, 22, ![1, 12, 2, 8], ![1, 4, 10, 8], 1),
    (6, 26, ![1, 2, 12, 4], ![1, 2, 8, 12], 0), (6, 28, ![1, 2, 12, 8], ![1, 2, 12, 8], 0),
    (7, 51, ![3, 14, 2, 8], ![5, 4, 14, 8], 1), (7, 55, ![1, 14, 2, 8], ![1, 4, 14, 8], 1),
    (8, 12, ![2, 4, 1, 8], ![4, 1, 2, 8], 1), (8, 14, ![2, 4, 1, 12], ![4, 1, 2, 10], 1),
    (8, 18, ![2, 1, 4, 8], ![2, 1, 4, 8], 0), (8, 22, ![3, 4, 1, 12], ![4, 5, 2, 10], 1),
    (8, 26, ![2, 1, 4, 12], ![2, 1, 4, 12], 0), (8, 28, ![3, 4, 1, 8], ![4, 5, 2, 8], 1),
    (10, 12, ![2, 4, 3, 12], ![5, 1, 2, 10], 1), (10, 14, ![2, 4, 3, 8], ![5, 1, 2, 8], 1),
    (10, 18, ![1, 4, 3, 12], ![1, 5, 2, 10], 1), (10, 22, ![1, 3, 4, 12], ![1, 3, 4, 12], 0),
    (10, 26, ![1, 4, 3, 8], ![1, 5, 2, 8], 1), (10, 28, ![1, 3, 4, 8], ![1, 3, 4, 8], 0),
    (16, 12, ![2, 1, 8, 4], ![2, 1, 8, 4], 0), (16, 14, ![3, 8, 1, 12], ![4, 5, 10, 2], 1),
    (16, 18, ![2, 8, 1, 4], ![4, 1, 8, 2], 1), (16, 22, ![2, 8, 1, 12], ![4, 1, 10, 2], 1),
    (16, 26, ![3, 8, 1, 4], ![4, 5, 8, 2], 1), (16, 28, ![2, 1, 8, 12], ![2, 1, 12, 4], 0),
    (20, 12, ![1, 8, 3, 12], ![1, 5, 10, 2], 1), (20, 14, ![1, 3, 8, 12], ![1, 3, 12, 4], 0),
    (20, 18, ![2, 8, 3, 12], ![5, 1, 10, 2], 1), (20, 22, ![2, 8, 3, 4], ![5, 1, 8, 2], 1),
    (20, 26, ![1, 3, 8, 4], ![1, 3, 8, 4], 0), (20, 28, ![1, 8, 3, 4], ![1, 5, 8, 2], 1),
    (24, 12, ![3, 12, 1, 8], ![4, 5, 10, 8], 1), (24, 14, ![2, 1, 12, 4], ![2, 1, 8, 12], 0),
    (24, 18, ![3, 12, 1, 4], ![4, 5, 8, 10], 1), (24, 22, ![2, 1, 12, 8], ![2, 1, 12, 8], 0),
    (24, 26, ![2, 12, 1, 4], ![4, 1, 8, 10], 1), (24, 28, ![2, 12, 1, 8], ![4, 1, 10, 8], 1),
    (30, 12, ![1, 3, 12, 8], ![1, 3, 12, 8], 0), (30, 14, ![1, 12, 3, 8], ![1, 5, 10, 8], 1),
    (30, 18, ![1, 3, 12, 4], ![1, 3, 8, 12], 0), (30, 22, ![1, 12, 3, 4], ![1, 5, 8, 10], 1),
    (30, 26, ![2, 12, 3, 8], ![5, 1, 10, 8], 1), (30, 28, ![2, 12, 3, 4], ![5, 1, 8, 10], 1),
    (32, 33, ![4, 8, 1, 2], ![4, 8, 1, 2], 1), (32, 37, ![4, 8, 1, 10], ![4, 10, 1, 2], 1),
    (36, 33, ![4, 8, 5, 10], ![5, 10, 1, 2], 1), (36, 37, ![4, 8, 5, 2], ![5, 8, 1, 2], 1),
    (48, 51, ![2, 8, 1, 6], ![4, 1, 9, 2], 1), (48, 55, ![2, 8, 1, 14], ![4, 1, 11, 2], 1),
    (52, 51, ![2, 8, 3, 14], ![5, 1, 11, 2], 1), (52, 55, ![2, 8, 3, 6], ![5, 1, 9, 2], 1)]

@[expose] def pairTab0 : List (Fin 64 × Fin 64 × (Fin 4 → ℕ) × (Fin 4 → ℕ) × Fin 2) :=
  [(12, 22, ![1, 2, 4, 8], ![1, 2, 4, 8], 0), (12, 26, ![1, 3, 12, 8], ![1, 3, 12, 8], 0),
    (14, 18, ![1, 3, 8, 12], ![1, 3, 12, 4], 0), (14, 28, ![1, 2, 4, 12], ![1, 2, 4, 12], 0),
    (18, 14, ![1, 2, 8, 4], ![1, 2, 8, 4], 0), (18, 28, ![1, 3, 12, 4], ![1, 3, 8, 12], 0),
    (18, 33, ![1, 2, 4, 8], ![1, 2, 4, 8], 1), (18, 37, ![1, 10, 4, 8], ![1, 10, 4, 8], 1),
    (18, 51, ![1, 6, 4, 8], ![1, 6, 4, 8], 1), (18, 55, ![1, 14, 4, 8], ![1, 14, 4, 8], 1),
    (22, 12, ![1, 3, 4, 12], ![1, 3, 4, 12], 0), (22, 26, ![1, 2, 8, 12], ![1, 2, 12, 4], 0),
    (22, 33, ![1, 2, 12, 8], ![1, 2, 12, 8], 1),
    (22, 37, ![1, 10, 12, 8], ![1, 10, 12, 8], 1),
    (22, 51, ![1, 6, 12, 8], ![1, 14, 12, 8], 1),
    (22, 55, ![1, 14, 12, 8], ![1, 6, 12, 8], 1),
    (26, 12, ![1, 2, 12, 4], ![1, 2, 8, 12], 0), (26, 22, ![1, 3, 8, 4], ![1, 3, 8, 4], 0),
    (28, 14, ![1, 3, 4, 8], ![1, 3, 4, 8], 0), (28, 18, ![1, 2, 12, 8], ![1, 2, 12, 8], 0),
    (33, 18, ![1, 4, 2, 8], ![1, 4, 2, 8], 1), (33, 22, ![1, 12, 2, 8], ![1, 4, 10, 8], 1),
    (33, 51, ![1, 6, 2, 8], ![1, 4, 6, 8], 1), (33, 55, ![1, 14, 2, 8], ![1, 4, 14, 8], 1),
    (37, 18, ![1, 4, 10, 8], ![1, 12, 2, 8], 1),
    (37, 22, ![1, 12, 10, 8], ![1, 12, 10, 8], 1),
    (37, 51, ![1, 6, 10, 8], ![1, 12, 14, 8], 1),
    (37, 55, ![1, 14, 10, 8], ![1, 12, 6, 8], 1), (51, 18, ![1, 4, 6, 8], ![1, 6, 2, 8], 1),
    (51, 22, ![1, 12, 6, 8], ![1, 14, 10, 8], 1), (51, 33, ![1, 2, 6, 8], ![1, 2, 6, 8], 1),
    (51, 37, ![1, 10, 6, 8], ![1, 10, 14, 8], 1),
    (55, 18, ![1, 4, 14, 8], ![1, 14, 2, 8], 1),
    (55, 22, ![1, 12, 14, 8], ![1, 6, 10, 8], 1),
    (55, 33, ![1, 2, 14, 8], ![1, 2, 14, 8], 1), (55, 37, ![1, 10, 14, 8], ![1, 10, 6, 8], 1)]

@[expose] def PairGood (tab : List (Fin 64 × Fin 64 × (Fin 4 → ℕ) × (Fin 4 → ℕ) × Fin 2))
    (f₀ f₁ : Fin 2 → Fin 64) (cx cy : Fin 64) : Prop :=
  match tab.find? (fun t => t.1 = cx ∧ t.2.1 = cy) with
  | some t => toM4 t.2.2.1 * toM4 t.2.2.2.1 = 1 ∧
      toM4 t.2.2.1 * up4 cx * toM4 t.2.2.2.1 = up4 (f₀ t.2.2.2.2) ∧
      toM4 t.2.2.1 * up4 cy * toM4 t.2.2.2.1 = up4 (f₁ t.2.2.2.2)
  | none => False

instance (tab : List (Fin 64 × Fin 64 × (Fin 4 → ℕ) × (Fin 4 → ℕ) × Fin 2)) (f₀ f₁ : Fin 2 → Fin 64)
    (cx cy : Fin 64) : Decidable (PairGood tab f₀ f₁ cx cy) := by
  unfold PairGood
  split <;> infer_instance

set_option maxRecDepth 100000 in
theorem pairTab4_spec : ∀ cx ∈ tvL, ∀ cy ∈ ntvL, up4 cx * up4 cy = up4 cy * up4 cx →
    PairGood pairTab4 ![2, 1] ![12, 33] cx cy := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem pairTab0_spec : ∀ cx ∈ ntvL, ∀ cy ∈ ntvL, cx ≠ cy → up4 cx * up4 cy = up4 cy * up4 cx →
    code4 (up4 cx * up4 cy) ∈ ntvL → PairGood pairTab0 ![12, 18] ![22, 33] cx cy := by
  decide +kernel

@[expose] def tvCA : List (Fin 64 × (Fin 4 → ZMod 2) × (Fin 4 → ZMod 2)) :=
  [(1, ![1, 0, 0, 0], ![0, 1, 0, 0]), (2, ![1, 0, 0, 0], ![0, 0, 1, 0]),
    (3, ![1, 0, 0, 0], ![0, 1, 1, 0]), (4, ![1, 0, 0, 0], ![0, 0, 0, 1]),
    (5, ![1, 0, 0, 0], ![0, 1, 0, 1]), (6, ![1, 0, 0, 0], ![0, 0, 1, 1]),
    (7, ![1, 0, 0, 0], ![0, 1, 1, 1]), (8, ![0, 1, 0, 0], ![0, 0, 1, 0]),
    (10, ![1, 1, 0, 0], ![0, 0, 1, 0]), (16, ![0, 1, 0, 0], ![0, 0, 0, 1]),
    (20, ![1, 1, 0, 0], ![0, 0, 0, 1]), (24, ![0, 1, 0, 0], ![0, 0, 1, 1]),
    (30, ![1, 1, 0, 0], ![0, 0, 1, 1]), (32, ![0, 0, 1, 0], ![0, 0, 0, 1]),
    (36, ![1, 0, 1, 0], ![0, 0, 0, 1]), (48, ![0, 1, 1, 0], ![0, 0, 0, 1]),
    (52, ![1, 1, 1, 0], ![0, 0, 0, 1])]

@[expose] def tvC (c : Fin 64) : Fin 4 → ZMod 2 :=
  ((tvCA.find? fun t => t.1 = c).map (·.2.1)).getD 0

@[expose] def tvA (c : Fin 64) : Fin 4 → ZMod 2 :=
  ((tvCA.find? fun t => t.1 = c).map (·.2.2)).getD 0

theorem tvCA_spec : ∀ c ∈ tvL, up4 c = 1 + vecMulVec (tvC c) (tvA c) ∧ tvC c ≠ 0 ∧ tvA c ≠ 0 ∧
    tvA c ⬝ᵥ tvC c = 0 := by
  decide

theorem compat_center_or_axis : ∀ cx ∈ tvL, ∀ cy ∈ tvL, cx ≠ cy →
    up4 cx * up4 cy = up4 cy * up4 cx → code4 (up4 cx * up4 cy) ∈ tvL →
    tvC cx = tvC cy ∨ tvA cx = tvA cy := by
  decide

@[expose] def nbT (x : Fin 64) : List (Fin 64) :=
  tvL.filter fun y => decide (y ≠ x ∧ up4 x * up4 y = up4 y * up4 x ∧ code4 (up4 x * up4 y) ∈ tvL)

@[expose] def nbN (x : Fin 64) : List (Fin 64) :=
  ntvL.filter fun y =>
    decide (y ≠ x ∧ up4 x * up4 y = up4 y * up4 x ∧ code4 (up4 x * up4 y) ∈ ntvL)

theorem nbT_short : ∀ x ∈ ([8, 10, 24, 30] : List (Fin 64)), (nbT x).length ≤ 4 := by
  decide

theorem nbN_short : ∀ x ∈ ntvL, x ≠ 18 → x ≠ 22 → (nbN x).length ≤ 4 := by
  decide

theorem nbT_low : ∀ x ∈ ([1, 2, 3, 5, 6, 7] : List (Fin 64)),
    ∀ y ∈ ([16, 20, 32, 36, 48, 52] : List (Fin 64)),
    ¬ (up4 x * up4 y = up4 y * up4 x ∧ code4 (up4 x * up4 y) ∈ tvL) := by
  decide

theorem tv_high : ∀ y : Fin 64, y ∈ tvL → y ∉ ([8, 10, 24, 30] : List (Fin 64)) → 8 ≤ (y : ℕ) →
    y ∈ ([16, 20, 32, 36, 48, 52] : List (Fin 64)) := by
  decide

end CFSG.Quasithin.B42Ln
