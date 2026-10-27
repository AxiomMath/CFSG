module

public import CFSG.Quasithin.Recognition.J2RecCzModel
public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.Presentation
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition

open CFSG.Quasithin.J2Cz CFSG.Quasithin.J2Cz.QM CFSG.Quasithin.J2Cz.F2

@[expose] def relsH : List (List (Fin 7 × Bool)) :=
  j3WordsRest.filter (fun r => !(r.any fun x => x.1.val == 6))

@[expose] noncomputable def aL : L0 := ⟨phiA, phiA_mem⟩

@[expose] noncomputable def bL : L0 := ⟨phiB, phiB_mem⟩

@[expose] noncomputable def modelTuple : Fin 6 → Model
  | 0 => ⟨⟨i, o, i, i, i⟩, aL * bL⁻¹ * aL * bL * aL * bL⟩
  | 1 => ⟨⟨o, o, o, i, o⟩, 1⟩
  | 2 => ⟨⟨i, o, o, o, i⟩, 1⟩
  | 3 => ⟨⟨i, o, o, o, o⟩, 1⟩
  | 4 => ⟨⟨o, i, o, o, o⟩, aL * bL * aL * bL⁻¹ * aL * bL⁻¹⟩
  | 5 => ⟨⟨o, o, o, o, o⟩, bL * aL * bL⁻¹⟩

@[expose] noncomputable def modelTuple7 : Fin 7 → Model := fun k =>
  if h : k.val < 6 then modelTuple ⟨k.val, h⟩ else 1

@[expose] noncomputable def evalWord {X : Type*} [Group X] (e : Fin 7 → X)
    (r : List (Fin 7 × Bool)) : X :=
  (r.map fun x => cond x.2 (e x.1) (e x.1)⁻¹).prod

theorem lift_mk_eq_evalWord {X : Type*} [Group X] (e : Fin 7 → X) (r : List (Fin 7 × Bool)) :
    FreeGroup.lift e (FreeGroup.mk r) = evalWord e r := by
  rw [FreeGroup.lift_mk]
  rfl

def IsTrivialCheck (P : Model) : Prop :=
  P.left = 1 ∧ ∀ j : Fin 4, (L0.subtype P.right) (x j.succ) = x j.succ

noncomputable instance (P : Model) : Decidable (IsTrivialCheck P) :=
  inferInstanceAs (Decidable (P.left = 1 ∧
    ∀ j : Fin 4, (L0.subtype P.right) (x j.succ) = x j.succ))

theorem eq_one_of_check {P : Model} (h : IsTrivialCheck P) : P = 1 := by
  apply SemidirectProduct.ext
  · exact h.1
  · apply Subtype.ext
    apply aut_ext
    intro j
    exact h.2 j

theorem modelTuple_relsH : ∀ r ∈ relsH, IsTrivialCheck (evalWord modelTuple7 r) := by
  decide +kernel

theorem modelTuple_zero_cube : modelTuple 0 * modelTuple 0 * modelTuple 0 = 1 :=
  eq_one_of_check (by decide +kernel)

theorem modelTuple_zero_ne_one : modelTuple 0 ≠ 1 := by
  intro h
  have h1 : (modelTuple 0).left = (1 : Model).left := by rw [h]
  revert h1
  decide +kernel

@[expose] noncomputable def evalM (r : List (Fin 6 × Bool)) : Model :=
  (r.map fun x => cond x.2 (modelTuple x.1) (modelTuple x.1)⁻¹).prod

theorem evalM_mem (r : List (Fin 6 × Bool)) :
    evalM r ∈ Subgroup.closure (Set.range modelTuple) := by
  apply Subgroup.list_prod_mem
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  have h : modelTuple x.1 ∈ Subgroup.closure (Set.range modelTuple) :=
    Subgroup.subset_closure ⟨x.1, rfl⟩
  cases x.2
  · exact inv_mem h
  · exact h

@[expose] def xWord : Fin 4 → List (Fin 6 × Bool)
  | 0 => [(4, true), (4, true), (4, true)]
  | 1 => [(3, true), (4, false), (1, true), (4, true)]
  | 2 => [(1, true)]
  | 3 => [(2, true), (3, true)]

@[expose] def aWord : List (Fin 6 × Bool) := [(1, true), (3, true), (4, false), (0, true)]

@[expose] def bWord : List (Fin 6 × Bool) :=
  [(0, true), (4, true), (4, true), (5, true), (2, true), (4, true)]

theorem evalM_z : evalM [(3, true)] = ⟨QM.z, 1⟩ := rfl

theorem evalM_x : ∀ j : Fin 4, IsTrivialCheck ((evalM (xWord j))⁻¹ * ⟨x j.succ, 1⟩) := by
  decide +kernel

theorem evalM_a : IsTrivialCheck ((evalM aWord)⁻¹ * ⟨1, aL⟩) := by
  decide +kernel

theorem evalM_b : IsTrivialCheck ((evalM bWord)⁻¹ * ⟨1, bL⟩) := by
  decide +kernel

theorem liftT_mem {G : Type*} [Group G] (S : Subgroup G) {w : G} {y : Fin 4 → G} (hw : w ∈ S)
    (hy : ∀ j, y j ∈ S) (p : QM) {g : G} (hg : g ∈ S) : liftT w y p g ∈ S := by
  have hp : ∀ (t : F2) (u : G), u ∈ S → pw u t ∈ S := by
    intro t u hu
    cases t
    · exact one_mem S
    · exact hu
  unfold liftT
  exact mul_mem (hp _ _ hw) (mul_mem (hp _ _ (hy 0)) (mul_mem (hp _ _ (hy 1))
    (mul_mem (hp _ _ (hy 2)) (mul_mem (hp _ _ (hy 3)) hg))))

@[expose] def a5words : List (List ℕ) := [
  [],
  [0],
  [1],
  [2],
  [0, 1],
  [0, 2],
  [1, 0],
  [2, 0],
  [0, 1, 0],
  [0, 2, 0],
  [1, 0, 1],
  [1, 0, 2],
  [2, 0, 1],
  [2, 0, 2],
  [0, 1, 0, 1],
  [0, 1, 0, 2],
  [0, 2, 0, 1],
  [0, 2, 0, 2],
  [1, 0, 1, 0],
  [1, 0, 2, 0],
  [2, 0, 1, 0],
  [2, 0, 2, 0],
  [0, 1, 0, 1, 0],
  [0, 1, 0, 2, 0],
  [0, 2, 0, 1, 0],
  [0, 2, 0, 2, 0],
  [1, 0, 1, 0, 2],
  [1, 0, 2, 0, 1],
  [1, 0, 2, 0, 2],
  [2, 0, 1, 0, 1],
  [2, 0, 1, 0, 2],
  [2, 0, 2, 0, 1],
  [0, 1, 0, 2, 0, 1],
  [0, 1, 0, 2, 0, 2],
  [0, 2, 0, 1, 0, 1],
  [0, 2, 0, 1, 0, 2],
  [1, 0, 1, 0, 2, 0],
  [1, 0, 2, 0, 1, 0],
  [2, 0, 1, 0, 2, 0],
  [2, 0, 2, 0, 1, 0],
  [0, 1, 0, 2, 0, 1, 0],
  [0, 2, 0, 1, 0, 2, 0],
  [1, 0, 1, 0, 2, 0, 1],
  [1, 0, 1, 0, 2, 0, 2],
  [1, 0, 2, 0, 1, 0, 1],
  [1, 0, 2, 0, 1, 0, 2],
  [2, 0, 1, 0, 2, 0, 1],
  [2, 0, 1, 0, 2, 0, 2],
  [2, 0, 2, 0, 1, 0, 1],
  [2, 0, 2, 0, 1, 0, 2],
  [0, 1, 0, 2, 0, 1, 0, 1],
  [0, 1, 0, 2, 0, 1, 0, 2],
  [0, 2, 0, 1, 0, 2, 0, 1],
  [0, 2, 0, 1, 0, 2, 0, 2],
  [1, 0, 2, 0, 1, 0, 2, 0],
  [2, 0, 1, 0, 2, 0, 1, 0],
  [0, 1, 0, 2, 0, 1, 0, 2, 0],
  [0, 2, 0, 1, 0, 2, 0, 1, 0],
  [1, 0, 2, 0, 1, 0, 2, 0, 1],
  [0, 1, 0, 2, 0, 1, 0, 2, 0, 1]
]

@[expose] def evalP (w : List ℕ) : Equiv.Perm (Fin 5) :=
  (w.map fun c => if c = 0 then pa else if c = 1 then pb else pb⁻¹).prod

@[expose] noncomputable def evalL (w : List ℕ) : L0 :=
  (w.map fun c => if c = 0 then aL else if c = 1 then bL else bL⁻¹).prod

theorem a5words_spec : ∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 → ∃ w ∈ a5words,
    evalP w = σ := by
  decide +kernel

theorem linePerm_aL : linePerm (aL : MulAut QM) = pa := linePerm_phiA

theorem linePerm_bL : linePerm (bL : MulAut QM) = pb := linePerm_phiB

theorem linePerm_evalL (w : List ℕ) : linePerm (evalL w : MulAut QM) = evalP w := by
  have h : ∀ l : L0, linePerm (l : MulAut QM) = (linePermHom.comp L0.subtype) l := fun l => rfl
  have ha : (linePermHom.comp L0.subtype) aL = pa := linePerm_aL
  have hb : (linePermHom.comp L0.subtype) bL = pb := linePerm_bL
  rw [h, evalL, map_list_prod, evalP, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c _
  simp only [Function.comp]
  by_cases h0 : c = 0
  · simp [h0, ha]
  · by_cases h1 : c = 1
    · simp [h1, hb]
    · simp [h0, h1, map_inv, hb]

theorem exists_evalL_eq (α : L0) : ∃ w ∈ a5words, evalL w = α := by
  have hs : Equiv.Perm.sign (linePerm (α : MulAut QM)) = 1 :=
    Equiv.Perm.mem_alternatingGroup.mp (linePerm_mem_alternatingGroup α.2)
  obtain ⟨w, hw, hwe⟩ := a5words_spec _ hs
  refine ⟨w, hw, Subtype.ext (aut_ext fun j => ?_)⟩
  have h : linePerm (evalL w : MulAut QM) = linePerm (α : MulAut QM) := by
    rw [linePerm_evalL, hwe]
  rw [(evalL w).2, α.2, h]

theorem evalL_mem (K : Subgroup L0) (ha : aL ∈ K) (hb : bL ∈ K) (w : List ℕ) : evalL w ∈ K := by
  apply Subgroup.list_prod_mem
  intro y hy
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hy
  by_cases h0 : c = 0
  · simp [h0, ha]
  · by_cases h1 : c = 1
    · simp [h1, hb]
    · simp [h0, h1, hb]

theorem closure_modelTuple : Subgroup.closure (Set.range modelTuple) = ⊤ := by
  set K := Subgroup.closure (Set.range modelTuple) with hK
  have hz : (⟨QM.z, 1⟩ : Model) ∈ K := evalM_z ▸ evalM_mem _
  have hx : ∀ j : Fin 4, (⟨x j.succ, 1⟩ : Model) ∈ K := fun j => by
    have h := eq_one_of_check (evalM_x j)
    rw [inv_mul_eq_one] at h
    rw [← h]
    exact evalM_mem _
  have ha : (⟨1, aL⟩ : Model) ∈ K := by
    have h := eq_one_of_check evalM_a
    rw [inv_mul_eq_one] at h
    rw [← h]
    exact evalM_mem _
  have hb : (⟨1, bL⟩ : Model) ∈ K := by
    have h := eq_one_of_check evalM_b
    rw [inv_mul_eq_one] at h
    rw [← h]
    exact evalM_mem _
  have hq : ∀ p : QM, (⟨p, 1⟩ : Model) ∈ K := fun p => by
    have h : p ∈ K.comap (SemidirectProduct.inl : QM →* Model) := by
      rw [← liftT_x p]
      exact liftT_mem (K.comap (SemidirectProduct.inl : QM →* Model)) (w := QM.z)
        (y := fun j => x j.succ) hz hx p (one_mem _)
    exact h
  have hl : ∀ l : L0, (⟨1, l⟩ : Model) ∈ K := fun l => by
    obtain ⟨w, _, rfl⟩ := exists_evalL_eq l
    have h : evalL w ∈ K.comap (SemidirectProduct.inr : L0 →* Model) :=
      evalL_mem _ ha hb w
    exact h
  rw [eq_top_iff]
  intro g _
  have : g = ⟨g.left, 1⟩ * ⟨1, g.right⟩ := by
    apply SemidirectProduct.ext <;> simp
  rw [this]
  exact mul_mem (hq _) (hl _)

theorem eq_one_or_z_of_central (c : Model) (hc : ∀ g : Model, g * c = c * g) :
    c = 1 ∨ c = ⟨QM.z, 1⟩ := by
  have hp : ∀ p : QM, p * c.left = c.left * (L0.subtype c.right) p := fun p => by
    have h := congrArg SemidirectProduct.left (hc ⟨p, 1⟩)
    simpa using h
  have hl : ∀ k : Fin 5, (L0.subtype c.right) (x k) = x (linePerm (c.right : MulAut QM) k) :=
    fun k => c.right.2 k
  have hconj : ∀ k : Fin 5, x (linePerm (c.right : MulAut QM) k) = x k := by
    intro k
    have h1 := hp (x k)
    rw [hl k] at h1
    have h4 : x (linePerm (c.right : MulAut QM) k) = c.left⁻¹ * x k * c.left := by
      calc x (linePerm (c.right : MulAut QM) k)
          = c.left⁻¹ * (c.left * x (linePerm (c.right : MulAut QM) k)) := by group
        _ = c.left⁻¹ * x k * c.left := by rw [← h1]; group
    have h5 := conj_x c.left⁻¹ k
    simp only [inv_inv] at h5
    rcases h5 with h5 | h5
    · exact h4.trans h5
    · exact absurd (h4.trans h5) (x_ne _ _)
  have hx : ∀ k : Fin 5, c.left * x k = x k * c.left := by
    intro k
    have h1 := hp (x k)
    rw [hl k, hconj k] at h1
    exact h1.symm
  have hr : c.right = 1 :=
    Subtype.ext (aut_ext fun j => (hl j.succ).trans (hconj j.succ))
  rcases eq_of_comm_x c.left hx with h | h
  · left
    exact SemidirectProduct.ext h hr
  · right
    exact SemidirectProduct.ext h hr

end CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition
