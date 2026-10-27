module

public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.FreeGroup.Reduce

public section

namespace CFSG.Walter.J1Recog

abbrev Word (k : ℕ) := List (Fin k × Bool)

namespace Word

variable {k : ℕ}

@[expose] def gen (i : Fin k) : Word k := [(i, true)]

@[expose] def inv (w : Word k) : Word k := FreeGroup.invRev w

@[expose] def pow (w : Word k) : ℕ → Word k
  | 0 => []
  | j + 1 => w ++ pow w j

@[expose] def conj (x y : Word k) : Word k := inv y ++ x ++ y

@[expose] def comm (x y : Word k) : Word k := inv x ++ inv y ++ x ++ y

end Word

open Word

variable {k : ℕ}

noncomputable def ev {G : Type*} [Group G] (f : Fin k → G) (w : Word k) : G :=
  FreeGroup.lift f (FreeGroup.mk w)

section Ev

variable {G : Type*} [Group G] (f : Fin k → G)

@[simp] theorem ev_nil : ev f [] = 1 := map_one _

@[simp] theorem ev_append (a b : Word k) : ev f (a ++ b) = ev f a * ev f b := by
  rw [ev, ev, ev, ← FreeGroup.mul_mk, map_mul]

@[simp] theorem ev_gen (i : Fin k) : ev f (gen i) = f i := FreeGroup.lift_apply_of

@[simp] theorem ev_inv (w : Word k) : ev f (inv w) = (ev f w)⁻¹ := by
  rw [ev, ev, inv, ← FreeGroup.inv_mk, map_inv]

@[simp] theorem ev_pow (w : Word k) (j : ℕ) : ev f (pow w j) = ev f w ^ j := by
  induction j with
  | zero => rw [pow, ev_nil, pow_zero]
  | succ j ih => rw [pow, ev_append, ih, pow_succ']

@[simp] theorem ev_conj (x y : Word k) : ev f (conj x y) = (ev f y)⁻¹ * ev f x * ev f y := by
  simp [Word.conj, mul_assoc]

@[simp] theorem ev_comm (x y : Word k) :
    ev f (comm x y) = (ev f x)⁻¹ * (ev f y)⁻¹ * ev f x * ev f y := by
  simp [Word.comm, mul_assoc]

@[simp] theorem ev_reduce (w : Word k) : ev f (FreeGroup.reduce w) = ev f w := by
  rw [ev, ev, FreeGroup.reduce.self]

theorem map_ev {H : Type*} [Group H] (φ : G →* H) (w : Word k) :
    φ (ev f w) = ev (fun i => φ (f i)) w := by
  rw [ev, ev, ← MonoidHom.comp_apply]
  congr 1
  exact FreeGroup.ext_hom _ _ fun i => by simp

end Ev

@[expose] def hRaw (t n m : Word k) : List (Word k) :=
  [pow t 2, pow n 7, pow m 3, inv m ++ n ++ m ++ pow (inv n) 2, comm t m, comm t (conj t n),
    comm t (conj t (pow n 2)), pow (inv n) 3 ++ t ++ n ++ t ++ pow n 2 ++ t,
    inv m ++ inv n ++ t ++ n ++ m ++ pow (inv n) 2 ++ t ++ pow n 2,
    inv m ++ pow (inv n) 2 ++ t ++ pow n 2 ++ m ++ pow (inv n) 2 ++ t ++ n ++ t ++ n ++ t]

@[expose] def wt : Word 5 := gen 0
@[expose] def wn : Word 5 := gen 1
@[expose] def wm : Word 5 := gen 2
@[expose] def ws : Word 5 := gen 3
@[expose] def wu : Word 5 := gen 4

@[expose] def p1Raw : List (Word 5) :=
  hRaw wt wn wm ++ [pow ws 2, comm ws wm, pow (ws ++ wn) 2, pow (wt ++ ws) 5, pow wu 2,
    pow (wu ++ wm) 2, comm wu wt, comm wu ws]

@[expose] def ct1Raw : List (Word 5) :=
  [pow (wu ++ wt ++ conj wt wn) 5, pow (wu ++ wt ++ conj wt (pow wn 2)) 3,
    pow (wu ++ conj wt wn ++ conj wt (pow wn 2)) 5]

@[expose] def ct2Raw : List (Word 5) :=
  [pow (wt ++ wu ++ wt ++ conj wt wn) 5, pow (wt ++ wu ++ wt ++ conj wt (pow wn 2)) 3,
    pow (wt ++ wu ++ conj wt wn ++ conj wt (pow wn 2)) 5]

@[expose] def wa : Word 5 := wm ++ wu

@[expose] def wb : Word 5 := wn ++ wt ++ wu ++ inv wn

@[expose] def wb2 : Word 5 := conj (wt ++ wu) (wm ++ pow wn 4)

inductive Case
  | O1a
  | O1b
  | O2a
  | O2b
  deriving DecidableEq

@[expose] def extraRel : Case → Word 5
  | .O1a => comm wb wa
  | .O1b => comm wb (conj wa (conj wt wn))
  | .O2a => comm wb2 wa
  | .O2b => comm wb2 (conj wa (conj wt wn))

@[expose] def rels (c : Case) : List (Word 5) :=
  (p1Raw ++ (match c with
    | .O1a | .O1b => ct1Raw
    | .O2a | .O2b => ct2Raw) ++ [extraRel c]).map FreeGroup.reduce

@[expose] def hRels : List (Word 3) := (hRaw (gen 0) (gen 1) (gen 2)).map FreeGroup.reduce

@[expose] def relSet {k : ℕ} (l : List (Word k)) : Set (FreeGroup (Fin k)) :=
  {r | ∃ w ∈ l, r = FreeGroup.mk w}

abbrev Pres (c : Case) := PresentedGroup (relSet (rels c))

abbrev PresH := PresentedGroup (relSet hRels)

theorem mk_mem_relSet {l : List (Word k)} {w : Word k} (hw : w ∈ l) :
    FreeGroup.mk w ∈ relSet l :=
  ⟨w, hw, rfl⟩

theorem presentedGroup_mk_eq_ev {rels : Set (FreeGroup (Fin k))} (w : Word k) :
    PresentedGroup.mk rels (FreeGroup.mk w) = ev PresentedGroup.of w := by
  rw [ev]
  congr 1
  exact FreeGroup.ext_hom _ _ fun i => by simp [PresentedGroup.of]

theorem ev_of_mem {l : List (Word k)} {w : Word k} (hw : w ∈ l) :
    ev (PresentedGroup.of (rels := relSet l)) w = 1 := by
  rw [← presentedGroup_mk_eq_ev]
  exact PresentedGroup.one_of_mem (mk_mem_relSet hw)

noncomputable def lift {G : Type*} [Group G] (l : List (Word k)) (f : Fin k → G)
    (hf : ∀ w ∈ l, ev f w = 1) : PresentedGroup (relSet l) →* G :=
  PresentedGroup.toGroup (f := f) (by
    rintro r ⟨w, hw, rfl⟩
    exact hf w hw)

@[simp] theorem lift_of {G : Type*} [Group G] (l : List (Word k)) (f : Fin k → G)
    (hf : ∀ w ∈ l, ev f w = 1) (i : Fin k) :
    lift l f hf (PresentedGroup.of i) = f i :=
  PresentedGroup.toGroup.of _

end CFSG.Walter.J1Recog
