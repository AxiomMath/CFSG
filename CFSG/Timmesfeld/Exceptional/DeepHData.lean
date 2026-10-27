module

public import CFSG.Timmesfeld.Exceptional.DeepQData
public import CFSG.Timmesfeld.Exceptional.TotallyOpposite

public section

namespace CFSG.Timmesfeld.Moufang.Deep

open CFSG.Certificates CFSG.Certificates.CosetEnumeration

variable {G : Type*} [Group G]

@[expose] def ua : List (Fin 4 × Bool) := [(1, false), (2, true), (1, true), (3, true)]

@[expose] def ub : List (Fin 4 × Bool) :=
  [(2, true), (1, true), (3, true), (1, true), (3, false), (0, false), (1, false), (0, false)]

@[expose] def zw : List (Fin 4 × Bool) :=
  [(1, true), (0, true), (2, true), (1, true), (3, true), (2, true), (1, true), (0, true),
    (1, true), (3, true), (2, true), (1, true), (3, true), (0, true)]

@[expose] def cwW : Fin 8 → List (Fin 4 × Bool) :=
  ![[(3, true), (0, true), (1, true), (2, true), (3, true), (1, true)],
    [(3, true), (1, true), (2, true), (3, true), (1, true)],
    [(1, true), (3, true), (2, true), (1, true)],
    [(2, true), (0, true), (1, true), (3, true), (2, true), (1, true)],
    [(2, true), (1, true), (3, true), (2, true), (1, true)],
    [(0, true), (1, true), (3, true), (2, true), (1, true)],
    [(1, true), (2, true), (3, true), (1, true)],
    [(0, true), (1, true), (2, true), (3, true), (1, true)]]

@[expose] def cwZ : Fin 4 → List (Fin 4 × Bool) :=
  ![[(0, true), (1, true), (2, true), (0, true), (1, true)],
    [(0, true), (1, true), (3, true), (1, true), (0, true), (1, true)],
    [(3, true), (1, true), (2, true), (1, true), (0, true), (1, true)],
    [(3, true), (1, true), (2, true), (0, true), (1, true)]]

@[expose] def eY : Fin 4 → ℕ := ![1, 2, 2, 2]

@[expose] def eW : Fin 8 → ℕ := ![0, 0, 1, 2, 0, 2, 1, 0]

@[expose] def eZ : Fin 4 → ℕ := ![2, 1, 1, 0]

@[expose] def fA6 : Fin 4 → ℕ := ![1, 0, 1, 1]

@[expose] def subst (w : List (Fin 3 × Bool)) : List (Fin 4 × Bool) :=
  w.flatMap fun l => if l.1 = 0 then (if l.2 then ua else FreeGroup.invRev ua)
    else if l.1 = 1 then (if l.2 then ub else FreeGroup.invRev ub) else []

@[expose] def zInv (k : ℕ) : List (Fin 4 × Bool) :=
  (List.replicate k (FreeGroup.invRev zw)).flatten

@[expose] def tY : Fin 4 → List (Fin 4 × Bool) :=
  ![[(0, true), (2, true)], [(2, true)], [(0, true), (3, true)], [(3, true)]]

@[expose] def tW (i : Fin 8) : List (Fin 4 × Bool) :=
  cwW i ++ [(0, true)] ++ FreeGroup.invRev (cwW i)

@[expose] def tZ (i : Fin 4) : List (Fin 4 × Bool) :=
  cwZ i ++ [(0, true)] ++ FreeGroup.invRev (cwZ i)

abbrev WalkA6 (w : List (Fin 4 × Bool)) : Prop :=
  Exc.coverWalk (2 * 4) A6Data.fx A6Data.fy A6Data.ffi 0 (w.map letterCode) = 0

theorem walk_zc :
    ∀ i : Fin 4, WalkA6 (zw ++ [(i, true)] ++ FreeGroup.invRev zw ++ [(i, false)]) := by
  decide +kernel

theorem walk_z3 : WalkA6 (zw ++ zw ++ zw) := by decide +kernel

theorem walk_rA6 : ∀ i : Fin 4, WalkA6 (subst (relsA6.getD i []) ++ zInv (fA6 i)) := by
  decide +kernel

theorem walk_P : WalkA6 (subst wP ++ zInv 1 ++ [(0, false)]) := by decide +kernel

theorem walk_C : WalkA6 (subst wC ++ zInv 1 ++ [(1, false)]) := by decide +kernel

theorem walk_Y : ∀ i, WalkA6 (subst (wY i) ++ zInv (eY i) ++ FreeGroup.invRev (tY i)) := by
  decide +kernel

theorem walk_W : ∀ i, WalkA6 (subst (wW i) ++ zInv (eW i) ++ FreeGroup.invRev (tW i)) := by
  decide +kernel

theorem walk_Z : ∀ i, WalkA6 (subst (wZ i) ++ zInv (eZ i) ++ FreeGroup.invRev (tZ i)) := by
  decide +kernel

@[expose] def yW : Fin 8 → Fin 4 := ![0, 0, 3, 2, 2, 3, 1, 1]

@[expose] def wZ' : Fin 4 → Fin 8 := ![3, 7, 2, 3]

@[expose] def nearZ : Fin 4 → Fin 4 := ![2, 1, 3, 2]

@[expose] def farZ : Fin 4 → Fin 4 := ![0, 2, 0, 0]

theorem yW_wZ' : ∀ i, yW (wZ' i) = nearZ i := by decide

theorem walk_gW : ∀ i, WalkA6 ([(0, true)] ++ tW i ++ [(0, true)] ++ tW i ++
    FreeGroup.invRev (tY (yW i))) := by
  decide +kernel

theorem walk_gZ3 : ∀ i, WalkA6 ((List.replicate 3 ([(0, true)] ++ tZ i)).flatten) := by
  decide +kernel

theorem walk_gZc : ∀ i, WalkA6 (tW (wZ' i) ++ tZ i ++ FreeGroup.invRev (tW (wZ' i)) ++
    FreeGroup.invRev (tZ i)) := by
  decide +kernel

theorem walk_gZ5 : ∀ i, WalkA6 ((List.replicate 5 (tY (farZ i) ++ tZ i)).flatten) := by
  decide +kernel

theorem signedProd_invRev {m : ℕ} {K : Type*} [Group K] (x : Fin m → K)
    (w : List (Fin m × Bool)) : signedProd x (FreeGroup.invRev w) = (signedProd x w)⁻¹ := by
  rw [← lift_mk_eq_signedProd, ← lift_mk_eq_signedProd, ← FreeGroup.inv_mk, map_inv]

theorem signedProd_zInv {K : Type*} [Group K] (y : Fin 4 → K) (k : ℕ) :
    signedProd y (zInv k) = (signedProd y zw)⁻¹ ^ k := by
  rw [zInv, signedProd_replicate, signedProd_invRev]

theorem signedProd_subst {K : Type*} [Group K] (y : Fin 4 → K) (x : Fin 3 → K)
    (ha : x 0 = signedProd y ua) (hb : x 1 = signedProd y ub) :
    ∀ w : List (Fin 3 × Bool), (∀ l ∈ w, l.1 ≠ 2) → signedProd x w = signedProd y (subst w) := by
  intro w
  induction w with
  | nil => intro _; rfl
  | cons l w ih =>
    intro hw
    rw [subst, List.flatMap_cons, signedProd_append, ← subst, signedProd_cons,
      ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')]
    congr 1
    obtain ⟨i, b⟩ := l
    have hi : i ≠ 2 := hw (i, b) List.mem_cons_self
    fin_cases i
    · cases b <;> simp [ha, signedProd_invRev]
    · cases b <;> simp [hb, signedProd_invRev]
    · exact absurd rfl hi

theorem signedProd_eq_one_of_walk {K : Type*} [Group K] {y : Fin 4 → K}
    (hy : ∀ r ∈ lineRels 2 false, signedProd y r = 1) {w : List (Fin 4 × Bool)}
    (hw : WalkA6 w) : signedProd y w = 1 :=
  Exc.signedProd_eq_one_of_mk_eq_one (Exc.mk_eq_one_a6 w hw) y hy

@[expose] def zEl (p c : G) (x : Fin 2 → G) : G := signedProd (lineGens p c x) zw

@[expose] def yPt (p c : G) (x : Fin 2 → G) (i : Fin 4) : G :=
  signedProd (lineGens p c x) (tY i)

@[expose] def wPt (p c : G) (x : Fin 2 → G) (i : Fin 8) : G :=
  signedProd (lineGens p c x) (tW i)

@[expose] def zPt (p c : G) (x : Fin 2 → G) (i : Fin 4) : G :=
  signedProd (lineGens p c x) (tZ i)

theorem yPt_eq (p c : G) (x : Fin 2 → G) :
    yPt p c x 0 = p * x 0 ∧ yPt p c x 1 = x 0 ∧ yPt p c x 2 = p * x 1 ∧ yPt p c x 3 = x 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [yPt, tY, signedProd, lineGens]

theorem commute_of_signedProd {K : Type*} [Group K] {y : Fin 4 → K} (i : Fin 4)
    (h : signedProd y (zw ++ [(i, true)] ++ FreeGroup.invRev zw ++ [(i, false)]) = 1) :
    Commute (signedProd y zw) (y i) := by
  simp only [signedProd_append, signedProd_invRev, signedProd_cons, signedProd_nil, mul_one,
    ite_true, Bool.false_eq_true, ite_false] at h
  have h' := mul_inv_eq_one.1 h
  rw [mul_inv_eq_iff_eq_mul] at h'
  exact h'

theorem zEl_commute_lineGens {p c : G} {x : Fin 2 → G} (hcfg : LineConfig p c x) (i : Fin 4) :
    Commute (zEl p c x) (lineGens p c x i) :=
  commute_of_signedProd i (signedProd_eq_one_of_walk (hcfg.signedProd_lineRels (by simp))
    (walk_zc i))

theorem zEl_pow_three {p c : G} {x : Fin 2 → G} (hcfg : LineConfig p c x) :
    zEl p c x ^ 3 = 1 := by
  have h := signedProd_eq_one_of_walk (hcfg.signedProd_lineRels (by simp)) walk_z3
  rw [signedProd_append, signedProd_append] at h
  rw [pow_three, ← mul_assoc]
  exact h

theorem lineGens_two {α : Type*} (p c : α) (x : Fin 2 → α) : lineGens p c x 2 = x 0 := by
  simp [lineGens]

theorem lineGens_three {α : Type*} (p c : α) (x : Fin 2 → α) : lineGens p c x 3 = x 1 := by
  simp [lineGens]

theorem zEl_facts {p c : G} {x : Fin 2 → G} (hcfg : LineConfig p c x) :
    Commute (zEl p c x) p ∧ Commute (zEl p c x) c ∧ (∀ i, Commute (zEl p c x) (x i)) ∧
      zEl p c x ^ 3 = 1 := by
  refine ⟨by simpa using zEl_commute_lineGens hcfg 0, by simpa using zEl_commute_lineGens hcfg 1,
    fun i => ?_, zEl_pow_three hcfg⟩
  fin_cases i
  · simpa [lineGens_two] using zEl_commute_lineGens hcfg 2
  · simpa [lineGens_three] using zEl_commute_lineGens hcfg 3


end CFSG.Timmesfeld.Moufang.Deep
