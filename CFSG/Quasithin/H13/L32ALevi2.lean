module

public import CFSG.Quasithin.H13.L32ALevi1

public section

namespace CFSG.Quasithin.H13.L32A.C.Levi

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

structure PP where
  m : ℕ
  m' : ℕ
deriving DecidableEq

namespace PP

@[expose] def Valid (p : PP) : Prop := toM p.m * toM p.m' = 1

@[expose] noncomputable def toSL (p : PP) : Lin.SLn 4 := sl p.m p.m'

@[expose] def mul (p q : PP) : PP := ⟨bmul p.m q.m, bmul q.m' p.m'⟩

@[expose] def inv (p : PP) : PP := ⟨p.m', p.m⟩

@[expose] def gam (p : PP) : PP := ⟨perm16 p.m', perm16 p.m⟩

@[expose] def gamE (e : Bool) (p : PP) : PP := if e then gam p else p

@[expose] def sameB (p q : PP) : Bool := uMemB (bmul p.m' q.m)

@[expose] def act (u : PP) (e : Bool) (g : PP) : PP := mul u (gamE e g)

theorem valid_of_eq {p : PP} (h : bmul p.m p.m' = idN) : p.Valid := by
  rw [Valid, ← toM_bmul, h, toM_idN]

theorem Valid.symm {p : PP} (h : p.Valid) : toM p.m' * toM p.m = 1 := by
  rw [← Matrix.inv_eq_right_inv h]
  exact Matrix.nonsing_inv_mul _ (by rw [det_eq_one_of_mul h]; exact isUnit_one)

theorem Valid.mul {p q : PP} (hp : p.Valid) (hq : q.Valid) : (PP.mul p q).Valid := by
  rw [PP.Valid, PP.mul, toM_bmul, toM_bmul, Matrix.mul_assoc, ← Matrix.mul_assoc (toM q.m),
    show toM q.m * toM q.m' = 1 from hq, Matrix.one_mul]
  exact hp

theorem Valid.inv {p : PP} (hp : p.Valid) : (PP.inv p).Valid := hp.symm

theorem Valid.gam {p : PP} (hp : p.Valid) : (PP.gam p).Valid := by
  rw [PP.Valid, PP.gam, toM_perm16, toM_perm16, Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul,
    show toM p.m * toM p.m' = 1 from hp, Matrix.transpose_one, Matrix.submatrix_one_equiv]

theorem Valid.gamE {p : PP} (hp : p.Valid) (e : Bool) : (PP.gamE e p).Valid := by
  cases e
  · exact hp
  · exact hp.gam

theorem Valid.act {u g : PP} (hu : u.Valid) (e : Bool) (hg : g.Valid) :
    (PP.act u e g).Valid :=
  hu.mul (hg.gamE e)

theorem coe_toSL {p : PP} (hp : p.Valid) :
    ((toSL p : Lin.SLn 4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = toM p.m := by
  simp [toSL, sl, show toM p.m * toM p.m' = 1 from hp]

theorem toSL_mul {p q : PP} (hp : p.Valid) (hq : q.Valid) :
    toSL (mul p q) = toSL p * toSL q := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_toSL (hp.mul hq), coe_toSL hp, coe_toSL hq,
    show (PP.mul p q).m = bmul p.m q.m from rfl, toM_bmul]

theorem toSL_inv {p : PP} (hp : p.Valid) : toSL (inv p) = (toSL p)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one]
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, coe_toSL hp.inv,
    coe_toSL hp, show (PP.inv p).m = p.m' from rfl, hp.symm]

theorem toSL_gam {p : PP} (hp : p.Valid) :
    toSL (gam p) = BinaryParabolic.graphFun (toSL p) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [coe_toSL hp.gam, BinaryParabolic.coe_graphFun, ← toSL_inv hp, coe_toSL hp.inv, gam,
    toM_perm16]
  rfl

theorem toSL_gamE {p : PP} (hp : p.Valid) (e : Bool) :
    toSL (gamE e p) = if e then BinaryParabolic.graphFun (toSL p) else toSL p := by
  cases e
  · rfl
  · exact toSL_gam hp

theorem mem_unitriangular_iff {p : PP} (hp : p.Valid) :
    toSL p ∈ unitriangular 4 (ZMod 2) ↔ uMemB p.m = true := by
  rw [uMemB_iff]
  show ((∀ i j : Fin 4, j < i → ((toSL p : Lin.SLn 4) : Matrix _ _ (ZMod 2)) i j = 0) ∧
    ∀ i : Fin 4, ((toSL p : Lin.SLn 4) : Matrix _ _ (ZMod 2)) i i = 1) ↔ _
  rw [coe_toSL hp]

theorem sameB_iff {p q : PP} (hp : p.Valid) (hq : q.Valid) :
    sameB p q = true ↔ (toSL p)⁻¹ * toSL q ∈ unitriangular 4 (ZMod 2) := by
  rw [← toSL_inv hp, ← toSL_mul hp.inv hq, mem_unitriangular_iff (hp.inv.mul hq)]
  rfl

end PP

@[expose] noncomputable def mact (u : Lin.SLn 4) (e : Bool) (g : Lin.SLn 4) : Lin.SLn 4 :=
  u * if e then BinaryParabolic.graphFun g else g

theorem PP.toSL_act {u g : PP} (hu : u.Valid) (e : Bool) (hg : g.Valid) :
    toSL (act u e g) = mact (toSL u) e (toSL g) := by
  rw [act, toSL_mul hu (hg.gamE e), toSL_gamE hg, mact]

end CFSG.Quasithin.H13.L32A.C.Levi
