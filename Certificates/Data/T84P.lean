module

public import Certificates.Data.Asc82NormA6

public section

namespace Certificates.T84P

open Matrix
open Certificates.A5GL42 (Mat4 Vec4 ofCode vecOfCode)
open Certificates.Asc82NormA6 (rho codesS0)

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

set_option synthInstance.maxSize 4096

abbrev Elt : Type := Vec4 × Mat4

@[expose] def mulE (x y : Elt) : Elt := (x.1 + x.2 *ᵥ y.1, x.2 * y.2)

instance decEqElt : DecidableEq Elt := fun x y =>
  decidable_of_iff
    (x.1 0 = y.1 0 ∧ x.1 1 = y.1 1 ∧ x.1 2 = y.1 2 ∧ x.1 3 = y.1 3 ∧
      x.2 0 0 = y.2 0 0 ∧ x.2 0 1 = y.2 0 1 ∧ x.2 0 2 = y.2 0 2 ∧ x.2 0 3 = y.2 0 3 ∧
      x.2 1 0 = y.2 1 0 ∧ x.2 1 1 = y.2 1 1 ∧ x.2 1 2 = y.2 1 2 ∧ x.2 1 3 = y.2 1 3 ∧
      x.2 2 0 = y.2 2 0 ∧ x.2 2 1 = y.2 2 1 ∧ x.2 2 2 = y.2 2 2 ∧ x.2 2 3 = y.2 2 3 ∧
      x.2 3 0 = y.2 3 0 ∧ x.2 3 1 = y.2 3 1 ∧ x.2 3 2 = y.2 3 2 ∧ x.2 3 3 = y.2 3 3)
    (by
      obtain ⟨u, m⟩ := x
      obtain ⟨v, n⟩ := y
      constructor
      · rintro ⟨h0, h1, h2, h3, h00, h01, h02, h03, h10, h11, h12, h13, h20, h21, h22, h23,
          h30, h31, h32, h33⟩
        refine Prod.ext (funext fun i => ?_) (Matrix.ext fun i j => ?_)
        · fin_cases i
          exacts [h0, h1, h2, h3]
        · fin_cases i <;> fin_cases j
          exacts [h00, h01, h02, h03, h10, h11, h12, h13, h20, h21, h22, h23, h30, h31, h32, h33]
      · rintro h
        cases h
        simp)

instance beqElt : BEq Elt := instBEqOfDecidableEq

def z2 (n : ℕ) : ZMod 2 := (⟨n % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2)

theorem z2_eq (n : ℕ) : z2 n = (n : ZMod 2) := by
  apply ZMod.val_injective 2
  rw [ZMod.val_natCast]
  rfl

theorem z2_val (e : ZMod 2) : z2 e.val = e := by
  rw [z2_eq]
  exact ZMod.natCast_zmod_val e

def tabV (v : Vec4) : Array ℕ := #[(v 0).val, (v 1).val, (v 2).val, (v 3).val]

def tabN (m : Mat4) : Array ℕ := #[(m 0 0).val, (m 0 1).val, (m 0 2).val, (m 0 3).val,
  (m 1 0).val, (m 1 1).val, (m 1 2).val, (m 1 3).val,
  (m 2 0).val, (m 2 1).val, (m 2 2).val, (m 2 3).val,
  (m 3 0).val, (m 3 1).val, (m 3 2).val, (m 3 3).val]

def gV (t : Array ℕ) (i : Fin 4) : ℕ := t.getD i.val 0

def gN (t : Array ℕ) (i j : Fin 4) : ℕ := t.getD (4 * i.val + j.val) 0

theorem gV_tabV (v : Vec4) (i : Fin 4) : gV (tabV v) i = (v i).val := by
  fin_cases i <;> rfl

theorem gN_tabN (m : Mat4) (i j : Fin 4) : gN (tabN m) i j = (m i j).val := by
  fin_cases i <;> fin_cases j <;> rfl

@[noinline] def mkVec (t : Array ℕ) : Vec4 := fun i => z2 (gV t i)

@[noinline] def mkMat (t : Array ℕ) : Mat4 := Matrix.of fun i j => z2 (gN t i j)

def nfV (v : Vec4) : Vec4 := mkVec (tabV v)

def nfM (m : Mat4) : Mat4 := mkMat (tabN m)

theorem nfV_eq (v : Vec4) : nfV v = v := by
  funext i
  simp only [nfV, mkVec, gV_tabV, z2_val]

theorem nfM_eq (m : Mat4) : nfM m = m := by
  ext i j
  simp only [nfM, mkMat, gN_tabN, z2_val, Matrix.of_apply]

@[noinline] def mkElt (u a : Array ℕ) : Elt := (mkVec u, mkMat a)

def nfE (e : Elt) : Elt := mkElt (tabV e.1) (tabN e.2)

theorem nfE_eq (e : Elt) : nfE e = e := by
  show (nfV e.1, nfM e.2) = e
  rw [nfV_eq, nfM_eq]

def prodV (u w a : Array ℕ) (i : Fin 4) : ℕ :=
  gV u i + (gN a i 0 * gV w 0 + gN a i 1 * gV w 1 + gN a i 2 * gV w 2 + gN a i 3 * gV w 3)

def prodN (a b : Array ℕ) (i k : Fin 4) : ℕ :=
  gN a i 0 * gN b 0 k + gN a i 1 * gN b 1 k + gN a i 2 * gN b 2 k + gN a i 3 * gN b 3 k

@[noinline] def mulEAux (u w a b : Array ℕ) : Elt :=
  (mkVec #[prodV u w a 0, prodV u w a 1, prodV u w a 2, prodV u w a 3],
   mkMat #[prodN a b 0 0, prodN a b 0 1, prodN a b 0 2, prodN a b 0 3,
     prodN a b 1 0, prodN a b 1 1, prodN a b 1 2, prodN a b 1 3,
     prodN a b 2 0, prodN a b 2 1, prodN a b 2 2, prodN a b 2 3,
     prodN a b 3 0, prodN a b 3 1, prodN a b 3 2, prodN a b 3 3])

def mulEFast (x y : Elt) : Elt := mulEAux (tabV x.1) (tabV y.1) (tabN x.2) (tabN y.2)

theorem gV_mk (f : Fin 4 → ℕ) (i : Fin 4) : gV #[f 0, f 1, f 2, f 3] i = f i := by
  fin_cases i <;> rfl

theorem gN_mk (f : Fin 4 → Fin 4 → ℕ) (i k : Fin 4) :
    gN #[f 0 0, f 0 1, f 0 2, f 0 3, f 1 0, f 1 1, f 1 2, f 1 3,
      f 2 0, f 2 1, f 2 2, f 2 3, f 3 0, f 3 1, f 3 2, f 3 3] i k = f i k := by
  fin_cases i <;> fin_cases k <;> rfl

theorem mkVec_prod (x y : Elt) :
    mkVec #[prodV (tabV x.1) (tabV y.1) (tabN x.2) 0, prodV (tabV x.1) (tabV y.1) (tabN x.2) 1,
      prodV (tabV x.1) (tabV y.1) (tabN x.2) 2, prodV (tabV x.1) (tabV y.1) (tabN x.2) 3] =
      x.1 + x.2 *ᵥ y.1 := by
  funext i
  rw [mkVec, gV_mk (prodV (tabV x.1) (tabV y.1) (tabN x.2)) i]
  simp only [prodV, Pi.add_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four, z2_eq, gV_tabV,
    gN_tabN]
  push_cast
  simp only [ZMod.natCast_zmod_val]

theorem mkMat_prod (x y : Elt) :
    mkMat #[prodN (tabN x.2) (tabN y.2) 0 0, prodN (tabN x.2) (tabN y.2) 0 1,
      prodN (tabN x.2) (tabN y.2) 0 2, prodN (tabN x.2) (tabN y.2) 0 3,
      prodN (tabN x.2) (tabN y.2) 1 0, prodN (tabN x.2) (tabN y.2) 1 1,
      prodN (tabN x.2) (tabN y.2) 1 2, prodN (tabN x.2) (tabN y.2) 1 3,
      prodN (tabN x.2) (tabN y.2) 2 0, prodN (tabN x.2) (tabN y.2) 2 1,
      prodN (tabN x.2) (tabN y.2) 2 2, prodN (tabN x.2) (tabN y.2) 2 3,
      prodN (tabN x.2) (tabN y.2) 3 0, prodN (tabN x.2) (tabN y.2) 3 1,
      prodN (tabN x.2) (tabN y.2) 3 2, prodN (tabN x.2) (tabN y.2) 3 3] = x.2 * y.2 := by
  ext i k
  rw [mkMat, Matrix.of_apply, gN_mk (prodN (tabN x.2) (tabN y.2)) i k]
  simp only [prodN, Matrix.mul_apply, Fin.sum_univ_four, z2_eq, gN_tabN]
  push_cast
  simp only [ZMod.natCast_zmod_val]

@[csimp] theorem mulE_eq_mulEFast : @mulE = @mulEFast := by
  funext x y
  unfold mulEFast mulEAux
  rw [mkVec_prod, mkMat_prod]
  rfl

@[expose] def oneE : Elt := (0, 1)

@[expose] def commE (x y : Elt) : Prop := mulE x y = mulE y x

instance (x y : Elt) : Decidable (commE x y) := by unfold commE; infer_instance

@[expose] def M0l : List Elt :=
  (List.range 16).flatMap fun v => codesS0.map fun m => (vecOfCode v, ofCode m)

@[expose] def g1 : Equiv.Perm (Fin 6) := List.formPerm [0, 1, 2, 3] * List.formPerm [4, 5]

@[expose] def g2 : Equiv.Perm (Fin 6) := Equiv.swap 0 2 * Equiv.swap 4 5

@[expose] def D0l : List Mat4 :=
  (List.range 4).flatMap fun i => (List.range 2).map fun j => rho (g1 ^ i * g2 ^ j)

@[expose] def P0l : List Elt :=
  (List.range 16).flatMap fun v => D0l.map fun m => (vecOfCode v, m)

def P0lFast : List Elt :=
  ((List.range 16).flatMap fun v => D0l.map fun m => (vecOfCode v, m)).map nfE

@[csimp] theorem P0l_eq_P0lFast : P0l = P0lFast := by
  have h : nfE = id := funext nfE_eq
  unfold P0l P0lFast
  rw [h, List.map_id]

@[expose] def Vl : List Elt := (List.range 16).map fun v => (vecOfCode v, (1 : Mat4))

@[expose] def IsInvE (x : Elt) : Prop := x ≠ oneE ∧ mulE x x = oneE

instance (x : Elt) : Decidable (IsInvE x) := by unfold IsInvE; infer_instance

@[expose] def InvP : List Elt := P0l.filter fun x => decide (IsInvE x)

@[expose] def InvM : List Elt := M0l.filter fun x => decide (IsInvE x)

@[expose] def span4 (a b c d : Elt) : List Elt :=
  let s1 := [oneE, a]
  let s2 := s1 ++ s1.map (mulE b)
  let s3 := s2 ++ s2.map (mulE c)
  s3 ++ s3.map (mulE d)

@[expose] def f0Gens : List Elt :=
  [(vecOfCode 0, ofCode 32475), (vecOfCode 0, ofCode 8580), (vecOfCode 5, 1), (vecOfCode 10, 1)]

@[expose] def F0l : List Elt :=
  match f0Gens with
  | [a, b, c, d] => span4 a b c d
  | _ => []

@[expose] def Jl : List Elt := (Vl.flatMap fun x => F0l.map (mulE x)).dedup

@[expose] def P0Group : Prop :=
  P0l.Nodup ∧ P0l.length = 128 ∧ oneE ∈ P0l ∧ (∀ x ∈ P0l, x ∈ M0l) ∧
    ∀ x ∈ P0l, ∀ y ∈ P0l, mulE x y ∈ P0l

@[expose] def NormalE16 (A : List Elt) : Prop :=
  A.Nodup ∧ A.length = 16 ∧ (∀ x ∈ A, x ∈ P0l) ∧ (∀ x ∈ A, ∀ y ∈ A, mulE x y ∈ A) ∧
    (∀ x ∈ A, mulE x x = oneE) ∧ (∀ x ∈ A, ∀ y ∈ A, commE x y) ∧
    ∀ p ∈ P0l, ∀ q ∈ P0l, mulE p q = oneE → ∀ x ∈ A, mulE (mulE p x) q ∈ A

@[expose] def VFGroups : Prop :=
  NormalE16 Vl ∧ NormalE16 F0l ∧ (∃ x ∈ F0l, x ∉ Vl) ∧ (Vl.filter fun x => x ∈ F0l).length = 4

@[expose] def OnlyP : Prop :=
  ∀ a ∈ InvP, a ∉ Vl → ∀ b ∈ InvP, commE a b → ∀ c ∈ InvP, commE a c → commE b c →
    ∀ d ∈ InvP, commE a d → commE b d → commE c d → (span4 a b c d).Nodup →
      ∀ x ∈ span4 a b c d, x ∈ F0l

@[expose] def JGroup : Prop :=
  Jl.Nodup ∧ Jl.length = 64 ∧ (∀ x ∈ Jl, x ∈ P0l) ∧ ∀ x ∈ Jl, ∀ y ∈ Jl, mulE x y ∈ Jl

@[expose] def CentP : Prop :=
  (∀ p ∈ P0l, (∀ x ∈ Vl, commE p x) → p ∈ Vl) ∧ ∀ p ∈ P0l, (∀ x ∈ F0l, commE p x) → p ∈ F0l

@[expose] def YExists : Prop :=
  ∃ y ∈ M0l, y ≠ oneE ∧ mulE y (mulE y y) = oneE ∧
    (∀ j ∈ Jl, mulE (mulE y j) (mulE y y) ∈ Jl) ∧ (∀ j ∈ Jl, commE y j → j = oneE) ∧
    ∃ s ∈ P0l, s ∉ Jl ∧ mulE s s = oneE ∧ mulE (mulE s y) s = mulE y y ∧
      ∀ p ∈ P0l, p ∈ Jl ∨ mulE s p ∈ Jl

@[expose] def RankCent : Prop :=
  ∀ s ∈ InvM, ∃ a ∈ InvM, commE s a ∧ ∃ b ∈ InvM, commE s b ∧ commE a b ∧
    ∃ c ∈ InvM, commE s c ∧ commE a c ∧ commE b c ∧ (span4 s a b c).Nodup

structure Facts : Prop where
  p0 : P0Group
  vf : VFGroups
  only : OnlyP
  j : JGroup
  cent : CentP
  y : YExists
  rank : RankCent

end Certificates.T84P
