module

public import CFSG.Quasithin.EmptyFaithful.S143A6Nat

public section

namespace CFSG.Quasithin.S143

namespace A6Model

structure V4 where
  x0 : Bool
  x1 : Bool
  x2 : Bool
  x3 : Bool
  deriving DecidableEq

structure Mat4 where
  r0 : V4
  r1 : V4
  r2 : V4
  r3 : V4
  deriving DecidableEq

@[expose] def V4.add (v w : V4) : V4 := ⟨xor v.x0 w.x0, xor v.x1 w.x1, xor v.x2 w.x2, xor v.x3 w.x3⟩

@[expose] def V4.sm (b : Bool) (v : V4) : V4 := ⟨b && v.x0, b && v.x1, b && v.x2, b && v.x3⟩

@[expose] def vm (v : V4) (M : Mat4) : V4 :=
  (M.r0.sm v.x0).add ((M.r1.sm v.x1).add ((M.r2.sm v.x2).add (M.r3.sm v.x3)))

@[expose] def mm (A B : Mat4) : Mat4 := ⟨vm A.r0 B, vm A.r1 B, vm A.r2 B, vm A.r3 B⟩

@[expose] def I4 : Mat4 :=
  ⟨⟨true, false, false, false⟩, ⟨false, true, false, false⟩, ⟨false, false, true, false⟩,
    ⟨false, false, false, true⟩⟩

@[expose] def Mx : Mat4 :=
  ⟨⟨false, true, false, false⟩, ⟨true, true, false, false⟩, ⟨false, false, false, true⟩,
    ⟨false, false, true, true⟩⟩

@[expose] def Upar (p0 p1 p2 p3 p4 : Bool) : Mat4 :=
  ⟨⟨true, false, false, false⟩, ⟨p0, true, false, false⟩, ⟨p1, false, true, false⟩,
    ⟨p2, p3, p4, true⟩⟩

@[expose] def Ypar (q0 q1 q2 q3 q4 q5 q6 q7 q8 : Bool) : Mat4 :=
  ⟨⟨true, false, false, false⟩, ⟨q0, q1, q2, false⟩, ⟨q3, q4, q5, false⟩, ⟨q6, q7, q8, true⟩⟩

@[expose] def Rpar (s0 s1 s2 s3 : Bool) : Mat4 :=
  ⟨⟨true, false, false, false⟩, ⟨false, true, false, false⟩, ⟨s0, s1, true, false⟩,
    ⟨s2, s3, false, true⟩⟩

@[expose] def Rs1 : Mat4 := Rpar false true true false
@[expose] def Rs2 : Mat4 := Rpar true false true true
@[expose] def Rs3 : Mat4 := Rpar true true false true

@[expose] def Rstd4 : List Mat4 := [I4, Rs1, Rs2, Rs3]

@[expose] def RHypM (R1 R2 : Mat4) : Prop :=
  R1 ≠ I4 ∧ R2 ≠ I4 ∧ R1 ≠ R2 ∧
  (∀ P ∈ [I4, R1, R2, mm R1 R2], ∃ P' ∈ [I4, R1, R2, mm R1 R2], mm P Mx = mm Mx P') ∧
  (∃ P ∈ [I4, R1, R2, mm R1 R2], mm P Mx ≠ mm Mx P)

instance (R1 R2 : Mat4) : Decidable (RHypM R1 R2) := by
  unfold RHypM; infer_instance

@[expose] def RHyp (a0 a1 a2 a3 b0 b1 b2 b3 : Bool) : Prop :=
  RHypM (Rpar a0 a1 a2 a3) (Rpar b0 b1 b2 b3)

instance (a0 a1 a2 a3 b0 b1 b2 b3 : Bool) : Decidable (RHyp a0 a1 a2 a3 b0 b1 b2 b3) := by
  unfold RHyp; infer_instance

@[expose] def RConcl (R1 R2 : Mat4) : Prop :=
  (R1 ∈ [Rs1, Rs2, Rs3] ∧ R2 ∈ [Rs1, Rs2, Rs3] ∧ mm R1 R2 ∈ [Rs1, Rs2, Rs3]) ∧
  mm R1 R2 ≠ I4 ∧ mm R1 R2 ≠ R1 ∧ mm R1 R2 ≠ R2 ∧ (∀ P ∈ Rstd4, P ∈ [I4, R1, R2, mm R1 R2])

instance (R1 R2 : Mat4) : Decidable (RConcl R1 R2) := by
  unfold RConcl; infer_instance

set_option maxRecDepth 100000 in
theorem stageR : ∀ a0 a1 a2 a3 b0 b1 b2 b3 : Bool, RHyp a0 a1 a2 a3 b0 b1 b2 b3 →
    RConcl (Rpar a0 a1 a2 a3) (Rpar b0 b1 b2 b3) := by decide +kernel

@[expose] def UHypL (Rl : List Mat4) (N1 N2 : Mat4) : Prop :=
  mm N1 N2 = mm N2 N1 ∧ mm N1 N1 = I4 ∧ mm N2 N2 = I4 ∧ N1 ≠ I4 ∧ N2 ≠ I4 ∧ N1 ≠ N2 ∧
  (N1.r1 ≠ I4.r1 ∨ N1.r2 ≠ I4.r2) ∧ (N2.r1 ≠ I4.r1 ∨ N2.r2 ≠ I4.r2) ∧
  ((mm N1 N2).r1 ≠ I4.r1 ∨ (mm N1 N2).r2 ≠ I4.r2) ∧
  (∀ P ∈ Rl, ∃ P' ∈ Rl, mm P N1 = mm N1 P') ∧
  (∀ P ∈ Rl, ∃ P' ∈ Rl, mm P N2 = mm N2 P') ∧
  (∃ N ∈ [N1, N2, mm N1 N2], N ∈ Rl ∧ N ≠ I4)

instance (Rl : List Mat4) (N1 N2 : Mat4) : Decidable (UHypL Rl N1 N2) := by
  unfold UHypL; infer_instance

theorem UHypL_congr {Rl Rl' : List Mat4} (h : ∀ P, P ∈ Rl ↔ P ∈ Rl') (N1 N2 : Mat4) :
    UHypL Rl N1 N2 ↔ UHypL Rl' N1 N2 := by
  unfold UHypL
  simp only [h]

@[expose] def UHyp (p0 p1 p2 p3 p4 q0 q1 q2 q3 q4 : Bool) : Prop :=
  UHypL Rstd4 (Upar p0 p1 p2 p3 p4) (Upar q0 q1 q2 q3 q4)

instance (p0 p1 p2 p3 p4 q0 q1 q2 q3 q4 : Bool) :
    Decidable (UHyp p0 p1 p2 p3 p4 q0 q1 q2 q3 q4) := by
  unfold UHyp; infer_instance

@[expose] def Uset1 : List Mat4 := [I4, Upar true false false false true, Upar false true true true false,
  mm (Upar true false false false true) (Upar false true true true false)]

@[expose] def Uset2 : List Mat4 := [I4, Upar true false true false true, Upar false true true true false,
  mm (Upar true false true false true) (Upar false true true true false)]

@[expose] def YHypM (N1 N2 Y : Mat4) : Prop :=
  mm Y (mm Y Y) = I4 ∧
  (∀ x0 x1 x2 : Bool, vm ⟨x0, x1, x2, false⟩ Y = ⟨x0, x1, x2, false⟩ → (x1 = false ∧ x2 = false)) ∧
  (∀ N ∈ [N1, N2], ∃ N' ∈ [I4, N1, N2, mm N1 N2], mm N Y = mm Y N')

instance (N1 N2 Y : Mat4) : Decidable (YHypM N1 N2 Y) := by
  unfold YHypM; infer_instance

@[expose] def YHyp (p0 p1 p2 p3 p4 q0 q1 q2 q3 q4 y0 y1 y2 y3 y4 y5 y6 y7 y8 : Bool) : Prop :=
  YHypM (Upar p0 p1 p2 p3 p4) (Upar q0 q1 q2 q3 q4) (Ypar y0 y1 y2 y3 y4 y5 y6 y7 y8)

instance (p0 p1 p2 p3 p4 q0 q1 q2 q3 q4 y0 y1 y2 y3 y4 y5 y6 y7 y8 : Bool) :
    Decidable (YHyp p0 p1 p2 p3 p4 q0 q1 q2 q3 q4 y0 y1 y2 y3 y4 y5 y6 y7 y8) := by
  unfold YHyp; infer_instance

@[expose] def Ylist1 : List Mat4 := [
  Ypar false false true false true true false true true,
  Ypar false false true true true true true true false,
  Ypar false true true false true false false false true,
  Ypar false true true true true false true true false,
  Ypar true false true false true true false false false,
  Ypar true false true true true true false false true,
  Ypar true true true false true false false true true,
  Ypar true true true true true false false false false
]

@[expose] def Ylist2 : List Mat4 := [
  Ypar false false true false true true false false false,
  Ypar false false true true true true true false true,
  Ypar false true true false true false false false false,
  Ypar false true true true true false true true true,
  Ypar true false true false true true true true true,
  Ypar true false true true true true true true false,
  Ypar true true true false true false true true false,
  Ypar true true true true true false true false true
]

@[expose] def UYConcl (N1 N2 Y : Mat4) : Prop :=
  ((N1 ∈ Uset1 ∧ N2 ∈ Uset1 ∧ mm N1 N2 ∈ Uset1 ∧ Y ∈ Ylist1) ∨
    (N1 ∈ Uset2 ∧ N2 ∈ Uset2 ∧ mm N1 N2 ∈ Uset2 ∧ Y ∈ Ylist2)) ∧
  mm N1 N2 ≠ I4 ∧ mm N1 N2 ≠ N1 ∧ mm N1 N2 ≠ N2

instance (N1 N2 Y : Mat4) : Decidable (UYConcl N1 N2 Y) := by
  unfold UYConcl; infer_instance

set_option maxRecDepth 100000 in
theorem stageY : ∀ p0 p1 p2 p3 p4 q0 q1 q2 q3 q4 : Bool, UHyp p0 p1 p2 p3 p4 q0 q1 q2 q3 q4 →
    ∀ y0 y1 y2 y3 y4 y5 y6 y7 y8 : Bool,
      YHyp p0 p1 p2 p3 p4 q0 q1 q2 q3 q4 y0 y1 y2 y3 y4 y5 y6 y7 y8 →
      UYConcl (Upar p0 p1 p2 p3 p4) (Upar q0 q1 q2 q3 q4)
        (Ypar y0 y1 y2 y3 y4 y5 y6 y7 y8) := by decide +kernel


@[expose] def dot (a0 a1 a2 a3 m0 m1 m2 m3 : Bool) : Bool :=
  xor (a0 && m0) (xor (a1 && m1) (xor (a2 && m2) (a3 && m3)))

theorem vm_eq (v : V4) (M : Mat4) : vm v M =
    ⟨dot v.x0 v.x1 v.x2 v.x3 M.r0.x0 M.r1.x0 M.r2.x0 M.r3.x0,
     dot v.x0 v.x1 v.x2 v.x3 M.r0.x1 M.r1.x1 M.r2.x1 M.r3.x1,
     dot v.x0 v.x1 v.x2 v.x3 M.r0.x2 M.r1.x2 M.r2.x2 M.r3.x2,
     dot v.x0 v.x1 v.x2 v.x3 M.r0.x3 M.r1.x3 M.r2.x3 M.r3.x3⟩ := rfl

theorem dot_add : ∀ a0 a1 a2 a3 b0 b1 b2 b3 m0 m1 m2 m3 : Bool,
    dot (xor a0 b0) (xor a1 b1) (xor a2 b2) (xor a3 b3) m0 m1 m2 m3 =
      xor (dot a0 a1 a2 a3 m0 m1 m2 m3) (dot b0 b1 b2 b3 m0 m1 m2 m3) := by decide

theorem dot_sm : ∀ c a0 a1 a2 a3 m0 m1 m2 m3 : Bool,
    dot (c && a0) (c && a1) (c && a2) (c && a3) m0 m1 m2 m3 =
      (c && dot a0 a1 a2 a3 m0 m1 m2 m3) := by decide

theorem vm_add (v w : V4) (M : Mat4) : vm (v.add w) M = (vm v M).add (vm w M) := by
  rw [vm_eq, vm_eq, vm_eq]
  simp only [V4.add, dot_add]

theorem vm_sm (b : Bool) (v : V4) (M : Mat4) : vm (V4.sm b v) M = V4.sm b (vm v M) := by
  rw [vm_eq, vm_eq]
  simp only [V4.sm, dot_sm]

theorem vm_vm (w : V4) (A B : Mat4) : vm (vm w A) B = vm w (mm A B) := by
  have h : vm w A = (A.r0.sm w.x0).add ((A.r1.sm w.x1).add ((A.r2.sm w.x2).add (A.r3.sm w.x3))) := rfl
  rw [h, vm_add, vm_add, vm_add, vm_sm, vm_sm, vm_sm, vm_sm]
  rfl

theorem vm_e0 (M : Mat4) : vm ⟨true, false, false, false⟩ M = M.r0 := by
  rw [vm_eq]; simp [dot]
theorem vm_e1 (M : Mat4) : vm ⟨false, true, false, false⟩ M = M.r1 := by
  rw [vm_eq]; simp [dot]
theorem vm_e2 (M : Mat4) : vm ⟨false, false, true, false⟩ M = M.r2 := by
  rw [vm_eq]; simp [dot]
theorem vm_e3 (M : Mat4) : vm ⟨false, false, false, true⟩ M = M.r3 := by
  rw [vm_eq]; simp [dot]

@[expose] def nb0 : N6 := ⟨Multiplicative.ofAdd ![1, 1, 0, 0, 0, 0], by decide⟩
@[expose] def nb1 : N6 := ⟨Multiplicative.ofAdd ![0, 1, 1, 0, 0, 0], by decide⟩
@[expose] def nb2 : N6 := ⟨Multiplicative.ofAdd ![0, 0, 1, 1, 0, 0], by decide⟩
@[expose] def nb3 : N6 := ⟨Multiplicative.ofAdd ![0, 0, 0, 1, 1, 0], by decide⟩

@[expose] def ofCoords (v : V4) : N6 :=
  (if v.x0 then nb0 else 1) * (if v.x1 then nb1 else 1) * (if v.x2 then nb2 else 1) *
    (if v.x3 then nb3 else 1)

@[expose] def coordsN6 (a : N6) : V4 :=
  ⟨Multiplicative.toAdd a.1 0 == 1, (Multiplicative.toAdd a.1 0 + Multiplicative.toAdd a.1 1) == 1,
    (Multiplicative.toAdd a.1 0 + Multiplicative.toAdd a.1 1 + Multiplicative.toAdd a.1 2) == 1,
    Multiplicative.toAdd a.1 4 == 1⟩

theorem ofCoords_coordsN6 : ∀ a : N6, ofCoords (coordsN6 a) = a := by decide +kernel

theorem coordsN6_ofCoords : ∀ x0 x1 x2 x3 : Bool,
    coordsN6 (ofCoords ⟨x0, x1, x2, x3⟩) = ⟨x0, x1, x2, x3⟩ := by decide +kernel

theorem ofCoords_sm (b : Bool) (v : V4) : ofCoords (V4.sm b v) = if b then ofCoords v else 1 := by
  cases b <;> simp [V4.sm, ofCoords]

theorem ofCoords_add (v w : V4) : ofCoords (v.add w) = ofCoords v * ofCoords w := by
  have h : ∀ (b c : Bool) (n : N6), n * n = 1 →
      (if xor b c = true then n else 1) = (if b = true then n else 1) * (if c = true then n else 1) := by
    intro b c n hn
    cases b <;> cases c <;> simp [hn]
  have key : ofCoords (v.add w) = (if xor v.x0 w.x0 = true then nb0 else 1) *
      (if xor v.x1 w.x1 = true then nb1 else 1) * (if xor v.x2 w.x2 = true then nb2 else 1) *
      (if xor v.x3 w.x3 = true then nb3 else 1) := rfl
  rw [key, h v.x0 w.x0 nb0 (n6_mul_self _), h v.x1 w.x1 nb1 (n6_mul_self _),
    h v.x2 w.x2 nb2 (n6_mul_self _), h v.x3 w.x3 nb3 (n6_mul_self _)]
  unfold ofCoords
  ac_rfl

@[expose] def matOf6 (σ : Equiv.Perm (Fin 6)) : Mat4 :=
  ⟨coordsN6 (n6Act σ nb0), coordsN6 (n6Act σ nb1), coordsN6 (n6Act σ nb2), coordsN6 (n6Act σ nb3)⟩

theorem n6Act_ofCoords (σ : Equiv.Perm (Fin 6)) (v : V4) :
    n6Act σ (ofCoords v) = ofCoords (vm v (matOf6 σ)) := by
  have h : ∀ (b : Bool) (n : N6), n6Act σ (if b = true then n else 1) =
      if b = true then n6Act σ n else 1 := by
    intro b n; cases b <;> simp
  have hL : n6Act σ (ofCoords v) = (if v.x0 = true then n6Act σ nb0 else 1) *
      (if v.x1 = true then n6Act σ nb1 else 1) * (if v.x2 = true then n6Act σ nb2 else 1) *
      (if v.x3 = true then n6Act σ nb3 else 1) := by
    unfold ofCoords
    simp only [map_mul, h]
  have hv : vm v (matOf6 σ) = ((matOf6 σ).r0.sm v.x0).add (((matOf6 σ).r1.sm v.x1).add
      (((matOf6 σ).r2.sm v.x2).add ((matOf6 σ).r3.sm v.x3))) := rfl
  have hR : ofCoords (vm v (matOf6 σ)) = (if v.x0 = true then ofCoords (matOf6 σ).r0 else 1) *
      (if v.x1 = true then ofCoords (matOf6 σ).r1 else 1) *
      (if v.x2 = true then ofCoords (matOf6 σ).r2 else 1) *
      (if v.x3 = true then ofCoords (matOf6 σ).r3 else 1) := by
    rw [hv, ofCoords_add, ofCoords_add, ofCoords_add, ofCoords_sm, ofCoords_sm, ofCoords_sm,
      ofCoords_sm]
    ac_rfl
  have e0 : ofCoords (matOf6 σ).r0 = n6Act σ nb0 := ofCoords_coordsN6 _
  have e1 : ofCoords (matOf6 σ).r1 = n6Act σ nb1 := ofCoords_coordsN6 _
  have e2 : ofCoords (matOf6 σ).r2 = n6Act σ nb2 := ofCoords_coordsN6 _
  have e3 : ofCoords (matOf6 σ).r3 = n6Act σ nb3 := ofCoords_coordsN6 _
  rw [hL, hR, e0, e1, e2, e3]

@[expose] def psi (c : Mat4) (v : V4) : N6 := ofCoords (vm v c)

@[expose] def A6ok (c M : Mat4) : Prop :=
  ∃ σ : Equiv.Perm (Fin 6), σ.sign = 1 ∧ mm c (matOf6 σ) = mm M c

theorem psi_intertwine {c M : Mat4} {σ : Equiv.Perm (Fin 6)} (h : mm c (matOf6 σ) = mm M c)
    (w : V4) : n6Act σ (psi c w) = psi c (vm w M) := by
  unfold psi
  rw [n6Act_ofCoords, vm_vm, h, ← vm_vm]

@[expose] def mkPerm6 (f g : Fin 6 → Fin 6) (h1 : Function.LeftInverse g f)
    (h2 : Function.RightInverse g f) : Equiv.Perm (Fin 6) := ⟨f, g, h1, h2⟩

@[expose] def c1 : Mat4 :=
  ⟨⟨false, false, false, true⟩, ⟨true, false, false, false⟩, ⟨false, true, false, false⟩,
    ⟨false, false, true, false⟩⟩

@[expose] def c2 : Mat4 :=
  ⟨⟨true, true, true, true⟩, ⟨true, false, true, true⟩, ⟨true, false, false, true⟩,
    ⟨true, false, false, false⟩⟩

@[expose] def perms1 : List (Equiv.Perm (Fin 6)) := [
  mkPerm6 ![5, 2, 3, 1, 0, 4] ![4, 3, 1, 2, 5, 0] (by decide) (by decide),
  mkPerm6 ![0, 1, 2, 3, 4, 5] ![0, 1, 2, 3, 4, 5] (by decide) (by decide),
  mkPerm6 ![5, 2, 1, 3, 4, 0] ![5, 2, 1, 3, 4, 0] (by decide) (by decide),
  mkPerm6 ![1, 0, 5, 3, 4, 2] ![1, 0, 5, 3, 4, 2] (by decide) (by decide),
  mkPerm6 ![2, 5, 0, 3, 4, 1] ![2, 5, 0, 3, 4, 1] (by decide) (by decide),
  mkPerm6 ![0, 1, 2, 3, 4, 5] ![0, 1, 2, 3, 4, 5] (by decide) (by decide),
  mkPerm6 ![1, 0, 2, 4, 3, 5] ![1, 0, 2, 4, 3, 5] (by decide) (by decide),
  mkPerm6 ![1, 0, 5, 3, 4, 2] ![1, 0, 5, 3, 4, 2] (by decide) (by decide),
  mkPerm6 ![0, 1, 5, 4, 3, 2] ![0, 1, 5, 4, 3, 2] (by decide) (by decide),
  mkPerm6 ![1, 2, 0, 3, 4, 5] ![2, 0, 1, 3, 4, 5] (by decide) (by decide),
  mkPerm6 ![2, 1, 5, 3, 4, 0] ![5, 1, 0, 3, 4, 2] (by decide) (by decide),
  mkPerm6 ![2, 0, 1, 3, 4, 5] ![1, 2, 0, 3, 4, 5] (by decide) (by decide),
  mkPerm6 ![0, 2, 5, 3, 4, 1] ![0, 5, 1, 3, 4, 2] (by decide) (by decide),
  mkPerm6 ![5, 0, 2, 3, 4, 1] ![1, 5, 2, 3, 4, 0] (by decide) (by decide),
  mkPerm6 ![0, 5, 1, 3, 4, 2] ![0, 2, 5, 3, 4, 1] (by decide) (by decide),
  mkPerm6 ![5, 1, 0, 3, 4, 2] ![2, 1, 5, 3, 4, 0] (by decide) (by decide),
  mkPerm6 ![1, 5, 2, 3, 4, 0] ![5, 0, 2, 3, 4, 1] (by decide) (by decide)
]
@[expose] def perms2 : List (Equiv.Perm (Fin 6)) := [
  mkPerm6 ![3, 4, 0, 2, 5, 1] ![2, 5, 3, 0, 1, 4] (by decide) (by decide),
  mkPerm6 ![0, 1, 2, 3, 4, 5] ![0, 1, 2, 3, 4, 5] (by decide) (by decide),
  mkPerm6 ![0, 3, 5, 1, 4, 2] ![0, 3, 5, 1, 4, 2] (by decide) (by decide),
  mkPerm6 ![0, 2, 1, 5, 4, 3] ![0, 2, 1, 5, 4, 3] (by decide) (by decide),
  mkPerm6 ![0, 5, 3, 2, 4, 1] ![0, 5, 3, 2, 4, 1] (by decide) (by decide),
  mkPerm6 ![0, 1, 2, 3, 4, 5] ![0, 1, 2, 3, 4, 5] (by decide) (by decide),
  mkPerm6 ![4, 1, 2, 5, 0, 3] ![4, 1, 2, 5, 0, 3] (by decide) (by decide),
  mkPerm6 ![0, 2, 1, 5, 4, 3] ![0, 2, 1, 5, 4, 3] (by decide) (by decide),
  mkPerm6 ![4, 2, 1, 3, 0, 5] ![4, 2, 1, 3, 0, 5] (by decide) (by decide),
  mkPerm6 ![0, 1, 3, 5, 4, 2] ![0, 1, 5, 2, 4, 3] (by decide) (by decide),
  mkPerm6 ![0, 3, 1, 2, 4, 5] ![0, 2, 3, 1, 4, 5] (by decide) (by decide),
  mkPerm6 ![0, 1, 5, 2, 4, 3] ![0, 1, 3, 5, 4, 2] (by decide) (by decide),
  mkPerm6 ![0, 5, 1, 3, 4, 2] ![0, 2, 5, 3, 4, 1] (by decide) (by decide),
  mkPerm6 ![0, 5, 2, 1, 4, 3] ![0, 3, 2, 5, 4, 1] (by decide) (by decide),
  mkPerm6 ![0, 2, 5, 3, 4, 1] ![0, 5, 1, 3, 4, 2] (by decide) (by decide),
  mkPerm6 ![0, 2, 3, 1, 4, 5] ![0, 3, 1, 2, 4, 5] (by decide) (by decide),
  mkPerm6 ![0, 3, 2, 5, 4, 1] ![0, 5, 2, 1, 4, 3] (by decide) (by decide)
]


theorem forall₂_exists_of_mem_left {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) : ∀ a ∈ l₁, ∃ b, R a b := by
  induction h with
  | nil => intro a ha; simp at ha
  | cons hab _ ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_, hab⟩
    · exact ih a ha

set_option maxRecDepth 100000 in
theorem ok1' : List.Forall₂ (fun M σ => σ.sign = 1 ∧ mm c1 (matOf6 σ) = mm M c1)
    (Mx :: (Uset1 ++ (Rstd4 ++ Ylist1))) perms1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ok2' : List.Forall₂ (fun M σ => σ.sign = 1 ∧ mm c2 (matOf6 σ) = mm M c2)
    (Mx :: (Uset2 ++ (Rstd4 ++ Ylist2))) perms2 := by decide +kernel

theorem ok1 : ∀ M ∈ Mx :: (Uset1 ++ (Rstd4 ++ Ylist1)), A6ok c1 M := by
  intro M hM
  obtain ⟨σ, hσ⟩ := forall₂_exists_of_mem_left ok1' M hM
  exact ⟨σ, hσ.1, hσ.2⟩

theorem ok2 : ∀ M ∈ Mx :: (Uset2 ++ (Rstd4 ++ Ylist2)), A6ok c2 M := by
  intro M hM
  obtain ⟨σ, hσ⟩ := forall₂_exists_of_mem_left ok2' M hM
  exact ⟨σ, hσ.1, hσ.2⟩

theorem coordsN6_ofCoords' (u : V4) : coordsN6 (ofCoords u) = u := by
  obtain ⟨x0, x1, x2, x3⟩ := u
  exact coordsN6_ofCoords x0 x1 x2 x3

theorem cInj1 : ∀ a0 a1 a2 a3 b0 b1 b2 b3 : Bool,
    vm ⟨a0, a1, a2, a3⟩ c1 = vm ⟨b0, b1, b2, b3⟩ c1 → (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3) := by
  decide

theorem cInj2 : ∀ a0 a1 a2 a3 b0 b1 b2 b3 : Bool,
    vm ⟨a0, a1, a2, a3⟩ c2 = vm ⟨b0, b1, b2, b3⟩ c2 → (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3) := by
  decide

theorem psi_inj {c : Mat4} (hc : ∀ v w : V4, vm v c = vm w c → v = w) {v w : V4}
    (h : psi c v = psi c w) : v = w := by
  apply hc
  have := congrArg coordsN6 h
  unfold psi at this
  rwa [coordsN6_ofCoords', coordsN6_ofCoords'] at this

@[expose] def b2n (b : Bool) : ℕ := if b then 1 else 0

@[expose] def packV (v : V4) : ℕ := b2n v.x0 + 2 * b2n v.x1 + 4 * b2n v.x2 + 8 * b2n v.x3

@[expose] def pack (M : Mat4) : ℕ :=
  packV M.r0 + 16 * (packV M.r1 + 16 * (packV M.r2 + 16 * packV M.r3))

@[expose] def vmN (v B : ℕ) : ℕ :=
  (if v % 2 = 1 then B % 16 else 0) ^^^ ((if v / 2 % 2 = 1 then B / 16 % 16 else 0) ^^^
    ((if v / 4 % 2 = 1 then B / 256 % 16 else 0) ^^^ (if v / 8 % 2 = 1 then B / 4096 % 16 else 0)))

@[expose] def mmN (A B : ℕ) : ℕ :=
  vmN (A % 16) B + 16 * (vmN (A / 16 % 16) B + 16 * (vmN (A / 256 % 16) B +
    16 * vmN (A / 4096 % 16) B))

theorem packV_lt : ∀ a0 a1 a2 a3 : Bool, packV ⟨a0, a1, a2, a3⟩ < 16 := by decide

theorem packV_add : ∀ a0 a1 a2 a3 b0 b1 b2 b3 : Bool,
    packV (V4.add ⟨a0, a1, a2, a3⟩ ⟨b0, b1, b2, b3⟩) =
      packV ⟨a0, a1, a2, a3⟩ ^^^ packV ⟨b0, b1, b2, b3⟩ := by decide

theorem packV_sm : ∀ c a0 a1 a2 a3 : Bool,
    packV (V4.sm c ⟨a0, a1, a2, a3⟩) = if c then packV ⟨a0, a1, a2, a3⟩ else 0 := by decide

theorem packV_bit0 : ∀ a0 a1 a2 a3 : Bool, (packV ⟨a0, a1, a2, a3⟩ % 2 = 1 ↔ a0 = true) := by decide
theorem packV_bit1 : ∀ a0 a1 a2 a3 : Bool, (packV ⟨a0, a1, a2, a3⟩ / 2 % 2 = 1 ↔ a1 = true) := by decide
theorem packV_bit2 : ∀ a0 a1 a2 a3 : Bool, (packV ⟨a0, a1, a2, a3⟩ / 4 % 2 = 1 ↔ a2 = true) := by decide
theorem packV_bit3 : ∀ a0 a1 a2 a3 : Bool, (packV ⟨a0, a1, a2, a3⟩ / 8 % 2 = 1 ↔ a3 = true) := by decide

theorem packV_lt' (v : V4) : packV v < 16 := packV_lt v.x0 v.x1 v.x2 v.x3

theorem pack_mod_r0 (M : Mat4) : pack M % 16 = packV M.r0 := by
  have := packV_lt' M.r0; have := packV_lt' M.r1; have := packV_lt' M.r2; have := packV_lt' M.r3
  unfold pack; omega

theorem pack_mod_r1 (M : Mat4) : pack M / 16 % 16 = packV M.r1 := by
  have := packV_lt' M.r0; have := packV_lt' M.r1; have := packV_lt' M.r2; have := packV_lt' M.r3
  unfold pack; omega

theorem pack_mod_r2 (M : Mat4) : pack M / 256 % 16 = packV M.r2 := by
  have := packV_lt' M.r0; have := packV_lt' M.r1; have := packV_lt' M.r2; have := packV_lt' M.r3
  unfold pack; omega

theorem pack_mod_r3 (M : Mat4) : pack M / 4096 % 16 = packV M.r3 := by
  have := packV_lt' M.r0; have := packV_lt' M.r1; have := packV_lt' M.r2; have := packV_lt' M.r3
  unfold pack; omega

theorem packV_vm (v : V4) (B : Mat4) : packV (vm v B) = vmN (packV v) (pack B) := by
  have hv : vm v B = (B.r0.sm v.x0).add ((B.r1.sm v.x1).add ((B.r2.sm v.x2).add (B.r3.sm v.x3))) := rfl
  have a := fun (x y : V4) => packV_add x.x0 x.x1 x.x2 x.x3 y.x0 y.x1 y.x2 y.x3
  have s := fun (c : Bool) (x : V4) => packV_sm c x.x0 x.x1 x.x2 x.x3
  have b0 := packV_bit0 v.x0 v.x1 v.x2 v.x3
  have b1 := packV_bit1 v.x0 v.x1 v.x2 v.x3
  have b2 := packV_bit2 v.x0 v.x1 v.x2 v.x3
  have b3 := packV_bit3 v.x0 v.x1 v.x2 v.x3
  rw [hv, a, a, a, s, s, s, s]
  unfold vmN
  rw [pack_mod_r0, pack_mod_r1, pack_mod_r2, pack_mod_r3]
  simp only [b0, b1, b2, b3]

theorem pack_mm (A B : Mat4) : pack (mm A B) = mmN (pack A) (pack B) := by
  have h0 : mmN (pack A) (pack B) = vmN (packV A.r0) (pack B) + 16 * (vmN (packV A.r1) (pack B) +
      16 * (vmN (packV A.r2) (pack B) + 16 * vmN (packV A.r3) (pack B))) := by
    unfold mmN
    rw [pack_mod_r0 A, pack_mod_r1 A, pack_mod_r2 A, pack_mod_r3 A]
  rw [h0]
  show packV (vm A.r0 B) + 16 * (packV (vm A.r1 B) + 16 * (packV (vm A.r2 B) +
    16 * packV (vm A.r3 B))) = _
  rw [packV_vm, packV_vm, packV_vm, packV_vm]

inductive InGen (gens : List Mat4) : Mat4 → Prop
  | one : InGen gens I4
  | mul {M g : Mat4} : InGen gens M → g ∈ gens → InGen gens (mm M g)

@[expose] def stepAdd (e : ℕ) (st : List ℕ × List ℕ) (g : Mat4) : List ℕ × List ℕ :=
  if mmN e (pack g) ∈ st.1 then st
  else (mmN e (pack g) :: st.1, st.2 ++ [mmN e (pack g)])

@[expose] def wlN (gens : List Mat4) : ℕ → List ℕ → List ℕ → List ℕ
  | 0, cs, _ => cs
  | _ + 1, cs, [] => cs
  | n + 1, cs, e :: q =>
    let st := gens.foldl (stepAdd e) (cs, q)
    wlN gens n st.1 st.2

@[expose] def closureCodes (gens : List Mat4) : List ℕ := wlN gens 400 [pack I4] [pack I4]

def SInv (gens : List Mat4) (cs q : List ℕ) : Prop :=
  (∀ c ∈ cs, ∃ M, InGen gens M ∧ pack M = c) ∧ cs.Nodup ∧ ∀ c ∈ q, c ∈ cs

theorem stepAdd_inv {gens : List Mat4} {e : ℕ} (he : ∃ M, InGen gens M ∧ pack M = e) {g : Mat4}
    (hg : g ∈ gens) {st : List ℕ × List ℕ} (h : SInv gens st.1 st.2) :
    SInv gens (stepAdd e st g).1 (stepAdd e st g).2 := by
  obtain ⟨M, hM, rfl⟩ := he
  obtain ⟨h1, h2, h3⟩ := h
  unfold stepAdd
  by_cases hc : mmN (pack M) (pack g) ∈ st.1
  · simp only [hc, ite_true]
    exact ⟨h1, h2, h3⟩
  · simp only [hc, ite_false]
    refine ⟨?_, ?_, ?_⟩
    · intro c hcm
      rcases List.mem_cons.mp hcm with rfl | hcm
      · exact ⟨mm M g, InGen.mul hM hg, (pack_mm M g).symm ▸ rfl⟩
      · exact h1 c hcm
    · exact List.nodup_cons.mpr ⟨hc, h2⟩
    · intro c hcm
      rcases List.mem_append.mp hcm with hcm | hcm
      · exact List.mem_cons_of_mem _ (h3 c hcm)
      · rw [List.mem_singleton.mp hcm]
        exact List.mem_cons_self

theorem foldl_inv {gens : List Mat4} {e : ℕ} (he : ∃ M, InGen gens M ∧ pack M = e) :
    ∀ (l : List Mat4), (∀ g ∈ l, g ∈ gens) → ∀ (st : List ℕ × List ℕ), SInv gens st.1 st.2 →
      SInv gens (l.foldl (stepAdd e) st).1 (l.foldl (stepAdd e) st).2 := by
  intro l
  induction l with
  | nil => intro _ st h; exact h
  | cons g l ih =>
    intro hl st h
    exact ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) _
      (stepAdd_inv he (hl g List.mem_cons_self) h)

theorem wlN_inv (gens : List Mat4) :
    ∀ (n : ℕ) (cs q : List ℕ), SInv gens cs q →
      (∀ c ∈ wlN gens n cs q, ∃ M, InGen gens M ∧ pack M = c) ∧ (wlN gens n cs q).Nodup := by
  intro n
  induction n with
  | zero => intro cs q h; exact ⟨h.1, h.2.1⟩
  | succ n ih =>
    intro cs q h
    cases q with
    | nil => exact ⟨h.1, h.2.1⟩
    | cons e q =>
      have he : ∃ M, InGen gens M ∧ pack M = e := h.1 e (h.2.2 e List.mem_cons_self)
      have hq : SInv gens (cs : List ℕ) q := ⟨h.1, h.2.1, fun c hc => h.2.2 c (List.mem_cons_of_mem _ hc)⟩
      exact ih _ _ (foldl_inv he gens (fun _ h => h) (cs, q) hq)

theorem closureCodes_spec (gens : List Mat4) :
    (∀ c ∈ closureCodes gens, ∃ M, InGen gens M ∧ pack M = c) ∧ (closureCodes gens).Nodup :=
  wlN_inv gens 400 _ _ ⟨fun c hc => ⟨I4, InGen.one, by rw [List.mem_singleton.mp hc]⟩,
    List.nodup_singleton _, fun c hc => hc⟩

set_option maxRecDepth 100000 in
theorem closure1 : ∀ Y ∈ Ylist1, (closureCodes [Mx, Y]).length = 360 := by decide +kernel

set_option maxRecDepth 100000 in
theorem closure2 : ∀ Y ∈ Ylist2, (closureCodes [Mx, Y]).length = 360 := by decide +kernel

@[expose] def IsRMat (M : Mat4) : Prop :=
  M.r0 = ⟨true, false, false, false⟩ ∧ M.r1 = ⟨false, true, false, false⟩ ∧ M.r2.x2 = true ∧
    M.r2.x3 = false ∧ M.r3.x2 = false ∧ M.r3.x3 = true

@[expose] def IsUMat (M : Mat4) : Prop :=
  M.r0 = ⟨true, false, false, false⟩ ∧ M.r1.x1 = true ∧ M.r1.x2 = false ∧ M.r1.x3 = false ∧
    M.r2.x1 = false ∧ M.r2.x2 = true ∧ M.r2.x3 = false ∧ M.r3.x3 = true

@[expose] def IsYMat (M : Mat4) : Prop :=
  M.r0 = ⟨true, false, false, false⟩ ∧ M.r1.x3 = false ∧ M.r2.x3 = false ∧ M.r3.x3 = true

theorem IsRMat.exists_Rpar {M : Mat4} (h : IsRMat M) :
    ∃ a0 a1 a2 a3 : Bool, M = Rpar a0 a1 a2 a3 := by
  obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩, ⟨c0, c1, c2, c3⟩, ⟨d0, d1, d2, d3⟩⟩ := M
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  simp only [V4.mk.injEq] at h0 h1
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h0
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
  simp only at h2 h3 h4 h5
  subst h2 h3 h4 h5
  exact ⟨c0, c1, d0, d1, rfl⟩

theorem IsUMat.exists_Upar {M : Mat4} (h : IsUMat M) :
    ∃ p0 p1 p2 p3 p4 : Bool, M = Upar p0 p1 p2 p3 p4 := by
  obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩, ⟨c0, c1, c2, c3⟩, ⟨d0, d1, d2, d3⟩⟩ := M
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only [V4.mk.injEq] at h0
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h0
  simp only at h1 h2 h3 h4 h5 h6 h7
  subst h1 h2 h3 h4 h5 h6 h7
  exact ⟨b0, c0, d0, d1, d2, rfl⟩

theorem IsYMat.exists_Ypar {M : Mat4} (h : IsYMat M) :
    ∃ q0 q1 q2 q3 q4 q5 q6 q7 q8 : Bool, M = Ypar q0 q1 q2 q3 q4 q5 q6 q7 q8 := by
  obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩, ⟨c0, c1, c2, c3⟩, ⟨d0, d1, d2, d3⟩⟩ := M
  obtain ⟨h0, h1, h2, h3⟩ := h
  simp only [V4.mk.injEq] at h0
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h0
  simp only at h1 h2 h3
  subst h1 h2 h3
  exact ⟨b0, b1, b2, c0, c1, c2, d0, d1, d2, rfl⟩

set_option maxRecDepth 100000 in
theorem Rpar_distinct : ∀ a0 a1 a2 a3 b0 b1 b2 b3 : Bool, Rpar a0 a1 a2 a3 ≠ I4 →
    Rpar b0 b1 b2 b3 ≠ I4 → Rpar a0 a1 a2 a3 ≠ Rpar b0 b1 b2 b3 →
    (mm (Rpar a0 a1 a2 a3) (Rpar b0 b1 b2 b3) ≠ I4 ∧
      mm (Rpar a0 a1 a2 a3) (Rpar b0 b1 b2 b3) ≠ Rpar a0 a1 a2 a3 ∧
      mm (Rpar a0 a1 a2 a3) (Rpar b0 b1 b2 b3) ≠ Rpar b0 b1 b2 b3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem Upar_distinct : ∀ p0 p1 p2 p3 p4 q0 q1 q2 q3 q4 : Bool,
    mm (Upar p0 p1 p2 p3 p4) (Upar q0 q1 q2 q3 q4) = mm (Upar q0 q1 q2 q3 q4) (Upar p0 p1 p2 p3 p4) →
    mm (Upar p0 p1 p2 p3 p4) (Upar p0 p1 p2 p3 p4) = I4 →
    mm (Upar q0 q1 q2 q3 q4) (Upar q0 q1 q2 q3 q4) = I4 → Upar p0 p1 p2 p3 p4 ≠ I4 →
    Upar q0 q1 q2 q3 q4 ≠ I4 → Upar p0 p1 p2 p3 p4 ≠ Upar q0 q1 q2 q3 q4 →
    (mm (Upar p0 p1 p2 p3 p4) (Upar q0 q1 q2 q3 q4) ≠ I4 ∧
      mm (Upar p0 p1 p2 p3 p4) (Upar q0 q1 q2 q3 q4) ≠ Upar p0 p1 p2 p3 p4 ∧
      mm (Upar p0 p1 p2 p3 p4) (Upar q0 q1 q2 q3 q4) ≠ Upar q0 q1 q2 q3 q4) := by decide +kernel

theorem IsRMat.mm_distinct {R1 R2 : Mat4} (h1 : IsRMat R1) (h2 : IsRMat R2) (n1 : R1 ≠ I4)
    (n2 : R2 ≠ I4) (n12 : R1 ≠ R2) :
    mm R1 R2 ≠ I4 ∧ mm R1 R2 ≠ R1 ∧ mm R1 R2 ≠ R2 := by
  obtain ⟨a0, a1, a2, a3, rfl⟩ := h1.exists_Rpar
  obtain ⟨b0, b1, b2, b3, rfl⟩ := h2.exists_Rpar
  exact Rpar_distinct a0 a1 a2 a3 b0 b1 b2 b3 n1 n2 n12

theorem IsUMat.mm_distinct {N1 N2 : Mat4} (h1 : IsUMat N1) (h2 : IsUMat N2)
    (hc : mm N1 N2 = mm N2 N1) (s1 : mm N1 N1 = I4) (s2 : mm N2 N2 = I4) (n1 : N1 ≠ I4)
    (n2 : N2 ≠ I4) (n12 : N1 ≠ N2) :
    mm N1 N2 ≠ I4 ∧ mm N1 N2 ≠ N1 ∧ mm N1 N2 ≠ N2 := by
  obtain ⟨p0, p1, p2, p3, p4, rfl⟩ := h1.exists_Upar
  obtain ⟨q0, q1, q2, q3, q4, rfl⟩ := h2.exists_Upar
  exact Upar_distinct p0 p1 p2 p3 p4 q0 q1 q2 q3 q4 hc s1 s2 n1 n2 n12

theorem cInj1' (v w : V4) (h : vm v c1 = vm w c1) : v = w := by
  obtain ⟨a0, a1, a2, a3⟩ := v
  obtain ⟨b0, b1, b2, b3⟩ := w
  obtain ⟨h0, h1, h2, h3⟩ := cInj1 _ _ _ _ _ _ _ _ h
  subst h0 h1 h2 h3
  rfl

theorem cInj2' (v w : V4) (h : vm v c2 = vm w c2) : v = w := by
  obtain ⟨a0, a1, a2, a3⟩ := v
  obtain ⟨b0, b1, b2, b3⟩ := w
  obtain ⟨h0, h1, h2, h3⟩ := cInj2 _ _ _ _ _ _ _ _ h
  subst h0 h1 h2 h3
  rfl

set_option maxRecDepth 100000 in
theorem inter1 : ∀ P ∈ Rstd4, P ∈ Uset1 → P = I4 ∨ P = Rs2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem inter2 : ∀ P ∈ Rstd4, P ∈ Uset2 → P = I4 ∨ P = Rs2 := by decide +kernel

theorem model_main {R1 R2 N1 N2 Y : Mat4} (hR1 : IsRMat R1) (hR2 : IsRMat R2) (hR : RHypM R1 R2)
    (hN1 : IsUMat N1) (hN2 : IsUMat N2) (hU : UHypL [I4, R1, R2, mm R1 R2] N1 N2)
    (hY : IsYMat Y) (hYH : YHypM N1 N2 Y) :
    ∃ cm : Mat4, (∀ v w : V4, vm v cm = vm w cm → v = w) ∧
      (∀ P ∈ [I4, R1, R2, mm R1 R2], A6ok cm P) ∧ (∀ P ∈ [I4, N1, N2, mm N1 N2], A6ok cm P) ∧
      A6ok cm Mx ∧ A6ok cm Y ∧ (closureCodes [Mx, Y]).length = 360 ∧
      (∀ P ∈ [I4, R1, R2, mm R1 R2], P ∈ [I4, N1, N2, mm N1 N2] → P ≠ I4 →
        ∀ P' ∈ [I4, R1, R2, mm R1 R2], P' ∈ [I4, N1, N2, mm N1 N2] → P' ≠ I4 → P = P') := by
  obtain ⟨a0, a1, a2, a3, rfl⟩ := hR1.exists_Rpar
  obtain ⟨b0, b1, b2, b3, rfl⟩ := hR2.exists_Rpar
  obtain ⟨p0, p1, p2, p3, p4, rfl⟩ := hN1.exists_Upar
  obtain ⟨q0, q1, q2, q3, q4, rfl⟩ := hN2.exists_Upar
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, rfl⟩ := hY.exists_Ypar
  have hRc := stageR a0 a1 a2 a3 b0 b1 b2 b3 hR
  have hmem : ∀ P, P ∈ Rstd4 ↔
      P ∈ [I4, Rpar a0 a1 a2 a3, Rpar b0 b1 b2 b3, mm (Rpar a0 a1 a2 a3) (Rpar b0 b1 b2 b3)] := by
    intro P
    constructor
    · exact hRc.2.2.2.2 P
    · intro hP
      have h1 := hRc.1
      simp only [Rstd4, List.mem_cons, List.not_mem_nil, or_false] at h1 hP ⊢
      rcases hP with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · rcases h1.1 with h | h | h <;> simp [h]
      · rcases h1.2.1 with h | h | h <;> simp [h]
      · rcases h1.2.2 with h | h | h <;> simp [h]
  have hU' : UHyp p0 p1 p2 p3 p4 q0 q1 q2 q3 q4 := by
    unfold UHyp
    exact (UHypL_congr (fun P => (hmem P).symm) _ _).mp hU
  have hYc := stageY p0 p1 p2 p3 p4 q0 q1 q2 q3 q4 hU' y0 y1 y2 y3 y4 y5 y6 y7 y8 hYH
  have hRok : ∀ P ∈ [I4, Rpar a0 a1 a2 a3, Rpar b0 b1 b2 b3,
      mm (Rpar a0 a1 a2 a3) (Rpar b0 b1 b2 b3)], P ∈ Rstd4 := fun P hP => (hmem P).mpr hP
  rcases hYc.1 with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · have hsubU : ∀ P ∈ [I4, Upar p0 p1 p2 p3 p4, Upar q0 q1 q2 q3 q4,
        mm (Upar p0 p1 p2 p3 p4) (Upar q0 q1 q2 q3 q4)], P ∈ Uset1 := by
      intro P hP
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl | rfl | rfl
      · simp [Uset1]
      · exact h1
      · exact h2
      · exact h3
    refine ⟨c1, fun v w h => cInj1' v w h, fun P hP => ok1 P ?_, fun P hP => ok1 P ?_,
      ok1 _ List.mem_cons_self, ok1 _ ?_, closure1 _ h4, ?_⟩
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_left _ (hRok P hP)))
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (hsubU P hP))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_right _ h4))
    · intro P hP hPU hP1 P' hP' hP'U hP'1
      rcases inter1 P (hRok P hP) (hsubU P hPU) with a | a
      · exact absurd a hP1
      · rcases inter1 P' (hRok P' hP') (hsubU P' hP'U) with b | b
        · exact absurd b hP'1
        · exact a.trans b.symm
  · have hsubU : ∀ P ∈ [I4, Upar p0 p1 p2 p3 p4, Upar q0 q1 q2 q3 q4,
        mm (Upar p0 p1 p2 p3 p4) (Upar q0 q1 q2 q3 q4)], P ∈ Uset2 := by
      intro P hP
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl | rfl | rfl
      · simp [Uset2]
      · exact h1
      · exact h2
      · exact h3
    refine ⟨c2, fun v w h => cInj2' v w h, fun P hP => ok2 P ?_, fun P hP => ok2 P ?_,
      ok2 _ List.mem_cons_self, ok2 _ ?_, closure2 _ h4, ?_⟩
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_left _ (hRok P hP)))
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (hsubU P hP))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_right _ h4))
    · intro P hP hPU hP1 P' hP' hP'U hP'1
      rcases inter2 P (hRok P hP) (hsubU P hPU) with a | a
      · exact absurd a hP1
      · rcases inter2 P' (hRok P' hP') (hsubU P' hP'U) with b | b
        · exact absurd b hP'1
        · exact a.trans b.symm

end A6Model

end CFSG.Quasithin.S143
