module

public import CFSG.LocalAnalysis.StandardType.FF81.CentAModelDefs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

public section

namespace CFSG.StandardType.FF81.CentA

open Matrix RootFusionLin

variable {m : ℕ}

private theorem caUnip_eq_zero_of_forall_mul_eq_zero {b : Matrix (Fin m) (Fin 1) (ZMod 2)}
    (h : ∀ a' : Matrix (Fin 1) (Fin m) (ZMod 2), a' * b = 0) : b = 0 := by
  ext j i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  have hj := congrFun₂ (h (Matrix.single (0 : Fin 1) j 1)) (0 : Fin 1) (0 : Fin 1)
  rw [Matrix.single_mul_apply_same, one_mul] at hj
  simpa only [Matrix.zero_apply] using hj

private theorem caUnip_eq_zero_of_forall_mul_eq_zero_left {a : Matrix (Fin 1) (Fin m) (ZMod 2)}
    (h : ∀ b' : Matrix (Fin m) (Fin 1) (ZMod 2), a * b' = 0) : a = 0 := by
  ext i j
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  have hj := congrFun₂ (h (Matrix.single j (0 : Fin 1) 1)) (0 : Fin 1) (0 : Fin 1)
  rw [Matrix.mul_single_apply_same, mul_one] at hj
  simpa only [Matrix.zero_apply] using hj

private theorem caUnip_conj_uGL_uOne {a : Matrix (Fin 1) (Fin m) (ZMod 2)}
    {b : Matrix (Fin m) (Fin 1) (ZMod 2)} {c : Matrix (Fin 1) (Fin 1) (ZMod 2)}
    {v : GL (BlkIdx 1 m) (ZMod 2)} (hv : v ∈ uOne m) :
    uGL a b c * v * (uGL a b c)⁻¹ ∈ uOne m := by
  obtain ⟨x, z, rfl⟩ := hv
  have hcomm := uGL_commutator (r := 1) (m := m) a x b 0 c z
  have h : uGL a b c * uGL x 0 z * (uGL a b c)⁻¹ =
      uGL 0 0 (a * (0 : Matrix (Fin m) (Fin 1) (ZMod 2)) + x * b) * uGL x 0 z := by
    calc uGL a b c * uGL x 0 z * (uGL a b c)⁻¹
        = (uGL a b c * uGL x 0 z * (uGL a b c)⁻¹ * (uGL x 0 z)⁻¹) * uGL x 0 z := by
          group
      _ = uGL 0 0 (a * (0 : Matrix (Fin m) (Fin 1) (ZMod 2)) + x * b) * uGL x 0 z := by
            rw [hcomm]
  rw [h]
  exact (uOne m).mul_mem
    ⟨0, a * (0 : Matrix (Fin m) (Fin 1) (ZMod 2)) + x * b, rfl⟩ ⟨x, z, rfl⟩

private theorem caUnip_conj_uGL_uTwo {a : Matrix (Fin 1) (Fin m) (ZMod 2)}
    {b : Matrix (Fin m) (Fin 1) (ZMod 2)} {c : Matrix (Fin 1) (Fin 1) (ZMod 2)}
    {v : GL (BlkIdx 1 m) (ZMod 2)} (hv : v ∈ uTwo m) :
    uGL a b c * v * (uGL a b c)⁻¹ ∈ uTwo m := by
  obtain ⟨y, z, rfl⟩ := hv
  have hcomm := uGL_commutator (r := 1) (m := m) a 0 b y c z
  have h : uGL a b c * uGL 0 y z * (uGL a b c)⁻¹ =
      uGL 0 0 (a * y + (0 : Matrix (Fin 1) (Fin m) (ZMod 2)) * b) * uGL 0 y z := by
    calc uGL a b c * uGL 0 y z * (uGL a b c)⁻¹
        = (uGL a b c * uGL 0 y z * (uGL a b c)⁻¹ * (uGL 0 y z)⁻¹) * uGL 0 y z := by
          group
      _ = uGL 0 0 (a * y + (0 : Matrix (Fin 1) (Fin m) (ZMod 2)) * b) * uGL 0 y z := by
            rw [hcomm]
  rw [h]
  exact (uTwo m).mul_mem
    ⟨0, a * y + (0 : Matrix (Fin 1) (Fin m) (ZMod 2)) * b, rfl⟩ ⟨y, z, rfl⟩

private theorem caUnip_levi_conj_uOne (R : GL (Fin m) (ZMod 2))
    (x : Matrix (Fin 1) (Fin m) (ZMod 2)) (z : Matrix (Fin 1) (Fin 1) (ZMod 2)) :
    levi (1 : GL (Fin 1) (ZMod 2)) R * uGL x 0 z *
      (levi (1 : GL (Fin 1) (ZMod 2)) R)⁻¹ ∈ uOne m := by
  rw [levi_conj_uGL]
  refine ⟨((1 : GL (Fin 1) (ZMod 2)) : Matrix (Fin 1) (Fin 1) (ZMod 2)) * x *
      ((R⁻¹ : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)),
    ((1 : GL (Fin 1) (ZMod 2)) : Matrix (Fin 1) (Fin 1) (ZMod 2)) * z *
      (((1 : GL (Fin 1) (ZMod 2))⁻¹) : Matrix (Fin 1) (Fin 1) (ZMod 2)), ?_⟩
  simp

private theorem caUnip_levi_conj_uTwo (R : GL (Fin m) (ZMod 2))
    (y : Matrix (Fin m) (Fin 1) (ZMod 2)) (z : Matrix (Fin 1) (Fin 1) (ZMod 2)) :
    levi (1 : GL (Fin 1) (ZMod 2)) R * uGL 0 y z *
      (levi (1 : GL (Fin 1) (ZMod 2)) R)⁻¹ ∈ uTwo m := by
  rw [levi_conj_uGL]
  refine ⟨((R : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) * y *
      (((1 : GL (Fin 1) (ZMod 2))⁻¹) : Matrix (Fin 1) (Fin 1) (ZMod 2)),
    ((1 : GL (Fin 1) (ZMod 2)) : Matrix (Fin 1) (Fin 1) (ZMod 2)) * z *
      (((1 : GL (Fin 1) (ZMod 2))⁻¹) : Matrix (Fin 1) (Fin 1) (ZMod 2)), ?_⟩
  simp

theorem zSub_eq_zpowers (m : ℕ) : zSub 1 m = Subgroup.zpowers (jGL 1 m) := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    have h2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    have hc : c = 0 ∨ c = 1 := by
      rcases h2 (c 0 0) with h0 | h1
      · left
        ext i j
        have hi : i = 0 := Subsingleton.elim i 0
        have hj : j = 0 := Subsingleton.elim j 0
        rw [hi, hj, h0]
        rfl
      · right
        ext i j
        have hi : i = 0 := Subsingleton.elim i 0
        have hj : j = 0 := Subsingleton.elim j 0
        rw [hi, hj, h1]
        rfl
    rcases hc with h | h
    · rw [h, uGL_zero]
      exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers (jGL 1 m)
  · exact Subgroup.zpowers_le.mpr (jGL_mem_zSub 1 m)

theorem commutator_mem_zSub {u v : GL (BlkIdx 1 m) (ZMod 2)} (hu : u ∈ uSub 1 m)
    (hv : v ∈ uSub 1 m) : u * v * u⁻¹ * v⁻¹ ∈ zSub 1 m := by
  obtain ⟨a, b, c, rfl⟩ := hu
  obtain ⟨a', b', c', rfl⟩ := hv
  rw [uGL_commutator]
  exact ⟨a * b' + a' * b, rfl⟩

theorem mul_self_eq_one_of_mem_uOne {u : GL (BlkIdx 1 m) (ZMod 2)} (hu : u ∈ uOne m) :
    u * u = 1 := by
  obtain ⟨a, c, rfl⟩ := hu
  rw [uGL_mul]
  have ha : a + a = 0 := by
    ext i j
    simpa using CharTwo.add_self_eq_zero (a i j)
  have hc : c + c = 0 := by
    ext i j
    simpa using CharTwo.add_self_eq_zero (c i j)
  rw [ha, hc, Matrix.mul_zero, add_zero]
  exact uGL_zero

theorem mul_self_eq_one_of_mem_uTwo {u : GL (BlkIdx 1 m) (ZMod 2)} (hu : u ∈ uTwo m) :
    u * u = 1 := by
  obtain ⟨b, c, rfl⟩ := hu
  rw [uGL_mul]
  have hb : b + b = 0 := by
    ext i j
    simpa using CharTwo.add_self_eq_zero (b i j)
  have hc : c + c = 0 := by
    ext i j
    simpa using CharTwo.add_self_eq_zero (c i j)
  rw [hb, hc, Matrix.zero_mul b, add_zero]
  exact uGL_zero

theorem conj_mem_uOne {g u : GL (BlkIdx 1 m) (ZMod 2)} (hg : g ∈ Cent 1 m) (hu : u ∈ uOne m) :
    g * u * g⁻¹ ∈ uOne m := by
  obtain ⟨a, b, c, P, R, rfl⟩ := (mem_cent_iff 1 m).mp hg
  have hP : P = 1 := glOne_eq_one P
  subst P
  obtain ⟨x, z, rfl⟩ := hu
  have hrearr : (uGL a b c * levi (1 : GL (Fin 1) (ZMod 2)) R) * uGL x 0 z *
      (uGL a b c * levi (1 : GL (Fin 1) (ZMod 2)) R)⁻¹ =
      uGL a b c * (levi (1 : GL (Fin 1) (ZMod 2)) R * uGL x 0 z *
        (levi (1 : GL (Fin 1) (ZMod 2)) R)⁻¹) * (uGL a b c)⁻¹ := by
    group
  rw [hrearr]
  exact caUnip_conj_uGL_uOne (caUnip_levi_conj_uOne R x z)

theorem conj_mem_uTwo {g u : GL (BlkIdx 1 m) (ZMod 2)} (hg : g ∈ Cent 1 m) (hu : u ∈ uTwo m) :
    g * u * g⁻¹ ∈ uTwo m := by
  obtain ⟨a, b, c, P, R, rfl⟩ := (mem_cent_iff 1 m).mp hg
  have hP : P = 1 := glOne_eq_one P
  subst P
  obtain ⟨y, z, rfl⟩ := hu
  have hrearr : (uGL a b c * levi (1 : GL (Fin 1) (ZMod 2)) R) * uGL 0 y z *
      (uGL a b c * levi (1 : GL (Fin 1) (ZMod 2)) R)⁻¹ =
      uGL a b c * (levi (1 : GL (Fin 1) (ZMod 2)) R * uGL 0 y z *
        (levi (1 : GL (Fin 1) (ZMod 2)) R)⁻¹) * (uGL a b c)⁻¹ := by
    group
  rw [hrearr]
  exact caUnip_conj_uGL_uTwo (caUnip_levi_conj_uTwo R y z)

theorem mem_uOne_of_commute {u : GL (BlkIdx 1 m) (ZMod 2)} (hu : u ∈ uSub 1 m)
    (hc : ∀ v ∈ uOne m, u * v = v * u) : u ∈ uOne m := by
  obtain ⟨a, b, c, rfl⟩ := hu
  have key : ∀ a' : Matrix (Fin 1) (Fin m) (ZMod 2), a' * b = 0 := by
    intro a'
    have hv : uGL a' 0 (0 : Matrix (Fin 1) (Fin 1) (ZMod 2)) ∈ uOne m := ⟨a', 0, rfl⟩
    have h := hc _ hv
    rw [uGL_mul, uGL_mul] at h
    obtain ⟨-, -, h3⟩ := uGL_injective h
    have h4 : c = c + a' * b := by simpa [Matrix.mul_zero] using h3
    exact add_left_cancel (a := c) (by simpa using h4.symm)
  have hb : b = 0 := caUnip_eq_zero_of_forall_mul_eq_zero key
  subst hb
  exact ⟨a, c, rfl⟩

theorem mem_uTwo_of_commute {u : GL (BlkIdx 1 m) (ZMod 2)} (hu : u ∈ uSub 1 m)
    (hc : ∀ v ∈ uTwo m, u * v = v * u) : u ∈ uTwo m := by
  obtain ⟨a, b, c, rfl⟩ := hu
  have key : ∀ b' : Matrix (Fin m) (Fin 1) (ZMod 2), a * b' = 0 := by
    intro b'
    have hv : uGL 0 b' (0 : Matrix (Fin 1) (Fin 1) (ZMod 2)) ∈ uTwo m := ⟨b', 0, rfl⟩
    have h := hc _ hv
    rw [uGL_mul, uGL_mul] at h
    obtain ⟨-, -, h3⟩ := uGL_injective h
    simp only [Matrix.zero_mul, add_zero, zero_add] at h3
    exact add_left_cancel (a := c) (by rw [add_zero]; exact h3)
  have ha : a = 0 := caUnip_eq_zero_of_forall_mul_eq_zero_left key
  subst ha
  exact ⟨b, c, rfl⟩

theorem not_uOne_le_uTwo (hm : 1 ≤ m) : ¬ uOne m ≤ uTwo m := by
  intro hle
  let j : Fin m := ⟨0, hm⟩
  let a : Matrix (Fin 1) (Fin m) (ZMod 2) := Matrix.single 0 j 1
  have hu : uGL a 0 0 ∈ uOne m := ⟨a, 0, rfl⟩
  obtain ⟨b, c, hbc⟩ := hle hu
  obtain ⟨ha, -, -⟩ := uGL_injective hbc
  have h1 : a 0 j = 1 := by
    simp [a, Matrix.single_apply]
  have h0 : a 0 j = 0 := by
    rw [ha]
    rfl
  exact one_ne_zero (h1.symm.trans h0)

theorem not_uTwo_le_uOne (hm : 1 ≤ m) : ¬ uTwo m ≤ uOne m := by
  intro hle
  let j : Fin m := ⟨0, hm⟩
  let b : Matrix (Fin m) (Fin 1) (ZMod 2) := Matrix.single j 0 1
  have hu : uGL 0 b 0 ∈ uTwo m := ⟨b, 0, rfl⟩
  obtain ⟨a, c, hbc⟩ := hle hu
  obtain ⟨-, hb, -⟩ := uGL_injective hbc
  have h1 : b j 0 = 1 := by
    simp [b, Matrix.single_apply]
  have h0 : b j 0 = 0 := by
    rw [hb]
    rfl
  exact one_ne_zero (h1.symm.trans h0)

theorem eq_one_of_forall_commute {g : GL (BlkIdx 1 m) (ZMod 2)} (h : ∀ x, g * x = x * g) :
    g = 1 := by
  have hg : g ∈ Subgroup.center (GL (BlkIdx 1 m) (ZMod 2)) :=
    Subgroup.mem_center_iff.mpr fun x => (h x).symm
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg
  obtain ⟨u, rfl⟩ := hg
  have hu : u = 1 := Subsingleton.elim u 1
  rw [hu]
  exact map_one _

end CFSG.StandardType.FF81.CentA

end
