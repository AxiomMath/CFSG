module

public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

public section

namespace CFSG.StandardType.E7F3

open Matrix

abbrev F3 := ZMod 3
abbrev V7 := Fin 7 → F3

@[expose] def C7 : Matrix (Fin 7) (Fin 7) F3 :=
  !![2, 0, 2, 0, 0, 0, 2;
     0, 2, 0, 2, 0, 0, 0;
     2, 0, 2, 2, 0, 0, 0;
     0, 2, 2, 2, 2, 0, 0;
     0, 0, 0, 2, 2, 2, 0;
     0, 0, 0, 0, 2, 2, 0;
     2, 0, 0, 0, 0, 0, 2]

@[expose] def pair (u v : V7) : F3 := u ⬝ᵥ (C7 *ᵥ v)

@[expose] def norm (v : V7) : F3 := pair v v

@[expose] def reflFun (h v : V7) : V7 := v - pair v h • h

@[expose] def e (i : Fin 7) : V7 := Pi.single i 1

@[expose] def rvec : V7 := ![1, 0, 2, 0, 1, 2, 0]

@[expose] def goodBase : V7 := e 6

@[expose] def badBase : V7 := ![0, 0, 0, 0, 1, 2, 1]

@[expose] def badImage : V7 := ![1, 2, 0, 1, 0, 0, 0]

@[expose] def badWitnessWord : List (Fin 7) := [6, 0, 3, 1, 2, 3, 6, 3, 2, 1, 3, 0, 6]

lemma C7_isSymm : C7.IsSymm := by
  decide +kernel

lemma pair_comm (u v : V7) : pair u v = pair v u :=
  C7_isSymm.dotProduct_mulVec_comm

lemma pair_add_left (u w v : V7) : pair (u + w) v = pair u v + pair w v := by
  simp [pair, Matrix.mulVec_add, add_dotProduct]

lemma pair_add_right (u v w : V7) : pair u (v + w) = pair u v + pair u w := by
  simp [pair, Matrix.mulVec_add, dotProduct_add]

lemma pair_smul_left (a : F3) (u v : V7) : pair (a • u) v = a * pair u v := by
  simp [pair, smul_dotProduct, mul_assoc]

lemma pair_smul_right (a : F3) (u v : V7) : pair u (a • v) = a * pair u v := by
  simp [pair, Matrix.mulVec_smul, dotProduct_smul, mul_assoc, mul_left_comm, mul_comm]

lemma smul_neg_vec (a : F3) (w : V7) : (-a) • w = -(a • w) := by
  ext x
  simp only [Pi.smul_apply, Pi.neg_apply]
  exact neg_mul a (w x)

lemma pair_neg_left (u v : V7) : pair (-u) v = -pair u v := by
  simp only [pair, dotProduct]
  calc
    ∑ i, (-u) i * (C7 *ᵥ v) i = ∑ i, -(u i * (C7 *ᵥ v) i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Pi.neg_apply]
      exact neg_mul (u i) ((C7 *ᵥ v) i)
    _ = -∑ i, u i * (C7 *ᵥ v) i := by
      have h (s : Finset (Fin 7)) (f : Fin 7 → F3) :
          (∑ i ∈ s, -f i) = -∑ i ∈ s, f i :=
        Finset.sum_neg_distrib (s := s) (f := f)
      simpa using h Finset.univ (fun i => u i * (C7 *ᵥ v) i)

lemma pair_neg_right (u v : V7) : pair u (-v) = -pair u v := by
  rw [pair_comm u (-v), pair_neg_left v u, pair_comm v u]

lemma pair_sub_left (u w v : V7) : pair (u - w) v = pair u v - pair w v := by
  rw [sub_eq_add_neg, pair_add_left, sub_eq_add_neg]
  congr 1
  exact pair_neg_left w v

lemma pair_sub_right (u v w : V7) : pair u (v - w) = pair u v - pair u w := by
  rw [sub_eq_add_neg, pair_add_right, sub_eq_add_neg]
  congr 1
  exact pair_neg_right u w

lemma norm_neg (h : V7) : norm (-h) = norm h := by
  simp only [norm, pair_neg_left, pair_neg_right]
  exact neg_neg _

lemma norm_neg_two (h : V7) (hn : norm h = 2) : norm (-h) = 2 := by
  simpa [norm_neg] using hn

lemma reflFun_add (h u v : V7) : reflFun h (u + v) = reflFun h u + reflFun h v := by
  simp only [reflFun, pair_add_left, add_smul]
  module

lemma reflFun_smul (h : V7) (a : F3) (u : V7) :
    reflFun h (a • u) = a • reflFun h u := by
  simp only [reflFun, pair_smul_left, smul_sub, smul_smul]

lemma reflFun_involutive (h : V7) (hn : norm h = 2) : Function.Involutive (reflFun h) := by
  intro v
  have hh : pair h h = 2 := by simpa [norm] using hn
  have hcalc : pair (v - pair v h • h) h = -pair v h := by
    rw [pair_sub_left, pair_smul_left]
    change pair v h - pair v h * pair h h = -pair v h
    rw [hh]
    ring_nf
  change v - pair v h • h - pair (v - pair v h • h) h • h = v
  have hneg : (-pair v h) • h = -(pair v h • h) := smul_neg_vec (pair v h) h
  rw [hcalc, hneg]
  abel

@[expose] noncomputable def reflPerm (h : V7) (hn : norm h = 2) : Equiv.Perm V7 :=
  (reflFun_involutive h hn).toPerm (reflFun h)

lemma reflPerm_apply (h : V7) (hn : norm h = 2) (v : V7) :
    reflPerm h hn v = reflFun h v := rfl

lemma reflPerm_neg_apply (h : V7) (hn : norm h = 2) (v : V7) :
    reflPerm (-h) (by simpa [norm_neg] using hn) v = reflPerm h hn v := by
  rw [reflPerm_apply, reflPerm_apply]
  ext x
  simp [reflFun, pair_neg_right]

lemma reflPerm_preserves_pair (h : V7) (hn : norm h = 2) (u v : V7) :
    pair (reflPerm h hn u) (reflPerm h hn v) = pair u v := by
  have hh : pair h h = 2 := by simpa [norm] using hn
  rw [reflPerm_apply, reflPerm_apply]
  simp only [reflFun, pair_sub_left, pair_sub_right, pair_smul_left, pair_smul_right,
    pair_comm, hh]
  ring

@[expose] def IsLinearPerm (g : Equiv.Perm V7) : Prop :=
  ∀ (a : F3) (u v : V7), g (u + a • v) = g u + a • g v

@[expose] def linearPerms : Subgroup (Equiv.Perm V7) where
  carrier := {g | IsLinearPerm g}
  one_mem' := by
    intro a u v
    simp
  mul_mem' := by
    intro g h hg hh a u v
    simp only [Equiv.Perm.mul_apply]
    rw [hh a u v, hg a (h u) (h v)]
  inv_mem' := by
    intro g hg a u v
    apply g.injective
    change g (g.symm (u + a • v)) = g (g.symm u + a • g.symm v)
    rw [Equiv.apply_symm_apply]
    rw [hg a (g.symm u) (g.symm v)]
    simp

@[expose] def PreservesPair (g : Equiv.Perm V7) : Prop :=
  ∀ u v : V7, pair (g u) (g v) = pair u v

@[expose] def pairPres : Subgroup (Equiv.Perm V7) where
  carrier := {g | PreservesPair g}
  one_mem' := by
    intro u v
    rfl
  mul_mem' := by
    intro g h hg hh u v
    simp only [Equiv.Perm.mul_apply]
    rw [hg (h u) (h v), hh u v]
  inv_mem' := by
    intro g hg u v
    have h := hg (g.symm u) (g.symm v)
    simpa using h.symm

lemma conj_reflPerm {g : Equiv.Perm V7} (hlin : IsLinearPerm g)
    (hpair : PreservesPair g) {h : V7} (hn : norm h = 2) :
    g * reflPerm h hn * g⁻¹ = reflPerm (g h) (by
      change pair (g h) (g h) = 2
      rw [hpair h h]
      simpa [norm] using hn) := by
  apply Equiv.ext
  intro v
  change g (reflFun h (g.symm v)) = reflFun (g h) v
  rw [reflFun, reflFun]
  have hsub : ∀ (u w : V7) (a : F3), g (u - a • w) = g u - a • g w := by
    intro u w a
    calc
      g (u - a • w) = g (u + (-a) • w) := by
        congr 1
        ext x
        simp only [sub_eq_add_neg, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
        congr 1
        exact (neg_mul a (w x)).symm
      _ = g u + (-a) • g w := hlin (-a) u w
      _ = g u - a • g w := by
        rw [smul_neg_vec, sub_eq_add_neg]
  rw [hsub (g.symm v) h (pair (g.symm v) h)]
  rw [show g ((Equiv.symm g) v) = v from Equiv.apply_symm_apply g v]
  have hpair' : pair v (g h) = pair (g.symm v) h := by
    calc
      pair v (g h) = pair (g (g.symm v)) (g h) := by
        rw [Equiv.apply_symm_apply]
      _ = pair (g.symm v) h := hpair (g.symm v) h
  rw [hpair']

@[expose] def digits6 (v : V7) : List ℕ :=
  List.ofFn (fun i : Fin 6 => (v i.castSucc).val)

@[expose] def key6 (v : V7) : ℕ :=
  Nat.ofDigits 3 (digits6 v)

@[expose] def keyDigit (k i : ℕ) : ℕ := (k / 3 ^ i) % 3

@[expose] def vOfKey (k : ℕ) : V7 := fun i =>
  if h : i = 6 then 1 else (keyDigit k i.val : F3)

@[expose] def goodTable : List (ℕ × List (Fin 6)) := [
  (0, []),
  (1, [0]),
  (10, [0, 2]),
  (37, [0, 2, 3]),
  (118, [0, 2, 3, 4]),
  (361, [0, 2, 3, 4, 5]),
  (40, [0, 2, 3, 1]),
  (121, [0, 2, 3, 1, 4]),
  (364, [0, 2, 3, 1, 4, 5]),
  (148, [0, 2, 3, 1, 4, 3]),
  (391, [0, 2, 3, 1, 4, 3, 5]),
  (472, [0, 2, 3, 1, 4, 3, 5, 4]),
  (427, [0, 2, 3, 1, 4, 3, 2, 5, 4, 3]),
  (157, [0, 2, 3, 1, 4, 3, 2]),
  (400, [0, 2, 3, 1, 4, 3, 2, 5]),
  (481, [0, 2, 3, 1, 4, 3, 2, 5, 4]),
  (430, [0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1]),
  (410, [0, 2, 3, 1, 4, 3, 2, 0, 5, 4, 3, 2]),
  (428, [0, 2, 3, 1, 4, 3, 2, 0, 5, 4, 3]),
  (158, [0, 2, 3, 1, 4, 3, 2, 0]),
  (401, [0, 2, 3, 1, 4, 3, 2, 0, 5]),
  (482, [0, 2, 3, 1, 4, 3, 2, 0, 5, 4]),
  (413, [0, 2, 3, 1, 4, 3, 2, 0, 5, 4, 3, 1, 2]),
  (278, [0, 2, 3, 1, 4, 3, 2, 0, 5, 4, 3, 1, 2, 3, 4]),
  (521, [0, 2, 3, 1, 4, 3, 2, 0, 5, 4, 3, 1, 2, 3, 4, 5]),
  (440, [0, 2, 3, 1, 4, 3, 2, 0, 5, 4, 3, 1, 2, 3]),
  (431, [0, 2, 3, 1, 4, 3, 2, 0, 5, 4, 3, 1])
]

@[expose] def badTable : List (ℕ × List (Fin 6)) := [
  (567, []),
  (405, [3, 1, 2, 3, 4, 3, 1, 2, 3, 5, 4, 3, 1, 2, 3]),
  (594, [3]),
  (189, [3, 4, 5]),
  (675, [3, 4]),
  (135, [3, 1, 2, 4, 3, 1, 2, 5, 4, 3, 1, 2]),
  (378, [3, 1, 2, 3, 4, 3, 1, 2, 5, 4, 3, 1, 2]),
  (459, [3, 1, 2, 3, 4, 3, 1, 2, 3, 5, 4, 3, 1, 2]),
  (603, [3, 2]),
  (198, [3, 2, 4, 5]),
  (684, [3, 2, 4]),
  (63, [3, 2, 4, 3, 5, 4]),
  (225, [3, 2, 4, 3, 5]),
  (711, [3, 2, 4, 3]),
  (45, [3, 1, 4, 3, 2, 5, 4, 3, 1]),
  (126, [3, 1, 2, 4, 3, 2, 5, 4, 3, 1]),
  (369, [3, 1, 2, 3, 4, 3, 2, 5, 4, 3, 1]),
  (153, [3, 1, 2, 4, 3, 1, 2, 5, 4, 3, 1]),
  (396, [3, 1, 2, 3, 4, 3, 1, 2, 5, 4, 3, 1]),
  (477, [3, 1, 2, 3, 4, 3, 1, 2, 3, 5, 4, 3, 1]),
  (597, [3, 1]),
  (192, [3, 1, 4, 5]),
  (678, [3, 1, 4]),
  (57, [3, 1, 4, 3, 5, 4]),
  (219, [3, 1, 4, 3, 5]),
  (705, [3, 1, 4, 3]),
  (255, [3, 1, 2, 3, 4, 3, 5]),
  (498, [3, 1, 2, 3, 4, 3]),
  (93, [3, 1, 2, 4, 3, 5, 4]),
  (336, [3, 1, 2, 3, 4, 3, 5, 4]),
  (174, [3, 1, 2, 4, 3, 5]),
  (660, [3, 1, 2, 4, 3]),
  (606, [3, 1, 2]),
  (201, [3, 1, 2, 4, 5]),
  (687, [3, 1, 2, 4]),
  (309, [3, 1, 2, 3, 4, 5]),
  (552, [3, 1, 2, 3, 4]),
  (633, [3, 1, 2, 3]),
  (264, [3, 1, 2, 3, 4, 3, 2, 5]),
  (507, [3, 1, 2, 3, 4, 3, 2]),
  (102, [3, 1, 2, 4, 3, 2, 5, 4]),
  (345, [3, 1, 2, 3, 4, 3, 2, 5, 4]),
  (183, [3, 1, 2, 4, 3, 2, 5]),
  (669, [3, 1, 2, 4, 3, 2]),
  (48, [3, 1, 4, 3, 2, 5, 4, 3]),
  (129, [3, 1, 2, 4, 3, 2, 5, 4, 3]),
  (372, [3, 1, 2, 3, 4, 3, 2, 5, 4, 3]),
  (75, [3, 1, 4, 3, 2, 5, 4]),
  (237, [3, 1, 4, 3, 2, 5]),
  (723, [3, 1, 4, 3, 2]),
  (33, [3, 2, 4, 3, 1, 5, 4, 3, 2]),
  (114, [3, 1, 2, 4, 3, 1, 5, 4, 3, 2]),
  (357, [3, 1, 2, 3, 4, 3, 1, 5, 4, 3, 2]),
  (141, [3, 1, 2, 4, 3, 1, 2, 5, 4, 3, 2]),
  (384, [3, 1, 2, 3, 4, 3, 1, 2, 5, 4, 3, 2]),
  (465, [3, 1, 2, 3, 4, 3, 1, 2, 3, 5, 4, 3, 2]),
  (258, [3, 1, 2, 3, 4, 3, 1, 5]),
  (501, [3, 1, 2, 3, 4, 3, 1]),
  (96, [3, 1, 2, 4, 3, 1, 5, 4]),
  (339, [3, 1, 2, 3, 4, 3, 1, 5, 4]),
  (177, [3, 1, 2, 4, 3, 1, 5]),
  (663, [3, 1, 2, 4, 3, 1]),
  (42, [3, 2, 4, 3, 1, 5, 4, 3]),
  (123, [3, 1, 2, 4, 3, 1, 5, 4, 3]),
  (366, [3, 1, 2, 3, 4, 3, 1, 5, 4, 3]),
  (69, [3, 2, 4, 3, 1, 5, 4]),
  (231, [3, 2, 4, 3, 1, 5]),
  (717, [3, 2, 4, 3, 1]),
  (267, [3, 1, 2, 3, 4, 3, 1, 2, 5]),
  (510, [3, 1, 2, 3, 4, 3, 1, 2]),
  (105, [3, 1, 2, 4, 3, 1, 2, 5, 4]),
  (348, [3, 1, 2, 3, 4, 3, 1, 2, 5, 4]),
  (186, [3, 1, 2, 4, 3, 1, 2, 5]),
  (672, [3, 1, 2, 4, 3, 1, 2]),
  (294, [3, 1, 2, 3, 4, 3, 1, 2, 3, 5]),
  (537, [3, 1, 2, 3, 4, 3, 1, 2, 3]),
  (456, [3, 1, 2, 3, 4, 3, 1, 2, 3, 5, 4]),
  (159, [3, 1, 2, 4, 3, 1, 2, 5, 4, 3]),
  (402, [3, 1, 2, 3, 4, 3, 1, 2, 5, 4, 3]),
  (483, [3, 1, 2, 3, 4, 3, 1, 2, 3, 5, 4, 3]),
  (568, [0]),
  (406, [3, 1, 2, 3, 4, 3, 1, 2, 3, 5, 4, 3, 1, 2, 0, 3]),
  (595, [0, 3]),
  (190, [0, 3, 4, 5]),
  (676, [0, 3, 4]),
  (136, [3, 1, 2, 4, 3, 1, 2, 5, 4, 3, 1, 2, 0]),
  (379, [3, 1, 2, 3, 4, 3, 1, 2, 5, 4, 3, 1, 2, 0]),
  (460, [3, 1, 2, 3, 4, 3, 1, 2, 3, 5, 4, 3, 1, 2, 0]),
  (577, [0, 2]),
  (415, [3, 1, 2, 3, 4, 3, 1, 2, 3, 5, 4, 3, 1, 2, 0, 3, 2]),
  (307, [0, 2, 3, 4, 5]),
  (550, [0, 2, 3, 4]),
  (631, [0, 2, 3]),
  (262, [0, 2, 3, 2, 4, 3, 5]),
  (505, [0, 2, 3, 2, 4, 3]),
  (100, [0, 3, 2, 4, 3, 5, 4]),
  (343, [0, 2, 3, 2, 4, 3, 5, 4]),
  (181, [0, 3, 2, 4, 3, 5]),
  (667, [0, 3, 2, 4, 3]),
  (613, [0, 3, 2]),
  (208, [0, 3, 2, 4, 5]),
  (694, [0, 3, 2, 4]),
  (316, [0, 2, 3, 2, 4, 5]),
  (559, [0, 2, 3, 2, 4]),
  (640, [0, 2, 3, 2]),
  (598, [0, 3, 1]),
  (193, [0, 3, 1, 4, 5]),
  (679, [0, 3, 1, 4]),
  (58, [0, 3, 1, 4, 3, 5, 4]),
  (220, [0, 3, 1, 4, 3, 5]),
  (706, [0, 3, 1, 4, 3]),
  (22, [3, 2, 0, 4, 3, 1, 2, 5, 4, 3, 1, 2, 0]),
  (589, [0, 3, 1, 2, 3]),
  (616, [0, 3, 1, 2]),
  (211, [0, 3, 1, 2, 4, 5]),
  (697, [0, 3, 1, 2, 4]),
  (34, [3, 2, 4, 3, 1, 5, 4, 3, 2, 0]),
  (115, [3, 1, 2, 4, 3, 1, 5, 4, 3, 2, 0]),
  (358, [3, 1, 2, 3, 4, 3, 1, 5, 4, 3, 2, 0]),
  (142, [3, 1, 2, 4, 3, 1, 2, 5, 4, 3, 2, 0]),
  (385, [3, 1, 2, 3, 4, 3, 1, 2, 5, 4, 3, 2, 0]),
  (466, [3, 1, 2, 3, 4, 3, 1, 2, 3, 5, 4, 3, 2, 0]),
  (286, [0, 2, 3, 1, 4, 3, 5]),
  (529, [0, 2, 3, 1, 4, 3]),
  (448, [0, 2, 3, 1, 4, 3, 5, 4]),
  (313, [0, 2, 3, 1, 4, 5]),
  (556, [0, 2, 3, 1, 4]),
  (637, [0, 2, 3, 1]),
  (25, [3, 2, 0, 4, 3, 1, 2, 5, 4, 3, 2, 0]),
  (592, [0, 2, 3, 1, 2, 3]),
  (52, [3, 2, 0, 4, 3, 1, 5, 4, 3, 2, 0]),
  (133, [3, 1, 2, 0, 4, 3, 1, 5, 4, 3, 2, 0]),
  (376, [3, 1, 2, 0, 3, 4, 3, 1, 5, 4, 3, 2, 0]),
  (322, [0, 2, 3, 1, 2, 4, 5]),
  (565, [0, 2, 3, 1, 2, 4]),
  (646, [0, 2, 3, 1, 2]),
  (245, [0, 2, 3, 2, 0, 4, 3, 2, 5]),
  (488, [0, 2, 3, 2, 0, 4, 3, 2]),
  (83, [0, 3, 2, 0, 4, 3, 2, 5, 4]),
  (326, [0, 2, 3, 2, 0, 4, 3, 2, 5, 4]),
  (164, [0, 3, 2, 0, 4, 3, 2, 5]),
  (650, [0, 3, 2, 0, 4, 3, 2]),
  (29, [3, 2, 0, 4, 3, 2, 5, 4, 3]),
  (110, [0, 3, 2, 0, 4, 3, 2, 5, 4, 3]),
  (353, [0, 2, 3, 2, 0, 4, 3, 2, 5, 4, 3]),
  (56, [3, 2, 0, 4, 3, 2, 5, 4]),
  (218, [3, 2, 0, 4, 3, 2, 5]),
  (704, [3, 2, 0, 4, 3, 2]),
  (605, [3, 2, 0]),
  (200, [3, 2, 0, 4, 5]),
  (686, [3, 2, 0, 4]),
  (65, [3, 2, 0, 4, 3, 5, 4]),
  (227, [3, 2, 0, 4, 3, 5]),
  (713, [3, 2, 0, 4, 3]),
  (263, [0, 2, 3, 2, 0, 4, 3, 5]),
  (506, [0, 2, 3, 2, 0, 4, 3]),
  (101, [0, 3, 2, 0, 4, 3, 5, 4]),
  (344, [0, 2, 3, 2, 0, 4, 3, 5, 4]),
  (182, [0, 3, 2, 0, 4, 3, 5]),
  (668, [0, 3, 2, 0, 4, 3]),
  (614, [0, 3, 2, 0]),
  (209, [0, 3, 2, 0, 4, 5]),
  (695, [0, 3, 2, 0, 4]),
  (317, [0, 2, 3, 2, 0, 4, 5]),
  (560, [0, 2, 3, 2, 0, 4]),
  (641, [0, 2, 3, 2, 0]),
  (5, [3, 2, 0, 4, 3, 1, 2, 5, 4, 3, 1]),
  (572, [0, 3, 1, 2, 0, 3, 2]),
  (32, [3, 2, 0, 4, 3, 2, 5, 4, 3, 1]),
  (113, [0, 3, 2, 0, 4, 3, 2, 5, 4, 3, 1]),
  (356, [0, 2, 3, 2, 0, 4, 3, 2, 5, 4, 3, 1]),
  (302, [3, 1, 2, 0, 3, 2, 4, 5]),
  (545, [3, 1, 2, 0, 3, 2, 4]),
  (626, [3, 1, 2, 0, 3, 2]),
  (257, [3, 1, 2, 0, 3, 4, 3, 5]),
  (500, [3, 1, 2, 0, 3, 4, 3]),
  (95, [3, 1, 2, 0, 4, 3, 5, 4]),
  (338, [3, 1, 2, 0, 3, 4, 3, 5, 4]),
  (176, [3, 1, 2, 0, 4, 3, 5]),
  (662, [3, 1, 2, 0, 4, 3]),
  (608, [3, 1, 2, 0]),
  (203, [3, 1, 2, 0, 4, 5]),
  (689, [3, 1, 2, 0, 4]),
  (311, [3, 1, 2, 0, 3, 4, 5]),
  (554, [3, 1, 2, 0, 3, 4]),
  (635, [3, 1, 2, 0, 3]),
  (23, [3, 2, 0, 4, 3, 1, 2, 5, 4, 3, 1, 2]),
  (590, [0, 3, 1, 2, 0, 3]),
  (617, [0, 3, 1, 2, 0]),
  (212, [0, 3, 1, 2, 0, 4, 5]),
  (698, [0, 3, 1, 2, 0, 4]),
  (8, [3, 2, 0, 4, 3, 1, 2, 5, 4, 3]),
  (575, [0, 2, 3, 1, 2, 0, 3, 2]),
  (62, [3, 2, 0, 4, 3, 1, 2, 5, 4]),
  (224, [3, 2, 0, 4, 3, 1, 2, 5]),
  (710, [3, 2, 0, 4, 3, 1, 2]),
  (260, [3, 1, 2, 0, 3, 4, 3, 1, 5]),
  (503, [3, 1, 2, 0, 3, 4, 3, 1]),
  (98, [3, 1, 2, 0, 4, 3, 1, 5, 4]),
  (341, [3, 1, 2, 0, 3, 4, 3, 1, 5, 4]),
  (179, [3, 1, 2, 0, 4, 3, 1, 5]),
  (665, [3, 1, 2, 0, 4, 3, 1]),
  (44, [3, 2, 0, 4, 3, 1, 5, 4, 3]),
  (125, [3, 1, 2, 0, 4, 3, 1, 5, 4, 3]),
  (368, [3, 1, 2, 0, 3, 4, 3, 1, 5, 4, 3]),
  (71, [3, 2, 0, 4, 3, 1, 5, 4]),
  (233, [3, 2, 0, 4, 3, 1, 5]),
  (719, [3, 2, 0, 4, 3, 1]),
  (26, [3, 2, 0, 4, 3, 1, 2, 5, 4, 3, 2]),
  (593, [0, 2, 3, 1, 2, 0, 3]),
  (53, [3, 2, 0, 4, 3, 1, 5, 4, 3, 2]),
  (134, [3, 1, 2, 0, 4, 3, 1, 5, 4, 3, 2]),
  (377, [3, 1, 2, 0, 3, 4, 3, 1, 5, 4, 3, 2]),
  (323, [0, 2, 3, 1, 2, 0, 4, 5]),
  (566, [0, 2, 3, 1, 2, 0, 4]),
  (647, [0, 2, 3, 1, 2, 0])
]

@[expose] def rootList : List V7 := [
  ![0, 0, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 2, 0],
  ![0, 0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 0, 1, 1, 0],
  ![0, 0, 0, 0, 2, 0, 0],
  ![0, 0, 0, 0, 2, 2, 0],
  ![0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 1, 1, 0, 0],
  ![0, 0, 0, 1, 1, 1, 0],
  ![0, 0, 0, 2, 0, 0, 0],
  ![0, 0, 0, 2, 2, 0, 0],
  ![0, 0, 0, 2, 2, 2, 0],
  ![0, 0, 1, 0, 0, 0, 0],
  ![0, 0, 1, 1, 0, 0, 0],
  ![0, 0, 1, 1, 1, 0, 0],
  ![0, 0, 1, 1, 1, 1, 0],
  ![0, 0, 2, 0, 0, 0, 0],
  ![0, 0, 2, 2, 0, 0, 0],
  ![0, 0, 2, 2, 2, 0, 0],
  ![0, 0, 2, 2, 2, 2, 0],
  ![0, 1, 0, 0, 0, 0, 0],
  ![0, 1, 0, 1, 0, 0, 0],
  ![0, 1, 0, 1, 1, 0, 0],
  ![0, 1, 0, 1, 1, 1, 0],
  ![0, 1, 1, 1, 0, 0, 0],
  ![0, 1, 1, 1, 1, 0, 0],
  ![0, 1, 1, 1, 1, 1, 0],
  ![0, 1, 1, 2, 1, 0, 0],
  ![0, 1, 1, 2, 1, 1, 0],
  ![0, 1, 1, 2, 2, 1, 0],
  ![0, 2, 0, 0, 0, 0, 0],
  ![0, 2, 0, 2, 0, 0, 0],
  ![0, 2, 0, 2, 2, 0, 0],
  ![0, 2, 0, 2, 2, 2, 0],
  ![0, 2, 2, 1, 1, 2, 0],
  ![0, 2, 2, 1, 2, 0, 0],
  ![0, 2, 2, 1, 2, 2, 0],
  ![0, 2, 2, 2, 0, 0, 0],
  ![0, 2, 2, 2, 2, 0, 0],
  ![0, 2, 2, 2, 2, 2, 0],
  ![1, 0, 0, 0, 0, 0, 0],
  ![1, 0, 1, 0, 0, 0, 0],
  ![1, 0, 1, 1, 0, 0, 0],
  ![1, 0, 1, 1, 1, 0, 0],
  ![1, 0, 1, 1, 1, 1, 0],
  ![1, 1, 1, 1, 0, 0, 0],
  ![1, 1, 1, 1, 1, 0, 0],
  ![1, 1, 1, 1, 1, 1, 0],
  ![1, 1, 1, 2, 1, 0, 0],
  ![1, 1, 1, 2, 1, 1, 0],
  ![1, 1, 1, 2, 2, 1, 0],
  ![1, 1, 2, 0, 2, 1, 0],
  ![1, 1, 2, 2, 1, 0, 0],
  ![1, 1, 2, 2, 1, 1, 0],
  ![1, 1, 2, 2, 2, 1, 0],
  ![1, 2, 2, 0, 2, 1, 0],
  ![2, 0, 0, 0, 0, 0, 0],
  ![2, 0, 2, 0, 0, 0, 0],
  ![2, 0, 2, 2, 0, 0, 0],
  ![2, 0, 2, 2, 2, 0, 0],
  ![2, 0, 2, 2, 2, 2, 0],
  ![2, 1, 1, 0, 1, 2, 0],
  ![2, 2, 1, 0, 1, 2, 0],
  ![2, 2, 1, 1, 1, 2, 0],
  ![2, 2, 1, 1, 2, 0, 0],
  ![2, 2, 1, 1, 2, 2, 0],
  ![2, 2, 2, 1, 1, 2, 0],
  ![2, 2, 2, 1, 2, 0, 0],
  ![2, 2, 2, 1, 2, 2, 0],
  ![2, 2, 2, 2, 0, 0, 0],
  ![2, 2, 2, 2, 2, 0, 0],
  ![2, 2, 2, 2, 2, 2, 0]
]

@[expose] def goodKeys : List ℕ := List.map Prod.fst goodTable

@[expose] def badKeys : List ℕ := List.map Prod.fst badTable

@[expose] def applyL (v : V7) (w : List (Fin 6)) : V7 :=
  w.foldl (fun v i => reflFun (e i.castSucc) v) v

lemma key6_lt (v : V7) : key6 v < 729 := by
  rw [key6]
  have hlen : (digits6 v).length = 6 := by simp [digits6]
  have hdig : ∀ x ∈ digits6 v, x < 3 := by
    intro x hx
    simp only [digits6, List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (v i.castSucc).val_lt
  have hlt := Nat.ofDigits_lt_base_pow_length (b := 3) (by norm_num) hdig
  rw [hlen] at hlt
  norm_num at hlt
  exact hlt

lemma key6_digit (v : V7) (i : Fin 6) :
    keyDigit (key6 v) i.val = (v i.castSucc).val := by
  simp only [keyDigit, key6]
  have hdig : ∀ x ∈ digits6 v, x < 3 := by
    intro x hx
    simp only [digits6, List.mem_ofFn] at hx
    obtain ⟨j, rfl⟩ := hx
    exact (v j.castSucc).val_lt
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop (i : ℕ) (by norm_num) (digits6 v) hdig]
  rw [Nat.ofDigits_mod_eq_head!]
  have hlen : (i : ℕ) < (digits6 v).length := by simp [digits6]
  rw [List.drop_eq_getElem_cons hlen]
  have hget : (digits6 v)[i.val] = (v i.castSucc).val := by
    simp only [digits6, List.getElem_ofFn]
  rw [hget]
  exact Nat.mod_eq_of_lt (v i.castSucc).val_lt

lemma vOfKey_key6 (v : V7) (hv : v 6 = 1) : vOfKey (key6 v) = v := by
  funext i
  by_cases hi : i = 6
  · subst i
    simp [vOfKey, hv]
  · have hlt : i.val < 6 := by
      have := i.isLt
      omega
    let j : Fin 6 := ⟨i.val, hlt⟩
    have hcast : j.castSucc = i := Fin.ext rfl
    simp only [vOfKey, dif_neg hi]
    rw [← hcast]
    have h := key6_digit v j
    have h' : (keyDigit (key6 v) j.val : F3) = v j.castSucc := by
      rw [h, ZMod.natCast_zmod_val]
    simpa [j] using h'

lemma goodTable_words :
    ∀ p ∈ goodTable, ∀ i : Fin 7, applyL goodBase p.2 i = vOfKey p.1 i := by
  decide +kernel

lemma badTable_words :
    ∀ p ∈ badTable, ∀ i : Fin 7, applyL badBase p.2 i = vOfKey p.1 i := by
  decide +kernel

lemma key_coverage :
    ∀ k ∈ List.range 729, norm (vOfKey k) = 2 → k ∈ goodKeys ∨ k ∈ badKeys := by
  decide +kernel

lemma norm_e_all : ∀ i : Fin 7, norm (e i) = 2 := by
  decide +kernel

lemma norm_goodBase : norm goodBase = 2 := by
  simpa [goodBase] using norm_e_all 6

lemma norm_badBase : norm badBase = 2 := by
  decide +kernel

lemma e2_mem_rootList : e 2 ∈ rootList := by
  decide +kernel

lemma badImage_not_mem_rootList : badImage ∉ rootList := by
  decide +kernel

@[expose] noncomputable def s7 (i : Fin 7) : Equiv.Perm V7 :=
  reflPerm (e i) (norm_e_all i)

@[expose] noncomputable def genBad : Equiv.Perm V7 :=
  reflPerm badBase norm_badBase

@[expose] def firstSixSet : Set (Fin 7) := {i | i.val < 6}

@[expose] noncomputable def L : Subgroup (Equiv.Perm V7) :=
  Subgroup.closure (s7 '' firstSixSet)

@[expose] noncomputable def G7 : Subgroup (Equiv.Perm V7) :=
  Subgroup.closure (Set.range s7)

lemma L_le_G7 : L ≤ G7 := by
  apply (Subgroup.closure_le G7).mpr
  rintro _ ⟨i, hi, rfl⟩
  exact Subgroup.subset_closure ⟨i, rfl⟩

lemma s7_linear (i : Fin 7) : IsLinearPerm (s7 i) := by
  intro a u v
  simp only [s7, reflPerm_apply]
  rw [reflFun_add, reflFun_smul]

lemma s7_pair (i : Fin 7) : PreservesPair (s7 i) := by
  intro u v
  simpa only [s7, reflPerm_apply] using reflPerm_preserves_pair (e i) (norm_e_all i) u v

lemma L_le_linear : L ≤ linearPerms := by
  apply (Subgroup.closure_le linearPerms).mpr
  rintro _ ⟨i, hi, rfl⟩
  exact s7_linear i

lemma L_le_pairPres : L ≤ pairPres := by
  apply (Subgroup.closure_le pairPres).mpr
  rintro _ ⟨i, hi, rfl⟩
  exact s7_pair i

lemma reflFun_rootList_all :
    ∀ i : Fin 7, i.val < 6 → ∀ v ∈ rootList, reflFun (e i) v ∈ rootList := by
  decide +kernel

lemma s7_root_iff (i : Fin 7) (hi : i.val < 6) (v : V7) :
    v ∈ rootList ↔ s7 i v ∈ rootList := by
  constructor
  · intro hv
    simpa only [s7, reflPerm_apply] using reflFun_rootList_all i hi v hv
  · intro hv
    have hv' : reflFun (e i) v ∈ rootList := by
      simpa only [s7, reflPerm_apply] using hv
    have h2 := reflFun_rootList_all i hi (reflFun (e i) v) hv'
    have hinv : reflFun (e i) (reflFun (e i) v) = v :=
      reflFun_involutive (e i) (norm_e_all i) v
    rwa [hinv] at h2

@[expose] noncomputable def wordL : List (Fin 6) → Equiv.Perm V7
  | [] => 1
  | i :: w => wordL w * s7 i.castSucc

lemma wordL_mem {A : Subgroup (Equiv.Perm V7)} (hL : L ≤ A) (w : List (Fin 6)) :
    wordL w ∈ A := by
  induction w with
  | nil => exact one_mem A
  | cons i w ih =>
      rw [wordL]
      apply mul_mem ih
      apply hL
      exact Subgroup.subset_closure ⟨i.castSucc, by simp [firstSixSet], rfl⟩

lemma wordL_apply (w : List (Fin 6)) (v : V7) : wordL w v = applyL v w := by
  induction w generalizing v with
  | nil => rfl
  | cons i w ih =>
      simp only [wordL, Equiv.Perm.mul_apply, ih, applyL, List.foldl_cons,
        s7, reflPerm_apply]

@[expose] def badRoot (i : Fin 7) : V7 :=
  if i = 6 then badBase else e i

@[expose] noncomputable def genW (i : Fin 7) : Equiv.Perm V7 :=
  if i = 6 then genBad else s7 i

@[expose] noncomputable def wordW : List (Fin 7) → Equiv.Perm V7
  | [] => 1
  | i :: w => wordW w * genW i

@[expose] def applyW (v : V7) (w : List (Fin 7)) : V7 :=
  w.foldl (fun v i => reflFun (badRoot i) v) v

lemma wordW_mem {A : Subgroup (Equiv.Perm V7)} (hL : L ≤ A) (hbad : genBad ∈ A)
    (w : List (Fin 7)) : wordW w ∈ A := by
  induction w with
  | nil => exact one_mem A
  | cons i w ih =>
      rw [wordW]
      apply mul_mem ih
      by_cases hi : i = 6
      · simpa [genW, hi] using hbad
      · have hlt : i.val < 6 := by
          have := i.isLt
          omega
        have hgen : genW i = s7 i := by simp [genW, hi]
        rw [hgen]
        exact hL (Subgroup.subset_closure ⟨i, by simpa [firstSixSet] using hlt, rfl⟩)

lemma wordW_apply (w : List (Fin 7)) (v : V7) : wordW w v = applyW v w := by
  induction w generalizing v with
  | nil => rfl
  | cons i w ih =>
      simp only [wordW, Equiv.Perm.mul_apply, ih, applyW, List.foldl_cons,
        genW, badRoot, s7]
      by_cases hi : i = 6 <;> simp [hi, genBad, reflPerm_apply]

@[expose] noncomputable def badWitness : Equiv.Perm V7 :=
  wordW badWitnessWord

lemma badWitness_image : badWitness (e 2) = badImage := by
  rw [badWitness, wordW_apply]
  decide +kernel

lemma bad_word_of_key {h : V7} (hl : h 6 = 1) (hbad : key6 h ∈ badKeys) :
    ∃ w : List (Fin 6), h = wordL w badBase := by
  rcases List.mem_map.mp hbad with ⟨p, hp, hpk⟩
  have hw : applyL badBase p.2 = h := by
    rw [← vOfKey_key6 h hl, ← hpk]
    funext i
    exact badTable_words p hp i
  refine ⟨p.2, ?_⟩
  rw [← hw, wordL_apply]

lemma good_word_of_key {h : V7} (hl : h 6 = 1) (hgood : key6 h ∈ goodKeys) :
    ∃ w : List (Fin 6), h = wordL w goodBase := by
  rcases List.mem_map.mp hgood with ⟨p, hp, hpk⟩
  have hw : applyL goodBase p.2 = h := by
    rw [← vOfKey_key6 h hl, ← hpk]
    funext i
    exact goodTable_words p hp i
  refine ⟨p.2, ?_⟩
  rw [← hw, wordL_apply]

lemma reflPerm_proof_irrel (h : V7) (hn hn' : norm h = 2) :
    reflPerm h hn = reflPerm h hn' := by
  apply Equiv.ext
  intro v
  rfl

lemma reflPerm_neg (h : V7) (hn : norm h = 2) :
    reflPerm (-h) (norm_neg_two h hn) = reflPerm h hn := by
  apply Equiv.ext
  intro v
  simpa [norm_neg_two] using reflPerm_neg_apply h hn v

lemma goodBase_eq_e6 : goodBase = e 6 := rfl

lemma good_refl_eq_conj {g : Equiv.Perm V7} {h : V7} (hn : norm h = 2)
    (hgL : g ∈ L) (hg : h = g goodBase) :
    reflPerm h hn = g * s7 6 * g⁻¹ := by
  subst h
  symm
  simpa [s7, goodBase] using
    conj_reflPerm (L_le_linear hgL) (L_le_pairPres hgL) (h := e 6) (norm_e_all 6)

lemma neg_good_refl_eq_conj {g : Equiv.Perm V7} {h : V7} (hn : norm h = 2)
    (hgL : g ∈ L) (hg : h = -(g goodBase)) :
    reflPerm h hn = g * s7 6 * g⁻¹ := by
  have hnormg : norm (g goodBase) = 2 := by
    change pair (g goodBase) (g goodBase) = 2
    rw [L_le_pairPres hgL goodBase goodBase]
    simpa [norm] using norm_goodBase
  subst h
  calc
    reflPerm (-(g goodBase)) hn =
        reflPerm (-(g goodBase)) (norm_neg_two (g goodBase) hnormg) :=
      reflPerm_proof_irrel _ _ _
    _ = reflPerm (g goodBase) hnormg := reflPerm_neg (g goodBase) hnormg
    _ = g * s7 6 * g⁻¹ := by
      symm
      simpa [s7, goodBase] using
        conj_reflPerm (L_le_linear hgL) (L_le_pairPres hgL) (h := e 6) (norm_e_all 6)

end CFSG.StandardType.E7F3

end
