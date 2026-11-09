module

public import CFSG.Quasithin.EmptyFaithful.SzN32Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.Quasithin.SzN32

namespace Model

abbrev M6 : Type := Matrix (Fin 6) (Fin 6) (ZMod 2)

@[expose] def A0 : M6 := !![0, 1, 0, 0, 0, 0;
                            1, 1, 0, 0, 0, 0;
                            0, 0, 1, 0, 0, 0;
                            0, 0, 0, 1, 0, 0;
                            0, 0, 0, 0, 1, 0;
                            0, 0, 0, 0, 0, 1]

@[expose] def S0 : M6 := !![0, 0, 0, 0, 1, 0;
                            0, 0, 0, 0, 0, 1;
                            1, 0, 0, 0, 0, 0;
                            0, 1, 0, 0, 0, 0;
                            0, 0, 1, 0, 0, 0;
                            0, 0, 0, 1, 0, 0]

set_option maxRecDepth 100000 in
@[expose] def ga : GL (Fin 6) (ZMod 2) := ⟨A0, A0 * A0, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
@[expose] def gs : GL (Fin 6) (ZMod 2) := ⟨S0, S0 * S0, by decide +kernel, by decide +kernel⟩

@[expose] def ga1 : GL (Fin 6) (ZMod 2) := gs⁻¹ * ga * gs

@[expose] def ga2 : GL (Fin 6) (ZMod 2) := gs⁻¹ * ga1 * gs

@[expose] def nf (i j k l : Fin 3) : GL (Fin 6) (ZMod 2) :=
  ga ^ (i : ℕ) * ga1 ^ (j : ℕ) * ga2 ^ (k : ℕ) * gs ^ (l : ℕ)

set_option maxRecDepth 100000 in
theorem cubes : ga ^ 3 = 1 ∧ gs ^ 3 = 1 ∧ ga1 ^ 3 = 1 ∧ ga2 ^ 3 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem nf_mul_ga :
    ∀ i j k l : Fin 3, ∃ i' j' k' l' : Fin 3, nf i j k l * ga = nf i' j' k' l' := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem nf_mul_gs :
    ∀ i j k l : Fin 3, ∃ i' j' k' l' : Fin 3, nf i j k l * gs = nf i' j' k' l' := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem nf_inj : ∀ i j k l i' j' k' l' : Fin 3,
    nf i j k l = nf i' j' k' l' → (i = i' ∧ j = j' ∧ k = k' ∧ l = l') := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem nf0_mul_ga :
    ∀ i j k : Fin 3, ∃ i' j' k' : Fin 3, nf i j k 0 * ga = nf i' j' k' 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem nf0_mul_ga1 :
    ∀ i j k : Fin 3, ∃ i' j' k' : Fin 3, nf i j k 0 * ga1 = nf i' j' k' 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem nf0_mul_ga2 :
    ∀ i j k : Fin 3, ∃ i' j' k' : Fin 3, nf i j k 0 * ga2 = nf i' j' k' 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem nf0_cube : ∀ i j k : Fin 3, nf i j k 0 ^ 3 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ga_comm_ga1 : ga * ga1 = ga1 * ga := by decide +kernel

set_option maxRecDepth 100000 in
theorem ga_comm_ga2 : ga * ga2 = ga2 * ga := by decide +kernel

set_option maxRecDepth 100000 in
theorem ga1_comm_ga2 : ga1 * ga2 = ga2 * ga1 := by decide +kernel

theorem nf0_eq (i j k : Fin 3) : nf i j k 0 = ga ^ (i : ℕ) * ga1 ^ (j : ℕ) * ga2 ^ (k : ℕ) := by
  rw [nf, Fin.val_zero, pow_zero, mul_one]

theorem nf0_commute_gens (i j k : Fin 3) :
    Commute (nf i j k 0) ga ∧ Commute (nf i j k 0) ga1 ∧ Commute (nf i j k 0) ga2 := by
  have c1 : Commute ga ga1 := ga_comm_ga1
  have c2 : Commute ga ga2 := ga_comm_ga2
  have c3 : Commute ga1 ga2 := ga1_comm_ga2
  rw [nf0_eq]
  exact ⟨(((Commute.refl ga).pow_left _).mul_left (c1.symm.pow_left _)).mul_left
      (c2.symm.pow_left _),
    ((c1.pow_left _).mul_left ((Commute.refl ga1).pow_left _)).mul_left (c3.symm.pow_left _),
    ((c2.pow_left _).mul_left (c3.pow_left _)).mul_left ((Commute.refl ga2).pow_left _)⟩

theorem nf0_comm : ∀ i j k i' j' k' : Fin 3,
    nf i j k 0 * nf i' j' k' 0 = nf i' j' k' 0 * nf i j k 0 := by
  intro i j k i' j' k'
  obtain ⟨h1, h2, h3⟩ := nf0_commute_gens i j k
  have h : Commute (nf i j k 0) (nf i' j' k' 0) := by
    rw [nf0_eq i' j' k']
    exact ((h1.pow_right _).mul_right (h2.pow_right _)).mul_right (h3.pow_right _)
  exact h.eq

set_option maxRecDepth 100000 in
theorem u_comm_a : cm ga gs * ga = ga * cm ga gs := by decide +kernel

set_option maxRecDepth 100000 in
theorem z_comm_a : cm (cm ga gs) gs * ga = ga * cm (cm ga gs) gs := by decide +kernel

set_option maxRecDepth 100000 in
theorem z_comm_s : cm (cm ga gs) gs * gs = gs * cm (cm ga gs) gs := by decide +kernel

set_option maxRecDepth 100000 in
theorem z_ne_one : cm (cm ga gs) gs ≠ 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem u_ne : cm ga gs ≠ 1 ∧ cm ga gs ≠ cm (cm ga gs) gs ∧
    cm ga gs ≠ cm (cm ga gs) gs * cm (cm ga gs) gs := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem uz_cube : cm ga gs ^ 3 = 1 ∧ cm (cm ga gs) gs ^ 3 = 1 := by decide +kernel

end Model

end CFSG.Quasithin.SzN32
