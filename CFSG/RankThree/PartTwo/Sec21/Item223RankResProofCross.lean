module

public import CFSG.RankThree.PartOne.SEITZ11.G2SevenAPI
public import CFSG.Assembly.Subnormal
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item223RankResProof

open CFSG.RankThree.PartOne.SEITZ11 CFSG.RankThree.PartOne.SEITZ11.G2Seven Matrix

section Cross

variable {R : Type*} [CommRing R]

@[expose] def cross7 (u v : Fin 7 → R) : Fin 7 → R :=
  ![u 1 * v 3 - u 3 * v 1 - u 2 * v 5 + u 5 * v 2 - u 4 * v 6 + u 6 * v 4,
    -2 * (u 0 * v 1 - u 1 * v 0) - 2 * (u 4 * v 5 - u 5 * v 4),
    -2 * (u 0 * v 2 - u 2 * v 0) + 2 * (u 3 * v 4 - u 4 * v 3),
    2 * (u 0 * v 3 - u 3 * v 0) - 2 * (u 2 * v 6 - u 6 * v 2),
    2 * (u 0 * v 4 - u 4 * v 0) - 2 * (u 1 * v 2 - u 2 * v 1),
    2 * (u 0 * v 5 - u 5 * v 0) - 2 * (u 1 * v 6 - u 6 * v 1),
    -2 * (u 0 * v 6 - u 6 * v 0) + 2 * (u 3 * v 5 - u 5 * v 3)]

@[expose] def bil7 (u v : Fin 7 → R) : R := u ⬝ᵥ (G2Seven.gram R *ᵥ v)

theorem bil7_eq (u v : Fin 7 → R) :
    bil7 u v = 2 * u 0 * v 0 - u 1 * v 3 + u 2 * v 5 - u 3 * v 1 - u 4 * v 6 + u 5 * v 2 -
      u 6 * v 4 := by
  simp [bil7, G2Seven.gram, gramZ, dotProduct, Matrix.mulVec, Fin.sum_univ_seven]
  ring

theorem cross7_smul_left (c : R) (u v : Fin 7 → R) : cross7 (c • u) v = c • cross7 u v := by
  funext k
  fin_cases k <;> simp [cross7] <;> ring

theorem cross7_smul_right (c : R) (u v : Fin 7 → R) : cross7 u (c • v) = c • cross7 u v := by
  funext k
  fin_cases k <;> simp [cross7] <;> ring

theorem cross7_cross7 (x y z : Fin 7 → R) :
    cross7 x (cross7 z y) + cross7 z (cross7 x y) =
      (4 * bil7 x z) • y - (2 * bil7 x y) • z - (2 * bil7 z y) • x := by
  rw [bil7_eq, bil7_eq, bil7_eq]
  funext k
  fin_cases k <;> simp [cross7] <;> ring

theorem rootMat_mulVec_apply (g : ℕ) (t : R) (w : Fin 7 → R) (i : Fin 7) :
    (rootMat g t *ᵥ w) i = w i +
      t * ((ent7 g).map fun e => if e.1 = i then (e.2.2 : R) * w e.2.1 else 0).sum +
      t * t * ((ent7sq g).map fun e => if e.1 = i then (e.2.2 : R) * w e.2.1 else 0).sum := by
  simp only [rootMat, opMat, opMatSq, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, entMat_mulVec]

local macro "cross_root_tac" : tactic =>
  `(tactic| (funext k; fin_cases k <;>
    simp only [rootMat_mulVec_apply, cross7, ent7, ent7sq, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil] <;> simp <;> ring))

theorem rootMat_cross7_0 (t : R) (u v : Fin 7 → R) :
    rootMat 0 t *ᵥ cross7 u v = cross7 (rootMat 0 t *ᵥ u) (rootMat 0 t *ᵥ v) := by
  cross_root_tac

theorem rootMat_cross7_1 (t : R) (u v : Fin 7 → R) :
    rootMat 1 t *ᵥ cross7 u v = cross7 (rootMat 1 t *ᵥ u) (rootMat 1 t *ᵥ v) := by
  cross_root_tac

theorem rootMat_cross7_2 (t : R) (u v : Fin 7 → R) :
    rootMat 2 t *ᵥ cross7 u v = cross7 (rootMat 2 t *ᵥ u) (rootMat 2 t *ᵥ v) := by
  cross_root_tac

theorem rootMat_cross7_3 (t : R) (u v : Fin 7 → R) :
    rootMat 3 t *ᵥ cross7 u v = cross7 (rootMat 3 t *ᵥ u) (rootMat 3 t *ᵥ v) := by
  cross_root_tac

theorem rootMat_cross7_4 (t : R) (u v : Fin 7 → R) :
    rootMat 4 t *ᵥ cross7 u v = cross7 (rootMat 4 t *ᵥ u) (rootMat 4 t *ᵥ v) := by
  cross_root_tac

theorem rootMat_cross7_5 (t : R) (u v : Fin 7 → R) :
    rootMat 5 t *ᵥ cross7 u v = cross7 (rootMat 5 t *ᵥ u) (rootMat 5 t *ᵥ v) := by
  cross_root_tac

theorem rootMat_cross7_6 (t : R) (u v : Fin 7 → R) :
    rootMat 6 t *ᵥ cross7 u v = cross7 (rootMat 6 t *ᵥ u) (rootMat 6 t *ᵥ v) := by
  cross_root_tac

theorem rootMat_cross7_7 (t : R) (u v : Fin 7 → R) :
    rootMat 7 t *ᵥ cross7 u v = cross7 (rootMat 7 t *ᵥ u) (rootMat 7 t *ᵥ v) := by
  cross_root_tac

theorem rootMat_cross7_8 (t : R) (u v : Fin 7 → R) :
    rootMat 8 t *ᵥ cross7 u v = cross7 (rootMat 8 t *ᵥ u) (rootMat 8 t *ᵥ v) := by
  cross_root_tac

theorem rootMat_cross7_9 (t : R) (u v : Fin 7 → R) :
    rootMat 9 t *ᵥ cross7 u v = cross7 (rootMat 9 t *ᵥ u) (rootMat 9 t *ᵥ v) := by
  cross_root_tac

theorem rootMat_cross7_10 (t : R) (u v : Fin 7 → R) :
    rootMat 10 t *ᵥ cross7 u v = cross7 (rootMat 10 t *ᵥ u) (rootMat 10 t *ᵥ v) := by
  cross_root_tac

theorem rootMat_cross7_11 (t : R) (u v : Fin 7 → R) :
    rootMat 11 t *ᵥ cross7 u v = cross7 (rootMat 11 t *ᵥ u) (rootMat 11 t *ᵥ v) := by
  cross_root_tac

theorem rootMat_cross7 (g : ℕ) (hg : g < 12) (t : R) (u v : Fin 7 → R) :
    rootMat g t *ᵥ cross7 u v = cross7 (rootMat g t *ᵥ u) (rootMat g t *ᵥ v) := by
  interval_cases g
  · exact rootMat_cross7_0 t u v
  · exact rootMat_cross7_1 t u v
  · exact rootMat_cross7_2 t u v
  · exact rootMat_cross7_3 t u v
  · exact rootMat_cross7_4 t u v
  · exact rootMat_cross7_5 t u v
  · exact rootMat_cross7_6 t u v
  · exact rootMat_cross7_7 t u v
  · exact rootMat_cross7_8 t u v
  · exact rootMat_cross7_9 t u v
  · exact rootMat_cross7_10 t u v
  · exact rootMat_cross7_11 t u v

@[expose] def crossSubgroup (R : Type*) [CommRing R] : Subgroup (GL (Fin 7) R) where
  carrier := {A | ∀ u v, (A : Matrix (Fin 7) (Fin 7) R) *ᵥ cross7 u v =
    cross7 ((A : Matrix (Fin 7) (Fin 7) R) *ᵥ u) ((A : Matrix (Fin 7) (Fin 7) R) *ᵥ v)}
  one_mem' := by simp
  mul_mem' := fun {A B} hA hB u v => by
    simp only [Set.mem_ofPred_eq, Units.val_mul] at hA hB ⊢
    rw [← Matrix.mulVec_mulVec, hB, hA, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  inv_mem' := fun {A} hA u v => by
    simp only [Set.mem_ofPred_eq] at hA ⊢
    set M : Matrix (Fin 7) (Fin 7) R := (A : Matrix (Fin 7) (Fin 7) R) with hM
    set N : Matrix (Fin 7) (Fin 7) R := ((A⁻¹ : GL (Fin 7) R) : Matrix (Fin 7) (Fin 7) R)
      with hN
    have hMN : M * N = 1 := by rw [hM, hN, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hNM : N * M = 1 := by rw [hM, hN, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc N *ᵥ cross7 u v = N *ᵥ cross7 (M *ᵥ (N *ᵥ u)) (M *ᵥ (N *ᵥ v)) := by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hMN, Matrix.one_mulVec,
            Matrix.one_mulVec]
      _ = N *ᵥ (M *ᵥ cross7 (N *ᵥ u) (N *ᵥ v)) := by rw [hA]
      _ = cross7 (N *ᵥ u) (N *ᵥ v) := by rw [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]

theorem posU_mem_crossSubgroup (g : ℕ) (hg : g < 12) (t : R) : posU R g t ∈ crossSubgroup R := by
  intro u v
  rw [val_posU R g hg]
  exact rootMat_cross7 g hg t u v

theorem rootMat_map {S : Type*} [CommRing S] (f : R →+* S) (g : ℕ) (t : R) :
    (rootMat g t).map f = rootMat g (f t) := by
  have h1 : ∀ i j, f (opMat R g i j) = opMat S g i j := fun i j => by
    rw [← opMat_map R, ← opMat_map S]
    simp
  have h2 : ∀ i j, f (opMatSq R g i j) = opMatSq S g i j := fun i j => by
    rw [← opMatSq_map R, ← opMatSq_map S]
    simp
  ext i j
  simp only [rootMat, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    map_add, map_mul, h1, h2, Matrix.one_apply]
  split_ifs <;> simp

theorem map_posU {S : Type*} [CommRing S] (f : R →+* S) (g : ℕ) (hg : g < 12) (t : R) :
    Matrix.GeneralLinearGroup.map f (posU R g t) = posU S g (f t) := by
  apply Units.ext
  change (((posU R g t : GL (Fin 7) R) : Matrix (Fin 7) (Fin 7) R)).map f = _
  rw [val_posU R g hg, val_posU S g hg, rootMat_map]

end Cross

section Image

variable
    (k : Type) [Field k] [Finite k] {S : Type*} [CommRing S] (f : k →+* S)

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

omit [Finite k] in
theorem yfam_map_mem {T : Subgroup (GL (Fin 7) S)} (hT : ∀ g < 12, ∀ t : S, posU S g t ∈ T)
    (γ : Fin (Tag.rank .G2) → ℤ) (hγ : IsRoot .G2 γ) (c : k) :
    Matrix.GeneralLinearGroup.map f (yfam k γ c) ∈ T := by
  classical
  unfold yfam
  split_ifs
  rw [map_posU f _ (pos_lt_twelve _)]
  exact hT _ (pos_lt_twelve _) (f c)

theorem rep7_map_mem_crossSubgroup (g : adjointGroup .G2 k) :
    Matrix.GeneralLinearGroup.map f (rep7 k g) ∈ crossSubgroup S :=
  rep7_mem_of_roots k ((crossSubgroup S).comap (Matrix.GeneralLinearGroup.map f))
    (fun γ hγ c => yfam_map_mem k f (fun g hg t => posU_mem_crossSubgroup g hg t) γ hγ c) g

theorem rep7_map_mem_formSubgroup (g : adjointGroup .G2 k) :
    Matrix.GeneralLinearGroup.map f (rep7 k g) ∈ formSubgroup S :=
  rep7_mem_of_roots k ((formSubgroup S).comap (Matrix.GeneralLinearGroup.map f))
    (fun γ hγ c => yfam_map_mem k f (fun g hg t => posU_mem_formSubgroup S g hg t) γ hγ c) g

end Image

theorem gram_det_ne_zero {L : Type*} [Field L] (h2 : (2 : L) ≠ 0) :
    (G2Seven.gram L).det ≠ 0 := by
  refine Matrix.det_ne_zero_of_left_inverse (B := Matrix.of fun i j =>
    if i = 0 ∧ j = 0 then (2 : L)⁻¹ else G2Seven.gram L i j) ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [G2Seven.gram, gramZ, Matrix.mul_apply, Fin.sum_univ_seven, h2]

end CFSG.RankThree.PartTwo.Sec21.Item223RankResProof
