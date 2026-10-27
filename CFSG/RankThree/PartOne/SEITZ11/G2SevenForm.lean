module

public import CFSG.RankThree.PartOne.SEITZ11.G2SevenData

public section

namespace CFSG.RankThree.PartOne.SEITZ11.G2Seven

@[expose] def rootMat' {R : Type*} [CommRing R] (t : R) (E E2 : Matrix (Fin 7) (Fin 7) R) :
    Matrix (Fin 7) (Fin 7) R := 1 + t • E + (t * t) • E2

@[expose] def gramZ : Matrix (Fin 7) (Fin 7) ℤ :=
  !![2, 0, 0, 0, 0, 0, 0;
     0, 0, 0, -1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0;
     0, -1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, -1;
     0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, -1, 0, 0]

@[expose] def gram (R : Type*) [CommRing R] : Matrix (Fin 7) (Fin 7) R :=
  gramZ.map (Int.castRingHom R)

@[expose] def formVal {R : Type*} [CommRing R] (v : Fin 7 → R) : R := v ⬝ᵥ (gram R).mulVec v

theorem int_form_ident : ∀ g : Fin 12,
    (opMat ℤ g.val).transpose * gramZ + gramZ * opMat ℤ g.val = 0 ∧
    (opMatSq ℤ g.val).transpose * gramZ + gramZ * opMatSq ℤ g.val +
      (opMat ℤ g.val).transpose * gramZ * opMat ℤ g.val = 0 ∧
    (opMat ℤ g.val).transpose * gramZ * opMatSq ℤ g.val +
      (opMatSq ℤ g.val).transpose * gramZ * opMat ℤ g.val = 0 ∧
    (opMatSq ℤ g.val).transpose * gramZ * opMatSq ℤ g.val = 0 := by
  decide +kernel

section
variable {R : Type*} [CommRing R]

theorem opMat_transpose_map (g : ℕ) :
    ((opMat ℤ g).transpose).map (Int.castRingHom R) = (opMat R g).transpose := by
  rw [Matrix.transpose_map, opMat_map]

theorem opMatSq_transpose_map (g : ℕ) :
    ((opMatSq ℤ g).transpose).map (Int.castRingHom R) = (opMatSq R g).transpose := by
  rw [Matrix.transpose_map, opMatSq_map]

theorem rootMat_form (g : ℕ) (hg : g < 12) (t : R) :
    (rootMat g t).transpose * gram R * rootMat g t = gram R := by
  obtain ⟨h1, h2, h3, h4⟩ := int_form_ident ⟨g, hg⟩
  have e1 : (opMat R g).transpose * gram R + gram R * opMat R g = 0 := by
    have := congrArg (Int.castRingHom R).mapMatrix h1
    simpa only [gram, map_add, map_mul, map_zero, RingHom.mapMatrix_apply, opMat_map,
      opMat_transpose_map] using this
  have e2 : (opMatSq R g).transpose * gram R + gram R * opMatSq R g +
      (opMat R g).transpose * gram R * opMat R g = 0 := by
    have := congrArg (Int.castRingHom R).mapMatrix h2
    simpa only [gram, map_add, map_mul, map_zero, RingHom.mapMatrix_apply, opMat_map, opMatSq_map,
      opMat_transpose_map, opMatSq_transpose_map] using this
  have e3 : (opMat R g).transpose * gram R * opMatSq R g +
      (opMatSq R g).transpose * gram R * opMat R g = 0 := by
    have := congrArg (Int.castRingHom R).mapMatrix h3
    simpa only [gram, map_add, map_mul, map_zero, RingHom.mapMatrix_apply, opMat_map, opMatSq_map,
      opMat_transpose_map, opMatSq_transpose_map] using this
  have e4 : (opMatSq R g).transpose * gram R * opMatSq R g = 0 := by
    have := congrArg (Int.castRingHom R).mapMatrix h4
    simpa only [gram, map_mul, map_zero, RingHom.mapMatrix_apply, opMatSq_map,
      opMatSq_transpose_map] using this
  have hT : (rootMat g t).transpose = 1 + t • (opMat R g).transpose +
      (t * t) • (opMatSq R g).transpose := by
    simp [rootMat, Matrix.transpose_add, Matrix.transpose_smul]
  rw [hT, show rootMat g t = rootMat' t (opMat R g) (opMatSq R g) from rfl]
  generalize gram R = G at e1 e2 e3 e4 ⊢
  generalize opMat R g = E at e1 e2 e3 e4 ⊢
  generalize opMatSq R g = E2 at e1 e2 e3 e4 ⊢
  rw [← sub_eq_zero]
  have key : (1 + t • E.transpose + (t * t) • E2.transpose) * G * (rootMat' t E E2) - G =
      t • (E.transpose * G + G * E) +
      (t * t) • (E2.transpose * G + G * E2 + E.transpose * G * E) +
      (t * t * t) • (E.transpose * G * E2 + E2.transpose * G * E) +
      (t * t * t * t) • (E2.transpose * G * E2) := by
    simp only [rootMat', add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
      Matrix.mul_assoc]
    module
  rw [key, e1, e2, e3, e4]
  simp

end

end CFSG.RankThree.PartOne.SEITZ11.G2Seven
