module

public import CFSG.RankThree.Lattice.SteinbergBIChecks

public section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley Matrix Polynomial

variable {n : ℕ}

@[expose] noncomputable def polyOfList : List ℤ → ℤ[X]
  | [] => 0
  | c :: cs => C c + X * polyOfList cs

@[expose] def lzero (n : ℕ) : List (List ℤ) := lofFn n fun _ _ => 0

theorem toMat_lzero (n : ℕ) : toMat n (lzero n) = 0 := by
  rw [lzero, toMat_lofFn]
  rfl

@[expose] def lpolyEval (n : ℕ) (A : List (List ℤ)) : List ℤ → List (List ℤ)
  | [] => lzero n
  | c :: cs => ladd n (lsmul n c (lid n)) (lmul n A (lpolyEval n A cs))

theorem toMat_lpolyEval (A : List (List ℤ)) (cs : List ℤ) :
    toMat n (lpolyEval n A cs) = aeval (toMat n A) (polyOfList cs) := by
  induction cs with
  | nil => rw [lpolyEval, toMat_lzero, polyOfList, map_zero]
  | cons c cs ih =>
    rw [lpolyEval, toMat_ladd, toMat_lsmul, toMat_lid, toMat_lmul, ih, polyOfList, map_add,
      map_mul, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one]

theorem charpoly_eq_of_lists {A : List (List ℤ)} {cs : List ℤ} {p : ℤ[X]} (hp : p.Monic)
    (hpn : p.natDegree = n) (hcs : polyOfList cs = p) (heval : lpolyEval n A cs = lzero n)
    (x : List ℤ) (hx : IsUnit (orbitMat (toMat n A) (toVec n x) n).det) :
    (toMat n A).charpoly = p := by
  refine charpoly_eq_of_cyclic (toMat n A) (toVec n x) hp hpn ?_ hx.ne_zero
  rw [← hcs, ← toMat_lpolyEval, heval, toMat_lzero, Matrix.zero_mulVec]

theorem isUnit_det_of_lmul_eq_lid {M N : List (List ℤ)} (h : lmul n M N = lid n) :
    IsUnit (toMat n M).det :=
  Matrix.isUnit_det_of_right_inverse (by rw [← toMat_lmul, h, toMat_lid])

theorem isUnit_det_orbitMat_of_reps {τ : Tag} {W : List (List ℤ)} (reps : List (List ℤ))
    (m : ℕ) (hW : IsUnit (toMat τ.rank W).det)
    (hcover : ∀ l ∈ τ.artifactRoots, ∃ ρ ∈ reps, l ∈ lorbit τ.rank W ρ m)
    (hrep : ∀ ρ ∈ reps, IsUnit (orbitMat (toMat τ.rank W) (toVec τ.rank ρ) τ.rank).det) :
    ∀ α, IsRoot τ α → IsUnit (orbitMat (toMat τ.rank W) α τ.rank).det := by
  rw [forall_isRoot_iff]
  intro l hl
  obtain ⟨ρ, hρ, hlρ⟩ := hcover l hl
  simp only [lorbit, List.mem_map, List.mem_range] at hlρ
  obtain ⟨j, -, rfl⟩ := hlρ
  rw [toVec_lmulVec, toMat_lpow, det_orbitMat_pow_mulVec]
  exact (hW.pow j).mul (hrep ρ hρ)

theorem isUnit_det_orbitMat_of_certs {τ : Tag} {W : List (List ℤ)}
    (certs : List (List ℤ × List (List ℤ))) (m : ℕ) (hW : IsUnit (toMat τ.rank W).det)
    (hcover : ∀ l ∈ τ.artifactRoots, ∃ p ∈ certs, l ∈ lorbit τ.rank W p.1 m)
    (hinv : ∀ p ∈ certs,
      lmul τ.rank (lcols τ.rank (lorbit τ.rank W p.1 τ.rank)) p.2 = lid τ.rank) :
    ∀ α, IsRoot τ α → IsUnit (orbitMat (toMat τ.rank W) α τ.rank).det := by
  refine isUnit_det_orbitMat_of_reps (certs.map Prod.fst) m hW (fun l hl => ?_) ?_
  · obtain ⟨p, hp, hlp⟩ := hcover l hl
    exact ⟨p.1, List.mem_map_of_mem hp, hlp⟩
  · intro ρ hρ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hρ
    rw [orbitMat_eq_toMat]
    exact isUnit_det_of_lmul_eq_lid (hinv p hp)

@[expose] def lowerTri (n : ℕ) (T : List (List ℤ)) : Bool :=
  (List.finRange n).all fun i => (List.finRange n).all fun j => !(decide (i < j)) || lget T i j == 0

@[expose] def ldiagProd (n : ℕ) (T : List (List ℤ)) : ℤ :=
  (List.ofFn fun i : Fin n => lget T i i).prod

theorem det_toMat_of_lowerTri {T : List (List ℤ)} (h : lowerTri n T = true) :
    (toMat n T).det = ldiagProd n T := by
  rw [Matrix.det_of_isLowerTriangular, ldiagProd, List.prod_ofFn]
  · rfl
  · intro i j hij
    simp only [lowerTri, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
      Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq] at h
    rcases h i j with h | h
    · exact absurd hij h
    · exact h

theorem natAbs_det_of_cert {M U U' T : List (List ℤ)} (h₁ : lmul n M U = T)
    (h₂ : lmul n U U' = lid n) (h₃ : lowerTri n T = true) :
    (toMat n M).det.natAbs = (ldiagProd n T).natAbs := by
  have hU : IsUnit (toMat n U).det := isUnit_det_of_lmul_eq_lid h₂
  have hdet : (toMat n M).det * (toMat n U).det = ldiagProd n T := by
    rw [← Matrix.det_mul, ← toMat_lmul, h₁, det_toMat_of_lowerTri h₃]
  rw [← hdet, Int.natAbs_mul, Int.isUnit_iff_natAbs_eq.1 hU, mul_one]

theorem natAbs_det_orbitMat_of_reps {τ : Tag} {W : List (List ℤ)} (reps : List (List ℤ)) (m : ℕ)
    (hW : IsUnit (toMat τ.rank W).det)
    (hcover : ∀ l ∈ τ.artifactRoots, ∃ ρ ∈ reps, l ∈ lorbit τ.rank W ρ m) (P : ℕ → Prop)
    (hrep : ∀ ρ ∈ reps, P (orbitMat (toMat τ.rank W) (toVec τ.rank ρ) τ.rank).det.natAbs) :
    ∀ α, IsRoot τ α → P (orbitMat (toMat τ.rank W) α τ.rank).det.natAbs := by
  rw [forall_isRoot_iff]
  intro l hl
  obtain ⟨ρ, hρ, hlρ⟩ := hcover l hl
  simp only [lorbit, List.mem_map, List.mem_range] at hlρ
  obtain ⟨j, -, rfl⟩ := hlρ
  rw [toVec_lmulVec, toMat_lpow, det_orbitMat_pow_mulVec, Int.natAbs_mul, Int.natAbs_pow,
    Int.isUnit_iff_natAbs_eq.1 hW, one_pow, one_mul]
  exact hrep ρ hρ

theorem natAbs_det_orbitMat_of_certs {W : List (List ℤ)}
    (certs : List (List ℤ × List (List ℤ) × List (List ℤ) × List (List ℤ)))
    (h : ∀ p ∈ certs, lmul n (lcols n (lorbit n W p.1 n)) p.2.1 = p.2.2.2 ∧
      lmul n p.2.1 p.2.2.1 = lid n ∧ lowerTri n p.2.2.2 = true) :
    ∀ p ∈ certs, (orbitMat (toMat n W) (toVec n p.1) n).det.natAbs =
      (ldiagProd n p.2.2.2).natAbs := by
  intro p hp
  obtain ⟨h₁, h₂, h₃⟩ := h p hp
  rw [orbitMat_eq_toMat]
  exact natAbs_det_of_cert h₁ h₂ h₃

theorem natAbs_det_orbitMat_mem_of_certs {τ : Tag} {W : List (List ℤ)}
    (certs : List (List ℤ × List (List ℤ) × List (List ℤ) × List (List ℤ))) (m : ℕ)
    (hW : IsUnit (toMat τ.rank W).det)
    (hcover : ∀ l ∈ τ.artifactRoots, ∃ p ∈ certs, l ∈ lorbit τ.rank W p.1 m) (S : List ℕ)
    (h : ∀ p ∈ certs, lmul τ.rank (lcols τ.rank (lorbit τ.rank W p.1 τ.rank)) p.2.1 = p.2.2.2 ∧
      lmul τ.rank p.2.1 p.2.2.1 = lid τ.rank ∧ lowerTri τ.rank p.2.2.2 = true ∧
        (ldiagProd τ.rank p.2.2.2).natAbs ∈ S) :
    ∀ α, IsRoot τ α → (orbitMat (toMat τ.rank W) α τ.rank).det.natAbs ∈ S := by
  refine natAbs_det_orbitMat_of_reps (certs.map Prod.fst) m hW (fun l hl => ?_) (· ∈ S) ?_
  · obtain ⟨p, hp, hlp⟩ := hcover l hl
    exact ⟨p.1, List.mem_map_of_mem hp, hlp⟩
  · intro ρ hρ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hρ
    obtain ⟨h₁, h₂, h₃, h₄⟩ := h p hp
    rw [natAbs_det_orbitMat_of_certs [p] (fun q hq => by
      rw [List.mem_singleton] at hq
      subst hq
      exact ⟨h₁, h₂, h₃⟩) p (List.mem_singleton_self p)]
    exact h₄

end CFSG.RankThree.Lattice
