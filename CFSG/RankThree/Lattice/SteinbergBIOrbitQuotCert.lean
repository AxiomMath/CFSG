module

public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotient
public import CFSG.RankThree.Lattice.SteinbergBIPrimeKernel

public section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley Polynomial Matrix Module

variable {n : ℕ}

structure QCert where
  rep : List ℤ
  k : ℕ
  d : ℕ
  P : List (List ℤ)
  P' : List (List ℤ)
deriving Inhabited

namespace QCert

@[expose] def cols (n : ℕ) (W : List (List ℤ)) (c : QCert) : List (List ℤ) :=
  (lorbit n W c.rep c.k).map (lmulVec n c.P')

@[expose] def mat (n : ℕ) (W : List (List ℤ)) (c : QCert) : Matrix (Fin c.k) (Fin c.k) ℤ :=
  Matrix.of fun a j => vget ((c.cols n W).getD j []) a

@[expose] def check (n : ℕ) (W : List (List ℤ)) (rel : List ℤ) (c : QCert) : Bool :=
  decide (c.k ≤ n) && (lpolyVec n W rel c.rep == vofFn n fun _ => 0) &&
    (lmul n c.P c.P' == lid n) &&
    ((c.cols n W).all fun col => (List.range n).all fun i => decide (i < c.k) || vget col i == 0) &&
    decide ((CFSG.LieType.Chevalley.laplaceDet c.k (c.mat n W)).natAbs = c.d) && decide (c.d ≠ 0)

theorem cols_getD (W : List (List ℤ)) (c : QCert) {j : ℕ} (hj : j < c.k) :
    (c.cols n W).getD j [] = lmulVec n c.P' (lmulVec n (lpow n W j) c.rep) := by
  have hlen : j < (c.cols n W).length := by simpa [cols, lorbit] using hj
  rw [List.getD_eq_getElem _ _ hlen]
  simp [cols, lorbit]

theorem toVec_cols_getD (W : List (List ℤ)) (c : QCert) {j : ℕ} (hj : j < c.k) :
    toVec n ((c.cols n W).getD j []) = toMat n c.P' *ᵥ ((toMat n W ^ j) *ᵥ toVec n c.rep) := by
  rw [cols_getD W c hj, toVec_lmulVec, toVec_lmulVec, toMat_lpow]

theorem cols_getD_mem (W : List (List ℤ)) (c : QCert) {j : ℕ} (hj : j < c.k) :
    (c.cols n W).getD j [] ∈ c.cols n W := by
  rw [List.getD_eq_getElem _ _ (by simpa [cols, lorbit] using hj)]
  exact List.getElem_mem _

theorem spec {W : List (List ℤ)} {rel : List ℤ} {c : QCert} (hc : c.check n W rel = true)
    {p g : ℤ[X]} (hp : p.Monic) (hpk : p.natDegree = c.k) (hrel : polyOfList rel = p)
    (hchar : (toMat n W).charpoly = p * g) :
    finrank ℤ (orbitLattice (toMat n W) (toVec n c.rep)) = c.k ∧
      LinearIndependent ℤ (fun j : Fin c.k => (toMat n W ^ (j : ℕ)) *ᵥ toVec n c.rep) ∧
      Submodule.span ℤ (Set.range fun j : Fin c.k => (toMat n W ^ (j : ℕ)) *ᵥ toVec n c.rep) =
        orbitLattice (toMat n W) (toVec n c.rep) ∧
      satIndex (orbitLattice (toMat n W) (toVec n c.rep)) = c.d ∧
      ∃ h : ratSpan (orbitLattice (toMat n W) (toVec n c.rep)) ≤
          (ratSpan (orbitLattice (toMat n W) (toVec n c.rep))).comap (ratEnd (toMat n W)),
        ((ratEnd (toMat n W)).restrict h).charpoly = p.map (Int.castRingHom ℚ) ∧
        ((ratSpan (orbitLattice (toMat n W) (toVec n c.rep))).mapQ _ (ratEnd (toMat n W))
          h).charpoly = g.map (Int.castRingHom ℚ) := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hk, hpol⟩, hPP⟩, hcols⟩, hdetd⟩, hd0⟩ := hc
  have hrel' : (aeval (toMat n W) p) *ᵥ toVec n c.rep = 0 := by
    rw [← hrel, ← toVec_lpolyVec, hpol, toVec_vofFn]
    rfl
  have hPP' : toMat n c.P * toMat n c.P' = 1 := by rw [← toMat_lmul, hPP, toMat_lid]
  have hzero : ∀ i : Fin n, c.k ≤ (i : ℕ) → ∀ j : Fin c.k,
      (toMat n c.P' *ᵥ ((toMat n W ^ (j : ℕ)) *ᵥ toVec n c.rep)) i = 0 := by
    intro i hi j
    rw [← toVec_cols_getD W c j.isLt]
    rcases hcols _ (cols_getD_mem W c j.isLt) i i.isLt with h | h
    · exact absurd h (by omega)
    · exact h
  have hmat : certMat hk (fun j : Fin c.k => (toMat n W ^ (j : ℕ)) *ᵥ toVec n c.rep)
      (toMat n c.P') = c.mat n W := by
    ext a j
    simp only [certMat, mat, Matrix.of_apply]
    rw [← toVec_cols_getD W c j.isLt]
    rfl
  have hdet : (certMat hk (fun j : Fin c.k => (toMat n W ^ (j : ℕ)) *ᵥ toVec n c.rep)
      (toMat n c.P')).det.natAbs = c.d := by
    rw [hmat, ← CFSG.LieType.Chevalley.laplaceDet_eq_det, hdetd]
  have hdet0 : (certMat hk (fun j : Fin c.k => (toMat n W ^ (j : ℕ)) *ᵥ toVec n c.rep)
      (toMat n c.P')).det ≠ 0 := by
    intro h0
    rw [h0] at hdet
    exact hd0 hdet.symm
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    orbitQuot_of_cert (toMat n W) (toVec n c.rep) hk hp hpk hrel' hchar hPP' hzero hdet0
  exact ⟨h1, h2, h3, h4.trans hdet, h5⟩

@[expose] def find (n : ℕ) (W : List (List ℤ)) (m : ℕ) (certs : List QCert) (l : List ℤ) :
    QCert :=
  (certs.find? fun c => decide (l ∈ lorbit n W c.rep m)).getD default

variable {τ : Tag} {W : List (List ℤ)} {m : ℕ}

theorem forall_root (hm : 0 < m) (hW : lpow τ.rank W m = lid τ.rank) (rel : ℕ → List ℤ)
    (certs : List QCert) (hcheck : certs.all (fun c => c.check τ.rank W (rel c.k)) = true)
    (hcover : τ.artifactRoots.all (fun l =>
      (certs.find? fun c => decide (l ∈ lorbit τ.rank W c.rep m)).isSome) = true)
    (ks : List ℕ) (hks : certs.all (fun c => decide (c.k ∈ ks)) = true) (polyOf quotOf : ℕ → ℤ[X])
    (hpoly : ∀ k ∈ ks, (polyOf k).Monic ∧ (polyOf k).natDegree = k ∧
      polyOfList (rel k) = polyOf k ∧ (toMat τ.rank W).charpoly = polyOf k * quotOf k)
    {l : List ℤ} (hl : l ∈ τ.artifactRoots) :
    find τ.rank W m certs l ∈ certs ∧
      finrank ℤ (orbitLattice (toMat τ.rank W) (toVec τ.rank l)) = (find τ.rank W m certs l).k ∧
      satIndex (orbitLattice (toMat τ.rank W) (toVec τ.rank l)) = (find τ.rank W m certs l).d ∧
      LinearIndependent ℤ (fun j : Fin (find τ.rank W m certs l).k =>
        (toMat τ.rank W ^ (j : ℕ)) *ᵥ toVec τ.rank l) ∧
      Submodule.span ℤ (Set.range fun j : Fin (find τ.rank W m certs l).k =>
        (toMat τ.rank W ^ (j : ℕ)) *ᵥ toVec τ.rank l) =
        orbitLattice (toMat τ.rank W) (toVec τ.rank l) ∧
      ∃ h : ratSpan (orbitLattice (toMat τ.rank W) (toVec τ.rank l)) ≤
          (ratSpan (orbitLattice (toMat τ.rank W) (toVec τ.rank l))).comap
            (ratEnd (toMat τ.rank W)),
        ((ratEnd (toMat τ.rank W)).restrict h).charpoly =
          (polyOf (find τ.rank W m certs l).k).map (Int.castRingHom ℚ) ∧
        ((ratSpan (orbitLattice (toMat τ.rank W) (toVec τ.rank l))).mapQ _
          (ratEnd (toMat τ.rank W)) h).charpoly =
          (quotOf (find τ.rank W m certs l).k).map (Int.castRingHom ℚ) := by
  have hc := List.all_eq_true.1 hcover l hl
  obtain ⟨c, hfind⟩ := Option.isSome_iff_exists.1 hc
  have hfc : find τ.rank W m certs l = c := by rw [find, hfind, Option.getD_some]
  rw [hfc]
  have hcmem : c ∈ certs := List.mem_of_find?_eq_some hfind
  have hlc : l ∈ lorbit τ.rank W c.rep m := by simpa using List.find?_some hfind
  have hck : c.check τ.rank W (rel c.k) = true := List.all_eq_true.1 hcheck c hcmem
  have hkk : c.k ∈ ks := by simpa using List.all_eq_true.1 hks c hcmem
  obtain ⟨hp, hpk, hrel, hchar⟩ := hpoly c.k hkk
  obtain ⟨h1, h2, -, h4, h5⟩ := spec hck hp hpk hrel hchar
  have hw : toMat τ.rank W ^ m = 1 := by rw [← toMat_lpow, hW, toMat_lid]
  simp only [lorbit, List.mem_map, List.mem_range] at hlc
  obtain ⟨j, -, rfl⟩ := hlc
  rw [toVec_lmulVec, toMat_lpow]
  have hΛ := orbitLattice_pow_mulVec hm hw (toVec τ.rank c.rep) j
  rw [hΛ]
  refine ⟨hcmem, h1, h4, linearIndependent_pow_mulVec hm hw h2 j, ?_, h5⟩
  rw [← hΛ]
  refine (orbitLattice_eq_span_of_monic _ _ hp hpk ?_).symm
  have hpol : lpolyVec τ.rank W (rel c.k) c.rep = vofFn τ.rank fun _ => 0 := by
    simp only [check, Bool.and_eq_true, beq_iff_eq] at hck
    exact hck.1.1.1.1.2
  rw [aeval_mulVec_pow_mulVec, ← hrel, ← toVec_lpolyVec, hpol, toVec_vofFn]
  exact Matrix.mulVec_zero _

theorem ncard_root (hm : 0 < m) (hW : lpow τ.rank W m = lid τ.rank) (rel : ℕ → List ℤ)
    (certs : List QCert) (hcheck : certs.all (fun c => c.check τ.rank W (rel c.k)) = true)
    (hcover : τ.artifactRoots.all (fun l =>
      (certs.find? fun c => decide (l ∈ lorbit τ.rank W c.rep m)).isSome) = true)
    (ks : List ℕ) (hks : certs.all (fun c => decide (c.k ∈ ks)) = true) (polyOf quotOf : ℕ → ℤ[X])
    (hpoly : ∀ k ∈ ks, (polyOf k).Monic ∧ (polyOf k).natDegree = k ∧
      polyOfList (rel k) = polyOf k ∧ (toMat τ.rank W).charpoly = polyOf k * quotOf k)
    (Q : ℕ → ℕ → Prop) [∀ a b, Decidable (Q a b)] :
    {α | IsRoot τ α ∧ Q (finrank ℤ (orbitLattice (toMat τ.rank W) α))
      (satIndex (orbitLattice (toMat τ.rank W) α))}.ncard =
      (τ.artifactRoots.filter fun l =>
        decide (Q (find τ.rank W m certs l).k (find τ.rank W m certs l).d)).length := by
  classical
  rw [ncard_isRoot_and]
  congr 1
  refine List.filter_congr fun l hl => ?_
  obtain ⟨-, h1, h2, -⟩ := forall_root hm hW rel certs hcheck hcover ks hks polyOf quotOf hpoly hl
  rw [h1, h2]

end QCert

end CFSG.RankThree.Lattice
