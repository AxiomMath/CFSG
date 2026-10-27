module

public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotCert

public section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley Matrix Polynomial Module

@[expose] def e6Q8W : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ := wordMat .E6 [0, 1, 2, 3, 4]

@[expose] def e6Q8Rel : ℕ → List ℤ
  | 4 => [1, 0, 0, 0, 1]
  | 5 => [1, 1, 0, 0, 1, 1]
  | _ => [-1, 0, 1, 0, -1, 0, 1]

@[expose] noncomputable def e6Q8Poly : ℕ → ℤ[X]
  | 4 => X ^ 4 + 1
  | 5 => (X ^ 4 + 1) * (X + 1)
  | _ => (X ^ 4 + 1) * (X ^ 2 - 1)

@[expose] noncomputable def e6Q8Quot : ℕ → ℤ[X]
  | 4 => X ^ 2 - 1
  | 5 => X - 1
  | _ => 1

@[expose] def e6Q8WList : List (List ℤ) :=
  [[0, 1, 0, 0, -1, 1], [0, 0, 1, 0, -1, 1], [1, 1, 0, 0, -1, 1], [0, 1, 1, 0, -1, 1],
   [0, 0, 0, 1, -1, 1], [0, 0, 0, 0, 0, 1]]

@[expose] def e6Q8Certs : List QCert := [
  ⟨[-1, -2, -2, -3, -2, -1], 6, 1,
    [[1, 0, 0, 0, 0, 0], [2, 1, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0], [3, 0, 2, 1, 0, 0],
     [2, 0, 2, 1, 1, 0], [1, 0, 1, 1, 1, 1]],
    [[1, 0, 0, 0, 0, 0], [-2, 1, 0, 0, 0, 0], [-2, 0, 1, 0, 0, 0], [1, 0, -2, 1, 0, 0],
     [1, 0, 0, -1, 1, 0], [-1, 0, 1, 0, -1, 1]]⟩,
  ⟨[-1, -1, -2, -2, -2, -1], 6, 1,
    [[1, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0], [2, 1, 1, 0, 0, 0], [2, 2, 0, 1, 0, 0],
     [2, 1, 0, 1, 1, 0], [1, 1, 0, 1, 1, 1]],
    [[1, 0, 0, 0, 0, 0], [-1, 1, 0, 0, 0, 0], [-1, -1, 1, 0, 0, 0], [0, -2, 0, 1, 0, 0],
     [-1, 1, 0, -1, 1, 0], [1, 0, 0, 0, -1, 1]]⟩,
  ⟨[-1, -1, -2, -2, -1, 0], 4, 1,
    [[1, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0], [2, 1, 0, 1, 0, 0], [2, 2, 1, 0, 0, 0],
     [1, 1, 1, 0, 1, 0], [0, 0, 0, 0, 0, 1]],
    [[1, 0, 0, 0, 0, 0], [-1, 1, 0, 0, 0, 0], [0, -2, 0, 1, 0, 0], [-1, -1, 1, 0, 0, 0],
     [0, 1, 0, -1, 1, 0], [0, 0, 0, 0, 0, 1]]⟩,
  ⟨[-1, -1, -1, -2, -1, 0], 4, 2,
    [[1, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0], [1, 1, 0, 0, 0, 0], [2, 1, 2, 1, 0, 0],
     [1, 1, 1, 1, 1, 0], [0, 0, 0, 0, 0, 1]],
    [[1, 0, 0, 0, 0, 0], [-1, 0, 1, 0, 0, 0], [-1, 1, 0, 0, 0, 0], [1, -2, -1, 1, 0, 0],
     [0, 1, 0, -1, 1, 0], [0, 0, 0, 0, 0, 1]]⟩,
  ⟨[-1, -1, -1, -1, -1, 0], 5, 1,
    [[1, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0], [1, 1, 0, 0, 0, 0], [1, 1, 1, 1, 0, 0],
     [1, 0, 1, 1, 1, 0], [0, 0, 0, 0, 0, 1]],
    [[1, 0, 0, 0, 0, 0], [-1, 0, 1, 0, 0, 0], [-1, 1, 0, 0, 0, 0], [1, -1, -1, 1, 0, 0],
     [-1, 0, 1, -1, 1, 0], [0, 0, 0, 0, 0, 1]]⟩,
  ⟨[-1, 0, -1, -1, -1, 0], 4, 1,
    [[1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0], [1, 1, 0, 0, 0, 0], [1, 1, 1, 0, 0, 0],
     [1, 1, 1, -1, 1, 0], [0, 0, 0, 0, 0, 1]],
    [[1, 0, 0, 0, 0, 0], [-1, 0, 1, 0, 0, 0], [0, 0, -1, 1, 0, 0], [0, 1, 0, 0, 0, 0],
     [0, 1, 0, -1, 1, 0], [0, 0, 0, 0, 0, 1]]⟩,
  ⟨[-1, 0, -1, -1, 0, 0], 5, 1,
    [[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [1, 1, 0, 0, 1, 0], [1, 1, 1, 0, 0, 0],
     [0, 1, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1]],
    [[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [-1, -1, 0, 1, 0, 0], [0, -1, 0, 0, 1, 0],
     [-1, -1, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1]]⟩,
  ⟨[0, 0, 0, 0, 0, 1], 6, 1,
    [[0, 1, 0, -1, 1, 1], [0, 1, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0], [0, 1, 1, 1, 0, 0],
     [0, 1, 0, 0, 1, 0], [1, 0, 0, 0, 0, 0]],
    [[0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0], [0, -1, 1, 0, 0, 0], [0, 0, -1, 1, 0, 0],
     [0, -1, 0, 0, 1, 0], [1, 0, -1, 1, -1, 0]]⟩,
  ⟨[0, 0, 1, 1, 1, 1], 6, 1,
    [[0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0], [1, 1, 0, 1, 0, 0],
     [1, 1, 0, 1, 1, 0], [1, 1, 0, 1, 1, 1]],
    [[0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0], [0, -1, -1, 1, 0, 0],
     [0, 0, 0, -1, 1, 0], [0, 0, 0, 0, -1, 1]]⟩]

theorem e6Q8W_eq : e6Q8W = toMat Tag.E6.rank e6Q8WList :=
  wordMat_eq_toMat .E6 _ (by decide +kernel)

theorem e6Q8_pow : lpow Tag.E6.rank e6Q8WList 8 = lid Tag.E6.rank := by
  decide +kernel

theorem e6Q8_cyclic : lorbitDet Tag.E6.rank e6Q8WList [0, 0, 0, 0, 0, 1] = 1 := by
  decide +kernel

theorem e6Q8_charpoly :
    (toMat Tag.E6.rank e6Q8WList).charpoly = (X ^ 4 + 1) * (X ^ 2 - 1) :=
  charpoly_eq_of_lists (cs := [-1, 0, 1, 0, -1, 0, 1]) (by monicity!) (by compute_degree!)
    (by simp [polyOfList]; ring) (by decide +kernel) [0, 0, 0, 0, 0, 1]
    (by rw [det_orbitMat_toVec, e6Q8_cyclic]; exact isUnit_one)

theorem e6Q8_check :
    e6Q8Certs.all (fun c => c.check Tag.E6.rank e6Q8WList (e6Q8Rel c.k)) = true := by
  decide +kernel

theorem e6Q8_cover : Tag.E6.artifactRoots.all (fun l =>
    (e6Q8Certs.find? fun c => decide (l ∈ lorbit Tag.E6.rank e6Q8WList c.rep 8)).isSome) =
      true := by
  decide +kernel

theorem e6Q8_ks : e6Q8Certs.all (fun c => decide (c.k ∈ [4, 5, 6])) = true := by
  decide +kernel

theorem e6Q8_kd :
    e6Q8Certs.all (fun c => decide ((c.k, c.d) ∈ [(6, 1), (4, 1), (4, 2), (5, 1)])) = true := by
  decide +kernel

theorem e6Q8_poly : ∀ k ∈ [4, 5, 6], (e6Q8Poly k).Monic ∧ (e6Q8Poly k).natDegree = k ∧
    polyOfList (e6Q8Rel k) = e6Q8Poly k ∧
    (toMat Tag.E6.rank e6Q8WList).charpoly = e6Q8Poly k * e6Q8Quot k := by
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rw [e6Q8_charpoly]
  rcases hk with rfl | rfl | rfl
  · refine ⟨by simp only [e6Q8Poly]; monicity!, by simp only [e6Q8Poly]; compute_degree!,
      by simp [e6Q8Rel, e6Q8Poly, polyOfList]; ring, by simp only [e6Q8Poly, e6Q8Quot]⟩
  · refine ⟨by simp only [e6Q8Poly]; monicity!, by simp only [e6Q8Poly]; compute_degree!,
      by simp [e6Q8Rel, e6Q8Poly, polyOfList]; ring, by simp only [e6Q8Poly, e6Q8Quot]; ring⟩
  · refine ⟨by simp only [e6Q8Poly]; monicity!, by simp only [e6Q8Poly]; compute_degree!,
      by simp [e6Q8Rel, e6Q8Poly, polyOfList]; ring, by simp only [e6Q8Poly, e6Q8Quot, mul_one]⟩

theorem E6_order_eight_cyclic_lattice_and_root_orbit_quotients :
    orderOf e6Q8W = 8 ∧ e6Q8W.charpoly = (X ^ 4 + 1) * (X ^ 2 - 1) ∧
    (∃ v, IsRoot .E6 v ∧
      LinearIndependent ℤ (fun j : Fin Tag.E6.rank => (e6Q8W ^ (j : ℕ)) *ᵥ v) ∧
      Submodule.span ℤ (Set.range fun j : Fin Tag.E6.rank => (e6Q8W ^ (j : ℕ)) *ᵥ v) = ⊤) ∧
    (∀ α, IsRoot .E6 α → (finrank ℤ (orbitLattice e6Q8W α), satIndex (orbitLattice e6Q8W α)) ∈
      [(6, 1), (4, 1), (4, 2), (5, 1)]) ∧
    {α | IsRoot .E6 α ∧ finrank ℤ (orbitLattice e6Q8W α) = 6 ∧
      satIndex (orbitLattice e6Q8W α) = 1}.ncard = 32 ∧
    {α | IsRoot .E6 α ∧ finrank ℤ (orbitLattice e6Q8W α) = 4 ∧
      satIndex (orbitLattice e6Q8W α) = 1}.ncard = 16 ∧
    {α | IsRoot .E6 α ∧ finrank ℤ (orbitLattice e6Q8W α) = 4 ∧
      satIndex (orbitLattice e6Q8W α) = 2}.ncard = 8 ∧
    {α | IsRoot .E6 α ∧ finrank ℤ (orbitLattice e6Q8W α) = 5 ∧
      satIndex (orbitLattice e6Q8W α) = 1}.ncard = 16 ∧
    (∀ α, IsRoot .E6 α →
      LinearIndependent ℤ (fun j : Fin (finrank ℤ (orbitLattice e6Q8W α)) =>
        (e6Q8W ^ (j : ℕ)) *ᵥ α) ∧
      Submodule.span ℤ (Set.range fun j : Fin (finrank ℤ (orbitLattice e6Q8W α)) =>
        (e6Q8W ^ (j : ℕ)) *ᵥ α) = orbitLattice e6Q8W α) ∧
    (∀ α, IsRoot .E6 α → finrank ℤ (orbitLattice e6Q8W α) = 4 →
      ∃ h : ratSpan (orbitLattice e6Q8W α) ≤ (ratSpan (orbitLattice e6Q8W α)).comap (ratEnd e6Q8W),
        ((ratEnd e6Q8W).restrict h).charpoly = X ^ 4 + 1 ∧
        ((ratSpan (orbitLattice e6Q8W α)).mapQ _ (ratEnd e6Q8W) h).charpoly = X ^ 2 - 1) ∧
    (∀ α, IsRoot .E6 α → finrank ℤ (orbitLattice e6Q8W α) = 5 →
      ∃ h : ratSpan (orbitLattice e6Q8W α) ≤ (ratSpan (orbitLattice e6Q8W α)).comap (ratEnd e6Q8W),
        ((ratEnd e6Q8W).restrict h).charpoly = (X ^ 4 + 1) * (X + 1) ∧
        ((ratSpan (orbitLattice e6Q8W α)).mapQ _ (ratEnd e6Q8W) h).charpoly = X - 1) := by
  have hroot := fun (l : List ℤ) (hl : l ∈ Tag.E6.artifactRoots) =>
    QCert.forall_root (by norm_num) e6Q8_pow e6Q8Rel e6Q8Certs e6Q8_check e6Q8_cover [4, 5, 6]
      e6Q8_ks e6Q8Poly e6Q8Quot e6Q8_poly hl
  have hcount := QCert.ncard_root (by norm_num) e6Q8_pow e6Q8Rel e6Q8Certs e6Q8_check e6Q8_cover
    [4, 5, 6] e6Q8_ks e6Q8Poly e6Q8Quot e6Q8_poly
  rw [e6Q8W_eq]
  refine ⟨orderOf_toMat_eq (by norm_num) e6Q8_pow (by decide +kernel), e6Q8_charpoly,
    ⟨toVec Tag.E6.rank [0, 0, 0, 0, 0, 1], isRoot_toVec (by decide +kernel),
      (isBasis_iff_isUnit_det _ _).2 (by rw [det_orbitMat_toVec, e6Q8_cyclic]; exact isUnit_one)⟩,
    ?_, (hcount fun k d => k = 6 ∧ d = 1).trans (by decide +kernel),
    (hcount fun k d => k = 4 ∧ d = 1).trans (by decide +kernel),
    (hcount fun k d => k = 4 ∧ d = 2).trans (by decide +kernel),
    (hcount fun k d => k = 5 ∧ d = 1).trans (by decide +kernel), ?_, ?_, ?_⟩
  · rw [forall_isRoot_iff]
    intro l hl
    obtain ⟨hmem, h1, h2, -⟩ := hroot l hl
    rw [h1, h2]
    simpa using List.all_eq_true.1 e6Q8_kd _ hmem
  · rw [forall_isRoot_iff]
    intro l hl
    obtain ⟨-, h1, -, h3, h4, -⟩ := hroot l hl
    rw [h1]
    exact ⟨h3, h4⟩
  · rw [forall_isRoot_iff]
    intro l hl hk
    obtain ⟨-, h1, -, -, -, h5⟩ := hroot l hl
    rw [h1] at hk
    rw [hk] at h5
    simpa [e6Q8Poly, e6Q8Quot] using h5
  · rw [forall_isRoot_iff]
    intro l hl hk
    obtain ⟨-, h1, -, -, -, h5⟩ := hroot l hl
    rw [h1] at hk
    rw [hk] at h5
    simpa [e6Q8Poly, e6Q8Quot] using h5

end CFSG.RankThree.Lattice
