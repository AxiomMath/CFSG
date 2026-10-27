module

public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotCert

public section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley Polynomial Matrix Module

variable {n : ℕ}

theorem satIndex_eq_index {Λ : Submodule ℤ (Fin n → ℤ)} (h : saturation Λ = ⊤) :
    satIndex Λ = Λ.toAddSubgroup.index := by
  rw [satIndex, h, Submodule.top_toAddSubgroup, AddSubgroup.relIndex_top_right]

theorem saturation_eq_self_of_satIndex {Λ : Submodule ℤ (Fin n → ℤ)} (h : satIndex Λ = 1) :
    saturation Λ = Λ := by
  refine le_antisymm ?_ (le_saturation Λ)
  have h' := AddSubgroup.relIndex_eq_one.1 h
  exact fun v hv => h' hv

namespace QCert

theorem saturation_eq_top {W : List (List ℤ)} {rel : List ℤ} {c : QCert}
    (hc : c.check n W rel = true) {p : ℤ[X]} (hp : p.Monic) (hpk : p.natDegree = c.k)
    (hrel : polyOfList rel = p) (hkn : c.k = n) :
    saturation (orbitLattice (toMat n W) (toVec n c.rep)) = ⊤ := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hk, hpol⟩, hPP⟩, hcols⟩, hdetd⟩, hd0⟩ := hc
  have hrel' : (aeval (toMat n W) p) *ᵥ toVec n c.rep = 0 := by
    rw [← hrel, ← toVec_lpolyVec, hpol, toVec_vofFn]
    rfl
  have hPP' : toMat n c.P * toMat n c.P' = 1 := by rw [← toMat_lmul, hPP, toMat_lid]
  have hzero : ∀ i : Fin n, c.k ≤ (i : ℕ) → ∀ j : Fin c.k,
      (toMat n c.P' *ᵥ ((toMat n W ^ (j : ℕ)) *ᵥ toVec n c.rep)) i = 0 :=
    fun i hi => absurd i.isLt (by omega)
  have hmat : certMat hk (fun j : Fin c.k => (toMat n W ^ (j : ℕ)) *ᵥ toVec n c.rep)
      (toMat n c.P') = c.mat n W := by
    ext a j
    simp only [certMat, mat, Matrix.of_apply]
    rw [← toVec_cols_getD W c j.isLt]
    rfl
  have hdet0 : (certMat hk (fun j : Fin c.k => (toMat n W ^ (j : ℕ)) *ᵥ toVec n c.rep)
      (toMat n c.P')).det ≠ 0 := by
    intro h0
    rw [hmat, ← CFSG.LieType.Chevalley.laplaceDet_eq_det] at h0
    rw [h0] at hdetd
    exact hd0 hdetd.symm
  rw [orbitLattice_eq_span_of_monic _ _ hp hpk hrel']
  ext v
  simp only [Submodule.mem_top, iff_true]
  exact (mem_saturation_span_iff hPP' hzero hdet0 v).2 fun i hi => absurd i.isLt (by omega)

variable {τ : Tag} {W : List (List ℤ)} {m : ℕ}

theorem root_data (hm : 0 < m) (hW : lpow τ.rank W m = lid τ.rank) (rel : ℕ → List ℤ)
    (certs : List QCert) (hcheck : certs.all (fun c => c.check τ.rank W (rel c.k)) = true)
    (hcover : τ.artifactRoots.all (fun l =>
      (certs.find? fun c => decide (l ∈ lorbit τ.rank W c.rep m)).isSome) = true)
    (ks : List ℕ) (hks : certs.all (fun c => decide (c.k ∈ ks)) = true) (polyOf quotOf : ℕ → ℤ[X])
    (hpoly : ∀ k ∈ ks, (polyOf k).Monic ∧ (polyOf k).natDegree = k ∧
      polyOfList (rel k) = polyOf k ∧ (toMat τ.rank W).charpoly = polyOf k * quotOf k)
    (α : Fin τ.rank → ℤ) (hα : IsRoot τ α) :
    ∃ c ∈ certs, finrank ℤ (orbitLattice (toMat τ.rank W) α) = c.k ∧
      satIndex (orbitLattice (toMat τ.rank W) α) = c.d ∧
      (c.k = τ.rank → (orbitLattice (toMat τ.rank W) α).toAddSubgroup.index = c.d) ∧
      LinearIndependent ℤ (fun j : Fin c.k => (toMat τ.rank W ^ (j : ℕ)) *ᵥ α) ∧
      Submodule.span ℤ (Set.range fun j : Fin c.k => (toMat τ.rank W ^ (j : ℕ)) *ᵥ α) =
        orbitLattice (toMat τ.rank W) α ∧
      ∃ h : ratSpan (orbitLattice (toMat τ.rank W) α) ≤
          (ratSpan (orbitLattice (toMat τ.rank W) α)).comap (ratEnd (toMat τ.rank W)),
        ((ratEnd (toMat τ.rank W)).restrict h).charpoly =
          (polyOf c.k).map (Int.castRingHom ℚ) ∧
        ((ratSpan (orbitLattice (toMat τ.rank W) α)).mapQ _ (ratEnd (toMat τ.rank W)) h).charpoly =
          (quotOf c.k).map (Int.castRingHom ℚ) := by
  revert α
  rw [forall_isRoot_iff]
  intro l hl
  obtain ⟨hmem, h1, h2, h3, h4, h5⟩ :=
    forall_root hm hW rel certs hcheck hcover ks hks polyOf quotOf hpoly hl
  refine ⟨_, hmem, h1, h2, fun hkn => ?_, h3, h4, h5⟩
  rw [← h2, satIndex_eq_index]
  have hc := List.all_eq_true.1 hcover l hl
  obtain ⟨c, hfind⟩ := Option.isSome_iff_exists.1 hc
  have hfc : find τ.rank W m certs l = c := by rw [find, hfind, Option.getD_some]
  rw [hfc] at hkn
  have hcmem : c ∈ certs := List.mem_of_find?_eq_some hfind
  have hlc : l ∈ lorbit τ.rank W c.rep m := by simpa using List.find?_some hfind
  have hck : c.check τ.rank W (rel c.k) = true := List.all_eq_true.1 hcheck c hcmem
  have hkk : c.k ∈ ks := by simpa using List.all_eq_true.1 hks c hcmem
  obtain ⟨hp, hpk, hrel, -⟩ := hpoly c.k hkk
  have hw : toMat τ.rank W ^ m = 1 := by rw [← toMat_lpow, hW, toMat_lid]
  simp only [lorbit, List.mem_map, List.mem_range] at hlc
  obtain ⟨j, -, rfl⟩ := hlc
  rw [toVec_lmulVec, toMat_lpow, orbitLattice_pow_mulVec hm hw]
  exact saturation_eq_top hck hp hpk hrel hkn

end QCert

end CFSG.RankThree.Lattice
