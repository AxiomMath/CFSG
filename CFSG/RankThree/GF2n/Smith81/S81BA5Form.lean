module

public import CFSG.RankThree.GF2n.Smith81.S81BA5Frame
public import CFSG.RankThree.GF2n.Smith81.S81A5Beta

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix exteriorPower CFSG.Open CFSG.RankThree.GF2n.Smith81.EGeom

variable {K : Type} [Field K]

@[expose] def S013 : Set.powersetCard (Fin 6) 3 :=
  tripleSet 0 1 3 (by decide) (by decide) (by decide)

@[expose] def S135 : Set.powersetCard (Fin 6) 3 :=
  tripleSet 1 3 5 (by decide) (by decide) (by decide)

theorem cubeBasis_S013 : cubeBasis K S013 = ιMulti K 3 ![e K 0, e K 1, e K 3] := by
  have hs : ∀ s : Fin 3, enum S013 s = ![(0 : Fin 6), 1, 3] s := fun s =>
    enum_tripleSet (by decide) (by decide) s
  unfold cubeBasis
  rw [exteriorPower.basis_apply]
  unfold ιMulti_family
  congr 1
  funext s
  rw [Function.comp_apply, hs s]
  fin_cases s <;> simp [e]

theorem cubeBasis_S135 : cubeBasis K S135 = ιMulti K 3 ![e K 1, e K 3, e K 5] := by
  have hs : ∀ s : Fin 3, enum S135 s = ![(1 : Fin 6), 3, 5] s := fun s =>
    enum_tripleSet (by decide) (by decide) s
  unfold cubeBasis
  rw [exteriorPower.basis_apply]
  unfold ιMulti_family
  congr 1
  funext s
  rw [Function.comp_apply, hs s]
  fin_cases s <;> simp [e]

theorem det_of_append_swap (v w : Fin 3 → Fin 6 → K) :
    (Matrix.of (Fin.append w v)).det = -(Matrix.of (Fin.append v w)).det := by
  have hsign : Equiv.Perm.sign
      (Equiv.swap (0 : Fin 6) 3 * Equiv.swap (1 : Fin 6) 4 * Equiv.swap (2 : Fin 6) 5) = -1 := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (show (0 : Fin 6) ≠ 3 by decide),
      Equiv.Perm.sign_swap (show (1 : Fin 6) ≠ 4 by decide),
      Equiv.Perm.sign_swap (show (2 : Fin 6) ≠ 5 by decide)]
    decide
  have hmat : (Matrix.of (Fin.append v w)).submatrix
      (Equiv.swap (0 : Fin 6) 3 * Equiv.swap (1 : Fin 6) 4 * Equiv.swap (2 : Fin 6) 5) id =
      Matrix.of (Fin.append w v) := by
    ext i j
    fin_cases i <;> rfl
  rw [← hmat, Matrix.det_permute, hsign]
  simp

theorem beta_skew (v w : Cube K) : beta K v w = - beta K w v := by
  have pure : ∀ v' w' : Fin 3 → Fin 6 → K,
      beta K (ιMulti K 3 v') (ιMulti K 3 w') = -beta K (ιMulti K 3 w') (ιMulti K 3 v') := by
    intro v' w'
    rw [beta_ιMulti, beta_ιMulti, det_of_append_swap v' w', neg_neg]
  have key : beta K = -(LinearMap.flip (beta K)) := by
    refine LinearMap.ext_on_range (exteriorPower.ιMulti_span K 3 (Fin 6 → K)) fun v' => ?_
    refine LinearMap.ext_on_range (exteriorPower.ιMulti_span K 3 (Fin 6 → K)) fun w' => ?_
    simp only [LinearMap.neg_apply, LinearMap.flip_apply]
    exact pure v' w'
  have h := LinearMap.congr_fun (LinearMap.congr_fun key v) w
  simpa only [LinearMap.neg_apply, LinearMap.flip_apply] using h

theorem Gam_beta_inv {g : Cube K ≃ₗ[K] Cube K} (hg : g ∈ Gam K) (v w : Cube K) :
    beta K (g v) (g w) = beta K v w := by
  obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hg
  have hdet : (A : Matrix (Fin 6) (Fin 6) K).det = 1 :=
    CFSG.Open.StatedAPI.mem_statedSL_iff.mp hA
  have h := beta_rho A v w
  rw [hdet, one_mul] at h
  rw [rhoEquiv_apply, rhoEquiv_apply]
  exact h

theorem odd_count_of_disjoint_S024 (J : Set.powersetCard (Fin 6) 3)
    (h : Disjoint S024.val J.val) : 2 ≤ (J.val.filter (fun i : Fin 6 => i.val % 2 = 1)).card := by
  have key : ∀ s : Finset (Fin 6), s.card = 3 → Disjoint ({0, 2, 4} : Finset (Fin 6)) s →
      2 ≤ (s.filter (fun i : Fin 6 => i.val % 2 = 1)).card := by
    decide
  exact key J.val (beta1_card J) h

theorem beta_p0_of_mem_W0 {r : Cube K} (hr : r ∈ Wsp (Submodule.span K {p0 K}) (U0 K)) :
    beta K (p0 K) r = 0 := by
  rw [beta1_expand_right (p0 K) r]
  refine Finset.sum_eq_zero fun J _ => ?_
  by_cases hd : Disjoint S024.val J.val
  · rw [coord_eq_zero_of_mem_W0 hr J (odd_count_of_disjoint_S024 J hd), zero_mul]
  · rw [p0, beta_cubeBasis_of_not_disjoint hd, mul_zero]

theorem exists_gam_p0_eq_iota (w : Fin 3 → Fin 6 → K) (hw : LinearIndependent K w) :
    ∃ g ∈ Gam K, g (p0 K) = ιMulti K 3 w := by
  have hv : LinearIndependent K ![e K 0, e K 2, e K 4] := by
    apply linearIndependent_of_ιMulti_ne_zero
    rw [← p0_eq]
    exact p0_ne_zero
  obtain ⟨g, hdet, hgv⟩ := exists_sl_of_linearIndependent (by norm_num : 3 < 6) hv hw
  have hg0 : g.det ≠ 0 := by
    rw [hdet]
    exact one_ne_zero
  set G : GL (Fin 6) K := Matrix.GeneralLinearGroup.mkOfDetNeZero g hg0 with hG_def
  have hGval : (G : Matrix (Fin 6) (Fin 6) K) = g := rfl
  have hGS : G ∈ StatedSL 6 K :=
    CFSG.Open.StatedAPI.mem_statedSL_iff.mpr (by rw [hGval]; exact hdet)
  have key : rhoEquiv K G (p0 K) = ιMulti K 3 w := by
    rw [rhoEquiv_apply, p0_eq, rho_ιMulti, hGval]
    congr 1
    funext i
    exact hgv i
  exact ⟨rhoEquiv K G, Subgroup.mem_map_of_mem _ hGS, key⟩

theorem special_exists : ∃ g ∈ Gam K, beta K (p0 K) (g (p0 K)) = 0 ∧
    g (p0 K) ∉ Wsp (Submodule.span K {p0 K}) (U0 K) := by
  have hli : LinearIndependent K ![e K 0, e K 1, e K 3] :=
    linearIndependent_of_ιMulti_ne_zero (by rw [← cubeBasis_S013]; exact (cubeBasis K).ne_zero S013)
  obtain ⟨g, hg, hgp⟩ := exists_gam_p0_eq_iota ![e K 0, e K 1, e K 3] hli
  refine ⟨g, hg, ?_, ?_⟩
  · have hnd : ¬ Disjoint S024.val S013.val := by
      show ¬ Disjoint ({0, 2, 4} : Finset (Fin 6)) ({0, 1, 3} : Finset (Fin 6))
      decide
    rw [hgp, ← cubeBasis_S013, p0, beta_cubeBasis_of_not_disjoint hnd]
  · intro hmem
    have hodd : 2 ≤ (S013.val.filter (fun i : Fin 6 => i.val % 2 = 1)).card := by
      show 2 ≤ (({0, 1, 3} : Finset (Fin 6)).filter (fun i : Fin 6 => i.val % 2 = 1)).card
      decide
    have h1 := coord_eq_zero_of_mem_W0 hmem S013 hodd
    rw [hgp, ← cubeBasis_S013, coord_cubeBasis, if_pos rfl] at h1
    exact one_ne_zero h1

theorem opposite_exists : ∃ g ∈ Gam K, beta K (p0 K) (g (p0 K)) ≠ 0 := by
  have hli : LinearIndependent K ![e K 1, e K 3, e K 5] :=
    linearIndependent_of_ιMulti_ne_zero (by rw [← cubeBasis_S135]; exact (cubeBasis K).ne_zero S135)
  obtain ⟨g, hg, hgp⟩ := exists_gam_p0_eq_iota ![e K 1, e K 3, e K 5] hli
  refine ⟨g, hg, ?_⟩
  have hd : Disjoint S024.val S135.val := by
    show Disjoint ({0, 2, 4} : Finset (Fin 6)) ({1, 3, 5} : Finset (Fin 6))
    decide
  rw [hgp, ← cubeBasis_S135, p0]
  exact beta_cubeBasis_ne_zero_of_disjoint hd

end CFSG.RankThree.GF2n.Smith81.A5Cube
