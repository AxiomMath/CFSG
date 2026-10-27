module

public import CFSG.RankThree.GF2n.Smith81.S81U6Basic
public import CFSG.RankThree.GF2n.Smith81.S81A5Fixed
public import CFSG.RankThree.GF2n.Smith81.S81A5FE6a

public section

namespace CFSG.RankThree.GF2n.Smith81.U6Cube

open CFSG.RankThree.GF2n.Smith81.A5Cube Matrix exteriorPower CFSG.LieType.Universal.Unitary
  CFSG.ClassicalGroups.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K}

@[expose] def RootPt (σ : K ≃+* K) : Set (Cube K) :=
  {ξ | ξ ∈ Wsub σ ∧ ξ ≠ 0 ∧ IsPure K ξ}

theorem rho_mem_RootPt [CharP K 2] {g : GL (Fin 6) K} (hg : g ∈ SUid σ 6) {ξ : Cube K}
    (hξ : ξ ∈ RootPt σ) : rho K g ξ ∈ RootPt σ := by
  refine ⟨rho_mem_Wsub hg hξ.1, ?_, hξ.2.2.rho g⟩
  intro h0
  apply hξ.2.1
  have h1 : rho K g⁻¹ (rho K g ξ) = ξ := by
    rw [← Module.End.mul_apply, ← rho_mul, inv_mul_cancel, rho_one, Module.End.one_apply]
  rw [← h1, h0, map_zero]

theorem smul_mem_RootPt {c : K} (hc : σ c = c) (hc0 : c ≠ 0) {ξ : Cube K} (hξ : ξ ∈ RootPt σ) :
    c • ξ ∈ RootPt σ := by
  refine ⟨smul_mem_Wsub hc hξ.1, smul_ne_zero hc0 hξ.2.1, ?_⟩
  obtain ⟨v, rfl⟩ := hξ.2.2
  refine ⟨Function.update v 0 (c • v 0), ?_⟩
  have h := (ιMulti K 3).map_update_smul v 0 c (v 0)
  rw [Function.update_eq_self] at h
  exact h.symm

theorem theta_cubeBasis (I : Set.powersetCard (Fin 6) 3) :
    theta σ (cubeBasis K I) = cubeBasis K (cmpl I) := by
  rw [theta_apply, Finset.sum_eq_single I]
  · have : coord K (cubeBasis K I) I = 1 := by simp [coord]
    rw [this, map_one, one_smul]
  · intro J _ hJ
    have : coord K (cubeBasis K I) J = 0 := by
      simp [coord, Finsupp.single_apply, Ne.symm hJ]
    rw [this, map_zero, zero_smul]
  · intro h; exact absurd (Finset.mem_univ I) h

@[expose] noncomputable def pt0 (K : Type*) [Field K] : Cube K :=
  ιMulti K 3 ![e K 0 + e K 1, e K 2 + e K 3, e K 4 + e K 5]

private theorem e_triple_eq (i j k : Fin 6) (hij : i < j) (hjk : j < k) :
    ιMulti K 3 ![e K i, e K j, e K k] =
      cubeBasis K (tripleSet i j k hij.ne (hij.trans hjk).ne hjk.ne) := by
  rw [cubeBasis_apply]
  congr 1
  funext s
  rw [enum_tripleSet hij hjk s]
  fin_cases s <;> rfl

theorem pt0_eq :
    pt0 K = cubeBasis K (tripleSet 0 2 4 (by decide) (by decide) (by decide)) +
      cubeBasis K (tripleSet 0 2 5 (by decide) (by decide) (by decide)) +
      cubeBasis K (tripleSet 0 3 4 (by decide) (by decide) (by decide)) +
      cubeBasis K (tripleSet 0 3 5 (by decide) (by decide) (by decide)) +
      cubeBasis K (tripleSet 1 2 4 (by decide) (by decide) (by decide)) +
      cubeBasis K (tripleSet 1 2 5 (by decide) (by decide) (by decide)) +
      cubeBasis K (tripleSet 1 3 4 (by decide) (by decide) (by decide)) +
      cubeBasis K (tripleSet 1 3 5 (by decide) (by decide) (by decide)) := by
  unfold pt0
  simp only [ι3_add_fst, ι3_add_snd, ι3_add_thd]
  rw [e_triple_eq 0 2 4 (by decide) (by decide), e_triple_eq 0 2 5 (by decide) (by decide),
    e_triple_eq 0 3 4 (by decide) (by decide), e_triple_eq 0 3 5 (by decide) (by decide),
    e_triple_eq 1 2 4 (by decide) (by decide), e_triple_eq 1 2 5 (by decide) (by decide),
    e_triple_eq 1 3 4 (by decide) (by decide), e_triple_eq 1 3 5 (by decide) (by decide)]
  abel

private theorem cmpl_triple (i j k i' j' k' : Fin 6) (h1 : i ≠ j) (h2 : i ≠ k) (h3 : j ≠ k)
    (h1' : i' ≠ j') (h2' : i' ≠ k') (h3' : j' ≠ k')
    (h : Finset.univ \ ({i, j, k} : Finset (Fin 6)) = {i', j', k'}) :
    cmpl (tripleSet i j k h1 h2 h3) = tripleSet i' j' k' h1' h2' h3' :=
  Subtype.ext h

theorem theta_pt0 : theta σ (pt0 K) = pt0 K := by
  rw [pt0_eq]
  simp only [map_add, theta_cubeBasis]
  rw [cmpl_triple 0 2 4 1 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
    cmpl_triple 0 2 5 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
    cmpl_triple 0 3 4 1 2 5 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
    cmpl_triple 0 3 5 1 2 4 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
    cmpl_triple 1 2 4 0 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
    cmpl_triple 1 2 5 0 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
    cmpl_triple 1 3 4 0 2 5 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
    cmpl_triple 1 3 5 0 2 4 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
  abel

theorem isPure_pt0 : IsPure K (pt0 K) := ⟨_, rfl⟩

theorem pt0_ne_zero : pt0 K ≠ 0 := by
  intro h
  have h1 := congrArg (fun ξ => coord K ξ (tripleSet 0 2 4 (by decide) (by decide) (by decide))) h
  rw [pt0_eq] at h1
  simp only [coord_add, coord_cubeBasis, coord_zero] at h1
  simp (config := {decide := true}) [Subtype.ext_iff, tripleSet] at h1

theorem pt0_mem_RootPt : pt0 K ∈ RootPt σ :=
  ⟨theta_pt0, pt0_ne_zero, isPure_pt0⟩

end CFSG.RankThree.GF2n.Smith81.U6Cube
