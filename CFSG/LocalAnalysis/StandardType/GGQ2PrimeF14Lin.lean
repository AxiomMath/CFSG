module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVU58Lin
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic

public section

namespace CFSG.GGQ2Prime

open Matrix Polynomial CFSG.RankThree.PartTwo.Sec4.RonanK429.RowV

theorem pow_fifteen_eq_one_of_commute {L : Type*} [Field L] [CharP L 2] [IsAlgClosed L]
    {B U : Matrix (Fin 5) (Fin 5) L} (hB4 : B.map (fun x => x ^ 4) = B)
    (hBu : (B.map (fun x => x ^ 2))ᵀ * B = 1) (h5 : B ^ 5 = 1)
    (hB1 : B ≠ 1) (hU4 : U.map (fun x => x ^ 4) = U) (hU : IsUnit U) (hUB : U * B = B * U) :
    U ^ 15 = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨f4, f2, hf4, hf2⟩ : ∃ f4 f2 : L →+* L, (∀ x, f4 x = x ^ 4) ∧ ∀ x, f2 x = x ^ 2 :=
    ⟨iterateFrobenius L 2 2, iterateFrobenius L 2 1, fun _ => rfl, fun _ => rfl⟩
  have hmap4 : ∀ M : Matrix (Fin 5) (Fin 5) L, M.map f4 = M.map (fun x => x ^ 4) := fun M => by
    ext i j
    simp [hf4]
  have hB4' : B.map f4 = B := by rw [hmap4, hB4]
  have hU4' : U.map f4 = U := by rw [hmap4, hU4]
  have hBu' : (B.map f2)ᵀ * B = 1 := by
    have e : B.map f2 = B.map (fun x => x ^ 2) := by
      ext i j
      simp [hf2]
    rw [e, hBu]
  have hdet : B.det = 1 := by
    have h := congrArg Matrix.det hBu'
    rw [det_mul, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hf2, det_one] at h
    have h5' : B.det ^ 5 = 1 := by rw [← det_pow, h5, det_one]
    linear_combination (1 + B.det ^ 3) * h - B.det * h5'
  obtain ⟨μ, v, hv, hBv, hμ1⟩ :=
    exists_eigenvalue_ne_one_of_pow_eq_one (natCast_ne_zero_of_odd (L := L) (n := 5) rfl) h5 hB1
  have hμ5 : μ ^ 5 = 1 := eigenvalue_pow_eq_one h5 hv hBv
  have hμ15 : μ ^ 15 = 1 := by rw [show 15 = 5 * 3 by norm_num, pow_mul, hμ5, one_pow]
  have hprim : IsPrimitiveRoot μ 5 := isPrimitiveRoot_of_eigen h5 hv hBv hμ1
  obtain ⟨hv4, hBv4⟩ := eigen_map f4 hB4' hv hBv
  obtain ⟨w3, hw3, hBw3⟩ := eigen_unitary f2 hBu' hv hBv
  obtain ⟨hv2, hBv2⟩ := eigen_map f4 hB4' hw3 hBw3
  have e3 : (f2 μ)⁻¹ = μ ^ 3 := by
    rw [hf2]
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add, hμ5]
  have e2 : f4 ((f2 μ)⁻¹) = μ ^ 2 := by
    rw [e3, hf4, ← pow_mul, show 3 * 4 = 5 * 2 + 2 by norm_num, pow_add, pow_mul, hμ5, one_pow,
      one_mul]
  rw [hf4] at hBv4
  rw [e2] at hBv2
  rw [e3] at hBw3
  have hmon := B.charpoly_monic
  have hroot : ∀ c : L, ∀ w : Fin 5 → L, w ≠ 0 → B *ᵥ w = c • w → c ∈ B.charpoly.roots := by
    intro c w hw hBw
    rw [Polynomial.mem_roots hmon.ne_zero, Polynomial.IsRoot, Matrix.eval_charpoly]
    exact Matrix.exists_mulVec_eq_zero_iff.mp
      ⟨w, hw, by rw [sub_mulVec, scalar_mulVec_eq, hBw, sub_self]⟩
  have hne : ∀ i j : ℕ, i < 5 → j < 5 → i ≠ j → μ ^ i ≠ μ ^ j := fun i j hi hj hij h =>
    hij (hprim.pow_inj hi hj h)
  set M4 : Multiset L := μ ::ₘ (μ ^ 2) ::ₘ (μ ^ 3) ::ₘ {μ ^ 4} with hM4
  have hM4nd : M4.Nodup := by
    have h12 := hne 1 2 (by norm_num) (by norm_num) (by norm_num)
    have h13 := hne 1 3 (by norm_num) (by norm_num) (by norm_num)
    have h14 := hne 1 4 (by norm_num) (by norm_num) (by norm_num)
    have h23 := hne 2 3 (by norm_num) (by norm_num) (by norm_num)
    have h24 := hne 2 4 (by norm_num) (by norm_num) (by norm_num)
    have h34 := hne 3 4 (by norm_num) (by norm_num) (by norm_num)
    rw [pow_one] at h12 h13 h14
    simp [hM4, h12, h13, h14, h23, h24, h34]
  have hM4le : M4 ≤ B.charpoly.roots := by
    rw [Multiset.le_iff_subset hM4nd]
    intro x hx
    simp only [hM4, Multiset.mem_cons, Multiset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hroot _ v hv hBv
    · exact hroot _ _ hv2 hBv2
    · exact hroot _ w3 hw3 hBw3
    · exact hroot _ _ hv4 hBv4
  obtain ⟨R', hR'⟩ := Multiset.le_iff_exists_add.mp hM4le
  have hcard : Multiset.card B.charpoly.roots = 5 := by
    rw [(Polynomial.splits_iff_card_roots).mp (IsAlgClosed.splits _),
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hR'card : Multiset.card R' = 1 := by
    have h := congrArg Multiset.card hR'
    rw [Multiset.card_add, hcard] at h
    simp [hM4] at h
    omega
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.mp hR'card
  have hprod : B.det = μ ^ 10 * c := by
    rw [Matrix.det_eq_prod_roots_charpoly, hR', hc]
    simp only [hM4, Multiset.prod_add, Multiset.prod_cons, Multiset.prod_singleton]
    ring
  have hc1 : c = 1 := by
    rw [hdet, show 10 = 5 * 2 by norm_num, pow_mul, hμ5, one_pow, one_mul] at hprod
    exact hprod.symm
  have h1mem : (1 : L) ∈ B.charpoly.roots := by
    rw [hR', hc, hc1]
    exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self 1))
  obtain ⟨v0, hv0, hBv0⟩ : ∃ w : Fin 5 → L, w ≠ 0 ∧ B *ᵥ w = μ ^ 0 • w := by
    rw [Polynomial.mem_roots hmon.ne_zero, Polynomial.IsRoot, Matrix.eval_charpoly] at h1mem
    obtain ⟨w, hw, hBw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h1mem
    refine ⟨w, hw, ?_⟩
    rw [sub_mulVec, scalar_mulVec_eq, sub_eq_zero] at hBw
    rw [pow_zero]
    exact hBw.symm
  set lam : Fin 5 → L := fun i => μ ^ (i : ℕ) with hlam
  set vec : Fin 5 → (Fin 5 → L) := ![v0, v, f4 ∘ w3, w3, f4 ∘ v] with hvec
  have hlaminj : Function.Injective lam := fun i j h => Fin.ext (hprim.pow_inj i.2 j.2 h)
  have hvB : ∀ i, vec i ≠ 0 ∧ B *ᵥ vec i = lam i • vec i := by
    intro i
    fin_cases i
    · exact ⟨by simpa [hvec] using hv0, by simpa [hvec, hlam] using hBv0⟩
    · exact ⟨by simpa [hvec] using hv, by simpa [hvec, hlam] using hBv⟩
    · exact ⟨by simpa [hvec] using hv2, by simpa [hvec, hlam] using hBv2⟩
    · exact ⟨by simpa [hvec] using hw3, by simpa [hvec, hlam] using hBw3⟩
    · exact ⟨by simpa [hvec] using hv4, by simpa [hvec, hlam] using hBv4⟩
  have hli : LinearIndependent L vec :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' B) lam hlaminj vec fun k => by
      rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
      exact ⟨(hvB k).2, (hvB k).1⟩
  have hspan : Submodule.span L (Set.range vec) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp)
  have hdiag : ∀ i, ∀ w : Fin 5 → L, B *ᵥ w = lam i • w → ∃ d : L, w = d • vec i := by
    intro i w hBw
    have hmem : w ∈ Submodule.span L (Set.range vec) := by
      rw [hspan]
      exact Submodule.mem_top
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun L).mp hmem
    have hsum : ∑ j, (a j * (lam j - lam i)) • vec j = 0 := by
      have h0 : B *ᵥ (∑ j, a j • vec j) - lam i • (∑ j, a j • vec j) = 0 := by
        rw [ha, hBw, sub_self]
      rw [← h0, mulVec_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mulVec_smul, (hvB j).2, smul_smul, smul_smul, ← sub_smul, mul_sub, mul_comm (lam i)]
    have hcoef := Fintype.linearIndependent_iff.mp hli _ hsum
    have haj : ∀ j, j ≠ i → a j = 0 := fun j hji =>
      (mul_eq_zero.mp (hcoef j)).resolve_right (sub_ne_zero.mpr fun h => hji (hlaminj h))
    refine ⟨a i, ?_⟩
    rw [← ha, Finset.sum_eq_single i (fun j _ hji => by rw [haj j hji, zero_smul])
      (fun h => absurd (Finset.mem_univ i) h)]
  have hUi : ∀ i, ∃ c : L, U *ᵥ vec i = c • vec i ∧ c ^ 15 = 1 := by
    intro i
    have hBU : B *ᵥ (U *ᵥ vec i) = lam i • (U *ᵥ vec i) := by
      rw [mulVec_mulVec, ← hUB, ← mulVec_mulVec, (hvB i).2, mulVec_smul]
    obtain ⟨c, hc⟩ := hdiag i _ hBU
    refine ⟨c, hc, ?_⟩
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hc
      exact (hvB i).1 ((Matrix.mulVec_injective_iff_isUnit.mpr hU) (hc.trans (mulVec_zero U).symm))
    obtain ⟨hw1, hBw1⟩ := eigen_map f4 hB4' (hvB i).1 (hvB i).2
    obtain ⟨hw2, hBw2⟩ := eigen_map f4 hB4' hw1 hBw1
    have hl16 : f4 (f4 (lam i)) = lam i := by
      simp only [hf4, hlam]
      rw [← pow_mul, ← pow_mul, show (i : ℕ) * (4 * 4) = i + 15 * i by ring, pow_add, pow_mul, hμ15,
        one_pow, mul_one]
    rw [hl16] at hBw2
    obtain ⟨d, hd⟩ := hdiag i _ hBw2
    obtain ⟨-, hUw1⟩ := eigen_map_aux f4 (hvB i).1 hc
    rw [hU4'] at hUw1
    obtain ⟨-, hUw2⟩ := eigen_map_aux f4 hw1 hUw1
    rw [hU4'] at hUw2
    have hUd : U *ᵥ (f4 ∘ (f4 ∘ vec i)) = c • (f4 ∘ (f4 ∘ vec i)) := by
      rw [hd, mulVec_smul, hc, smul_comm]
    have heq : (f4 (f4 c) - c) • (f4 ∘ (f4 ∘ vec i)) = 0 := by
      rw [sub_smul, ← hUw2, ← hUd, sub_self]
    have h16 : f4 (f4 c) = c := sub_eq_zero.mp ((smul_eq_zero.mp heq).resolve_right hw2)
    rw [hf4, hf4, ← pow_mul] at h16
    have h : c * (c ^ 15 - 1) = 0 := by linear_combination h16
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hc0)
  have hU15 : ∀ i, (U ^ 15) *ᵥ vec i = vec i := by
    intro i
    obtain ⟨c, hc, hc15⟩ := hUi i
    have hn : ∀ n : ℕ, (U ^ n) *ᵥ vec i = c ^ n • vec i := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ' U, ← mulVec_mulVec, ih, mulVec_smul, hc, smul_smul, ← pow_succ]
    rw [hn, hc15, one_smul]
  have hlin : Matrix.toLin' (U ^ 15) = Matrix.toLin' (1 : Matrix (Fin 5) (Fin 5) L) :=
    LinearMap.ext_on_range hspan fun i => by
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, one_mulVec, hU15 i]
  exact Matrix.toLin'.injective hlin

theorem pow_fifteen_eq_one_of_commute' {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) {B U : Matrix (Fin 5) (Fin 5) F}
    (hBu : (B.map (frobenius F 2))ᵀ * B = 1) (h5 : B ^ 5 = 1)
    (hB1 : B ≠ 1) (hU : IsUnit U) (hUB : U * B = B * U) : U ^ 15 = 1 := by
  have h4 : ∀ x : F, x ^ 4 = x := by
    let _ : Fintype F := Fintype.ofFinite F
    intro x
    have h := FiniteField.pow_card x
    rwa [← Nat.card_eq_fintype_card, hF] at h
  set ψ := algebraMap F (AlgebraicClosure F)
  have : CharP (AlgebraicClosure F) 2 := charP_of_injective_algebraMap ψ.injective 2
  have hinj : Function.Injective (ψ.mapMatrix (m := Fin 5)) :=
    Matrix.map_injective ψ.injective
  have hmap4 : ∀ M : Matrix (Fin 5) (Fin 5) F, (M.map ψ).map (fun x => x ^ 4) = M.map ψ := by
    intro M
    ext i j
    simp only [Matrix.map_apply]
    rw [← map_pow, h4]
  have hu : ((B.map ψ).map (fun x => x ^ 2))ᵀ * B.map ψ = 1 := by
    have h2 : (B.map ψ).map (fun x => x ^ 2) = (B.map (frobenius F 2)).map ψ := by
      ext i j
      simp only [Matrix.map_apply]
      rw [← map_pow]
      rfl
    rw [h2, ← transpose_map, ← Matrix.map_mul, hBu, Matrix.map_one ψ (map_zero ψ) (map_one ψ)]
  have hUL : IsUnit (U.map ψ) := by
    have h := hU.map ψ.mapMatrix
    rwa [RingHom.mapMatrix_apply] at h
  apply hinj
  rw [map_one, map_pow]
  exact pow_fifteen_eq_one_of_commute (B := B.map ψ) (hmap4 B) hu
    (by rw [← RingHom.mapMatrix_apply, ← map_pow, h5, map_one])
    (fun h => hB1 (hinj (by rw [RingHom.mapMatrix_apply, h, map_one])))
    (hmap4 U) hUL
    (by rw [← RingHom.mapMatrix_apply, ← map_mul, ← map_mul, hUB])

end CFSG.GGQ2Prime
