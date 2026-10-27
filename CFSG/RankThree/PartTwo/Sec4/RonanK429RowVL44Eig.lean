module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVSp64Lin
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429.RowV

open Matrix

theorem l44_three_le_card_of_commute_pow_seven {L : Type*} [Field L] [CharP L 2] [IsAlgClosed L]
    {B : Matrix (Fin 4) (Fin 4) L} {y : Fin 4 → L} (hB4 : B.map (fun x => x ^ 4) = B)
    (h7 : B ^ 7 = 1) (hB1 : B ≠ 1) (hy : ∀ k, y k ^ 3 = 1)
    (hAB : diagonal y * B = B * diagonal y) :
    ∃ i j k : Fin 4, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ y i = y j ∧ y i = y k := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  set A := diagonal y with hA
  obtain ⟨φ, hφ⟩ : ∃ φ : L →+* L, ∀ x : L, φ x = x ^ 4 :=
    ⟨iterateFrobenius L 2 2, fun x => rfl⟩
  have hBφ : B.map φ = B := by
    have h4 : B.map φ = B.map (fun x => x ^ 4) := by
      ext i j
      simp [hφ]
    rw [h4, hB4]
  have hAφ : A.map φ = A := by
    ext k l
    simp only [hA, Matrix.map_apply, diagonal_apply]
    split_ifs
    · rw [hφ, pow_succ, hy, one_mul]
    · exact map_zero φ
  have h7ne : (7 : L) ≠ 0 := by
    intro h
    have h' : ((7 : ℕ) : L) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff L 2] at h'
    norm_num at h'
  obtain ⟨μ, v, hv, hBv, hμ1⟩ := exists_eigenvalue_ne_one_of_pow_seven h7ne h7 hB1
  have hpowv : ∀ k : ℕ, B ^ k *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← mulVec_mulVec, hBv, mulVec_smul, ih, smul_smul, pow_succ']
  have hμ7 : μ ^ 7 = 1 := by
    have h := hpowv 7
    rw [h7, one_mulVec] at h
    by_contra hne
    apply hv
    have h' : (μ ^ 7 - 1) • v = 0 := by rw [sub_smul, ← h, one_smul, sub_self]
    exact (smul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hne)
  have hμo : orderOf μ = 7 := orderOf_eq_prime hμ7 hμ1
  have hprim : IsPrimitiveRoot μ 7 := hμo ▸ IsPrimitiveRoot.orderOf μ
  have hAB' : A * B = B * A := hAB
  obtain ⟨c, w, hw, hBw, hAw⟩ := exists_common_eigenvector hAB' hv hBv
  have hc3 : c ^ 3 = 1 := by
    obtain ⟨k, hk⟩ : ∃ k, w k ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hw (funext hcon)
    have hyk : y k = c := by
      by_contra hne
      exact hk (apply_eq_zero_of_diagonal_mulVec hAw hne)
    rw [← hyk]
    exact hy k
  have hφc : φ c = c := by rw [hφ, pow_succ, hc3, one_mul]
  obtain ⟨hw₁, hBw₁, hAw₁⟩ := frobenius_eigenvector φ hBφ hAφ hw hBw hAw
  rw [hφc] at hAw₁
  obtain ⟨hw₂, hBw₂, hAw₂⟩ := frobenius_eigenvector φ hBφ hAφ hw₁ hBw₁ hAw₁
  rw [hφc] at hAw₂
  have e2 : φ (φ μ) = μ ^ 2 := by
    rw [hφ, hφ, ← pow_mul, show 4 * 4 = 7 * 2 + 2 by norm_num, pow_add, pow_mul, hμ7, one_pow,
      one_mul]
  rw [e2] at hBw₂
  rw [hφ] at hBw₁
  set ex : Fin 3 → ℕ := ![1, 4, 2] with hex
  set lam : Fin 3 → L := fun i => μ ^ ex i with hlam
  set vec : Fin 3 → (Fin 4 → L) := ![w, φ ∘ w, φ ∘ (φ ∘ w)] with hvec
  have hexlt : ∀ i, ex i < 7 := by decide
  have hexinj : ∀ i j, ex i = ex j → i = j := by decide
  have hlaminj : Function.Injective lam := fun i j h =>
    hexinj i j (hprim.pow_inj (hexlt i) (hexlt j) h)
  have hvecB : ∀ i, B *ᵥ vec i = lam i • vec i := by
    intro i
    fin_cases i
    · simpa [hvec, hlam, hex] using hBw
    · simpa [hvec, hlam, hex] using hBw₁
    · simpa [hvec, hlam, hex] using hBw₂
  have hvec0 : ∀ i, vec i ≠ 0 := by
    intro i
    fin_cases i
    · simpa [hvec] using hw
    · simpa [hvec] using hw₁
    · simpa [hvec] using hw₂
  have hli : LinearIndependent L vec :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' B) lam hlaminj vec fun i => by
      rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
      exact ⟨hvecB i, hvec0 i⟩
  suffices h3 : 3 ≤ (Finset.univ.filter (fun k => y k = c)).card by
    obtain ⟨a, ha, b, hb, d, hd, hab, had, hbd⟩ :=
      (Finset.two_lt_card (s := Finset.univ.filter (fun k => y k = c))).mp (by omega)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hd
    exact ⟨a, b, d, hab, had, hbd, ha.trans hb.symm, ha.trans hd.symm⟩
  have hsupp : ∀ {x : Fin 4 → L}, A *ᵥ x = c • x →
      ∀ k, k ∉ Finset.univ.filter (fun k => y k = c) → x k = 0 := by
    intro x hx k hk
    refine apply_eq_zero_of_diagonal_mulVec hx ?_
    simpa using hk
  have := card_le_of_linearIndependent_supported hli (Finset.univ.filter (fun k => y k = c)) (by
    intro j k hk
    fin_cases j
    · exact hsupp hAw k hk
    · exact hsupp hAw₁ k hk
    · exact hsupp hAw₂ k hk)
  simpa using this

theorem l44_three_le_card_of_commute_pow_seven' {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) {B : Matrix (Fin 4) (Fin 4) F} {y : Fin 4 → F} (h7 : B ^ 7 = 1)
    (hB1 : B ≠ 1) (hy : ∀ k, y k ^ 3 = 1)
    (hAB : diagonal y * B = B * diagonal y) :
    ∃ i j k : Fin 4, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ y i = y j ∧ y i = y k := by
  have hpow4 : ∀ x : F, x ^ 4 = x := by
    intro x
    letI := Fintype.ofFinite F
    have h := FiniteField.pow_card x
    rw [← Nat.card_eq_fintype_card, hF] at h
    exact h
  set L := AlgebraicClosure F
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap F L).injective 2
  set ι := (algebraMap F L).mapMatrix (m := Fin 4) with hι
  have hinj : Function.Injective ι := Matrix.map_injective (algebraMap F L).injective
  have hdiag : ι (diagonal y) = diagonal (fun k => algebraMap F L (y k)) := by
    rw [hι, RingHom.mapMatrix_apply, diagonal_map (map_zero _)]
  obtain ⟨i, j, k, hij, hik, hjk, h1, h2⟩ := l44_three_le_card_of_commute_pow_seven (L := L)
    (B := ι B) (y := fun k => algebraMap F L (y k))
    (by
      ext i j
      simp only [hι, RingHom.mapMatrix_apply, Matrix.map_apply]
      rw [← map_pow, hpow4])
    (by rw [← map_pow, h7, map_one])
    (fun h => hB1 (hinj (by rw [h, map_one])))
    (fun k => by rw [← map_pow, hy k, map_one])
    (by rw [← hdiag, ← map_mul, ← map_mul, hAB])
  exact ⟨i, j, k, hij, hik, hjk, (algebraMap F L).injective h1, (algebraMap F L).injective h2⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK429.RowV
