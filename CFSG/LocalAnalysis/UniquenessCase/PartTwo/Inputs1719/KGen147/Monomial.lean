module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.IsDiag
import CFSG.LocalAnalysis.UniquenessCase.UC1K326SL3GenMatrix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen

open Matrix
open CFSG.RankThree.PartTwo.Sec15.KSL3Two

namespace Monomial

theorem cube_eq_id_imp_shift :
    ∀ τ : Fin 3 → Fin 3, τ ∘ τ ∘ τ = id → τ ≠ id →
      τ = ![1, 2, 0] ∨ τ = ![2, 0, 1] := by
  decide

theorem eq_diagonal_mul_perm {F : Type} [Field F] {τ : Fin 3 → Fin 3}
    (hτ : τ ∘ τ ∘ τ = id) {A : Matrix (Fin 3) (Fin 3) F}
    (hA : ∀ i j, A j i ≠ 0 ↔ j = τ i) :
    A = diagonal (fun j => A j (τ (τ j))) *
      Matrix.of (fun r c => if r = τ c then (1 : F) else 0) := by
  ext r c
  rw [Matrix.diagonal_mul]
  by_cases h : r = τ c
  · have hc : τ (τ (τ c)) = c := by simpa using congrFun hτ c
    rw [h]
    simp [hc]
  · have h0 : A r c = 0 := by
      by_contra hne
      exact h ((hA c r).mp hne)
    simp [h, h0]

end Monomial

theorem exists_diag_entry_ne_of_card {F : Type} [Field F] {p : ℕ} (hp : p.Prime)
    {R : Subgroup (GL (Fin 3) F)} (hdiag : ∀ u ∈ R, (u : Matrix (Fin 3) (Fin 3) F).IsDiag)
    (hdet : ∀ u ∈ R, (u : Matrix (Fin 3) (Fin 3) F).det = 1) (hexp : ∀ u ∈ R, u ^ p = 1)
    (hcard : Nat.card R = p ^ 2) {i j : Fin 3} (hij : i ≠ j) :
    ∃ u ∈ R, (u : Matrix (Fin 3) (Fin 3) F) i i ≠ (u : Matrix (Fin 3) (Fin 3) F) j j := by
  have hfin : Finite R :=
    (Nat.card_ne_zero.mp (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)).2
  refine exists_ne_diag_of_not_isCyclic ?_ hdiag hdet hij
  rw [isCyclic_iff_exists_zpowers_eq_top]
  rintro ⟨g, hg⟩
  have hord : orderOf g = p ^ 2 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers (fun x => by rw [hg]; exact Subgroup.mem_top x),
      hcard]
  have hgp : g ^ p = 1 := Subtype.ext (by simpa using hexp (g : GL (Fin 3) F) g.2)
  have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
  have hle : p ^ 2 ≤ p := by rw [← hord]; exact Nat.le_of_dvd hp.pos hdvd
  have hlt : p < p ^ 2 := by
    simpa using Nat.pow_lt_pow_right hp.one_lt (by norm_num : 1 < 2)
  exact absurd hle (not_le.mpr hlt)

theorem exists_diagonal_mul_shift_pow {F : Type} [Field F] {R : Subgroup (GL (Fin 3) F)}
    (hdiag : ∀ u ∈ R, (u : Matrix (Fin 3) (Fin 3) F).IsDiag)
    (hsep : ∀ i j : Fin 3, i ≠ j →
      ∃ u ∈ R, (u : Matrix (Fin 3) (Fin 3) F) i i ≠ (u : Matrix (Fin 3) (Fin 3) F) j j)
    {b : GL (Fin 3) F} (hb3 : b ^ 3 = 1) (hbR : ∀ u ∈ R, b * u * b⁻¹ ∈ R)
    (hbc : ∃ u ∈ R, b * u ≠ u * b) :
    ∃ (d : Fin 3 → F) (k : ℕ), (k = 1 ∨ k = 2) ∧
      (b : Matrix (Fin 3) (Fin 3) F) = diagonal d * !![0, 0, 1; 1, 0, 0; 0, 1, 0] ^ k := by
  have hb2 : b ^ 2 = b⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    simpa [pow_succ] using hb3
  have hb4 : b⁻¹ * b⁻¹ = b := by
    have h : b * b ^ 2 = 1 := by simpa [pow_succ'] using hb3
    have h' : (b ^ 2)⁻¹ = b := inv_eq_of_mul_eq_one_left h
    rwa [← inv_pow, pow_two] at h'
  have hbR' : ∀ u ∈ R, b⁻¹ * u * b ∈ R := by
    intro u hu
    have h1 : b * u * b⁻¹ ∈ R := hbR u hu
    have h2 : b * (b * u * b⁻¹) * b⁻¹ ∈ R := hbR _ h1
    have heq : b * (b * u * b⁻¹) * b⁻¹ = b⁻¹ * u * b := by
      have h : b * (b * u * b⁻¹) * b⁻¹ = b * b * u * (b⁻¹ * b⁻¹) := by group
      rw [h, hb4, ← pow_two, hb2]
    rwa [heq] at h2
  obtain ⟨τ, hmon⟩ := exists_monomial_of_normalizes hdiag hsep hbR'
  have hT : IsPGroup 3 (Subgroup.zpowers b) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers]
    simpa using orderOf_dvd_of_pow_eq_one hb3
  have hcube : τ ∘ τ ∘ τ = id :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.SL3G.monomial_perm_cube
      (G := GL (Fin 3) F) (MonoidHom.id (GL (Fin 3) F)) hT (Subgroup.mem_zpowers b) hmon
  have hτne : τ ≠ id := by
    intro hid
    obtain ⟨u, hu, hne⟩ := hbc
    apply hne
    have hbdiag : (b : Matrix (Fin 3) (Fin 3) F).IsDiag := by
      have h := hmon
      rw [hid] at h
      exact h.isDiag
    refine Units.ext ?_
    simpa only [Units.val_mul] using commute_of_isDiag hbdiag (hdiag u hu)
  obtain hτ | hτ := Monomial.cube_eq_id_imp_shift τ hcube hτne
  · rw [hτ] at hmon hcube
    have hperm := Monomial.eq_diagonal_mul_perm hcube hmon
    refine ⟨fun j => (b : Matrix (Fin 3) (Fin 3) F) j (![1, 2, 0] (![1, 2, 0] j)), 1,
      Or.inl rfl, ?_⟩
    rw [hperm, pow_one]
    ext r c
    rw [Matrix.diagonal_mul, Matrix.diagonal_mul]
    fin_cases r <;> fin_cases c <;> simp
  · rw [hτ] at hmon hcube
    have hperm := Monomial.eq_diagonal_mul_perm hcube hmon
    refine ⟨fun j => (b : Matrix (Fin 3) (Fin 3) F) j (![2, 0, 1] (![2, 0, 1] j)), 2,
      Or.inr rfl, ?_⟩
    rw [hperm, pow_two]
    ext r c
    rw [Matrix.diagonal_mul, Matrix.diagonal_mul]
    fin_cases r <;> fin_cases c <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen
