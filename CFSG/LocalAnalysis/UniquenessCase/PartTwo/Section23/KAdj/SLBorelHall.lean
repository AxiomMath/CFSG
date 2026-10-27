module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLModel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLFlagMat
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Hall
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aOvergroup
import CFSG.ClassicalGroups.SpecialLinear.DiagTorusOdd
import CFSG.ClassicalGroups.SpecialLinear.DiagTorusNormalizesUnitriangular

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Open
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.SpecialLinear

variable {k : ℕ} {K : Type} [Field K]

private theorem slMat_eq_symm_B03 (g : ↥(StatedSL k K)) :
    slMat g = ((specialLinearGroupEquivStatedSL k K).symm g : Matrix (Fin k) (Fin k) K) := by
  have h := specialLinearGroupEquivStatedSL_coe k K
    ((specialLinearGroupEquivStatedSL k K).symm g)
  rw [MulEquiv.apply_symm_apply] at h
  exact h

private theorem mem_diagTorus_of_isDiag_B03 {k : ℕ} {K : Type} [Field K]
    {d : Matrix.SpecialLinearGroup (Fin k) K}
    (hd : (d : Matrix (Fin k) (Fin k) K).IsDiag) : d ∈ diagTorus k K := by
  have hprod : ∏ j, (d : Matrix (Fin k) (Fin k) K) j j = 1 := by
    have h1 : (d : Matrix (Fin k) (Fin k) K).det =
        ∏ j, (d : Matrix (Fin k) (Fin k) K) j j := by
      conv_lhs => rw [← hd.diagonal_diag]
      exact Matrix.det_diagonal
    rw [← h1]
    exact d.2
  have hne : ∀ i, (d : Matrix (Fin k) (Fin k) K) i i ≠ 0 := by
    intro i hi
    have h0 : (∏ j, (d : Matrix (Fin k) (Fin k) K) j j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [hprod] at h0
    exact one_ne_zero h0
  rw [mem_diagTorus_iff]
  refine ⟨fun i => Units.mk0 ((d : Matrix (Fin k) (Fin k) K) i i) (hne i), ?_, ?_⟩
  · apply Units.ext
    rw [Units.coe_prod, Units.val_one]
    simp only [Units.val_mk0]
    exact hprod
  · exact hd.diagonal_diag.symm

theorem exists_conj_slU_diagonal [NeZero k] [Finite K] [CharP K 2] {t : ↥(StatedSL k K)}
    (hup : ∀ i j : Fin k, j < i → slMat t i j = 0) (hodd : Odd (orderOf t)) :
    ∃ s ∈ slU k K, ∀ i j : Fin k, i ≠ j → slMat (s * t * s⁻¹) i j = 0 := by
  classical
  set e := specialLinearGroupEquivStatedSL k K with he
  set t₀ : Matrix.SpecialLinearGroup (Fin k) K := e.symm t with ht₀
  have ht0mat : (t₀ : Matrix (Fin k) (Fin k) K) = slMat t := by
    rw [ht₀]
    exact (slMat_eq_symm_B03 t).symm
  have ht0up : t₀ ∈ LinearFlag.upperTriangular k K := by
    rw [LinearFlag.mem_upperTriangular]
    intro i j hij
    rw [ht0mat]
    exact hup i j hij
  obtain ⟨u, hu, d, hd, hbd⟩ :=
    CFSG.QuasithinUnique.Setup.X7a.exists_unitriangular_mul_diagonal (n := k) (K := K) ht0up
  have hdmem : d ∈ diagTorus k K := mem_diagTorus_of_isDiag_B03 hd
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero (NeZero.ne k)
  obtain ⟨P, hP⟩ := LinearFlag.exists_sylow_unitriangular (K := K) (n := k) 2 hk1
  have hE : IsPGroup 2 (LinearFlag.unitriangular k K) := hP ▸ P.isPGroup'
  have hET := CFSG.diagTorus_le_normalizer_unitriangular (n := k) (F := K)
  have hT : ¬ 2 ∣ Nat.card (diagTorus k K) := CFSG.not_two_dvd_card_diagTorus
  have ht : t₀ ∈ LinearFlag.unitriangular k K ⊔ diagTorus k K := by
    rw [hbd]
    exact Subgroup.mul_mem_sup hu hdmem
  have hto : ¬ 2 ∣ orderOf t₀ := by
    rw [ht₀, MulEquiv.orderOf_eq]
    exact hodd.not_two_dvd_nat
  obtain ⟨e₀, he₀, hconj⟩ :=
    exists_conj_mem_of_mem_sup (G := Matrix.SpecialLinearGroup (Fin k) K) (p := 2)
      (E := LinearFlag.unitriangular k K) (T := diagTorus k K) hET hE hT ht hto
  refine ⟨e e₀, Subgroup.mem_map.mpr ⟨e₀, he₀, rfl⟩, ?_⟩
  have h3 : e (e₀ * t₀ * e₀⁻¹) = e e₀ * t * (e e₀)⁻¹ := by
    rw [ht₀]
    simp
  intro i j hij
  rw [← h3]
  show ((e₀ * t₀ * e₀⁻¹ : Matrix.SpecialLinearGroup (Fin k) K) :
    Matrix (Fin k) (Fin k) K) i j = 0
  obtain ⟨d', _, hd'mat⟩ := (mem_diagTorus_iff (n := k) (F := K)).1 hconj
  rw [hd'mat, Matrix.diagonal_apply_ne _ hij]

theorem slMat_conj_slU_apply_self {s t : ↥(StatedSL k K)} (hs : s ∈ slU k K)
    (ht : ∀ i j : Fin k, j < i → slMat t i j = 0) (i : Fin k) :
    slMat (s * t * s⁻¹) i i = slMat t i i := by
  obtain ⟨hs1, hs2⟩ := mem_slU_iff.1 hs
  obtain ⟨hs1', hs2'⟩ := mem_slU_iff.1 (inv_mem hs)
  have hm : slMat (s * t * s⁻¹) = slMat s * slMat t * slMat s⁻¹ := by
    simp [slMat, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
  have hS : (slMat s).IsUpperTriangular := fun _ _ h => hs1 _ _ h
  have hS' : (slMat s⁻¹).IsUpperTriangular := fun _ _ h => hs1' _ _ h
  have hT : (slMat t).IsUpperTriangular := fun _ _ h => ht _ _ h
  rw [hm, LinearFlag.mul_apply_self_of_isUpperTriangular (Matrix.BlockTriangular.mul hS hT) hS',
    LinearFlag.mul_apply_self_of_isUpperTriangular hS hT, hs2, hs2', one_mul, mul_one]

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
