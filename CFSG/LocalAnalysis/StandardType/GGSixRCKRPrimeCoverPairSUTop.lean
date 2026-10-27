module

public import CFSG.LocalAnalysis.StandardType.GGInvolutionClassSURoot
import CFSG.LieType.Steinberg.CoreBasic

public section

namespace CFSG.StandardType.RCKRP

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.BorelTits CFSG.StandardType

private theorem exists_pos_of_mem_roots' {n : ℕ} {γ : Fin (n / 2) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartan n) (divisible n)) :
    ∃ a b : Fin n, a ≠ b ∧ toStd n γ = weight n a - weight n b := by
  rw [roots_eq] at hγ
  rcases hγ with ⟨i, j, hij, -, -, -, h⟩ | ⟨i, hi, h⟩ | ⟨he, i, hi, h⟩
  · exact ⟨i, j, hij, h⟩
  · exact ⟨i, Fin.rev i, hi, by rw [h, weight_rev', sub_neg_eq_add, two_nsmul]⟩
  · refine ⟨i, midIdx n he, fun h' => ?_, by rw [h, weight_eq_zero_of_rev_eq (rev_midIdx he),
      sub_zero]⟩
    rw [h'] at hi
    exact hi (rev_midIdx he).symm

private theorem toStd_neg' (n : ℕ) (v : Fin (n / 2) → ℤ) : toStd n (-v) = -toStd n v := by
  have h : toStd n (-v) + toStd n v = 0 := by
    rw [← toStd_add', neg_add_cancel, toStd_zero']
  funext a
  have h' := congrFun h a
  simp only [Pi.add_apply, Pi.zero_apply, Pi.neg_apply] at h' ⊢
  linarith

private theorem toStd_neg_ggTopRoot {n : ℕ} (hn : 2 ≤ n) :
    toStd n (-ggTopRoot n) =
      weight n (Fin.rev ⟨0, by omega⟩) - weight n ⟨0, by omega⟩ := by
  rw [toStd_neg', toStd_ggTopRoot hn, neg_sub]

theorem rckSU_eq_ggTopRoot_of_maxHeight {n : ℕ} (hn : 2 ≤ n) {γ₀ : Fin (n / 2) → ℤ}
    (hγ₀ : γ₀ ∈ roots (isFiniteType_cartan n) (divisible n))
    (hmax : ∀ δ ∈ roots (isFiniteType_cartan n) (divisible n), ∑ i, δ i ≤ ∑ i, γ₀ i) :
    γ₀ = ggTopRoot n := by
  have htop : ht (ggTopRoot n) ≤ ht γ₀ := hmax _ (ggTopRoot_mem_roots hn)
  rw [ht_ggTopRoot hn] at htop
  obtain ⟨a, b, -, hγ⟩ := exists_pos_of_mem_roots' hγ₀
  have hht : ht γ₀ = (b.val : ℤ) - a.val := ht_eq_of_weight_sub hγ.symm
  have ha' := a.isLt
  have hb' := b.isLt
  have ha : a.val = 0 := by omega
  have hb : b.val = n - 1 := by omega
  have ha0 : a = (⟨0, by omega⟩ : Fin n) := Fin.ext ha
  have hb0 : b = Fin.rev (⟨0, by omega⟩ : Fin n) := by
    apply Fin.ext
    simp only [Fin.val_rev]
    omega
  apply toStd_inj'
  rw [hγ, toStd_ggTopRoot hn]
  simp only [ha0, hb0]

variable {F : Type*} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)

private theorem mat_eq_of_mem_rootGroup_top {n : ℕ} (hn : 2 ≤ n) {x : SU σ n}
    (hx : x ∈ rootGroup σ hσ n (ggTopRoot n)) :
    mat σ n x = 1 + single ⟨0, by omega⟩ (Fin.rev ⟨0, by omega⟩)
      (mat σ n x ⟨0, by omega⟩ (Fin.rev ⟨0, by omega⟩)) := by
  have hts : ht (ggTopRoot n) = (n : ℤ) - 1 := ht_ggTopRoot hn
  have hne : (⟨0, by omega⟩ : Fin n) ≠ Fin.rev ⟨0, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_rev] at this
    omega
  ext a b
  by_cases hab : a = ⟨0, by omega⟩ ∧ b = Fin.rev ⟨0, by omega⟩
  · obtain ⟨rfl, rfl⟩ := hab
    rw [Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, Matrix.single_apply_same]
  · rw [mat_apply_of_mem_rootGroup hσ hx ?_ ?_, Matrix.add_apply, Matrix.single_apply,
      ite_eq_right (fun h => hab ⟨h.1.symm, h.2.symm⟩), add_zero]
    · intro h
      have hpos := ht_eq_of_weight_sub h
      rw [hts] at hpos
      have ha := a.isLt
      have hb := b.isLt
      apply hab
      constructor <;> apply Fin.ext <;> simp only [Fin.val_rev] <;> omega
    · intro h
      have h2 := two_mul_ht_eq_of_weight_sub h
      rw [hts] at h2
      have ha := a.isLt
      have hb := b.isLt
      omega

private theorem mat_eq_of_mem_rootGroup_neg_top {n : ℕ} (hn : 2 ≤ n) {x : SU σ n}
    (hx : x ∈ rootGroup σ hσ n (-ggTopRoot n)) :
    mat σ n x = 1 + single (Fin.rev ⟨0, by omega⟩) ⟨0, by omega⟩
      (mat σ n x (Fin.rev ⟨0, by omega⟩) ⟨0, by omega⟩) := by
  have hts : ht (-ggTopRoot n) = -((n : ℤ) - 1) := by
    rw [ht_neg, ht_ggTopRoot hn]
  have hne : (Fin.rev ⟨0, by omega⟩ : Fin n) ≠ ⟨0, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_rev] at this
    omega
  ext a b
  by_cases hab : a = Fin.rev ⟨0, by omega⟩ ∧ b = ⟨0, by omega⟩
  · obtain ⟨rfl, rfl⟩ := hab
    rw [Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, Matrix.single_apply_same]
  · rw [mat_apply_of_mem_rootGroup hσ hx ?_ ?_, Matrix.add_apply, Matrix.single_apply,
      ite_eq_right (fun h => hab ⟨h.1.symm, h.2.symm⟩), add_zero]
    · intro h
      have hpos := ht_eq_of_weight_sub h
      rw [hts] at hpos
      have ha := a.isLt
      have hb := b.isLt
      apply hab
      constructor <;> apply Fin.ext <;> simp only [Fin.val_rev] <;> omega
    · intro h
      have h2 := two_mul_ht_eq_of_weight_sub h
      rw [hts] at h2
      have ha := a.isLt
      have hb := b.isLt
      omega

private theorem add_eq_zero_of_mat_eq_one_add_single_neg {n : ℕ} (hn : 2 ≤ n) {x : SU σ n}
    {c : F} (hx : mat σ n x = 1 + single (Fin.rev ⟨0, by omega⟩) ⟨0, by omega⟩ c) :
    c + σ c = 0 := by
  have hiso := conjTr_mat_mul x
  rw [hx, conjTr_add, conjTr_one, conjTr_single] at hiso
  have hne : (⟨0, by omega⟩ : Fin n) ≠ Fin.rev ⟨0, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_rev] at this
    omega
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, antidiag_mul_single,
    single_mul_antidiag, Fin.rev_rev, single_mul_single_of_ne _ _ _ _ hne] at hiso
  have h := congrFun (congrFun hiso ⟨0, by omega⟩) ⟨0, by omega⟩
  simp only [Matrix.add_apply, Matrix.single_apply_same, Matrix.zero_apply] at h
  linear_combination h

theorem rckSU_mem_rootGroup_top_iff {n : ℕ} (hn : 2 ≤ n) (x : SU σ n) :
    x ∈ rootGroup σ hσ n (ggTopRoot n) ↔ ∃ c : F, c + σ c = 0 ∧
      mat σ n x = 1 + single ⟨0, by omega⟩ (Fin.rev ⟨0, by omega⟩) c := by
  constructor
  · intro hx
    have hmat := mat_eq_of_mem_rootGroup_top hσ hn hx
    exact ⟨_, add_eq_zero_of_mat_eq_one_add_single hn hmat, hmat⟩
  · rintro ⟨c, hc, hmat⟩
    have hi : (⟨0, by omega⟩ : Fin n) ≠ Fin.rev ⟨0, by omega⟩ := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_rev] at this
      omega
    have hw : 2 • weight n (⟨0, by omega⟩ : Fin n) = toStd n (ggTopRoot n) := by
      rw [toStd_ggTopRoot hn, weight_rev', sub_neg_eq_add, two_nsmul]
    let y : SU σ n := longRootHom σ hi (Multiplicative.ofAdd ⟨c, hc⟩)
    have hy : y ∈ rootGroup σ hσ n (ggTopRoot n) := longRootHom_mem hσ hi hw _
    have hy' : mat σ n y = 1 + single ⟨0, by omega⟩ (Fin.rev ⟨0, by omega⟩) c := by
      rw [mat_apply, coe_longRootHom, toAdd_ofAdd, longRootMatrix]
    exact (mat_injective (hy'.trans hmat.symm)) ▸ hy

theorem rckSU_mem_rootGroup_neg_top_iff {n : ℕ} (hn : 2 ≤ n) (x : SU σ n) :
    x ∈ rootGroup σ hσ n (-ggTopRoot n) ↔ ∃ c : F, c + σ c = 0 ∧
      mat σ n x = 1 + single (Fin.rev ⟨0, by omega⟩) ⟨0, by omega⟩ c := by
  constructor
  · intro hx
    have hmat := mat_eq_of_mem_rootGroup_neg_top hσ hn hx
    exact ⟨_, add_eq_zero_of_mat_eq_one_add_single_neg hn hmat, hmat⟩
  · rintro ⟨c, hc, hmat⟩
    have hi : (Fin.rev ⟨0, by omega⟩ : Fin n) ≠ Fin.rev (Fin.rev ⟨0, by omega⟩) := by
      rw [Fin.rev_rev]
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_rev] at this
      omega
    have hw : 2 • weight n (Fin.rev ⟨0, by omega⟩) = toStd n (-ggTopRoot n) := by
      rw [toStd_neg_ggTopRoot hn]
      have h0 : weight n (⟨0, by omega⟩ : Fin n) = -weight n (Fin.rev ⟨0, by omega⟩) := by
        have := weight_rev' (n := n) (i := Fin.rev (⟨0, by omega⟩ : Fin n))
        rwa [Fin.rev_rev] at this
      rw [h0, sub_neg_eq_add, two_nsmul]
    let y : SU σ n := longRootHom σ hi (Multiplicative.ofAdd ⟨c, hc⟩)
    have hy : y ∈ rootGroup σ hσ n (-ggTopRoot n) := longRootHom_mem hσ hi hw _
    have hy' : mat σ n y = 1 + single (Fin.rev ⟨0, by omega⟩) ⟨0, by omega⟩ c := by
      rw [mat_apply, coe_longRootHom, toAdd_ofAdd, longRootMatrix, Fin.rev_rev]
    exact (mat_injective (hy'.trans hmat.symm)) ▸ hy

theorem rckSU_exists_top {n : ℕ} (hn : 2 ≤ n) {c : F} (hc : c + σ c = 0) :
    ∃ x : SU σ n, mat σ n x = 1 + single ⟨0, by omega⟩ (Fin.rev ⟨0, by omega⟩) c := by
  have hi : (⟨0, by omega⟩ : Fin n) ≠ Fin.rev ⟨0, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_rev] at this
    omega
  refine ⟨longRootHom σ hi (Multiplicative.ofAdd ⟨c, hc⟩), ?_⟩
  rw [mat_apply, coe_longRootHom, toAdd_ofAdd, longRootMatrix]

theorem rckSU_exists_neg_top {n : ℕ} (hn : 2 ≤ n) {c : F} (hc : c + σ c = 0) :
    ∃ x : SU σ n, mat σ n x = 1 + single (Fin.rev ⟨0, by omega⟩) ⟨0, by omega⟩ c := by
  have hi : (Fin.rev ⟨0, by omega⟩ : Fin n) ≠ Fin.rev (Fin.rev ⟨0, by omega⟩) := by
    rw [Fin.rev_rev]
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_rev] at this
    omega
  refine ⟨longRootHom σ hi (Multiplicative.ofAdd ⟨c, hc⟩), ?_⟩
  rw [mat_apply, coe_longRootHom, toAdd_ofAdd, longRootMatrix, Fin.rev_rev]

end CFSG.StandardType.RCKRP
