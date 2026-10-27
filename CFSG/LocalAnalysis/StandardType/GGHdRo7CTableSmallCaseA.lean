module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CTableSmallAux

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7CSmallAux_case_c1_k1
    (hT : C2ReflTrickLeaf) (hSp : C2SuppTwoLeaf) {n : ℕ} (hn : 5 ≤ n)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hPA : ∀ a, C2SP 3 b a → a ∈ A)
    (hStab : ∀ a ∈ A, a (b 0) = b 0 → C2SP 3 b a)
    (r : V ≃ₗ[ZMod 3] V) (u : V) (φ : V →ₗ[ZMod 3] ZMod 3)
    (hnf : C2ReflNF 3 b A r u φ)
    (hcoef : ∀ i, i ≠ 0 → φ (b i) = 1 * b.coord i u)
    (S : Finset (Fin (n + 1)))
    (hS_mem : ∀ i, i ∈ S ↔ i ≠ 0 ∧ b.coord i u ≠ 0)
    (hScard : S.card = 1) (hu0val : b.coord 0 u = 1) :
    C2Swap 3 b r := by
  obtain ⟨i, hSi⟩ := Finset.card_eq_one.mp hScard
  have hi : i ∈ S := by rw [hSi]; simp
  have hine : i ≠ 0 := ((hS_mem i).mp hi).1
  set a : ZMod 3 := b.coord i u with ha
  have hai : a ≠ 0 := by rw [ha]; exact ((hS_mem i).mp hi).2
  have hi1 : a = 1 ∨ a = -1 := hdRo7CSmallAux_zmod3_ne_zero hai
  have hisq : a * a = 1 := hdRo7CSmallAux_zmod3_sq hai
  have h0i : (0 : Fin (n + 1)) ≠ i := fun h => hine h.symm
  have hu : u = b 0 + a • b i := by
    conv_lhs => rw [hdRo7CSmallAux_sum_repr_insert b u S hS_mem]
    rw [hSi, Finset.sum_insert (by simpa [Finset.mem_singleton] using h0i),
      Finset.sum_singleton, hu0val, ← ha, one_smul]
  refine ⟨i, -a, hine, ?_, ?_, ?_, ?_⟩
  · rcases hi1 with h | h <;> rw [h] <;> norm_num
  · rw [hnf.hform, hnf.hφ0]
    conv_lhs => rw [hu]
    rw [one_smul, neg_smul]
    abel
  · have hau : a • u = a • b 0 + b i := by
      rw [hu, smul_add, smul_smul, hisq, one_smul]
    rw [hnf.hform, hcoef i hine, one_mul, ← ha, hau, neg_smul]
    abel
  · intro j hj0 hji
    have hjS : j ∉ S := by
      intro hj; rw [hSi, Finset.mem_singleton] at hj; exact hji hj
    have hcj : b.coord j u = 0 := by
      by_contra hc
      exact hjS ((hS_mem j).mpr ⟨hj0, hc⟩)
    rw [hnf.hform, hcoef j hj0, hcj]
    simp

theorem hdRo7CSmallAux_case_c1_k2
    (hT : C2ReflTrickLeaf) (hSp : C2SuppTwoLeaf) {n : ℕ} (hn : 5 ≤ n)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hPA : ∀ a, C2SP 3 b a → a ∈ A)
    (hStab : ∀ a ∈ A, a (b 0) = b 0 → C2SP 3 b a)
    (r : V ≃ₗ[ZMod 3] V) (u : V) (φ : V →ₗ[ZMod 3] ZMod 3)
    (hnf : C2ReflNF 3 b A r u φ)
    (hcoef : ∀ i, i ≠ 0 → φ (b i) = 1 * b.coord i u)
    (S : Finset (Fin (n + 1)))
    (hS_mem : ∀ i, i ∈ S ↔ i ≠ 0 ∧ b.coord i u ≠ 0)
    (hScard : S.card = 2) (hu0val : b.coord 0 u = 0) :
    False := by
  exfalso
  exact hnf.hu0 hu0val

theorem hdRo7CSmallAux_case_cm1_k1
    (hT : C2ReflTrickLeaf) (hSp : C2SuppTwoLeaf) {n : ℕ} (hn : 5 ≤ n)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hPA : ∀ a, C2SP 3 b a → a ∈ A)
    (hStab : ∀ a ∈ A, a (b 0) = b 0 → C2SP 3 b a)
    (r : V ≃ₗ[ZMod 3] V) (u : V) (φ : V →ₗ[ZMod 3] ZMod 3)
    (hnf : C2ReflNF 3 b A r u φ)
    (hcoef : ∀ i, i ≠ 0 → φ (b i) = -1 * b.coord i u)
    (S : Finset (Fin (n + 1)))
    (hS_mem : ∀ i, i ∈ S ↔ i ≠ 0 ∧ b.coord i u ≠ 0)
    (hu0val : b.coord 0 u = 0) :
    False := by
  exfalso
  exact hnf.hu0 hu0val

theorem hdRo7CSmallAux_case_cm1_k3
    (hT : C2ReflTrickLeaf) (hSp : C2SuppTwoLeaf) {n : ℕ} (hn : 5 ≤ n)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hPA : ∀ a, C2SP 3 b a → a ∈ A)
    (hStab : ∀ a ∈ A, a (b 0) = b 0 → C2SP 3 b a)
    (r : V ≃ₗ[ZMod 3] V) (u : V) (φ : V →ₗ[ZMod 3] ZMod 3)
    (hnf : C2ReflNF 3 b A r u φ)
    (hcoef : ∀ i, i ≠ 0 → φ (b i) = -1 * b.coord i u)
    (S : Finset (Fin (n + 1)))
    (hS_mem : ∀ i, i ∈ S ↔ i ≠ 0 ∧ b.coord i u ≠ 0)
    (hScard : S.card = 3) (hu0val : b.coord 0 u = -1) :
    False := by
  have h0S : (0 : Fin (n + 1)) ∉ S := by rw [hS_mem]; simp
  exact hdRo7CSmallAux_case_m13 hn b A hPA hStab hT hSp r u φ hnf hcoef S hS_mem h0S hScard hu0val

end CFSG.StandardType.HdRo7C
