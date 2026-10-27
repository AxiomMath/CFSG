module

public import CFSG.LocalAnalysis.StandardType.GGEvenSignedReflDatum
public import CFSG.LocalAnalysis.StandardType.GGDRootFork
public import CFSG.LocalAnalysis.StandardType.GGHLDefs

public section

namespace CFSG.StandardType

@[expose] def signAt {k : ℕ} (y a : Fin k) : ℤ := if a = y then -1 else 1

theorem signAt_mul_self {k : ℕ} (y a : Fin k) : signAt y a * signAt y a = 1 := by
  unfold signAt
  split_ifs <;> norm_num

theorem signAt_mul_fork {k : ℕ} {Λ : Type} [DecidableEq Λ] {ρ : Λ → Fin k → ℤ} {y : Fin k}
    {i j : Λ} (hij : i ≠ j) (hj : ρ j = Function.update (ρ i) y (-ρ i y))
    (hm : ∀ m, m ≠ i → m ≠ j → ρ m y = 0) (m : Λ) (a : Fin k) :
    signAt y a * ρ m a = ρ (Equiv.swap i j m) a := by
  have hi : ρ i = Function.update (ρ j) y (-ρ j y) := by
    rw [hj]
    funext x
    by_cases hx : x = y
    · subst hx
      simp
    · simp [Function.update_of_ne hx]
  unfold signAt
  by_cases hmi : m = i
  · subst hmi
    rw [Equiv.swap_apply_left, hj]
    by_cases ha : a = y
    · subst ha
      simp
    · rw [ite_eq_right ha, one_mul, Function.update_of_ne ha]
  · by_cases hmj : m = j
    · subst hmj
      rw [Equiv.swap_apply_right, hi]
      by_cases ha : a = y
      · subst ha
        simp
      · rw [ite_eq_right ha, one_mul, Function.update_of_ne ha]
    · rw [Equiv.swap_apply_of_ne_of_ne hmi hmj]
      by_cases ha : a = y
      · subst ha
        rw [hm m hmi hmj, mul_zero]
      · rw [ite_eq_right ha, one_mul]

theorem exists_signChange_mem_ggDiagramSet {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {k : ℕ} (b : Module.Basis (Fin k) (ZMod p) V)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V) (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hrD : ∀ i, ∃ (σ : Equiv.Perm (Fin k)) (c : Fin k → ZMod p), (∀ a, c a = 1 ∨ c a = -1) ∧
      ∏ a, c a = 1 ∧ ∀ a, b a - α i (b a) • h i = c a • b (σ a))
    (hk : 3 ≤ k) (hcard : k ≤ Fintype.card Λ) :
    ∃ (y : Fin k) (g : V ≃ₗ[ZMod p] V), g ∈ ggDiagramSet h α ∧ g (b y) = -b y ∧
      ∀ a, a ≠ y → g (b a) = b a := by
  obtain ⟨l, ρ, hl, hρ, hgram, hh, hα⟩ :=
    exists_dRoots_of_evenSignedRefl hp2 b hM hC h α hpair hrD (by omega)
  obtain ⟨y, i, j, hij, -, hj, hm⟩ := exists_dRoot_fork hM hC ρ hρ hgram hk hcard
  have hs := signAt_mul_fork hij hj hm
  let u : Fin k → (ZMod p)ˣ := fun a => if a = y then -1 else 1
  have hu : ∀ a, ((u a : (ZMod p)ˣ) : ZMod p) = ((signAt y a : ℤ) : ZMod p) := by
    intro a
    simp only [u, signAt]
    split_ifs <;> simp
  let g : V ≃ₗ[ZMod p] V := b.equiv (b.unitsSMul u) (Equiv.refl _)
  have hg : ∀ a, g (b a) = ((signAt y a : ℤ) : ZMod p) • b a := by
    intro a
    simp only [g, Module.Basis.equiv_apply, Equiv.refl_apply, Module.Basis.unitsSMul_apply]
    rw [← hu a]
    rfl
  have hgr : ∀ v a, b.repr (g v) a = ((signAt y a : ℤ) : ZMod p) * b.repr v a := by
    intro v a
    conv_lhs => rw [← b.sum_repr v]
    simp only [map_sum, map_smul, hg, Module.Basis.repr_self, Finsupp.smul_single,
      Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single a]
    · simp [mul_comm]
    · intro x _ hx
      rw [ite_eq_right hx]
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  refine ⟨y, g, ⟨Equiv.swap i j, fun m => ⟨?_, fun v => ?_⟩⟩, ?_, fun a ha => ?_⟩
  · rw [hh m, hh, map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, hg, smul_smul, ← hs m a, Int.cast_mul, mul_comm]
  · rw [hα, hα]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hgr, ← hs m a, Int.cast_mul]
    have h1 := congrArg (fun z : ℤ => (z : ZMod p)) (signAt_mul_self y a)
    simp only [Int.cast_mul, Int.cast_one] at h1
    linear_combination (((ρ m a : ℤ) : ZMod p) * b.repr v a) * h1
  · rw [hg]
    simp [signAt]
  · rw [hg]
    simp [signAt, ha]

end CFSG.StandardType

end
