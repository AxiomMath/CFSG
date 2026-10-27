module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec16.KS1622GTwoProof

open scoped commutatorElement

section Heis

variable {M : Type*} [Group M] {a b : M}

theorem pow_mul_pow_comm (hc3 : ⁅a, b⁆ ^ 3 = 1) (hca : Commute ⁅a, b⁆ a)
    (hcb : Commute ⁅a, b⁆ b) (i j : ℕ) :
    b ^ j * a ^ i = a ^ i * b ^ j * ⁅a, b⁆ ^ (2 * i * j) := by
  set c := ⁅a, b⁆ with hc
  have hba : b * a = a * b * c ^ 2 := by
    have h1 : c * (b * a) = a * b := by
      rw [hc, commutatorElement_def]
      group
    have h2 : c ^ 2 * c = 1 := by rw [← pow_succ, hc3]
    calc b * a = (c ^ 2 * c) * (b * a) := by rw [h2, one_mul]
      _ = c ^ 2 * (a * b) := by rw [mul_assoc, h1]
      _ = a * b * c ^ 2 := by
        rw [((hca.pow_left 2).mul_right (hcb.pow_left 2)).eq]
  have hbai : ∀ i : ℕ, b * a ^ i = a ^ i * b * c ^ (2 * i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      calc b * a ^ (i + 1) = (b * a ^ i) * a := by rw [pow_succ, mul_assoc]
        _ = a ^ i * b * (c ^ (2 * i) * a) := by rw [ih, mul_assoc]
        _ = a ^ i * (b * a) * c ^ (2 * i) := by
          rw [((hca.pow_left (2 * i)).eq)]
          group
        _ = a ^ (i + 1) * b * c ^ (2 * (i + 1)) := by
          rw [hba, show 2 * (i + 1) = 2 + 2 * i by ring, pow_add c 2, pow_succ]
          group
  induction j with
  | zero => simp
  | succ j ih =>
    calc b ^ (j + 1) * a ^ i = b * (b ^ j * a ^ i) := by rw [pow_succ', mul_assoc]
      _ = (b * a ^ i) * b ^ j * c ^ (2 * i * j) := by rw [ih]; group
      _ = a ^ i * b * (c ^ (2 * i) * b ^ j) * c ^ (2 * i * j) := by rw [hbai]; group
      _ = a ^ i * b ^ (j + 1) * c ^ (2 * i * (j + 1)) := by
        rw [((hcb.pow_left (2 * i)).pow_right j).eq,
          show 2 * i * (j + 1) = 2 * i + 2 * i * j by ring, pow_add c (2 * i), pow_succ' b j]
        group

theorem pow_three_eq_one_of_mem_closure (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hca : Commute ⁅a, b⁆ a) (hcb : Commute ⁅a, b⁆ b) :
    ∀ g ∈ Subgroup.closure ({a, b} : Set M), g ^ 3 = 1 := by
  set c := ⁅a, b⁆ with hc
  have hconj : ∀ n : ℕ, a ^ n * b * (a ^ n)⁻¹ = c ^ n * b := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : a * b * a⁻¹ = c * b := by
        rw [hc, commutatorElement_def]
        group
      calc a ^ (n + 1) * b * (a ^ (n + 1))⁻¹ = a * (a ^ n * b * (a ^ n)⁻¹) * a⁻¹ := by
            rw [pow_succ']
            group
        _ = c ^ n * (a * b * a⁻¹) := by
          rw [ih, ← mul_assoc, ((hca.pow_left n).eq).symm]
          group
        _ = c ^ (n + 1) * b := by rw [h1, pow_succ, mul_assoc]
  have hc3 : c ^ 3 = 1 := by
    have h := hconj 3
    rw [ha, one_mul, inv_one, mul_one] at h
    exact (mul_eq_right.mp h.symm)
  have hcomm : ∀ i j : ℕ, b ^ j * a ^ i = a ^ i * b ^ j * c ^ (2 * i * j) :=
    pow_mul_pow_comm hc3 hca hcb
  have hcab : ∀ (k i j : ℕ), c ^ k * (a ^ i * b ^ j) = a ^ i * b ^ j * c ^ k := fun k i j =>
    ((hca.pow_pow k i).mul_right (hcb.pow_pow k j)).eq
  have hmul : ∀ i j k i' j' k' : ℕ, (a ^ i * b ^ j * c ^ k) * (a ^ i' * b ^ j' * c ^ k') =
      a ^ (i + i') * b ^ (j + j') * c ^ (k + k' + 2 * i' * j) := by
    intro i j k i' j' k'
    calc (a ^ i * b ^ j * c ^ k) * (a ^ i' * b ^ j' * c ^ k') =
        a ^ i * b ^ j * (c ^ k * (a ^ i' * b ^ j')) * c ^ k' := by group
      _ = a ^ i * (b ^ j * a ^ i') * b ^ j' * c ^ k * c ^ k' := by rw [hcab]; group
      _ = a ^ i * a ^ i' * b ^ j * (c ^ (2 * i' * j) * b ^ j') * c ^ k * c ^ k' := by
        rw [hcomm]; group
      _ = a ^ (i + i') * b ^ (j + j') * c ^ (k + k' + 2 * i' * j) := by
        rw [((hcb.pow_left _).pow_right j').eq, pow_add a, pow_add b,
          show k + k' + 2 * i' * j = 2 * i' * j + (k + k') by ring, pow_add c, pow_add c]
        group
  have hcube : ∀ i j k : ℕ, (a ^ i * b ^ j * c ^ k) ^ 3 = 1 := by
    intro i j k
    rw [pow_succ, pow_two, hmul, hmul, show i + i + i = 3 * i by ring,
      show j + j + j = 3 * j by ring, pow_mul, pow_mul, ha, hb, one_pow, one_pow, one_mul,
      one_mul, show k + k + 2 * i * j + k + 2 * i * (j + j) = 3 * (k + 2 * i * j) by ring,
      pow_mul, hc3, one_pow]
  have hform : ∀ g ∈ Subgroup.closure ({a, b} : Set M),
      ∃ i j k : ℕ, g = a ^ i * b ^ j * c ^ k := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨1, 0, 0, by simp⟩
      · exact ⟨0, 1, 0, by simp⟩
    | one => exact ⟨0, 0, 0, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨i, j, k, rfl⟩ := hx
      obtain ⟨i', j', k', rfl⟩ := hy
      exact ⟨_, _, _, hmul i j k i' j' k'⟩
    | inv x _ hx =>
      obtain ⟨i, j, k, rfl⟩ := hx
      have h3 := hcube i j k
      have hinv : (a ^ i * b ^ j * c ^ k)⁻¹ =
          (a ^ i * b ^ j * c ^ k) * (a ^ i * b ^ j * c ^ k) := by
        rw [inv_eq_iff_mul_eq_one, ← pow_three]
        exact h3
      exact ⟨i + i, j + j, k + k + 2 * i * j, by rw [hinv, hmul]⟩
  intro g hg
  obtain ⟨i, j, k, rfl⟩ := hform g hg
  exact hcube i j k

end Heis

end CFSG.RankThree.PartTwo.Sec16.KS1622GTwoProof

