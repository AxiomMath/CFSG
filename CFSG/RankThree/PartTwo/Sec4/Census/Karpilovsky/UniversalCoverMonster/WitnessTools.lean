module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.Heisenberg
public import CFSG.LocalAnalysis.SectionRank.SylowWitness

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

open CFSG.AGLEmbedding CFSG.AGLEmbedding.Norton.MON11_13 CFSG.SectionRank
  CFSG.SectionRank.LocalWitness
open scoped commutatorElement

section Closure

variable {X : Type} [Group X] [Finite X] {p : ℕ} [hp : Fact p.Prime]

private theorem isMulCommutative_of_card_pow_le_two {G : Type} [Group G] {m : ℕ}
    (hG : Nat.card G = p ^ m) (hm : m ≤ 2) : IsMulCommutative G := by
  interval_cases m
  · have : Subsingleton G := (Nat.card_eq_one_iff_unique.1 (by simpa using hG)).1
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  · have : IsCyclic G := isCyclic_of_prime_card (p := p) (by simpa using hG)
    infer_instance
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hG

theorem card_closure_pair_eq_sq {x y : X} (hxp : x ^ p = 1) (hyp : y ^ p = 1)
    (hxy : x * y = y * x) (hx1 : x ≠ 1) (hy : y ∉ Subgroup.zpowers x) :
    Nat.card (Subgroup.closure ({x, y} : Set X)) = p ^ 2 := by
  set P := Subgroup.closure ({x, y} : Set X) with hP
  have hel := isElemAbelian_closure_pair hxp hyp hxy
  have hPg : IsPGroup p P := fun g => ⟨1, Subtype.ext (by simpa using hel.2 g g.2)⟩
  obtain ⟨m, hm⟩ := hPg.exists_card_eq
  have hxP : x ∈ P := Subgroup.subset_closure (by simp)
  have hyP : y ∈ P := Subgroup.subset_closure (by simp)
  have hz : ⁅x, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hxy
  have hle : Nat.card P ≤ p ^ 2 := by
    let f : Fin p × Fin p → X := fun ij => x ^ (ij.1 : ℕ) * y ^ (ij.2 : ℕ)
    have hsub : (P : Set X) ⊆ Set.range f := by
      intro g hg
      obtain ⟨i, j, k, hi, hj, -, rfl⟩ := mem_closure_normalForm hp.out.pos hxp hyp
        (by rw [hz]; exact Commute.one_left _) (by rw [hz]; exact Commute.one_left _) hg
      exact ⟨(⟨i, hi⟩, ⟨j, hj⟩), by simp [f, hz]⟩
    calc Nat.card P = (P : Set X).ncard := Nat.card_coe_set_eq _
      _ ≤ (Set.range f).ncard := Set.ncard_le_ncard hsub (Set.finite_range f)
      _ ≤ Nat.card (Fin p × Fin p) := by
          rw [← Nat.card_coe_set_eq]; exact Finite.card_range_le f
      _ = p ^ 2 := by simp [sq]
  have hordx : orderOf x = p := orderOf_eq_prime hxp hx1
  have hzx : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hordx]
  have hzle : Subgroup.zpowers x ≤ P := by
    rw [Subgroup.zpowers_le]; exact hxP
  have hne : Subgroup.zpowers x ≠ P := fun h => hy (h ▸ hyP)
  have hlt : p < Nat.card P := by
    have hcard : Nat.card (Subgroup.zpowers x) ≤ Nat.card P :=
      Subgroup.card_le_of_le hzle
    rcases hcard.lt_or_eq with h | h
    · rwa [hzx] at h
    · exact absurd (Subgroup.eq_of_le_of_card_ge hzle h.ge) hne
  rw [hm] at hle hlt ⊢
  have hm2 : m ≤ 2 := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 hle
  have hm1 : 1 < m := by
    by_contra h
    push Not at h
    interval_cases m
    · have := hp.out.pos
      simp at hlt
      omega
    · simp at hlt
  congr 1
  omega

theorem card_closure_pair_eq_cube {x y : X} (hxp : x ^ p = 1) (hyp : y ^ p = 1)
    (hz : ⁅x, y⁆ ≠ 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) :
    Nat.card (Subgroup.closure ({x, y} : Set X)) = p ^ 3 := by
  set P := Subgroup.closure ({x, y} : Set X) with hP
  have hPg : IsPGroup p P := isPGroup_closure_of_central_commutator hp.out hxp hyp hzx hzy
  obtain ⟨m, hm⟩ := hPg.exists_card_eq
  have hle : Nat.card P ≤ p ^ 3 := by
    let f : Fin p × Fin p × Fin p → X := fun ijk =>
      x ^ (ijk.1 : ℕ) * y ^ (ijk.2.1 : ℕ) * ⁅x, y⁆ ^ (ijk.2.2 : ℕ)
    have hsub : (P : Set X) ⊆ Set.range f := by
      intro g hg
      obtain ⟨i, j, k, hi, hj, hk, rfl⟩ := mem_closure_normalForm hp.out.pos hxp hyp hzx hzy hg
      exact ⟨(⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩), rfl⟩
    calc Nat.card P = (P : Set X).ncard := Nat.card_coe_set_eq _
      _ ≤ (Set.range f).ncard := Set.ncard_le_ncard hsub (Set.finite_range f)
      _ ≤ Nat.card (Fin p × Fin p × Fin p) := by
          rw [← Nat.card_coe_set_eq]; exact Finite.card_range_le f
      _ = p ^ 3 := by simp [pow_succ]; ring
  rw [hm] at hle ⊢
  have hm3 : m ≤ 3 := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 hle
  have hm2 : ¬ m ≤ 2 := by
    intro h2
    have hcomm := isMulCommutative_of_card_pow_le_two (p := p) hm h2
    have hxP : x ∈ P := Subgroup.subset_closure (by simp)
    have hyP : y ∈ P := Subgroup.subset_closure (by simp)
    have := hcomm.is_comm.comm ⟨x, hxP⟩ ⟨y, hyP⟩
    exact hz (commutatorElement_eq_one_iff_mul_comm.2 (congrArg Subtype.val this))
  congr 1
  omega

end Closure

section Kernels

variable {X : Type} [Group X] [Finite X] {p : ℕ} [hp : Fact p.Prime]

theorem kernelTrivialAt_of_cubic_heisenberg {x y h : X} (hxp : x ^ p = 1) (hyp : y ^ p = 1)
    (hz1 : ⁅x, y⁆ ≠ 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (hS : ¬ p ^ 4 ∣ Nat.card X) {a b c d k l μ : ℕ}
    (hhx : h * x * h⁻¹ = x ^ a * y ^ b * ⁅x, y⁆ ^ k)
    (hhy : h * y * h⁻¹ = x ^ c * y ^ d * ⁅x, y⁆ ^ l) (hhz : h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ μ)
    (hdet : ((μ : ZMod p) * a - 1) * ((μ : ZMod p) * d - 1) - (μ : ZMod p) ^ 2 * b * c ≠ 0) :
    KernelTrivialAt X p :=
  kernelTrivialAt_of_cubic hxp hyp hz1 hzx hzy (card_closure_pair_eq_cube hxp hyp hz1 hzx hzy)
    hS hhx hhy hhz hdet

end Kernels

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
