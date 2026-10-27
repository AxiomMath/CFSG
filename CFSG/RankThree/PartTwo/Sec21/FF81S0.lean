module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

theorem pow_three_eq_one_of_isElemAb {G : Type} [Group G] {E : Subgroup G} {k : ℕ}
    (hE : IsElemAb 3 k E) {x : G} (hx : x ∈ E) : x ^ 3 = 1 := by
  have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hE.1.exponent_dvd_p ⟨x, hx⟩
  simpa using congrArg Subtype.val h

theorem ne_of_cycle {G : Type} [Group G] {b₁ b₂ b₃ c : G}
    (hE : IsElemAb 3 3 (Subgroup.closure ({b₁, b₂, b₃} : Set G)))
    (h12 : c * b₁ * c⁻¹ = b₂) (h23 : c * b₂ * c⁻¹ = b₃) (h31 : c * b₃ * c⁻¹ = b₁) : b₂ ≠ b₃ := by
  intro h
  subst h
  have h1 : b₁ = b₂ := h31.symm.trans h23
  subst h1
  have hcl : Subgroup.closure ({b₁, b₁, b₁} : Set G) = Subgroup.zpowers b₁ := by
    rw [Set.insert_eq_of_mem (by simp), Set.insert_eq_of_mem (by simp),
      Subgroup.zpowers_eq_closure]
  have hc := hE.2
  rw [hcl, Nat.card_zpowers] at hc
  have h3 : b₁ ^ 3 = 1 := by
    have := pow_three_eq_one_of_isElemAb hE (Subgroup.subset_closure (by simp) : b₁ ∈ _)
    exact this
  have := orderOf_le_of_pow_eq_one (by norm_num) h3
  omega

theorem ff81_s0 :
    ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G) (b₁ b₂ b₃ : G),
      FF81Basis b L B b₁ b₂ b₃ →
      ∃ s₀ : G, orderOf s₀ = 2 ∧ s₀ ∈ L ∧ s₀ ∈ CenS (Subgroup.closure {b, b₁, b₂ * b₃}) ∧
        s₀ * (b₂ * b₃ ^ 2) * s₀⁻¹ = (b₂ * b₃ ^ 2)⁻¹ := by
  intro G _ _ b L B b₁ b₂ b₃ hB
  obtain ⟨n, hnL, hn1, hn2, hn3⟩ := hB.monoL
  set B₁ := Subgroup.closure ({b₁, b₂, b₃} : Set G) with hB₁
  have hmem1 : b₁ ∈ B₁ := Subgroup.subset_closure (by simp)
  have hmem2 : b₂ ∈ B₁ := Subgroup.subset_closure (by simp)
  have hmem3 : b₃ ∈ B₁ := Subgroup.subset_closure (by simp)
  have hcube : ∀ x ∈ B₁, x ^ 3 = 1 := fun x hx => pow_three_eq_one_of_isElemAb hB.elem hx
  have hcomm : ∀ x ∈ B₁, ∀ y ∈ B₁, x * y = y * x := fun x hx y hy => by
    exact congrArg Subtype.val
      (hB.elem.1.toIsMulCommutative.is_comm.comm (⟨x, hx⟩ : B₁) ⟨y, hy⟩)
  have hfix : ∀ x ∈ B₁, n ^ 2 * x * (n ^ 2)⁻¹ = x := by
    have hle : B₁ ≤ Subgroup.centralizer {n ^ 2} := by
      refine (Subgroup.closure_le _).mpr ?_
      intro x hx
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases hx with h | h | h <;> rw [h]
      · calc b₁ * n ^ 2 = n * (n * b₁ * n⁻¹) * n⁻¹ * n ^ 2 := by rw [hn1, hn1]
          _ = n ^ 2 * b₁ := by simp only [sq]; group
      · calc b₂ * n ^ 2 = n * (n * b₂ * n⁻¹) * n⁻¹ * n ^ 2 := by rw [hn2, hn3]
          _ = n ^ 2 * b₂ := by simp only [sq]; group
      · calc b₃ * n ^ 2 = n * (n * b₃ * n⁻¹) * n⁻¹ * n ^ 2 := by rw [hn3, hn2]
          _ = n ^ 2 * b₃ := by simp only [sq]; group
    intro x hx
    have := Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
    rw [← this]; group
  have hn2B : n ^ 2 ∈ B₁ := by
    refine hB.selfcen.le ⟨L.pow_mem hnL 2, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    have := hfix x hx
    calc x * n ^ 2 = n ^ 2 * x * (n ^ 2)⁻¹ * n ^ 2 := by rw [this]
      _ = n ^ 2 * x := by group
  have hn6 : n ^ 6 = 1 := by
    have := hcube _ hn2B
    rw [← pow_mul] at this
    exact this
  set s := n ^ 3 with hs
  have hsL : s ∈ L := L.pow_mem hnL 3
  have hsconj : ∀ x ∈ B₁, s * x * s⁻¹ = n * x * n⁻¹ := fun x hx => by
    calc s * x * s⁻¹ = n * (n ^ 2 * x * (n ^ 2)⁻¹) * n⁻¹ := by rw [hs]; group
      _ = n * x * n⁻¹ := by rw [hfix x hx]
  have hs1 := hsconj b₁ hmem1
  have hs2 := hsconj b₂ hmem2
  have hs3 := hsconj b₃ hmem3
  rw [hn1] at hs1
  rw [hn2] at hs2
  rw [hn3] at hs3
  have hsq : s ^ 2 = 1 := by rw [hs, ← pow_mul]; exact hn6
  have hne : s ≠ 1 := fun h1 => by
    rw [h1] at hs2
    simp at hs2
    obtain ⟨c, -, -, hc1, hc2, hc3⟩ := hB.mono.2.2.2.2.2
    exact ne_of_cycle hB.elem hc1 hc2 hc3 hs2
  have hsb : s * b = b * s :=
    Subgroup.mem_centralizer_singleton_iff.mp (hB.hyp.hLC hsL)
  have hcomm23 := hcomm b₂ hmem2 b₃ hmem3
  refine ⟨s, orderOf_eq_prime hsq hne, hsL, ?_, ?_⟩
  · refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    have hle : Subgroup.closure ({b, b₁, b₂ * b₃} : Set G) ≤ Subgroup.centralizer {s} := by
      refine (Subgroup.closure_le _).mpr ?_
      intro y hy
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases hy with h | h | h <;> rw [h]
      · exact hsb.symm
      · calc b₁ * s = (s * b₁ * s⁻¹) * s := by rw [hs1]
          _ = s * b₁ := by group
      · calc b₂ * b₃ * s = (s * b₃ * s⁻¹) * (s * b₂ * s⁻¹) * s := by rw [hs2, hs3, hcomm23]
          _ = s * (b₃ * b₂) := by group
          _ = s * (b₂ * b₃) := by rw [hcomm23]
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  · have h2 : b₂ ^ 3 = 1 := hcube _ hmem2
    have h3 : b₃ ^ 3 = 1 := hcube _ hmem3
    have hinv : b₃ * b₂ ^ 2 = (b₂ * b₃ ^ 2)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      calc b₃ * b₂ ^ 2 * (b₂ * b₃ ^ 2) = b₃ * b₂ ^ 3 * b₃ ^ 2 := by
            simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := by
            rw [h2, mul_one, ← h3]
            simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    calc s * (b₂ * b₃ ^ 2) * s⁻¹ = (s * b₂ * s⁻¹) * (s * b₃ ^ 2 * s⁻¹) := by group
      _ = b₃ * b₂ ^ 2 := by rw [← conj_pow, hs2, hs3]
      _ = (b₂ * b₃ ^ 2)⁻¹ := hinv

end CFSG.RankThree.PartTwo.Sec21.FF81
