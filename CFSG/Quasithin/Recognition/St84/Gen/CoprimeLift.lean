module

public import Mathlib.GroupTheory.PGroup

import CFSG.Quasithin.Recognition.St84.Gen.CoprimeComplement

public section

namespace CFSG.Quasithin.F112R.St84

variable {G : Type*} [Group G]

theorem exists_mul_mem_centralizer_of_odd [Finite G] {Q J : Subgroup G} (hQ : IsPGroup 2 Q)
    (hJ : Odd (Nat.card J)) (hJQ : J ≤ Subgroup.normalizer (Q : Set G)) {c : G}
    (hcQ : c ∈ Subgroup.normalizer (Q : Set G)) (hc : ∀ j ∈ J, j * c * j⁻¹ * c⁻¹ ∈ Q) :
    ∃ q ∈ Q, q * c ∈ Subgroup.centralizer (J : Set G) := by
  classical
  let N : Subgroup G := Subgroup.normalizer (Q : Set G)
  let M : Subgroup G :=
    { carrier := {l : G | l ∈ N ∧ ∀ j ∈ J, j * l * j⁻¹ * l⁻¹ ∈ Q}
      one_mem' := by
        refine ⟨N.one_mem, fun j hj => ?_⟩
        simp
      mul_mem' := by
        rintro l₁ l₂ ⟨hl₁N, hl₁⟩ ⟨hl₂N, hl₂⟩
        refine ⟨N.mul_mem hl₁N hl₂N, fun j hj => ?_⟩
        have h₁ : j * l₁ * j⁻¹ * l₁⁻¹ ∈ Q := hl₁ j hj
        have h₂ : j * l₂ * j⁻¹ * l₂⁻¹ ∈ Q := hl₂ j hj
        have hconj : l₁ * (j * l₂ * j⁻¹ * l₂⁻¹) * l₁⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.mp hl₁N _).mp h₂
        have heq : j * (l₁ * l₂) * j⁻¹ * (l₁ * l₂)⁻¹ =
            (j * l₁ * j⁻¹ * l₁⁻¹) * (l₁ * (j * l₂ * j⁻¹ * l₂⁻¹) * l₁⁻¹) := by
          group
        rw [heq]
        exact Q.mul_mem h₁ hconj
      inv_mem' := by
        rintro l ⟨hlN, hl⟩
        refine ⟨N.inv_mem hlN, fun j hj => ?_⟩
        have h₁ : j * l * j⁻¹ * l⁻¹ ∈ Q := hl j hj
        have hconj : l * (j * l⁻¹ * j⁻¹ * l) * l⁻¹ ∈ Q := by
          have heq : l * (j * l⁻¹ * j⁻¹ * l) * l⁻¹ = (j * l * j⁻¹ * l⁻¹)⁻¹ := by
            group
          rw [heq]
          exact Q.inv_mem h₁
        have hx : j * l⁻¹ * j⁻¹ * l ∈ Q :=
          (Subgroup.mem_normalizer_iff.mp hlN (j * l⁻¹ * j⁻¹ * l)).mpr hconj
        simpa using hx }
  have hQM : Q ≤ M := by
    intro q hq
    refine ⟨Subgroup.le_normalizer hq, fun j hj => ?_⟩
    have hconj : j * q * j⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hJQ hj) q).mp hq
    exact Q.mul_mem hconj (Q.inv_mem hq)
  have hcM : c ∈ M := ⟨hcQ, hc⟩
  have hLM : Q ⊔ Subgroup.zpowers c ≤ M :=
    sup_le hQM (Subgroup.zpowers_le.mpr hcM)
  have hcomm : ∀ j ∈ J, ∀ l ∈ Q ⊔ Subgroup.zpowers c,
      j * l * j⁻¹ * l⁻¹ ∈ Q :=
    fun j hj l hl => (hLM hl).2 j hj
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hcop : Nat.Coprime (Nat.card J) (Nat.card Q) := by
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hJ)
  obtain ⟨q, hqQ, c', hc', hceq⟩ :=
    exists_mul_mem_inf_centralizer_of_coprime (L := Q ⊔ Subgroup.zpowers c)
      (Q := Q) (H := J) le_sup_left
      (sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hcQ)) hJQ hcop hcomm
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
  refine ⟨q⁻¹, Q.inv_mem hqQ, ?_⟩
  have hqc : q⁻¹ * c = c' := by rw [hceq]; group
  rw [hqc]
  exact hc'.2

end CFSG.Quasithin.F112R.St84

end
