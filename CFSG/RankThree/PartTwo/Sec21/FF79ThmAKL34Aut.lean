module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.KL34

open CFSG.ComponentClassification.PSL3Four


theorem exists_aut_rep {E : Type} [Group E] (ε : E ≃* ↥S) (φ : MulAut E) :
    ∃ r ∈ R, (∀ x : E, ((ε (φ x) : S) : Equiv.Perm (Fin 42)) =
      r * (ε x : Equiv.Perm (Fin 42)) * r⁻¹) ∧ ∀ k : ℕ, φ ^ k = 1 ↔ r ^ k = 1 := by
  obtain ⟨e, he, -⟩ := full_automorphism_action
  let α : MulAut ↥S := MulAut.congr ε φ
  refine ⟨((e.symm α : R) : Equiv.Perm (Fin 42)), (e.symm α).2, ?_, ?_⟩
  · intro x
    have h1 := he (e.symm α) (ε x)
    rw [MulEquiv.apply_symm_apply, Subgroup.coe_inv] at h1
    rw [← h1]
    simp [α, MulAut.congr_apply]
  · intro k
    have h1 : φ ^ k = 1 ↔ α ^ k = 1 := by
      rw [← map_pow, ← map_one (MulAut.congr ε)]
      exact (MulAut.congr ε).injective.eq_iff.symm
    have h2 : α ^ k = 1 ↔ ((e.symm α : R) : Equiv.Perm (Fin 42)) ^ k = 1 := by
      rw [← Subgroup.coe_pow, OneMemClass.coe_eq_one]
      constructor
      · intro h
        rw [← map_pow, h, map_one]
      · intro h
        apply e.symm.injective
        rw [map_pow, map_one]
        exact h
    exact h1.trans h2

theorem exists_equiv_map_eq {E : Type} [Group E] (ε : E ≃* ↥S) {P : Subgroup E}
    (hP9 : Nat.card P = 9) {A₀ : Subgroup (Equiv.Perm (Fin 42))} (hA₀S : A₀ ≤ S)
    (hA₀9 : Nat.card A₀ = 9) :
    ∃ ε' : E ≃* ↥S, (∀ a ∈ P, ((ε' a : S) : Equiv.Perm (Fin 42)) ∈ A₀) ∧
      (∀ c ∈ A₀, ∃ b ∈ P, ((ε' b : S) : Equiv.Perm (Fin 42)) = c) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS : Nat.card S = 20160 := card_S
  let P₀ : Subgroup ↥S := A₀.subgroupOf S
  let P₁ : Subgroup ↥S := P.map ε.toMonoidHom
  have hP₀ : Nat.card P₀ = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀S).toEquiv, hA₀9]
  have hP₁ : Nat.card P₁ = 9 := by
    rw [Subgroup.card_map_of_injective ε.injective, hP9]
  have hidx : ∀ Q : Subgroup ↥S, Nat.card Q = 9 → ¬ 3 ∣ Q.index := by
    intro Q hQ
    have h := Q.index_mul_card
    rw [hQ, hS] at h
    have : Q.index = 2240 := by omega
    rw [this]
    norm_num
  have hp : ∀ Q : Subgroup ↥S, Nat.card Q = 9 → IsPGroup 3 Q := fun Q hQ =>
    IsPGroup.of_card (n := 2) (by rw [hQ]; norm_num)
  let Q₀ : Sylow 3 ↥S := (hp P₀ hP₀).toSylow (hidx P₀ hP₀)
  let Q₁ : Sylow 3 ↥S := (hp P₁ hP₁).toSylow (hidx P₁ hP₁)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥S Q₀ Q₁
  have hQg : P₁ = P₀.map (MulAut.conj g).toMonoidHom := by
    have h1 : (Q₁ : Subgroup ↥S) = (Q₀ : Subgroup ↥S).map (MulAut.conj g).toMonoidHom := by
      rw [← hg, Sylow.coe_subgroup_smul]
      rfl
    simpa [Q₀, Q₁, IsPGroup.toSylow_coe] using h1
  refine ⟨ε.trans (MulAut.conj g⁻¹), ?_, ?_⟩
  · intro a ha
    have h1 : ε a ∈ P₁ := ⟨a, ha, rfl⟩
    rw [hQg] at h1
    obtain ⟨p, hp0, hpe⟩ := h1
    have h2 : ((ε.trans (MulAut.conj g⁻¹)) a : ↥S) = p := by
      have : ε a = g * p * g⁻¹ := hpe.symm
      simp [MulEquiv.trans_apply, MulAut.conj_apply, this, mul_assoc]
    rw [h2]
    exact Subgroup.mem_subgroupOf.1 hp0
  · intro a ha
    have h1 : (g * ⟨a, hA₀S ha⟩ * g⁻¹ : ↥S) ∈ P₁ := by
      rw [hQg]
      exact ⟨⟨a, hA₀S ha⟩, Subgroup.mem_subgroupOf.2 ha, rfl⟩
    obtain ⟨k, hk, hke⟩ := h1
    refine ⟨k, hk, ?_⟩
    have : ε k = g * ⟨a, hA₀S ha⟩ * g⁻¹ := hke
    simp [MulEquiv.trans_apply, MulAut.conj_apply, this, mul_assoc]

end CFSG.RankThree.PartTwo.Sec21.FF79.KL34
