module

public import CFSG.RankThree.OrthogonalInvolutions.OmegaClasses

public section

namespace CFSG.RankThree.OrthogonalInvolutions

open Module QuadraticMap

theorem orthogonal_involution_suzuki_types {K : Type*} [Field K] [Finite K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hm : 1 ≤ m) (hn : finrank K V = 2 * m) :
    ((∀ g, g ∈ omegaGroup Q hQ ↔
        g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ Even (finrank K (commSpace g))) ∧
      omegaGroup Q hQ ≤ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      (omegaGroup Q hQ).relIndex (TauCeti.QuadraticMap.orthogonalGroup Q) = 2 ∧
      (∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, ∀ h ∈ TauCeti.QuadraticMap.orthogonalGroup Q,
        (finrank K (commSpace (g * h)) : ZMod 2) =
          finrank K (commSpace g) + finrank K (commSpace h)) ∧
      (dicksonHom Q hQ).ker =
        (omegaGroup Q hQ).subgroupOf (TauCeti.QuadraticMap.orthogonalGroup Q)) ∧
    ∀ t ∈ TauCeti.QuadraticMap.orthogonalGroup Q, orderOf t = 2 →
      ((∀ x ∈ commSpace t, ∀ y ∈ commSpace t, polar Q x y = 0) ∧
        fixSpace t = LinearMap.BilinForm.orthogonal Q.polarBilin (commSpace t) ∧
        1 ≤ finrank K (commSpace t) ∧ finrank K (commSpace t) ≤ m) ∧
      ((∀ v, Q (t v - v) = polar Q (t v) v) ∧
        ((∀ x ∈ commSpace t, Q x = 0) ↔ ∀ v, polar Q (t v) v = 0) ∧
        (Odd (finrank K (commSpace t)) → ∃ x ∈ commSpace t, Q x ≠ 0) ∧
        (suzukiLetter Q t = .a ↔
          Even (finrank K (commSpace t)) ∧ ∀ x ∈ commSpace t, Q x = 0) ∧
        (suzukiLetter Q t = .b ↔ Odd (finrank K (commSpace t))) ∧
        (suzukiLetter Q t = .c ↔
          Even (finrank K (commSpace t)) ∧ ∃ x ∈ commSpace t, Q x ≠ 0)) ∧
      (∀ s ∈ TauCeti.QuadraticMap.orthogonalGroup Q, orderOf s = 2 →
        ((∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g * t * g⁻¹ = s) ↔
          suzukiLetter Q s = suzukiLetter Q t ∧
            finrank K (commSpace s) = finrank K (commSpace t))) ∧
      (t ∈ omegaGroup Q hQ ↔ suzukiLetter Q t = .a ∨ suzukiLetter Q t = .c) ∧
      (t ∈ omegaGroup Q hQ →
        (¬(suzukiLetter Q t = .a ∧ finrank K (commSpace t) = m) →
          {x | ∃ g ∈ omegaGroup Q hQ, g * t * g⁻¹ = x} =
            {x | ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g * t * g⁻¹ = x}) ∧
        (suzukiLetter Q t = .a ∧ finrank K (commSpace t) = m →
          IsGreatest {d | ∃ U : Submodule K V, (∀ x ∈ U, Q x = 0) ∧ finrank K U = d} m ∧
          (∃ s₁ ∈ {x | ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g * t * g⁻¹ = x},
            ∃ s₂ ∈ {x | ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g * t * g⁻¹ = x},
              {x | ∃ g ∈ omegaGroup Q hQ, g * s₁ * g⁻¹ = x} ≠
                  {x | ∃ g ∈ omegaGroup Q hQ, g * s₂ * g⁻¹ = x} ∧
                {x | ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g * t * g⁻¹ = x} =
                  {x | ∃ g ∈ omegaGroup Q hQ, g * s₁ * g⁻¹ = x} ∪
                    {x | ∃ g ∈ omegaGroup Q hQ, g * s₂ * g⁻¹ = x}) ∧
          ∀ s ∈ TauCeti.QuadraticMap.orthogonalGroup Q, orderOf s = 2 →
            suzukiLetter Q s = .a → finrank K (commSpace s) = m →
              (s ∈ {x | ∃ g ∈ omegaGroup Q hQ, g * t * g⁻¹ = x} ↔
                Even (finrank K ↥(commSpace s ⊓ commSpace t))))) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (M := V) (by omega)
  refine ⟨⟨fun g => mem_omegaGroup, omegaGroup_le Q hQ, relIndex_omegaGroup Q hQ,
    fun g hg h hh => natCast_finrank_commSpace_mul hQ hg hh, dicksonHom_ker Q hQ⟩, ?_⟩
  intro t htO ht2
  have htt : t * t = 1 := by rw [← pow_two]; exact (orderOf_eq_prime_iff.mp ht2).1
  have ht1 : t ≠ 1 := (orderOf_eq_prime_iff.mp ht2).2
  have hodd : Odd (finrank K (commSpace t)) → ∃ x ∈ commSpace t, Q x ≠ 0 := by
    intro hodd
    by_contra! h
    exact Nat.not_even_iff_odd.mpr hodd (even_finrank_commSpace_of_forall_eq_zero hQ htO htt h)
  refine ⟨⟨fun x hx y hy => polar_commSpace_eq_zero htO htt hx hy,
    fixSpace_eq_orthogonal_commSpace hQ htO htt, one_le_finrank_commSpace ht1,
    by have := two_mul_finrank_commSpace_le htt; omega⟩, ⟨map_sub_eq_polar htO, ?_, hodd,
    suzukiLetter_eq_a_iff, suzukiLetter_eq_b_iff, suzukiLetter_eq_c_iff⟩,
    fun s hsO hs2 => isConj_iff_suzukiLetter_eq hQ htO ht2 hsO hs2, ?_, fun htΩ => ⟨
    omega_conj_eq_of_not_typeA_half hQ hn htΩ ht2, fun ⟨hta, htm⟩ =>
    ⟨isGreatest_finrank_totallySingular hQ hn hta htm, omega_conj_two_classes hQ hm hn hta htm,
    fun s hsO hs2 hsa hsm => mem_omega_conj_iff_even hQ hn htO ht2 hta htm hsO hs2 hsa hsm⟩⟩⟩
  · constructor
    · intro h v
      rw [← map_sub_eq_polar htO]
      exact h _ (sub_mem_commSpace t v)
    · intro h x hx
      obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
      rw [map_sub_eq_polar htO]
      exact h v
  · rw [mem_omegaGroup, suzukiLetter_eq_a_iff, suzukiLetter_eq_c_iff]
    constructor
    · rintro ⟨-, he⟩
      by_cases hz : ∀ x ∈ commSpace t, Q x = 0
      · exact Or.inl ⟨he, hz⟩
      · push Not at hz
        exact Or.inr ⟨he, hz⟩
    · rintro (⟨he, -⟩ | ⟨he, -⟩) <;> exact ⟨htO, he⟩

end CFSG.RankThree.OrthogonalInvolutions
