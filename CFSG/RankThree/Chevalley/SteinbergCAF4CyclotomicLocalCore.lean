module

public import CFSG.RankThree.Chevalley.SteinbergBTEvenF4Noninner
public import CFSG.RankThree.Chevalley.SteinbergCFOddF4NoninnerLocalCore
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.LocalRank CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise commutatorElement

variable (K : Type) [Field K] [Finite K]

theorem F4_commutator_mem_range_conj
    (a b : MulAut (adjointGroup .F4 K)) :
    ⁅a, b⁆ ∈ (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hcard⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hf : 1 ≤ (n : ℕ) := n.pos
  by_cases hℓ2 : ringChar K = 2
  · rw [hℓ2] at hK
    have : CharP K ReeTag.F4.prime := finite_field_prime_power_characteristic Nat.prime_two hf hK
    obtain ⟨-, -, ⟨Θ, -, -, hΘker⟩, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
    have key : ∀ a b : MulAut (adjointGroup ReeTag.F4.tag K), ⁅a, b⁆ ∈
        (MulAut.conj : adjointGroup ReeTag.F4.tag K →*
          MulAut (adjointGroup ReeTag.F4.tag K)).range := fun a b => by
      have h : ⁅a, b⁆ ∈ Θ.ker := by
        rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact mul_comm _ _
      rw [hΘker] at h
      exact h
    exact key a b
  · obtain ⟨-, Θ, -, -, hΘker, -⟩ :=
      odd_F4_and_nonexceptional_G2_automorphism_normal_form hℓ hℓ2 hf K hK .F4 (Or.inl rfl)
    have h : ⁅a, b⁆ ∈ Θ.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact ringAut_mul_comm K _ _
    rw [hΘker] at h
    exact h

theorem F4_localCore_eq_bot_of_noninner
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (B : Subgroup (MulAut (adjointGroup .F4 K)))
    (hB : (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range ≤ B) (α : B)
    (hα : (α : MulAut (adjointGroup .F4 K)) ∉
      (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range)
    (hαp : orderOf α = p) :
    aschbacherSolvableCore p (Subgroup.centralizer {α} : Subgroup B) = ⊥ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hcard⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hf : 1 ≤ (n : ℕ) := n.pos
  by_cases hℓ2 : ringChar K = 2
  · rw [hℓ2] at hK
    have : CharP K ReeTag.F4.prime := finite_field_prime_power_characteristic Nat.prime_two hf hK
    obtain ⟨-, hNF, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
    obtain ⟨⟨x, a⟩, hxa, -⟩ := hNF α.1
    exact (even_F4_noninner_odd_prime_field_descent_and_local_core_trivial hf hK hp (by omega)
      B hB α hα hαp x a a.2 hxa).2.2.2.2
  · exact (odd_F4_noninner_prime_local_core_trivial hℓ hℓ2 hf K hK hp B hB).1 α hα hαp

end CFSG.RankThree.Chevalley
