module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3TNormAux

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22r3t_mem_normalizer_of_calLOf (D : Data G) (he : CFSG.Open.evenRank G = 3)
    {H K₁ : Subgroup G} (hTH : D.T ≤ H) (hK₁ : K₁ ∈ calLOf D.T D.M H)
    {b t : G} (hbK : b ∈ K₁) (hbM : b ∈ D.M)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hbo : orderOf b = q)
    (htK : t ∈ K₁) (hinv : t * b * t⁻¹ = b⁻¹)
    {z : G} (hzH : z ∈ H) (hzM : z ∈ D.M) (hzT : z ∈ normalizer (D.T : Set G))
    {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) {k : ℕ} (hzo : orderOf z = r ^ k) :
    z ∈ normalizer (K₁ : Set G) := by
  by_contra hznot
  have hbH : b ∈ H := CFSG.Quasithin.A3.subnormal_le hK₁.2 hbK
  have htH : t ∈ H := CFSG.Quasithin.A3.subnormal_le hK₁.2 htK
  have hpowT : ∀ i : ℕ, z ^ i ∈ normalizer (D.T : Set G) :=
    fun i => (Subgroup.normalizer (D.T : Set G)).pow_mem hzT i
  have hpowH : ∀ i : ℕ, z ^ i ∈ H := fun i => H.pow_mem hzH i
  have hKne : ∀ i j : Fin 4, i ≠ j →
      uniqueFourConj (z ^ (i : ℕ)) K₁ ≠ uniqueFourConj (z ^ (j : ℕ)) K₁ :=
    fun i j hij => uc22r3t_conj_ne_of_not_mem_normalizer hr hr5 hzo hznot hij
  have hcommA : ∀ i j : Fin 4, i ≠ j →
      ∀ x ∈ barImage H (uniqueFourConj (z ^ (i : ℕ)) K₁),
        ∀ y ∈ barImage H (uniqueFourConj (z ^ (j : ℕ)) K₁), x * y = y * x := by
    intro i j hij
    exact uc22r3t_barImage_conj_commute (T := D.T) (M := D.M) hTH hK₁
      (hpowH i) (hpowH j) (hpowT i) (hpowT j) (hKne i j hij)
  exact uc22r3t_false_of_rank_four D he hbK htK hbH htH hzH hbM hzM hq hq2 hbo hinv hcommA

end CFSG.LocalAnalysis.UniquenessCase.UC22
