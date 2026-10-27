module

public import CFSG.RankThree.CentralLift.LinearSplitting
public import CFSG.RankThree.CentralLiftU.UnitaryThreeLift

public section

namespace CFSG.RankThree.CentralLift

open CFSG.LocalAnalysis.ComponentInitial

theorem unitary_three_cross_splitting {p ℓ f : ℕ} (hp : p.Prime) (hp3 : 3 < p) {K : Type}
    [Field K] (h : UnitaryFieldData ℓ f K) (hℓodd : Odd ℓ) {V : Type*} [AddCommGroup V]
    [Module K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hV : Module.finrank K V = 3) {E : Type*} [Group E] [Finite E]
    (π : E →* sesqSpecialUnitaryGroup B) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup p π.ker) :
    (∃! s : sesqSpecialUnitaryGroup B →* E, π.comp s = MonoidHom.id _) ∧
      ∀ s : sesqSpecialUnitaryGroup B →* E, π.comp s = MonoidHom.id _ →
        ∃ e : π.ker × s.range ≃* E, ∀ c g, e (c, g) = (c : E) * g := by
  have : Finite (sesqSpecialUnitaryGroup B) := Finite.of_surjective π hπ
  exact ⟨(CFSG.RankThree.CentralLiftU.odd_unitary_three_central_large_prime_homomorphism_lifting'
      h hℓodd hB hBl hV hp hp3 π hπ hC hCp (MonoidHom.id _)).1,
    fun s hs => LinearRoots.exists_mulEquiv_prod_of_section hC hs⟩

end CFSG.RankThree.CentralLift
