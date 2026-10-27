module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcIndexTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

theorem exists_inv_extraGood_of_conj_index {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) {C : Subgroup G} (β : MulAut C) (z : G')
    (hβz : ∀ u : C, f (β u : G) = z * f (u : G) * z⁻¹)
    {R : Subgroup G'} (hCR : C.map f ≤ R)
    (hRn : R ≤ Subgroup.normalizer ((C.map f : Subgroup G') : Set G'))
    (hcop : Nat.Coprime ((C.map f).subgroupOf R).index 3)
    {T : Subgroup G'} {y : G'} (hTR : ∀ v ∈ T, y⁻¹ * v * y ∈ R)
    {u : T} (hu : orderOf u = 3) (hgood : IsExtraGood u)
    (hinv : y * z * y⁻¹ * (u : G') * (y * z * y⁻¹)⁻¹ = (u : G')⁻¹) :
    ∃ w : C, orderOf w = 3 ∧ β w = w⁻¹ ∧ IsExtraGood w := by
  obtain ⟨Q, N, huQ, hQ, hN⟩ := hgood
  obtain ⟨w, Q₀, hord, hβw, hwQ₀, ⟨φ⟩⟩ := exists_inv_of_conj_index f hf β z hβz hCR hRn hcop
    hTR hu huQ (fun v hv => by simpa using hQ.1 ⟨v, hv⟩) hinv
  exact ⟨w, hord, hβw, ⟨Q₀, N, hwQ₀, hQ.of_mulEquiv φ, hN⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
