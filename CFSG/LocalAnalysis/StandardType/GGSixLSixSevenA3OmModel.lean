module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3OmFrame
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3OmPullback

public section

namespace CFSG.StandardType

namespace CoordOm

open CFSG.Assembly Multiplicative
open CFSG.RankThree.Classical2 (orthDerived)

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} [Fact p.Prime]
  {G : Type} [Group G] {φ : ↥(orthDerived Q) →* G}

theorem exists_mem_normalizer_conj_le_of_model (hp2 : p ≠ 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hφ : Function.Injective φ) {Bs : Subgroup G} (hBφ : Bs ≤ φ.range)
    (hBel : IsElemAbelian p Bs) (h4 : p ^ 4 ≤ Nat.card Bs)
    (hmaxG : ∀ g ∈ φ.range ⊓ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {E J : Subgroup G} (hEB : E ≤ Bs) (hE : Nat.card E = p ^ 2)
    (hJ : IsComponentOf J (φ.range ⊓ Subgroup.centralizer (E : Set G)))
    (hCJ : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ E) (hJcard : Nat.card J ∣ 40320)
    (hJZ : ∀ z ∈ J, (∀ g ∈ J, z * g = g * z) → z ^ p = 1 → z = 1) :
    ∃ w ∈ φ.range ⊓ Subgroup.normalizer (Bs : Set G), ∀ e ∈ E, w⁻¹ * e * w ∈ J := by
  obtain ⟨hApow, hAcomm, hAmax⟩ := pullback_isElemAbelian_max hφ hBφ hBel hmaxG
  have hEφ : E ≤ φ.range := hEB.trans hBφ
  have hJφ : J ≤ φ.range := hJ.1.trans inf_le_left
  obtain ⟨w, hw, hconj⟩ := exists_mem_normalizer_conj_le_of_a3 hp2 hQ hT (pullback φ Bs)
    (pullback_le _) hApow hAcomm hAmax (by rw [card_pullback hφ hBφ]; exact h4)
    (pullback_mono hEB) (by rw [card_pullback hφ hEφ]; exact hE) (isComponentOf_pullback hφ hEφ hJ)
    (pullback_inf_centralizer_le hJφ hCJ) (by rw [card_pullback hφ hJφ]; exact hJcard)
    (central_pow_pullback hφ hJφ hJZ)
  exact conj_mem_of_pullback hBφ hEφ hw hconj

end Model

end CoordOm

end CFSG.StandardType
