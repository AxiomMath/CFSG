module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL5Sub
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL5Main

public section

namespace CFSG.Quasithin.F6.GoldAmL5

open CFSG.Open CFSG.Quasithin.F6.GoldAmL

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

theorem isGoldCaseM12_of_shape (h : GoldHyp G₁ G₂) {G₁' : Subgroup D} (hle₁ : G₁' ≤ G₁)
    (hi₁ : G₁'.relIndex G₁ = 2) (hv₁ : Vertex G₁' (G₁' ⊓ G₂))
    (e₁ : Nonempty (↥(pCoreOf 2 G₁') ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))
    (hnc : ∃ q ∈ pCoreOf 2 G₁, ∃ q' ∈ pCoreOf 2 G₁, q * q' ≠ q' * q)
    (h₂ : IsCentralProduct₂ ↥(pCoreOf 2 G₂) (QuaternionGroup 2) (QuaternionGroup 2))
    (hfpf : ∀ y ∈ G₂, y ≠ 1 → y ^ 3 = 1 → ∀ q ∈ pCoreOf 2 G₂, y * q * y⁻¹ = q →
      ∀ v ∈ pCoreOf 2 G₂, q * v = v * q) :
    IsGoldCaseM12 G₂ G₁ := by
  obtain ⟨a, b, s, x, ρ, hA, hAρ, hT, hcard, hG, hQ⟩ := exists_A_tuple5 h hle₁ hi₁ hv₁ e₁ hnc
  exact isGoldCaseM12_of_tuple h hA hAρ hT hcard hG hQ h₂ hfpf

end CFSG.Quasithin.F6.GoldAmL5
