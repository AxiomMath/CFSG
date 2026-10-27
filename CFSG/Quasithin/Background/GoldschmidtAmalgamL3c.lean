module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cSub
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL5M12

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3
  CFSG.Quasithin.F6.GoldAmL2T

namespace F6

namespace GoldAmL3c

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem m12Shapes_of_b3 (h : GoldHyp3 A B z V) (hU : Nat.card (conjClosure V B) = 8)
    (hT : Nat.card ↥(A ⊓ B) = 64) :
    (∃ A' : Subgroup D, A' ≤ A ∧ A'.relIndex A = 2 ∧ Vertex A' (A' ⊓ B) ∧
      Nonempty (↥(pCoreOf 2 A') ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) ∧
    (∃ q ∈ pCoreOf 2 A, ∃ q' ∈ pCoreOf 2 A, q * q' ≠ q' * q) ∧
    IsCentralProduct₂ ↥(pCoreOf 2 B) (QuaternionGroup 2) (QuaternionGroup 2) ∧
    (∀ y ∈ B, y ≠ 1 → y ^ 3 = 1 → ∀ q ∈ pCoreOf 2 B, y * q * y⁻¹ = q →
      ∀ v ∈ pCoreOf 2 B, q * v = v * q) := by
  obtain ⟨x, a, a₁, a₂, g⟩ := GoldHyp3.exists_gen3 h
  exact ⟨g.exists_A' hU hT, g.exists_noncomm_QA hU hT, g.isCentralProduct₂_QB hU hT,
    g.hfpf hU hT⟩

theorem isGoldCaseM12_of_b3 (h : GoldHyp3 A B z V) (hU : Nat.card (conjClosure V B) = 8)
    (hT : Nat.card ↥(A ⊓ B) = 64) : IsGoldCaseM12 B A := by
  obtain ⟨⟨A', hle, hi, hv, e⟩, hnc, h₂, hfpf⟩ := m12Shapes_of_b3 h hU hT
  exact GoldAmL5.isGoldCaseM12_of_shape h.gold hle hi hv e hnc h₂ hfpf

end GoldAmL3c

end F6

end CFSG.Quasithin
