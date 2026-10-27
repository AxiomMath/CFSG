module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2Sq
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL1Large

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom

namespace F6

namespace GoldAmL

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

theorem l2_critDist_two (h : GoldHyp G₁ G₂) (h32 : 32 ≤ Nat.card ↥(G₁ ⊓ G₂)) {z : D}
    {V : Subgroup D} (hn : IsNaturalAt G₁ (G₁ ⊓ G₂) z V)
    (hb : critDist (G₁ ⊔ G₂) G₁ G₂ V = 2) :
    (∀ y ∈ G₂, y * z * y⁻¹ = z) ∧
      (∀ z' V', IsNaturalAt G₁ (G₁ ⊓ G₂) z' V' → z' = z) ∧
      ⁅conjClosure V G₂, conjClosure V G₂⁆ = Subgroup.zpowers z ∧
      (∀ x ∈ conjClosure V G₂, x * x ∈ Subgroup.zpowers z) ∧
      ((∀ ω ∈ centerOf (G₁ ⊓ G₂), ω ^ 2 = 1 → ∀ y ∈ G₂, y * ω * y⁻¹ = ω) ↔
        (∀ ω ∈ centerOf (G₁ ⊓ G₂), ω ^ 2 = 1 → ω = 1 ∨ ω = z)) ∧
      ((∀ ε ∈ centerOf (G₁ ⊓ G₂), ε * ε = 1 → (∀ y ∈ G₁, y * ε = ε * y) → ε = 1) →
        ∀ r ∈ pCoreOf 2 G₁, r * r ∈ pCoreOf 2 G₂) := by
  have hiff := omega_labelling_iff h h32 hn hb
  refine ⟨centralizes_of_critDist_two h hn hb, fun z' V' hn' => centre_unique h h32 hn hb hn',
    (two_structure_of_critDist_two h hn hb).2.2.2,
    fun x hx => sq_mem_of_conjClosure h hn hb hx, hiff.1.trans hiff.2,
    fun hA => sq_mem_pCoreOf_of_critDist_two h h32 hn hb hA⟩

theorem l2_setup (h : GoldHyp G₁ G₂) (h32 : 32 ≤ Nat.card ↥(G₁ ⊓ G₂)) :
    ∃ A B : Subgroup D, ((A = G₁ ∧ B = G₂) ∨ (A = G₂ ∧ B = G₁)) ∧ GoldHyp A B ∧
      32 ≤ Nat.card ↥(A ⊓ B) ∧ ∃ z V, IsNaturalAt A (A ⊓ B) z V ∧ V ≤ pCoreOf 2 B ∧
        ((critDist (A ⊔ B) A B V = 2 ∧
            (∀ y ∈ B, y * z * y⁻¹ = z) ∧
            (∀ z' V', IsNaturalAt A (A ⊓ B) z' V' → z' = z) ∧
            ⁅conjClosure V B, conjClosure V B⁆ = Subgroup.zpowers z ∧
            (∀ x ∈ conjClosure V B, x * x ∈ Subgroup.zpowers z) ∧
            ((∀ ω ∈ centerOf (A ⊓ B), ω ^ 2 = 1 → ∀ y ∈ B, y * ω * y⁻¹ = ω) ↔
              (∀ ω ∈ centerOf (A ⊓ B), ω ^ 2 = 1 → ω = 1 ∨ ω = z)) ∧
            ((∀ ε ∈ centerOf (A ⊓ B), ε * ε = 1 → (∀ y ∈ A, y * ε = ε * y) → ε = 1) →
              ∀ r ∈ pCoreOf 2 A, r * r ∈ pCoreOf 2 B)) ∨
          (3 ≤ critDist (A ⊔ B) A B V ∧ IsElemAbelian 2 (conjClosure V B))) := by
  obtain ⟨A, B, hAB, hGH, z, V, hn, hV, -, -, -, hdi⟩ := l1_setup h h32
  have h32' : 32 ≤ Nat.card ↥(A ⊓ B) := by
    rcases hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h32
    · rwa [inf_comm]
  refine ⟨A, B, hAB, hGH, h32', z, V, hn, hV, ?_⟩
  rcases hdi with hb | hb
  · exact Or.inl ⟨hb, l2_critDist_two hGH h32' hn hb⟩
  · exact Or.inr hb

end GoldAmL

end F6

end CFSG.Quasithin
