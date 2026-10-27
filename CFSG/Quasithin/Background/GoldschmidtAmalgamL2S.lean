module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2SShape
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2Setup

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL2S

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

structure B2Structure (A B : Subgroup D) (z : D) (V : Subgroup D) : Prop where
  comm_U : ⁅conjClosure V B, conjClosure V B⁆ = Subgroup.zpowers z
  sq_U : ∀ x ∈ conjClosure V B, x * x ∈ Subgroup.zpowers z
  card_U : Nat.card ↥(conjClosure V B) = 16
  center_U : ∃ c : D, centerOf (conjClosure V B) = Subgroup.zpowers z ⊔ Subgroup.zpowers c ∧
    c * c ∈ Subgroup.zpowers z ∧ Nat.card ↥(centerOf (conjClosure V B)) = 4
  three_conjugates : ∃ x ∈ B, x ∉ A ⊓ B ∧ conjSub x V ≠ V ∧ conjSub (x * x) V ≠ V ∧
    conjSub x V ≠ conjSub (x * x) V ∧ ∀ b ∈ B, conjSub b V = V ∨ conjSub b V = conjSub x V ∨
      conjSub b V = conjSub (x * x) V
  V_inf_center : V ⊓ centerOf (conjClosure V B) = Subgroup.zpowers z
  kernel_eq : pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D) =
    centerOf (conjClosure V B)
  card_kernel : Nat.card ↥(pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D)) = 4
  card_QB : Nat.card ↥(pCoreOf 2 B) = 16 ∨ Nat.card ↥(pCoreOf 2 B) = 32
  card_T : Nat.card ↥(A ⊓ B) = 32 ∨ Nat.card ↥(A ⊓ B) = 64
  shape_A : Nat.card ↥(A ⊓ B) = 32 →
    Nonempty (↥(pCoreOf 2 A) ≃* Multiplicative (ZMod 4 × ZMod 4))
  shape_B : Nat.card ↥(A ⊓ B) = 32 →
    IsCentralProduct₂ ↥(pCoreOf 2 B) (Multiplicative (ZMod 4)) (QuaternionGroup 2)

theorem Hyp2.b2Structure [Finite D] (h : Hyp2 A B z V) : B2Structure A B z V where
  comm_U := h.comm_U
  sq_U := h.sq_U
  card_U := h.card_U
  center_U := by
    obtain ⟨x, a, a₁, a₂, g⟩ := h.exists_gen
    exact ⟨a * a₁ * a₂, g.center_U_eq.1, g.center_U_eq.2, h.card_center_U⟩
  three_conjugates := h.three_conjugates
  V_inf_center := h.V_inf_center
  kernel_eq := h.kerK_eq_center_U
  card_kernel := h.card_kerK
  card_QB := h.card_QB_eq
  card_T := h.card_T_eq
  shape_A := h.pCoreOf_left_mulEquiv
  shape_B := h.isCentralProduct₂_of_card_inf_eq_32

theorem l2s_main [Finite D] (h : GoldHyp A B) (h32 : 32 ≤ Nat.card ↥(A ⊓ B)) {z : D}
    {V : Subgroup D} (hn : IsNaturalAt A (A ⊓ B) z V) (hb : critDist (A ⊔ B) A B V = 2)
    (hA : ∀ ε ∈ centerOf (A ⊓ B), ε * ε = 1 → (∀ y ∈ A, y * ε = ε * y) → ε = 1) :
    B2Structure A B z V :=
  (Hyp2.of_critDist_two h h32 hn hb hA).b2Structure

theorem l2s_setup [Finite D] {G₁ G₂ : Subgroup D} (h : GoldHyp G₁ G₂)
    (h32 : 32 ≤ Nat.card ↥(G₁ ⊓ G₂)) :
    ∃ A B : Subgroup D, ((A = G₁ ∧ B = G₂) ∨ (A = G₂ ∧ B = G₁)) ∧ GoldHyp A B ∧
      32 ≤ Nat.card ↥(A ⊓ B) ∧ ∃ z V, IsNaturalAt A (A ⊓ B) z V ∧ V ≤ pCoreOf 2 B ∧
        ((critDist (A ⊔ B) A B V = 2 ∧ (∀ y ∈ B, y * z * y⁻¹ = z) ∧
            ((∀ ε ∈ centerOf (A ⊓ B), ε * ε = 1 → (∀ y ∈ A, y * ε = ε * y) → ε = 1) →
              B2Structure A B z V)) ∨
          (3 ≤ critDist (A ⊔ B) A B V ∧ IsElemAbelian 2 (conjClosure V B))) := by
  obtain ⟨A, B, hAB, hGH, h32', z, V, hn, hV, hcases⟩ := l2_setup h h32
  refine ⟨A, B, hAB, hGH, h32', z, V, hn, hV, ?_⟩
  rcases hcases with ⟨hb, hz, -⟩ | hb
  · exact Or.inl ⟨hb, hz, fun hA => l2s_main hGH h32' hn hb hA⟩
  · exact Or.inr hb

end GoldAmL2S

end F6

end CFSG.Quasithin
