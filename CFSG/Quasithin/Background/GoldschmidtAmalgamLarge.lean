module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2S
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Hyp
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL4G2Main
public import CFSG.Quasithin.Background.GoldschmidtAmalgamSplit

public section

universe u

namespace CFSG.Quasithin.F6.GoldAmLarge

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom GoldAmL GoldAmL3
  GoldAmL2S GoldAmL4

@[expose] def B2OmegaInput : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (A B : Subgroup D) (z : D) (V : Subgroup D),
    GoldHyp A B → 32 ≤ Nat.card ↥(A ⊓ B) → IsNaturalAt A (A ⊓ B) z V →
      critDist (A ⊔ B) A B V = 2 →
        ∀ ε ∈ centerOf (A ⊓ B), ε * ε = 1 → (∀ y ∈ A, y * ε = ε * y) → ε = 1

@[expose] def B2Card64Input : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (A B : Subgroup D) (z : D) (V : Subgroup D),
    GoldHyp A B → IsNaturalAt A (A ⊓ B) z V → critDist (A ⊔ B) A B V = 2 →
      (∀ ε ∈ centerOf (A ⊓ B), ε * ε = 1 → (∀ y ∈ A, y * ε = ε * y) → ε = 1) →
        Nat.card ↥(A ⊓ B) = 64 →
          ∃ A' B' : Subgroup D, A' ≤ A ∧ B' ≤ B ∧ A'.relIndex A = 2 ∧ B'.relIndex B = 2 ∧
            Vertex A' (A' ⊓ B') ∧ Vertex B' (A' ⊓ B') ∧
            Nonempty (↥(pCoreOf 2 A') ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ∧
            IsCentralProduct₂ ↥(pCoreOf 2 B') (Multiplicative (ZMod 4)) (QuaternionGroup 2) ∧
            IsSpecialTwoOnePlusFour ↥(pCoreOf 2 B)

@[expose] def B3LabelInput : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (A B : Subgroup D) (z : D) (V : Subgroup D),
    GoldHyp A B → 32 ≤ Nat.card ↥(A ⊓ B) → IsNaturalAt A (A ⊓ B) z V → V ≤ pCoreOf 2 B →
      3 ≤ critDist (A ⊔ B) A B V → IsElemAbelian 2 (conjClosure V B) →
        ∀ y ∈ B, y * z * y⁻¹ = z

@[expose] def B3ClassInput : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (A B : Subgroup D) (z : D) (V : Subgroup D),
    GoldHyp3 A B z V → 32 ≤ Nat.card ↥(A ⊓ B) →
      IsGoldCaseM12 B A ∨ IsGoldCaseAutM12Cat B A

variable {D : Type u} [Group D]

theorem isGoldCaseCat_of_vi {H₁ H₂ : Subgroup D} (h : IsGoldCaseVICat H₁ H₂) :
    IsGoldCaseCat H₁ H₂ :=
  Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

theorem goldschmidtCharTwoLargeV_of_inputs
    (hΩ : B2OmegaInput.{u}) (h64 : B2Card64Input.{u}) (hlab : B3LabelInput.{u})
    (h3 : B3ClassInput.{u}) :
    ∀ (D : Type u) [Group D] [Finite D] (G₁ G₂ : Subgroup D), IsGoldschmidtVAmalgam G₁ G₂ →
      CharTwo G₁ → CharTwo G₂ → 32 ≤ Nat.card ↥(G₁ ⊓ G₂) → IsGoldCaseCat G₁ G₂ := by
  intro D _ _ G₁ G₂ hG hc₁ hc₂ h32
  have hGH : GoldHyp G₁ G₂ := ⟨hG, hc₁, hc₂⟩
  obtain ⟨A, B, hAB, hgold, h32', z, V, hn, hVQ, hcase⟩ := l2s_setup hGH h32
  suffices hBA : IsGoldCaseCat B A by
    rcases hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact isGoldCaseCat_comm.mp hBA
    · exact hBA
  rcases hcase with ⟨hb, -, hS⟩ | ⟨hb, hU⟩
  · have hA := hΩ D A B z V hgold h32' hn hb
    have hst := hS hA
    rcases hst.card_T with hT | hT
    · obtain ⟨e₁⟩ := hst.shape_A hT
      exact isGoldCaseCat_of_vi (Or.inr (Or.inr (Or.inr (Or.inl
        (isGoldCaseG22Prime_of_shape hgold ⟨e₁.trans (MulEquiv.prodMultiplicative _ _)⟩
          (hst.shape_B hT))))))
    · obtain ⟨A', B', hle₁, hle₂, hi₁, hi₂, hv₁, hv₂, e₁, e₂, hsp⟩ :=
        h64 D A B z V hgold hn hb hA hT
      exact isGoldCaseCat_of_vi (Or.inr (Or.inr (Or.inl
        (isGoldCaseG22_of_index_two hgold hle₁ hle₂ hi₁ hi₂ hv₁ hv₂ e₁ e₂ hsp))))
  · have hz := hlab D A B z V hgold h32' hn hVQ hb hU
    rcases h3 D A B z V ⟨hgold, hn, hz, hU⟩ h32' with hm | hm
    · exact isGoldCaseCat_of_vi (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm)))))
    · exact isGoldCaseCat_of_vi (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hm)))))

theorem goldschmidtCharTwoLarge_of_inputs
    (hΩ : B2OmegaInput.{u}) (h64 : B2Card64Input.{u}) (hlab : B3LabelInput.{u})
    (h3 : B3ClassInput.{u}) : GoldschmidtCharTwoLarge.{u} := by
  intro D _ _ G₁ G₂ hG hc₁ hc₂ h32
  exact goldschmidtCharTwoLargeV_of_inputs hΩ h64 hlab h3 D G₁ G₂ hG.toVAmalgam hc₁ hc₂ h32

end CFSG.Quasithin.F6.GoldAmLarge
