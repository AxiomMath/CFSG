module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Tr

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

@[expose] def Stmt5_2_6_L2K_rank2_res : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n k : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n → 2 ≤ k → IsSL3Ch5 k (O2Q (oTwoUpper H)) →
    (∃ P : Subgroup G, IsMaxParabolicOver (oTwoUpper H) (T ⊓ oTwoUpper H) P ∧
      quasithinIsCComponent L₂ P) →
    IsPSL 2 2 k (ModO2 L₂) →
    Nat.card ↥(pCoreOf 2 (oTwoUpper H) ⊓ L₂) = 2 ^ (3 * k) →
    (F112E3 L₂ L (sec52S M H) ∨ F112E6 L₂ L (sec52S M H)) → F112Second L₂ L (sec52S M H) →
      False

variable {G : Type} [Group G] [Finite G]

theorem card_eq_two_pow_sub_of_mul {R₀ : Subgroup G} (hR : IsPGroup 2 R₀) {v m : ℕ}
    (h : Nat.card R₀ * 2 ^ v = 2 ^ m) : Nat.card R₀ = 2 ^ (m - v) ∧ v ≤ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d, hd⟩ := hR.exists_card_eq
  rw [hd, ← pow_add] at h
  have h' := Nat.pow_right_injective le_rfl h
  refine ⟨?_, by omega⟩
  rw [hd]
  congr 1
  omega

end CFSG.Quasithin.H13
