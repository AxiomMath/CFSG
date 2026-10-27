module

public import CFSG.Sporadic.Recognition.LyonsAmalgamCount
public import CFSG.Sporadic.Recognition.LyonsAmalgamGlue

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup

section Count

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

theorem LyData.card_Tx_of_borel (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (φ : ↥(NormX (x₁ : G)) ≃* Ly0.B0)
    (hφT : ((normalizer (A3 (x₁ : G) (x₂ : G) (x₃ : G) : Set G)).subgroupOf
      (NormX (x₁ : G))).map φ.toMonoidHom = Ly0.Tx) : Nat.card Ly0.Tx = 7776 := by
  rw [← hφT, Subgroup.card_map_of_injective φ.injective,
    ← Nat.card_congr (txEquivSubgroupOf (x₁ := (x₁ : G)) (x₂ := (x₂ : G))
      (x₃ := (x₃ : G))).toEquiv]
  exact D.card_TxN S

theorem LyData.card_Txy_of_borel (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (φ : ↥(NormX (x₁ : G)) ≃* Ly0.B0)
    (hφK : ((NN (x₁ : G) (x₂ : G) ⊓ normalizer (zpowers (x₃ : G) : Set G)).subgroupOf
      (NormX (x₁ : G))).map φ.toMonoidHom = Ly0.Txy) : Nat.card Ly0.Txy = 3888 := by
  rw [← hφK, Subgroup.card_map_of_injective φ.injective]
  have hle : KN (x₁ : G) (x₂ : G) (x₃ : G) ≤ NormX (x₁ : G) := fun _ hg => hg.1.1
  have e : (NN (x₁ : G) (x₂ : G) ⊓ normalizer (zpowers (x₃ : G) : Set G)) =
      KN (x₁ : G) (x₂ : G) (x₃ : G) := rfl
  rw [e, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
  exact D.card_KN S

end Count

end CFSG.Sporadic.Recognition.LyonsSims
