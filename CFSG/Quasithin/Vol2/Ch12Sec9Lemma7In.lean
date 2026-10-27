module

public import CFSG.Quasithin.Background.B4Misc
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Vol2.Ch12Sec2Setting

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

@[expose] def AsB4_12_two : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (G : Subgroup (MulAut V)) (v : V), Subgroup.closure (orbitOf G v) = ⊤ →
      (∃ U : Subgroup V, (∃ x ∈ U, ∃ y ∈ U, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y) ∧
        ∀ u ∈ U, u ≠ 1 → u ∈ orbitOf G v) →
      (Nonempty (↥G ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∨
        Nonempty (↥G ≃* alternatingGroup (Fin 7))) →
      Odd (Nat.card (orbitOf G v)) →
      Nonempty (↥(G ⊓ MulAction.stabilizer (MulAut V) v) ⧸
          CFSG.pCore 2 ↥(G ⊓ MulAction.stabilizer (MulAut V) v) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
      Nat.card V = 2 ^ 4 ∧ ∀ x : V, x ≠ 1 → x ∈ orbitOf G v

@[expose] def LatticeFact1297 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K S B Y : Subgroup G), K ≤ X →
    X ≤ Subgroup.normalizer (K : Set G) → QuasithinUnique.IsSylowTwoOf S X → K ⊔ S = X →
    (Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∨
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) →
    B ≤ K → S ≤ Subgroup.normalizer (B : Set G) →
    (∀ s ∈ S, ∃ b ∈ B, ∀ x ∈ B, (b⁻¹ * s) * x * (b⁻¹ * s)⁻¹ * x⁻¹ ∈ pCoreOf 2 B) →
    ((Nonempty (↥B ⧸ CFSG.pCore 2 ↥B ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
        (B ⊓ Y).relIndex B = 7 ∧
        (Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) →
          ∃ φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2),
            ((B.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).map φ.toMonoidHom =
              Subgroup.centralizer ({transvection15} : Set _))) ∨
      (Nonempty (↥B ⧸ CFSG.pCore 2 ↥B ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧
        (B ⊓ Y).relIndex B = 15)) →
    S ≤ Y → Y ≤ X → ¬ Y ≤ B ⊔ S → CFSG.Open.pRank 3 Y ≤ 1 → pCoreOf 2 B ≤ Y →
      Nonempty (↥B ⧸ CFSG.pCore 2 ↥B ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
      (Nonempty (↥(B ⊔ Y) ⧸ CFSG.pCore 2 ↥(B ⊔ Y) ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (↥(B ⊔ Y) ⧸ CFSG.pCore 2 ↥(B ⊔ Y) ≃*
          Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))) ∧
      CFSG.Quasithin.IsMaxSubgroupIn (B ⊔ Y) Y

end CFSG.Quasithin.H13
