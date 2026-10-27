module

public import CFSG.Quasithin.Vol2.KGFact12617L52b
public import CFSG.Quasithin.Vol2.KGFact12617LieW
public import CFSG.Quasithin.Vol2.KGFact12618h
public import CFSG.Quasithin.Vol2.KGFact12617Lie
public import CFSG.Quasithin.Vol2.KGFact12617

public section

namespace CFSG.Quasithin.H13.KG12617L52

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.LieType.BorelTits Module

@[expose] def LeafCentralizer : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (Y K T T₀ B R : Subgroup Γ), Conf12617 Y K T T₀ B R →
    Y ⊓ Subgroup.centralizer (K : Set Γ) = ⊥

@[expose] def LeafFive : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (B : Subgroup H),
    quasithinO2QuotientIso B ↥(alternatingGroup (Fin 6)) → ∃ x ∈ B, orderOf x = 5

@[expose] def LeafTwoElt : Prop :=
  ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 → ∀ x t : ↥(StatedSL 5 F),
    orderOf x = 5 → (∃ k : ℕ, t ^ 2 ^ k = 1) → x * t = t * x → t = 1

@[expose] def LeafCardPCore : Prop :=
  ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 → ∀ B : Subgroup ↥(StatedSL 5 F),
    ⁅B, B⁆ = B → quasithinO2QuotientIso B ↥(alternatingGroup (Fin 6)) →
    Nat.card ↥(pCoreOf 2 B) = 1 ∨
      (Nat.card ↥(pCoreOf 2 B) = 16 ∧
        finrank F ↥(fixFlag (natRep (StatedSL 5 F)) (pCoreOf 2 B) 1) ≠
          finrank F ↥(fixFlag (natRep (StatedSL 5 F)) ((pCoreOf 2 B).map theta.toMonoidHom) 1))

@[expose] def LeafOuter : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (F : Type) [Field F] [Finite F], Nat.card F = 2 →
    ∀ (Y K : Subgroup Γ), K ≤ Y → Y ≤ Subgroup.normalizer (K : Set Γ) →
    Y ⊓ Subgroup.centralizer (K : Set Γ) = ⊥ →
    ∀ (e : ↥K ≃* ↥(StatedSL 5 F)) (U : Subgroup Γ), U ≤ K →
    finrank F ↥(fixFlag (natRep (StatedSL 5 F)) ((U.subgroupOf K).map e.toMonoidHom) 1) ≠
      finrank F ↥(fixFlag (natRep (StatedSL 5 F))
        (((U.subgroupOf K).map e.toMonoidHom).map theta.toMonoidHom) 1) →
    ∀ y ∈ Y, y ∈ Subgroup.normalizer (U : Set Γ) → y ∈ K

@[expose] def LeafNormR : Prop :=
  ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 → ∀ B R : Subgroup ↥(StatedSL 5 F),
    ⁅B, B⁆ = B → quasithinO2QuotientIso B ↥(alternatingGroup (Fin 6)) →
    Nat.card ↥(pCoreOf 2 B) = 16 → R ≠ ⊥ → R ≤ pCoreOf 2 B →
    ¬ Subgroup.normalizer (R : Set ↥(StatedSL 5 F)) ≤
      Subgroup.normalizer (B : Set ↥(StatedSL 5 F))

end CFSG.Quasithin.H13.KG12617L52
