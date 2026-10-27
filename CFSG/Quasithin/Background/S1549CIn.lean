module

public import CFSG.Quasithin.Background.S1549CInsp

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
  CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

namespace S1549C

section Vocabulary

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

@[expose] def StrongOff {cx : Ctx49 G T Mc M V₁ V₂ t} {H : Subgroup G} (hb : InspBase cx H)
    (A : Subgroup (MulAut (UTil T M V₁ H))) : Prop :=
  @IsStrongFFStarOffender (UTil T M V₁ H) (modInst hb.hF98.toHypF91) (StarOf T M V₁ H H) A

structure LCtx {cx : Ctx49 G T Mc M V₁ V₂ t} {H : Subgroup G} (hb : InspBase cx H) {W : Subgroup G}
    {B : Subgroup (MulAut (UTil T M V₁ H))} (_od : OffData hb W B) (L : Subgroup G) : Prop where
  comp : L ∈ cComp (Jgrp hb B)
  comm : L = ⁅L, Y0 T Mc M⁆
  eq : H = conjClosure L T ⊔ Y0 T Mc M ⊔ T

@[expose] def IsLieOver2e (X : Type) [Group X] (e : ℕ) : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ e ∧
      Nonempty (X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K))) ∨
  (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ e ∧
      Nonempty (X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 K))) ∨
  (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ e ∧
      Nonempty (X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 K))) ∨
  (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ e ∧
      Nonempty (X ≃* ↥(CFSG.Open.quasithinG2 K)))

@[expose] def IsG2TwoDerived (X : Type) [Group X] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
    Nonempty (X ≃* ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆)

@[expose] def IsListL (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, 3 ≤ n ∧ n ≤ 5 ∧ Nonempty (X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2)))) ∨
    IsAlt 6 X ∨ IsHat X ↥(alternatingGroup (Fin 6)) ∨ IsAlt 7 X ∨ IsG2TwoDerived X

structure ListL (T Mc M V₁ H L : Subgroup G) : Prop where
  eq : conjClosure L T = L
  lie : IsListL ↥(StarOf T M V₁ H L)
  par : IsAlt 7 ↥(StarOf T M V₁ H L) ∨ IsHat ↥(StarOf T M V₁ H L) ↥(alternatingGroup (Fin 6)) ∨
    IsMinParabolicOf (StarOf T M V₁ H L) (StarOf T M V₁ H (Y0 T Mc M ⊔ (T ⊓ L)))

structure EndCtx {cx : Ctx49 G T Mc M V₁ V₂ t} {H : Subgroup G} (hb : InspBase cx H) {W : Subgroup G}
    {B : Subgroup (MulAut (UTil T M V₁ H))} (od : OffData hb W B) (L : Subgroup G) : Prop where
  lctx : LCtx hb od L
  k : Y0 T Mc M ≤ conjClosure L T
  l : ListL T Mc M V₁ H L

end Vocabulary

section Inputs

@[expose] def Input49I : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ : Subgroup G) (t : G)
    (cx : Ctx49 G T Mc M V₁ V₂ t) (H : Subgroup G) (hb : InspBase cx H) (W : Subgroup G)
    (B : Subgroup (MulAut (UTil T M V₁ H))), OffData hb W B →
      (cComp (Jgrp hb B)).Nonempty ∧ ∀ L ∈ cComp (Jgrp hb B), L = ⁅L, Y0 T Mc M⁆

@[expose] def Input49K : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ : Subgroup G) (t : G)
    (cx : Ctx49 G T Mc M V₁ V₂ t) (H : Subgroup G) (hb : InspBase cx H) (W : Subgroup G)
    (B : Subgroup (MulAut (UTil T M V₁ H))) (od : OffData hb W B) (L : Subgroup G),
    LCtx hb od L → Y0 T Mc M ≤ conjClosure L T

@[expose] def Input49E : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ : Subgroup G) (t : G)
    (cx : Ctx49 G T Mc M V₁ V₂ t) (H : Subgroup G) (hb : InspBase cx H) (W : Subgroup G)
    (B : Subgroup (MulAut (UTil T M V₁ H))) (od : OffData hb W B) (L : Subgroup G),
    LCtx hb od L → Y0 T Mc M ≤ conjClosure L T →
      ∀ e : ℕ, 1 < e → ¬ IsLieOver2e ↥(StarOf T M V₁ H L) e

@[expose] def Input49L : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ : Subgroup G) (t : G)
    (cx : Ctx49 G T Mc M V₁ V₂ t) (H : Subgroup G) (hb : InspBase cx H) (W : Subgroup G)
    (B : Subgroup (MulAut (UTil T M V₁ H))) (od : OffData hb W B) (L : Subgroup G),
    LCtx hb od L → Y0 T Mc M ≤ conjClosure L T →
      (∀ e : ℕ, 1 < e → ¬ IsLieOver2e ↥(StarOf T M V₁ H L) e) → ListL T Mc M V₁ H L

@[expose] def Input49S : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ : Subgroup G) (t : G)
    (cx : Ctx49 G T Mc M V₁ V₂ t) (H : Subgroup G) (hb : InspBase cx H) (W : Subgroup G)
    (B : Subgroup (MulAut (UTil T M V₁ H))) (od : OffData hb W B) (L : Subgroup G),
    EndCtx hb od L →
      (IsHat ↥(StarOf T M V₁ H L) ↥(alternatingGroup (Fin 6)) ∨ IsAlt 7 ↥(StarOf T M V₁ H L) ∨
        IsG2TwoDerived ↥(StarOf T M V₁ H L)) →
        ¬ ∃ A, StrongOff hb A

@[expose] def Input49L3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ : Subgroup G) (t : G)
    (cx : Ctx49 G T Mc M V₁ V₂ t) (H : Subgroup G) (hb : InspBase cx H) (W : Subgroup G)
    (B : Subgroup (MulAut (UTil T M V₁ H))) (od : OffData hb W B) (L : Subgroup G),
    EndCtx hb od L →
      Nonempty (↥(StarOf T M V₁ H L) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))) →
        ¬ ∃ A, StrongOff hb A ∧ A ≤ StarOf T M V₁ H (pCoreOf 2 (Y0 T Mc M ⊔ T))

@[expose] def Input49Ln : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ : Subgroup G) (t : G)
    (cx : Ctx49 G T Mc M V₁ V₂ t) (H : Subgroup G) (hb : InspBase cx H) (W : Subgroup G)
    (B : Subgroup (MulAut (UTil T M V₁ H))) (od : OffData hb W B) (L : Subgroup G),
    EndCtx hb od L → ∀ n : ℕ, (n = 4 ∨ n = 5) →
      ¬ Nonempty (↥(StarOf T M V₁ H L) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2)))

@[expose] def Input49A6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ : Subgroup G) (t : G)
    (cx : Ctx49 G T Mc M V₁ V₂ t) (H : Subgroup G) (hb : InspBase cx H) (W : Subgroup G)
    (B : Subgroup (MulAut (UTil T M V₁ H))) (od : OffData hb W B) (L : Subgroup G),
    EndCtx hb od L → IsAlt 6 ↥(StarOf T M V₁ H L) →
      ¬ ∃ A, StrongOff hb A ∧ A ≤ StarOf T M V₁ H (pCoreOf 2 (Y0 T Mc M ⊔ T))

end Inputs

end S1549C

end CFSG.Quasithin
