module

public import CFSG.Quasithin.Background.JonesParshallBasic
public import CFSG.Open.GriessSchurMultipliersMilestoneDefs
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.Vol2.Ch3Basic

public section

namespace CFSG.Quasithin.ASInputs

open CFSG.Open CFSG.QuasithinUnique

@[expose] def E111Hyp (G : Type) [Group G] (n : ℕ) : Prop :=
  ∀ (H K : Subgroup G), K ≤ H → ∀ [(K.subgroupOf H).Normal], CFSG.Open.IsSubnormal H ⊤ →
    IsSimpleGroup (↥H ⧸ K.subgroupOf H) → (∃ a b : ↥H ⧸ K.subgroupOf H, a * b ≠ b * a) →
    ∀ B : Subgroup (MulAut (↥H ⧸ K.subgroupOf H)), IsPGroup 2 B →
      IsSylowIn 2 (B ⊓ (MulAut.conj : ↥H ⧸ K.subgroupOf H →* _).range)
        (MulAut.conj : ↥H ⧸ K.subgroupOf H →* _).range →
      E1.nParam ((MulAut.conj : ↥H ⧸ K.subgroupOf H →* _).range ⊔ B) ≤ (n : ℕ∞)

@[expose] def AS_E_1_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n : ℕ), 1 ≤ n → E111Hyp G n →
    E1.nParam (⊤ : Subgroup G) ≤ (n : ℕ∞)

@[expose] def AS_p778_nParam : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H R : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T → InM T M →
    IsHStar T M H → E1.nParam H ≤ 1 → R ≤ T → E1.nParam (R ⊔ oTwoUpper H) ≤ 1

abbrev FStar (G : Type) [Group G] : Type := ↥(CFSG.generalizedFitting G)

@[expose] def AS_E_1_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), SQTKGroup G →
    IsSimpleGroup (FStar G) → quasithinIsSylowTwo T → CFSG.generalizedFitting G ⊔ T = ⊤ →
      (∀ n : ℕ, 1 ≤ n →
        (IsPSL 2 2 n (FStar G) ∨ IsSz n (FStar G) ∨ IsPSU 3 2 n (FStar G) ∨
          IsPSL 3 2 n (FStar G) ∨ (IsPSp4 2 n (FStar G) ∨ n = 1 ∧ IsAlt 6 (FStar G)) ∨
          (Is2F4 n (FStar G) ∨ n = 1 ∧ IsTits (FStar G)) ∨
          (IsG2 2 n (FStar G) ∨ n = 1 ∧ IsPSU 3 3 1 (FStar G))) →
          E1.nParam (⊤ : Subgroup G) = n) ∧
      (IsPSL 4 2 1 (FStar G) ∨ IsPSL 5 2 1 (FStar G) → E1.nParam (⊤ : Subgroup G) = 1) ∧
      (∀ n : ℕ, 1 ≤ n → Is3D4 2 n (FStar G) → E1.nParam (⊤ : Subgroup G) ≤ (3 * n : ℕ)) ∧
      (IsAlt 7 (FStar G) → E1.nParam (⊤ : Subgroup G) = 1) ∧
      (IsSporadic .M11 (FStar G) ∨ IsSporadic .M12 (FStar G) ∨ IsSporadic .M24 (FStar G) ∨
          IsSporadic .He (FStar G) → E1.nParam (⊤ : Subgroup G) = 1) ∧
      (IsSporadic .J1 (FStar G) ∨ IsSporadic .J2 (FStar G) ∨ IsSporadic .J4 (FStar G) ∨
          IsSporadic .M22 (FStar G) ∨ IsSporadic .M23 (FStar G) ∨ IsSporadic .HS (FStar G) ∨
          IsSporadic .Ru (FStar G) → E1.nParam (⊤ : Subgroup G) ≤ 2) ∧
      (∀ p e : ℕ, p.Prime → p ≠ 2 → 5 < p ^ e → IsPSL 2 p e (FStar G) →
        E1.nParam (⊤ : Subgroup G) = 1) ∧
      (∀ (s : Bool) (p : ℕ), p.Prime → p ≠ 2 → IsPSLEps3 s p 1 (FStar G) →
        E1.nParam (⊤ : Subgroup G) = 1)

@[expose] def AS_C_1_13_b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L T : Subgroup G), IsSylowTwoOf T (L ⊔ T) →
    T ≤ Subgroup.normalizer (L : Set G) → IsShort2 L →
      (∀ (W : Type) [AddCommGroup W] [Module (ZMod 2) W]
          (ρ : Representation (ZMod 2) (↥L ⧸ CFSG.pCore 2 ↥L) W)
          (β : ↥(blockU L) →* Multiplicative W), Function.Surjective β →
          β.ker = (blockZ L).subgroupOf (blockU L) →
          (∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
            Multiplicative.toAdd (β v) =
              ρ (QuotientGroup.mk ℓ : ↥L ⧸ CFSG.pCore 2 ↥L) (Multiplicative.toAdd (β u))) →
          (blockU L ⊔ (T ⊓ Subgroup.centralizer (L : Set G))).relIndex (pCoreOf 2 (L ⊔ T)) ≤
            2 ^ Module.finrank (ZMod 2) (JonesParshall.H1 ρ)) ∧
      (CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
        ∃ (_ : ((blockU L).subgroupOf (pCoreOf 2 L)).Normal)
          (f : griessHopfMultiplier (↥L ⧸ CFSG.pCore 2 ↥L) →*
            ↥(pCoreOf 2 L) ⧸ (blockU L).subgroupOf (pCoreOf 2 L)), Function.Surjective f) ∧
      (Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3 → pCoreOf 2 L = blockU L)

@[expose] def AS_I_1_3_Sp4 : Prop :=
  ∀ (e : ℕ), 2 ≤ e → ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ e →
    ∀ (L : Type) [Group L] [Finite L] (φ : L →* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)),
      Function.Surjective φ → commutator L = ⊤ → φ.ker ≤ Subgroup.center L →
        Function.Injective φ

end CFSG.Quasithin.ASInputs
