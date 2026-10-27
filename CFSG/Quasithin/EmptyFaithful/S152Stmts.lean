module

public import CFSG.Quasithin.EmptyFaithful.S152Defs
public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.Quasithin.Vol2.Ch1Xi
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.Background.F7
public import CFSG.Quasithin.Background.A3Structure316
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List
public import CFSG.Quasithin.Background.C2Defs
public import CFSG.Quasithin.Background.ThreePrimeGroup

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def IsLnTwo (n : ℕ) (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))

@[expose] def IsAutLnTwo (n : ℕ) (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)))

@[expose] def IsL2Prime (p : ℕ) (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))

@[expose] def StageTheorem15115 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M →
    ¬ (Case1517Four T M (V154 T Mc M) (mBar0 T Mc M) ∨
      (∃ p : ℕ, (p = 3 ∨ p = 5) ∧ Case1517Six T M (V154 T Mc M) (mBar0 T Mc M) p) ∨
      Case1517Seven T M (V154 T Mc M) (mBar0 T Mc M))

structure Lemma15201Concl (T Mc M : Subgroup G) : Prop where
  card : Nat.card (V154 T Mc M) = 16
  cases : Case1517One M (V154 T Mc M) (mBar0 T Mc M) ∨
    Case1517Two M (V154 T Mc M) (mBar0 T Mc M) ∨ Case1517Three M (V154 T Mc M) (mBar0 T Mc M) ∨
    Case1517Five T M (V154 T Mc M) (mBar0 T Mc M)
  lt_three : V154 T Mc M < VZ T M → Case1517Three M (V154 T Mc M) (mBar0 T Mc M)

@[expose] def StageLemma15201 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    Lemma15201Concl T Mc M

@[expose] def StageLemma15202 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ X : Subgroup G, T ≤ X → X ≤ M →
      ((m0Of T Mc M : Set G) ⊆ (X : Set G) *
          ((M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G) ∨
        (m0Of T Mc M : Set G) ⊆ (X : Set G) *
          ((M ⊓ Subgroup.normalizer
            ((quasithinOmegaOneCenter T ⊓ V154 T Mc M : Subgroup G) : Set G) : Subgroup G) :
              Set G)) →
      IsUniqueM X M

@[expose] def Case15203i (T Mc M : Subgroup G) : Prop :=
  autOn (yOf152 T Mc M) (V154 T Mc M) = oTwoUpper (mBar0 T Mc M) ∧
    yOf152 T Mc M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤ pCoreOf 2 M ∧
    (Case1517Three M (V154 T Mc M) (mBar0 T Mc M) →
      IsThreePrimeGroup (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)))

@[expose] def Case15203ii (T Mc M : Subgroup G) : Prop :=
  Case1517Three M (V154 T Mc M) (mBar0 T Mc M) ∧
    Nat.card (autOn (rcOf Mc M) (V154 T Mc M)) = 2 ∧
    InvertsOn (autOn (rcOf Mc M) (V154 T Mc M)) (oTwoUpper (mBar0 T Mc M)) ∧
    oTwoUpper (mBar0 T Mc M) = oTwoUpper (autOn M (V154 T Mc M)) ∧
    oTwoUpper (autOn M (V154 T Mc M)) = autOn (yOf152 T Mc M) (V154 T Mc M) ∧
    IsPOnePlusTwo 3 ↥(imageOTwoQuot M (yOf152 T Mc M)) ∧
    oTwoUpper (oTwoZIn (yOf152 T Mc M)) =
      thetaOf (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G))

@[expose] def Case15203iii (T Mc M : Subgroup G) : Prop :=
  Case1517Three M (V154 T Mc M) (mBar0 T Mc M) ∧
    Nat.card (autOn (rcOf Mc M) (V154 T Mc M)) = 2 ∧
    InvertsOn (autOn (rcOf Mc M) (V154 T Mc M)) (autOn (yOf152 T Mc M) (V154 T Mc M)) ∧
    Nat.card (autOn (yOf152 T Mc M) (V154 T Mc M)) = 3 ∧
    yOf152 T Mc M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤ pCoreOf 2 M ∧
    ∃ n : ℕ, 1 ≤ n ∧ ∀ P : Subgroup G, IsSylowIn 3 P M → IsZ3TimesZ3Pow n ↥P

structure Lemma15203Concl (T Mc M : Subgroup G) : Prop where
  ne_bot : autOn (yOf152 T Mc M) (V154 T Mc M) ≠ ⊥
  comm_eq : autOn (yOf152 T Mc M) (V154 T Mc M) =
    ⁅autOn (yOf152 T Mc M) (V154 T Mc M), autOn (rcOf Mc M) (V154 T Mc M)⁆
  cases : Case15203i T Mc M ∨ Case15203ii T Mc M ∨ Case15203iii T Mc M
  normal : M ≤ Subgroup.normalizer (yOf152 T Mc M : Set G)
  unique : autOn (yOf152 T Mc M) (V154 T Mc M) = oTwoUpper (mBar0 T Mc M) →
    IsUniqueM (yOf152 T Mc M ⊔ T) M
  frattini : (M : Set G) = ((M ⊓ Mc : Subgroup G) : Set G) * (oTwoUpper (m0Of T Mc M) : Set G)
  centralizes : ⁅rcOf Mc M ⊔ yOf152 T Mc M,
    M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)⁆ ≤ pCoreOf 2 M

@[expose] def StageLemma15203 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    Lemma15203Concl T Mc M

@[expose] def StageLemma15204 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H →
      ¬ Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 5) ≀ᵣ Multiplicative (ZMod 2))

@[expose] def StageLemma15205 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ M₁ : Subgroup G, InM T M₁ ↔ (M₁ = M ∨ M₁ = Mc)

structure IsY1 (T Mc M Y₁ : Subgroup G) : Prop where
  le : Y₁ ≤ yOf152 T Mc M
  normalized : T ≤ Subgroup.normalizer (Y₁ : Set G)
  eq_oTwo : Y₁ = oTwoUpper Y₁
  quot : IsSmallQuot152 (Y₁ ⊔ rcOf Mc M)
  centralizer : Y₁ ⊓ Subgroup.centralizer (V154 T Mc M : Set G) = pCoreOf 2 Y₁
  unique : IsUniqueM (Y₁ ⊔ T) M

@[expose] def StageLemma15206 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∃ Y₁ : Subgroup G, IsY1 T Mc M Y₁

structure Lemma15207Concl (T Mc M Y₁ : Subgroup G) : Prop where
  unique : IsUniqueM (yOf152 T Mc M ⊔ T) M
  normalizer_le : ∀ X : Subgroup G, X ≠ ⊥ → X = oTwoUpper X →
    X ≤ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) →
      T ≤ Subgroup.normalizer (X : Set G) → Subgroup.normalizer (X : Set G) ≤ M
  acts : ∀ X : Subgroup G, X ≠ ⊥ → X = oTwoUpper X →
    X ≤ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) →
      T ≤ Subgroup.normalizer (X : Set G) → (pCoreOf 2 X).relIndex X = 3 →
      X ≤ Subgroup.normalizer (Y₁ : Set G)

@[expose] def StageLemma15207 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ Y₁ : Subgroup G, IsY1 T Mc M Y₁ → Lemma15207Concl T Mc M Y₁

@[expose] def StageLemma15208 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H →
      Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2))

structure Notation15209Concl (T Mc M H : Subgroup G) : Prop where
  le_mc : H ≤ Mc
  eq_inf : T = M ⊓ H
  eq_normalizer : M ⊓ H = H ⊓ Subgroup.normalizer (V154 T Mc M : Set G)
  card_conj : (H ⊓ Subgroup.normalizer (V154 T Mc M : Set G)).relIndex H = 9
  pair : ∃ H₁ H₂ : Subgroup G, IsHPair H (V154 T Mc M) H₁ H₂
  card_delta : ∀ A ∈ deltaSet H (V154 T Mc M), (A ⊓ pCoreOf 2 H).relIndex A = 2
  sigmaPrime_nonempty : (sigmaPrime T H (V154 T Mc M)).Nonempty

@[expose] def StageNotation15209 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → Notation15209Concl T Mc M H

@[expose] def StageLemma15210 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ D : Subgroup (MulAut (V154 T Mc M)), D ∈ QsetOn T (V154 T Mc M) →
      D ≤ mBar0 T Mc M ∧ Nat.card D = 2 ∧
      Nat.card (⁅V154 T Mc M, preOn T (V154 T Mc M) D⁆ : Subgroup G) = 4 ∧
      T ≤ Subgroup.normalizer ((⁅V154 T Mc M, preOn T (V154 T Mc M) D⁆ : Subgroup G) : Set G)

structure Lemma15211Concl (T Mc M H B : Subgroup G) : Prop where
  quad : autOn B (V154 T Mc M) ∈ QsetOn M (V154 T Mc M)
  centralizes : oTwoUpper H ≤ Subgroup.centralizer ((⁅V154 T Mc M, B⁆ : Subgroup G) : Set G)
  card : Nat.card (⁅V154 T Mc M, B⁆ : Subgroup G) = 4
  elemAbelian : IsElemAbelian 2 (⁅V154 T Mc M, B⁆ : Subgroup G)
  normal : T ≤ Subgroup.normalizer ((⁅V154 T Mc M, B⁆ : Subgroup G) : Set G)

@[expose] def StageLemma15211 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ B ∈ sigmaPrime T H (V154 T Mc M),
      Lemma15211Concl T Mc M H B

@[expose] def Case15212ii (T Mc Kc : Subgroup G) : Prop :=
  quasithinIsMaximalLocal T Kc ∧ Kc ∈ cComp Mc ∧
    ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ IsAutLnTwo n (OTwoQuot (Kc ⊔ T))

@[expose] def Case15212iii (T Mc Kc : Subgroup G) : Prop :=
  ∃ (L : Subgroup G) (t : G), quasithinIsMaximalLocal T L ∧ L ∈ cComp Mc ∧ t ∈ T ∧
    t ∉ Subgroup.normalizer (L : Set G) ∧ Kc = L ⊔ conjSub t L ∧
    ⁅L, conjSub t L⁆ ≤ pCoreOf 2 Mc ∧
    ((∃ f : ℕ, Even f ∧ IsL2Quot f (OTwoQuot L)) ∨
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsL2Prime p (OTwoQuot L)))

@[expose] def Case15212He (T Mc Kc : Subgroup G) : Prop :=
  quasithinIsMaximalLocal T Kc ∧ Kc ∈ cComp Mc ∧
    Nonempty (OTwoQuot Kc ≃* CFSG.Blueprint.NativeSporadic.Carrier .He)

structure Lemma15212Concl (T Mc M H B : Subgroup G) : Prop where
  xi : IsXi T (oTwoUpper H)
  cases : conjClosure (oTwoUpper H) Mc = oTwoUpper H ∨
    Case15212ii T Mc (conjClosure (oTwoUpper H) Mc) ∨
    Case15212iii T Mc (conjClosure (oTwoUpper H) Mc) ∨
    Case15212He T Mc (conjClosure (oTwoUpper H) Mc)
  unique : IsUniqueM H Mc
  normal : H ≤ Subgroup.normalizer ((⁅V154 T Mc M, B⁆ : Subgroup G) : Set G)
  normalizer_le : Subgroup.normalizer ((⁅V154 T Mc M, B⁆ : Subgroup G) : Set G) ≤ Mc
  eq_oThreePrime : conjClosure (oTwoUpper H) Mc = oPrimeResidualOf 3 Mc
  le_centralizer : conjClosure (oTwoUpper H) Mc ≤
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)
  not_six : ¬ Case1512Six T Mc M
  eq_VZ : V154 T Mc M = VZ T M

@[expose] def StageLemma15212 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ B ∈ sigmaPrime T H (V154 T Mc M),
      Lemma15212Concl T Mc M H B

@[expose] def Case15213i (T Mc M : Subgroup G) : Prop :=
  (Case1517One M (V154 T Mc M) (mBar0 T Mc M) ∨ Case1517Five T M (V154 T Mc M) (mBar0 T Mc M)) ∧
    IsSmallGroup152 ↥(autOn M (V154 T Mc M))

structure Lemma15213Concl (T Mc M H : Subgroup G) : Prop where
  cases : Case15213i T Mc M ∨ Case15213ii T Mc M H
  exists_B0 : ∃ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ ∧
    (∀ B₀' : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀' → B₀' = B₀) ∧
    ∀ B ∈ sigmaPrime T H (V154 T Mc M), autOn B (V154 T Mc M) = B₀ ∧
      V154 T Mc M ⊓ Subgroup.centralizer (B : Set G) = ⁅V154 T Mc M, B⁆ ∧
      ⁅V154 T Mc M, B⁆ = ⁅V154 T Mc M, preOn T (V154 T Mc M) B₀⁆ ∧
      ⁅V154 T Mc M, preOn T (V154 T Mc M) B₀⁆ =
        V154 T Mc M ⊓ Subgroup.centralizer (preOn T (V154 T Mc M) B₀ : Set G)

@[expose] def StageLemma15213 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → Lemma15213Concl T Mc M H

structure Lemma15214Concl (T Mc M : Subgroup G) (B₀ : Subgroup (MulAut (V154 T Mc M))) : Prop where
  mc_eq : Mc = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)
  le_zS : quasithinOmegaOneCenter T ≤ zSOf T Mc M B₀
  cases : (sOf152 T Mc M B₀ = T ∧ quasithinOmegaOneCenter T = zSOf T Mc M B₀ ∧
      Nat.card (zSOf T Mc M B₀) = 4 ∧ IsElemAbelian 2 (zSOf T Mc M B₀)) ∨
    ((Nonempty (↥(autOn M (V154 T Mc M)) ≃* ↥(CFSG.Open.Sz 0)) ∨
        IsOmegaFourPlusOn M (V154 T Mc M)) ∧
      Nat.card (quasithinOmegaOneCenter T) = 2 ∧ (sOf152 T Mc M B₀).relIndex T = 2)
  baum_le : baum T ≤ sOf152 T Mc M B₀
  zS_eq : zSOf T Mc M B₀ = omegaOneCenterOf (sOf152 T Mc M B₀)
  inf_eq : M ⊓ Mc = M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ∧
    M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) =
      (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) ⊔ T
  params : ∃ hV : IsElemAbelian 2 (V154 T Mc M),
    E3.mParam (autI hV M) = 2 ∧ E3.aParam (autI hV M) = 1
  bar_T : sOf152 T Mc M B₀ = T → Nat.card (autOn T (V154 T Mc M)) = 2

@[expose] def StageLemma15214 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ → Lemma15214Concl T Mc M B₀

@[expose] def StageTheorem15215 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
      IsUniqueM (Mc ⊓ Subgroup.centralizer (zSOf T Mc M B₀ : Set G)) Mc

structure Lemma15216Concl (T Mc M H : Subgroup G) (B₀ : Subgroup (MulAut (V154 T Mc M)))
    (I : Subgroup G) : Prop where
  centralizer_eq : Subgroup.centralizer (zSOf T Mc M B₀ : Set G) =
    Mc ⊓ Subgroup.centralizer (zSOf T Mc M B₀ : Set G)
  centralizer_le : Mc ⊓ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) ≤ Mc ⊓ I
  KS_le : oTwoUpper H ⊔ sOf152 T Mc M B₀ ≤ Mc ⊓ I
  lt_zS : quasithinOmegaOneCenter T < zSOf T Mc M B₀

@[expose] def StageLemma15216 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
      ∀ I : Subgroup G, Hyp15215 T Mc M B₀ I → Lemma15216Concl T Mc M H B₀ I

@[expose] def StageLemma15217 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
      ∀ I : Subgroup G, Hyp15215 T Mc M B₀ I →
        (Nonempty (↥(autOn M (V154 T Mc M)) ≃* ↥(CFSG.Open.Sz 0)) ∨
          IsOmegaFourPlusOn M (V154 T Mc M)) ∧
        Nat.card (quasithinOmegaOneCenter T) = 2 ∧ (sOf152 T Mc M B₀).relIndex T = 2

structure Lemma15218Concl (T Mc M H : Subgroup G) (B₀ : Subgroup (MulAut (V154 T Mc M)))
    (I : Subgroup G) : Prop where
  sylow : IsSylowTwoOf (sOf152 T Mc M B₀) I
  baum_eq : baum T = baum (sOf152 T Mc M B₀)
  cgs_le : cgsIn I (baum T) ≤ M ⊓ I
  cases : Concl15218i Mc M I ∨ Concl15218ii T Mc M H B₀ I

@[expose] def StageLemma15218 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
      ∀ I : Subgroup G, Hyp15215 T Mc M B₀ I → Lemma15218Concl T Mc M H B₀ I

structure Lemma15220Concl (T Mc M : Subgroup G) (B₀ : Subgroup (MulAut (V154 T Mc M)))
    (I : Subgroup G) : Prop where
  hyp115 : ∀ z ∈ quasithinOmegaOneCenter T, z ≠ 1 → Lemma115Hyp I (sOf152 T Mc M B₀) Mc z
  charTwo : CharTwo (Mc ⊓ I)
  oddCore : oddCoreIn I = ⊥

@[expose] def StageLemma15220 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
      ∀ I : Subgroup G, Hyp15215 T Mc M B₀ I → Lemma15220Concl T Mc M B₀ I

structure Lemma15221Concl (T Mc M H H₁ H₂ : Subgroup G)
    (B₀ : Subgroup (MulAut (V154 T Mc M))) (I : Subgroup G) : Prop where
  one : ¬ IsIrredOnSection (sOf152 T Mc M B₀) (oTwoUpper H) (pCoreOf 2 (oTwoUpper H)) →
    oTwoUpper H ⊔ sOf152 T Mc M B₀ = H₁ ⊔ H₂ ∧
      (∀ t ∈ T, t ∉ sOf152 T Mc M B₀ → conjSub t (oTwoUpper H₁) = oTwoUpper H₂) ∧
      conjClosure (oTwoUpper H) Mc ≤ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) ∧
      conjClosure (oTwoUpper H) Mc = oPrimeResidualOf 3 (Mc ⊓ I)
  two : conjClosure (oTwoUpper H) Mc = oTwoUpper H →
    IsThreePrimeGroup (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G))
  three : IsLnTwo 4 (OTwoQuot (conjClosure (oTwoUpper H) Mc)) → Concl15218ii T Mc M H B₀ I →
    (∃ Y₁ : Subgroup G, Y₁ = oTwoUpper Y₁ ∧ Y₁ ≤ M ⊓ I ∧
        sOf152 T Mc M B₀ ≤ Subgroup.normalizer (Y₁ : Set G) ∧
        Nonempty (OTwoQuot (Y₁ ⊔ sOf152 T Mc M B₀) ≃* Equiv.Perm (Fin 3)) ∧
        ¬ Y₁ ≤ Mc ⊓ I) →
    IsIrredOnSection (sOf152 T Mc M B₀) (oTwoUpper H) (pCoreOf 2 (oTwoUpper H))

@[expose] def StageLemma15221 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ H₁ H₂ : Subgroup G, IsHPair H (V154 T Mc M) H₁ H₂ →
      ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
        ∀ I : Subgroup G, Hyp15215 T Mc M B₀ I → Lemma15221Concl T Mc M H H₁ H₂ B₀ I

@[expose] def StageLemma15222 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ H₁ H₂ : Subgroup G, IsHPair H (V154 T Mc M) H₁ H₂ →
      ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
        ∀ I : Subgroup G, Hyp15215 T Mc M B₀ I → Concl15218ii T Mc M H B₀ I → CharTwo I →
          IsThreePrimeGroup (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) →
          ¬ IsIrredOnSection (sOf152 T Mc M B₀) (oTwoUpper H) (pCoreOf 2 (oTwoUpper H)) →
          ∀ Y₁ : Subgroup G, Y₁ = oTwoUpper Y₁ → Y₁ ≤ M ⊓ I →
            sOf152 T Mc M B₀ ≤ Subgroup.normalizer (Y₁ : Set G) →
            Nonempty (OTwoQuot (Y₁ ⊔ sOf152 T Mc M B₀) ≃* Equiv.Perm (Fin 3)) →
            ¬ ⁅Y₁, oTwoUpper H₂⁆ ≤ Y₁ ⊓ oTwoUpper H₂

@[expose] def StageLemma15223 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
      ∀ I : Subgroup G, Hyp15215.Min T Mc M B₀ I → ¬ CharTwo I

@[expose] def StageLemma15224 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
      ∀ I : Subgroup G, Hyp15215.Min T Mc M B₀ I → ∀ L : Subgroup G, IsComponentIn L I →
        ¬ L ≤ Mc → ¬ Lemma115LieCharTwo (↥L ⧸ Subgroup.center ↥L)

@[expose] def Stage15215Tail : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ B ∈ sigmaPrime T H (V154 T Mc M),
      ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
        Lemma15212Concl T Mc M H B → Lemma15214Concl T Mc M B₀ →
        ∀ I : Subgroup G, Hyp15215.Min T Mc M B₀ I → Lemma15220Concl T Mc M B₀ I → ¬ CharTwo I →
          (∀ L : Subgroup G, IsComponentIn L I → ¬ L ≤ Mc →
            ¬ Lemma115LieCharTwo (↥L ⧸ Subgroup.center ↥L)) → False

structure Lemma15225Concl (T Mc M : Subgroup G) : Prop where
  cases : Case15213i T Mc M
  bar_S : ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
    autOn (sOf152 T Mc M B₀) (V154 T Mc M) = omegaOneOf (autOn T (V154 T Mc M))
  comm_le : ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
    ⁅V154 T Mc M, sOf152 T Mc M B₀⁆ ≤ zSOf T Mc M B₀
  lambda_le : ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
    lambdaOf T ≤ sOf152 T Mc M B₀

@[expose] def StageLemma15225 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    Lemma15225Concl T Mc M

structure Lemma15226Concl (T Mc M : Subgroup G) : Prop where
  r_gt : ∃ hV : IsElemAbelian 2 (V154 T Mc M),
    1 < E3.rParam (V154 T Mc M) ∧ 1 < E3.sParam hV
  w0_le : E3.wClos (V154 T Mc M) 0 T ≤ T ⊓ Subgroup.centralizer (V154 T Mc M : Set G)

@[expose] def StageLemma15226 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    Lemma15226Concl T Mc M ∧ ∀ H : Subgroup G, IsHStar T M H →
      E3.wClos (V154 T Mc M) 0 (pCoreOf 2 H) ≤
        H ⊓ Subgroup.centralizer (conjClosure (V154 T Mc M) H : Set G)

structure Lemma15227Concl (T Mc M H : Subgroup G) (B₀ : Subgroup (MulAut (V154 T Mc M))) :
    Prop where
  one : oTwoFstarIn Mc ≤ conjClosure (oTwoUpper H) Mc ⊔ (M ⊓ Mc)
  two : V154 T Mc M ≤ pCoreOf 2 Mc
  three : ∀ g : G, zSOf T Mc M B₀ ⊓ conjSub g (V154 T Mc M) ≠ ⊥ →
    ⁅V154 T Mc M, conjSub g (V154 T Mc M)⁆ = ⊥

@[expose] def StageLemma15227 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
      Lemma15227Concl T Mc M H B₀

@[expose] def StageLemma15228 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
      ⁅conjClosure (V154 T Mc M) H, lambdaOf (pCoreOf 2 H)⁆ ≤ zSOf T Mc M B₀

@[expose] def StageObserveF7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → AmalgamHypV (M ⊔ H) M H T (V154 T Mc M)

@[expose] def StageFinal152 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ H₁ H₂ : Subgroup G, IsHPair H (V154 T Mc M) H₁ H₂ →
      ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
        AmalgamHypV (M ⊔ H) M H T (V154 T Mc M) →
        Lemma1518Concl T Mc M →
        (V154 T Mc M ≤ pCoreOf 2 H ∧ IsElemAbelian 2 (conjClosure (V154 T Mc M) H)) →
        Concl319 T M (V154 T Mc M) H True →
        Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2)) →
        Lemma15225Concl T Mc M → Lemma15226Concl T Mc M →
        (E3.wClos (V154 T Mc M) 0 (pCoreOf 2 H) ≤
          H ⊓ Subgroup.centralizer (conjClosure (V154 T Mc M) H : Set G)) →
        Lemma15227Concl T Mc M H B₀ →
        ⁅conjClosure (V154 T Mc M) H, lambdaOf (pCoreOf 2 H)⁆ ≤ zSOf T Mc M B₀ → False

end CFSG.Quasithin
