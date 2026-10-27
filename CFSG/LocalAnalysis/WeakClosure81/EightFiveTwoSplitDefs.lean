module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoDispatch
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement Pointwise

@[expose] def W3Lem711Alt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ V H E : Subgroup G, Hyp711 V H E →
    (∀ u ∈ dSet V H E, ∀ v ∈ dSet V H E, ∃ k ∈ kSub V H E, u = k * v * k⁻¹) ∧
    ∀ (X : Type) [Group X] (φ : ↥(kSub V H E) →* X),
      IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ →
        SevenElevenAlt X (barSub (kSub V H E) φ V)

section Data

variable {G : Type} [Group G] [Finite G]

structure DispatchHyp (V H T U : Subgroup G) : Prop where
  hyp7 : Hyp7 V
  calH : IsCalH V H
  not_calH0 : ¬ IsCalH0 V H
  sylow : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G))
  eq_sup : H = kGenIn V H ⊔ T
  conj : ∃ g : G, U = conjSubgroup V g
  le_T : U ≤ T
  not_conj : ∀ h ∈ H, U ≠ conjSubgroup V h
  not_comm : ¬ ∀ h ∈ H, ∀ u ∈ U, ∀ v ∈ conjSubgroup V h, u * v = v * u
  inf_centralizer : U ⊓ Subgroup.centralizer (eSub V H T : Set G) = ⊥
  cent_eq : ∀ u ∈ U, u ≠ 1 → eSub V H T ⊓ Subgroup.centralizer (U : Set G) =
    eSub V H T ⊓ Subgroup.centralizer ({u} : Set G)
  comm_V : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u
  odd_comm : ∀ Q : Subgroup G, Q ≤ kGenIn V H → U ≤ Subgroup.normalizer (Q : Set G) →
    Odd ((Subgroup.centralizer (eSub V H T : Set G)).relIndex Q) →
      ⁅Q, U⁆ ≤ Subgroup.centralizer (eSub V H T : Set G)
  faithful : ∀ Y : Subgroup G, Y ≤ U → ⁅Y, kGenIn V H⁆ ≤ Subgroup.centralizer (eSub V H T : Set G) →
    Y = ⊥
  inf_V_ne_bot : V ⊓ Subgroup.centralizer (eSub V H T : Set G) ≠ ⊥

@[expose] def DispatchConcl (V H T : Subgroup G) : Prop :=
  ∃ m n : ℕ, 3 < m ∧ (KBarCenterShape V H T (fun X _ => IsSpGp X m n) ∨
    KBarCenterShape V H T (fun X _ => IsPSUGp X m n))

theorem w3Lem85TwoDispatch_iff :
    W3Lem85TwoDispatch G ↔
      ∀ V H T U : Subgroup G, DispatchHyp V H T U → DispatchConcl V H T := by
  constructor
  · intro h V H T U hD
    exact h V H T U hD.hyp7 hD.calH hD.not_calH0 hD.sylow hD.eq_sup hD.conj hD.le_T hD.not_conj
      hD.not_comm hD.inf_centralizer hD.cent_eq hD.comm_V hD.odd_comm hD.faithful hD.inf_V_ne_bot
  · intro h V H T U h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    exact h V H T U ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

end Data

section Ambient

variable {G : Type} [Group G]

abbrev ambV (V H : Subgroup G) : Subgroup ↥H := V.subgroupOf H

abbrev ambE (V H T : Subgroup G) : Subgroup ↥H :=
  eSub (V.subgroupOf H) (⊤ : Subgroup ↥H) (T.subgroupOf H)

abbrev ambK (V H T : Subgroup G) : Subgroup ↥H :=
  kSub (V.subgroupOf H) (⊤ : Subgroup ↥H) (ambE V H T)

end Ambient

section Abstract

structure BarSituation (X : Type) [Group X] (S : Subgroup X) : Prop where
  elemAbelian : IsElemAbelian 2 S
  normalClosure_eq_top : Subgroup.normalClosure (S : Set X) = ⊤
  pCore_eq_bot : CFSG.pCore 2 X = ⊥
  oddTransp : Nat.card S = 2 →
    CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp (Group.conjugatesOfSet ((S : Set X) \ {1}))

@[expose] def CentralInSylow (X : Type) [Group X] (S : Subgroup X) : Prop :=
  ∃ P : Sylow 2 X, S ≤ (P : Subgroup X) ∧ ∀ s ∈ S, ∀ p ∈ (P : Subgroup X), s * p = p * s

structure ActionFacts (X : Type) [Group X] (S : Subgroup X) (A : Subgroup (MulAut X))
    (Z₁ : Subgroup X) (r : ℕ) : Prop where
  elemAbelian : IsElemAbelian 2 A
  card_eq : Nat.card A = 2 ^ r
  card_lt : Nat.card S < 2 ^ r
  fixes : ∀ a ∈ A, ∀ s ∈ S, a s = s
  le_center : Z₁ ≤ Subgroup.center X
  oddComm : ∀ Q : Subgroup X, Odd (Nat.card Q) → (∀ a ∈ A, ∀ q ∈ Q, a q ∈ Q) →
    ∀ a ∈ A, ∀ q ∈ Q, a q * q⁻¹ ∈ Z₁

structure BarFacts (X : Type) [Group X] (S : Subgroup X) (A : Subgroup (MulAut X))
    (Z₁ : Subgroup X) (r : ℕ) : Prop extends ActionFacts X S A Z₁ r where
  situation : BarSituation X S
  central : Nat.card S = 2 → CentralInSylow X S
  rank_unitary : ∀ n : ℕ, IsPSUGp (X ⧸ Subgroup.center X) 3 n →
    (∀ s ∈ S, s ≠ 1 → IsUnitaryTransvection X 3 n s) → 2 * n + 1 ≤ r
  rank_l2 : ∀ n : ℕ, IsL2Gp (X ⧸ Subgroup.center X) n → n + 1 ≤ r

@[expose] def BarConcl (X : Type) [Group X] : Prop :=
  ∃ m n : ℕ, 3 < m ∧ (IsSpGp (X ⧸ Subgroup.center X) m n ∨ IsPSUGp (X ⧸ Subgroup.center X) m n)

end Abstract

@[expose] def L2RootCommutatorRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K I : Subgroup G) (n : ℕ),
    IsElemAbelian 2 I → K ≤ Subgroup.normalizer (I : Set G) →
    K ⊓ Subgroup.centralizer (I : Set G) ≤ pCoreOf 2 K →
    ∀ (X : Type) [Group X] (φ : ↥K →* X), IsBarMap K (pCoreOf 2 K) φ →
      IsL2Gp (X ⧸ Subgroup.center X) n →
      ∀ v : ↥K, (v : G) * (v : G) = 1 → φ v ≠ 1 →
        n ≤ rk ↥⁅I, Subgroup.zpowers (v : G)⁆

@[expose] def W3Lem85TwoGap1 : Prop :=
  (∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), IsPSUGp Y 3 n →
    ∀ A : Subgroup (MulAut Y), IsElemAbelian 2 A → Nat.card A ≤ 2 ^ (n + 1)) ∧
  (∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), IsSzGp Y n →
    ∀ P : Sylow 2 Y, Nat.card (Subgroup.center (P : Subgroup Y)) = 2 ^ n)

@[expose] def W3Lem85TwoGap2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (S : Subgroup X), BarSituation X S →
    SevenElevenLinearShape X S →
    ∀ A : Subgroup (MulAut X), IsElemAbelian 2 A → (∀ a ∈ A, ∀ s ∈ S, a s = s) →
      Nat.card A ≤ Nat.card S

@[expose] def W3Lem85TwoGap3 (G : Type) [Group G] [Finite G] : Prop :=
  (∀ (X : Type) [Group X] [Finite X] (S : Subgroup X), BarSituation X S →
    Nat.card (Subgroup.center X) = 3 → SevenElevenASixShape X S →
    ∀ A : Subgroup (MulAut X), IsElemAbelian 2 A → (∀ a ∈ A, ∀ s ∈ S, a s = s) →
      (∀ a ∈ A, ∀ z ∈ Subgroup.center X, a z = z) → Nat.card A ≤ Nat.card S) ∧
  (∀ V H T U : Subgroup G, DispatchHyp V H T U →
    ¬ KBarShape V H T (fun Y _ => Nonempty (Y ≃* alternatingGroup (Fin 6))))

@[expose] def W3Lem85TwoGap4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (S : Subgroup X), BarSituation X S → Nat.card S = 2 →
    ((∃ m n : ℕ, IsOrthGp (X ⧸ Subgroup.center X) m n) ∨
      (∃ n m : ℕ, 2 ≤ m ∧ IsL2WrSymGp (X ⧸ Subgroup.center X) n m)) →
    ¬ CentralInSylow X S

@[expose] def W3Lem85TwoGap5 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ V H T U : Subgroup G, DispatchHyp V H T U →
    ∀ (X : Type) [Group X] (φ : ↥(kGenIn V H) →* X),
      IsBarMap (kGenIn V H) (pCoreOf 2 (kGenIn V H)) φ →
      Nat.card (barSub (kGenIn V H) φ V) = 2 →
      (∃ n : ℕ, IsSymGp (X ⧸ fusionOddCore X) n) →
        KBarCenterShape V H T (fun Y _ => IsSpGp Y 4 1)

@[expose] def W3Lem85TwoGap6 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (S : Subgroup X), BarSituation X S → Nat.card S = 2 →
    IsThreeCoverOrth6Minus X → ¬ CentralInSylow X S

end CFSG.LocalAnalysis.WeakClosure81

end
