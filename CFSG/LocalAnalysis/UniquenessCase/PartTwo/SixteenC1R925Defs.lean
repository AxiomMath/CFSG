module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Inputs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def DvdOrThreeFree (n : ℕ) : CFSG.KCore.Catalogue.{0} :=
  fun S _ => Nat.card S ∣ n ∨ ¬ 3 ∣ Nat.card S

theorem isoInvariant_dvdOrThreeFree (n : ℕ) : CFSG.KCore.IsoInvariant (DvdOrThreeFree n) :=
  fun e h => by simpa only [DvdOrThreeFree, Nat.card_congr e.toEquiv] using h

@[expose] def IsPerfA5Cover (Y : Type) [Group Y] : Prop :=
  commutator Y = ⊤ ∧ ∃ (Z : Subgroup Y) (_ : Z.Normal), IsPGroup 2 Z ∧ IsAlt (Y ⧸ Z) 5

@[expose] def IsThreeGen {Γ : Type} [Group Γ] (A : Subgroup Γ) : Prop :=
  Subgroup.closure {a : Γ | a ∈ A ∧ ∃ k : ℕ, a ^ 3 ^ k = 1} = A

@[expose] def OddIdxProp (K : Type) [Group K] : Prop :=
  ∀ N Y D : Subgroup K, N ≠ ⊤ → Odd N.index → Nat.card D = 3 → D ≤ Y → Y ≤ N →
    normalizer (D : Set K) ≤ N → IsPerfA5Cover ↥Y →
    CFSG.KCore.KGroupNonab (DvdOrThreeFree 51840) ↥N → IsL3Five K ∧ IsSL2Prime ↥Y 5

@[expose] def OddIdxAll : Prop :=
  ∀ (Λ : Type) [Group Λ] [Finite Λ] (K N Y D : Subgroup Λ),
    CFSG.Open.IsKGroup ↥K → IsSimpleGroup ↥K → (∃ a b : ↥K, a * b ≠ b * a) →
    CFSG.Open.pRank 3 K = 1 → N ≤ K → N ≠ K → Odd (N.relIndex K) → Nat.card D = 3 → D ≤ Y →
    Y ≤ N → K ⊓ normalizer (D : Set Λ) ≤ N → IsPerfA5Cover ↥Y →
    CFSG.KCore.KGroupNonab (DvdOrThreeFree 51840) ↥N → IsL3Five ↥K ∧ IsSL2Prime ↥Y 5

structure R925Ctx (Γ : Type) [Group Γ] [Finite Γ] (Y K M : Subgroup Γ) : Prop where
  kgroup : CFSG.Open.IsKGroup Γ
  o2_eq_bot : CFSG.pCore 2 Γ = ⊥
  rank_three : CFSG.Open.pRank 3 (⊤ : Subgroup Γ) ≤ 1
  rank_gt_three : ∀ q : ℕ, q.Prime → 3 < q → CFSG.Open.pRank q (⊤ : Subgroup Γ) ≤ 2
  y_cover : IsPerfA5Cover ↥Y
  k_eq : K = Subgroup.normalClosure (Y : Set Γ)
  y_le : Y ≤ M
  m_catalogue : CFSG.KCore.KGroupNonab (DvdOrThreeFree 51840) ↥M
  m_odd : Odd M.index
  m_normalizer : ∀ D : Subgroup Γ, D ≤ M → Nat.card D = 3 → normalizer (D : Set Γ) ≤ M
  m_ne_top : M ≠ ⊤

abbrev ModO3p (Γ : Type) [Group Γ] : Type := Γ ⧸ CFSG.pPrimeCore 3 Γ

abbrev toModO3p (Γ : Type) [Group Γ] : Γ →* ModO3p Γ := QuotientGroup.mk' (CFSG.pPrimeCore 3 Γ)

@[expose] def R925Concl {Γ : Type} [Group Γ] (Y K : Subgroup Γ) : Prop :=
  IsSL2Prime ↥Y 5 ∧ (IsL3Five ↥K ∨ EqTimesOdd Y K)

structure R925Hyp {G : Type} [Group G] [Finite G] (D : Data G) (L P X H Y : Subgroup G) (z : G) :
    Prop where
  mem_calC : L ∈ calC D.M
  isU4 : IsU4 (Bar2 L) 1
  parabolic : IsParabolic2In L P
  x_eq : X = perfectCore P
  x_ne_bot : X ≠ ⊥
  not_le : ¬ H ≤ D.M
  fstar_eq : Fstar H = pCoreOf 2 H
  y_eq : Y = perfectCore (H ⊓ X)
  x_eq_sup : X = Y ⊔ pCoreOf 2 X
  o2_ne_bot : pCoreOf 2 Y ≠ ⊥
  odd_relIndex : Odd (D.M.relIndex H)
  sig_eq : D.sig = {3}
  rank_m : CFSG.Open.pRank 3 D.M = 3
  z_ne_one : z ≠ 1
  z_sq : z ^ 2 = 1
  h_eq : H = centralizer ({z} : Set G)
  rank_h : CFSG.Open.pRank 3 H = 1
  rank_h_gt : ∀ q : ℕ, q.Prime → 3 < q → CFSG.Open.pRank q H ≤ 2
  sylow : IsSylowIn 2 (D.T ⊓ H) H
  e16a5 : IsE16A5 ↥(starImg L Y)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
