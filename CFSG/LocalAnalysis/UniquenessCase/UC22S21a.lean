module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Lie
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open scoped Pointwise

section Section21Context

variable {G : Type} [Group G] [Finite G]

abbrev Choice2011 (G : Type) [Group G] : Type := Subgroup G → Subgroup G → Prop

@[expose] def AlphaCond (T B₀ : Subgroup G) (n : ℕ) : Prop :=
  ∀ e m : ℕ, Odd m → n = 2 ^ e * m →
    oPi {p | p.Prime ∧ p ∣ 2 ^ m - 1} B₀ ≤ normalizer (T : Set G)

structure Ctx21 (D : Data G) (Ch : Choice2011 G) where
  L0 : Subgroup G
  B0 : Subgroup G
  B : Subgroup G
  n : ℕ
  hL0 : L0 ∈ calLLow D.T D.M
  hn : NParam L0 n
  hB0 : B0 ∈ calB1 D.T D.M L0
  hpi : piSet B0 = etaSet n
  hα : AlphaCond D.T B0 n
  hBM : B0 ≤ D.M
  hch : Ch L0 B0
  hB : B ∈ calB1 D.T D.M L0
  hle : B ≤ B0

@[expose] def InvertedIn (M A : Subgroup G) : Prop :=
  ∃ m ∈ M, ∀ a ∈ A, m * a * m⁻¹ = a⁻¹

@[expose] def barImage (M P : Subgroup G) : Subgroup (Bar2 M) :=
  (P.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))

@[expose] def barPreimage (M : Subgroup G) (Y : Subgroup (Bar2 M)) : Subgroup G :=
  (Y.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype

@[expose] def oTwoEOf (M : Subgroup G) : Subgroup G :=
  barPreimage M (CFSG.layer (Bar2 M))

@[expose] def oTwoFOf (M : Subgroup G) : Subgroup G :=
  barPreimage M (CFSG.fittingSubgroup (Bar2 M))

@[expose] def centE (M : Subgroup G) : Subgroup (Bar2 M) :=
  Subgroup.centralizer (CFSG.layer (Bar2 M) : Set (Bar2 M))

@[expose] def conjSetOf (M L : Subgroup G) : Set (Subgroup G) :=
  {K | ∃ g ∈ M, K = L.map (MulAut.conj g).toMonoidHom}

@[expose] def conjClosure (M L : Subgroup G) : Subgroup G :=
  ⨆ K ∈ conjSetOf M L, K

@[expose] def IsPowTwo (n : ℕ) : Prop := ∃ k : ℕ, n = 2 ^ k

@[expose] def LieRankTwoEven (X : Type) [Group X] (n : ℕ) : Prop :=
  IsL3 X n ∨ IsSp4 X n ∨ IsG2 X n ∨ Is3D4 X n ∨ LieModel X .twistedF4 0 2 n ∨ IsU4 X n ∨
    IsU5 X n

end Section21Context

section Section21a

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_1 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ X : Subgroup G, (Nat.card X).Prime → Nat.card X ≠ 2 →
    IsSolvable ↥(X ⊔ D.T) → (∃ A : Subgroup G, IsHallOddIn A (X ⊔ D.T) ∧ IsMulCommutative A) →
    (∀ p ∈ piSet (X ⊔ D.T), p ≠ 2 → CFSG.Open.pRank p (X ⊔ D.T) ≤ 2) →
    X ∈ uniqueSet D.M →
      calMOf (X ⊔ D.T) = {D.M} ∧ ¬ X ≤ normalizer (D.T : Set G)

@[expose] def S21_2 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ A : Subgroup G, A ≤ c.B → ¬ normalizer (A : Set G) ≤ D.M

@[expose] def S21_8 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ n : ℕ, LieRankTwoEven (BarInf L) n →
    ¬ IsPowTwo n → ∀ r : ℕ, r.Prime → r ∣ 2 ^ n - 1 →
      (IsSp4 (Bar2 L) n ∧ (L.subgroupOf D.M).Normal ∧ ∃ t ∈ D.T, ActsNontrivOnDiagram L t) ∧
      (Odd n ∧ D.k = 1) ∧
      L = Opp r D.M ∧
      ∃ X : Subgroup G, Nat.card X = r ∧ X ≤ L ∧ X ∈ uniqueSet D.M

@[expose] def S21_12 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ p : ℕ, p.Prime → p ≠ 2 → IsChev (BarInf L) p →
    IsL2Odd (Bar2 L) p ∧ ⁅CFSG.Quasithin.opResidual 3 c.B, L⁆ ≤ CFSG.Open.pCoreOf 2 L

@[expose] def S21_16 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M,
    (∃ n : ℕ, Odd n ∧ IsSp4 (Bar2 L) n) ∨ (∃ n : ℕ, IsSU3 (Bar2 L) n) ∨
    (∃ n : ℕ, IsL2 (Bar2 L) n) ∨ (∃ n : ℕ, IsSz (Bar2 L) n) ∨
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsL2Odd (Bar2 L) p) ∨ IsJ1 (Bar2 L)

@[expose] def S21_17 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M,
    L = conjClosure D.M L ∨
    ((conjSetOf D.M L).ncard = 2 ∧ ∃ n : ℕ, 2 < n ∧ (IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n)) ∨
    ((conjSetOf D.M L).ncard = 2 ∧ IsJ1 (Bar2 L) ∧ c.n = 3 ∧ conjClosure D.M L = Opp 7 D.M ∧
      CFSG.Open.evenRank G = 3 ∧ ∀ A : Subgroup G, A ≤ L → Nat.card A = 7 → A ∈ uniqueSet D.M)

end Section21a

end CFSG.LocalAnalysis.UniquenessCase.UC22
