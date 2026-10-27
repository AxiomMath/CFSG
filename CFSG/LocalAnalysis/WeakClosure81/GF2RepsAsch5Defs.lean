module

public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs
public import CFSG.Quasithin.Background.A3Structure38Facts
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FSqIndex

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
  (IsL2 IsL3 IsU3 IsSp4 IsAlt Bar2 OInf Fstar)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (InEGroup InFGroup)
open CFSG.Blueprint (LieModel)

@[expose] def HasUniqueMaxOver {K : Type} [Group K] (T : Subgroup K) : Prop :=
  ∃ M : Subgroup K, M < ⊤ ∧ ∀ X : Subgroup K, T ≤ X → X < ⊤ → X ≤ M

@[expose] def innAutOf (L₀ : Type) [Group L₀] : Subgroup (MulAut L₀) :=
  (MulAut.conj : L₀ →* MulAut L₀).range

@[expose] def AlmostSimpleData (L₀ : Type) [Group L₀] (A S : Subgroup (MulAut L₀)) : Prop :=
  innAutOf L₀ ≤ A ∧ IsSylowIn 2 S A ∧ innAutOf L₀ ⊔ S = A

@[expose] def IsoInvPred (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (X Y : Type) [Group X] [Group Y], Nonempty (X ≃* Y) → P X → P Y

@[expose] def CFShape (K : Type) [Group K] (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (L : Type) [Group L], E1.IsCompositionFactor K L → (∃ a b : L, a * b ≠ b * a) → P L

@[expose] def Shape54 {Q : Type} [Group Q] [Finite Q] (H T L : Subgroup Q) : Prop :=
  HasQuotShape L (OInf H : Set Q) (fun X _ => IsL2 X 2 ∨ IsU3 X 2) ∨
  HasQuotShape L (OInf H : Set Q) (fun X _ => IsAlt X 6 ∨ IsL3 X 1) ∨
  (HasQuotShape L (OInf H : Set Q) (fun X _ => IsL3 X 2 ∨ IsSp4 X 2) ∧
    ∃ t ∈ T, ActsOnDynkinMod (OInf H) L t) ∨
  (∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ 9 < p ^ e ∧
    HasQuotShape L (OInf H : Set Q) (fun X _ => F6.IsL2 p e X)) ∨
  (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
    ((p % 4 = 3 ∧ HasQuotShape L (OInf H : Set Q) (fun X _ => LieModel X .PSL 3 p 1)) ∨
     (p % 4 = 1 ∧ HasQuotShape L (OInf H : Set Q) (fun X _ => LieModel X .PSU 3 p 1)))) ∨
  (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
    HasQuotShape L (OInf H : Set Q) (fun X _ => LieModel X .PSp 2 p 1))

@[expose] def Shape512 {Q : Type} [Group Q] [Finite Q] (H : Subgroup Q) : Prop :=
  (∃ p e : ℕ, p.Prime ∧ 5 ≤ p ∧ 9 < p ^ e ∧
    HasQuotShape (fStarMod (relPPrimeCore 3 H) H) (relPPrimeCore 3 H : Set Q)
      (fun X _ => F6.IsL2 p e X)) ∨
  (∃ p f : ℕ, p.Prime ∧ 5 ≤ p ∧
    ((p ^ f % 3 = 2 ∧ p ^ f % 4 = 3 ∧
        HasQuotShape (fStarMod (relPPrimeCore 3 H) H) (relPPrimeCore 3 H : Set Q)
          (fun X _ => LieModel X .PSL 3 p f)) ∨
     (p ^ f % 3 = 1 ∧ p ^ f % 4 = 1 ∧
        HasQuotShape (fStarMod (relPPrimeCore 3 H) H) (relPPrimeCore 3 H : Set Q)
          (fun X _ => LieModel X .PSU 3 p f)))) ∨
  (HasQuotShape (fStarMod (relPPrimeCore 3 H) H) (relPPrimeCore 3 H : Set Q)
      (fun X _ => F6.IsL2 7 1 X) ∧
    HasQuotShape H (relPPrimeCore 3 H : Set Q) (fun X _ => F6.IsPGL2 7 X)) ∨
  (∃ n : ℕ, 1 ≤ n ∧
    (HasQuotShape (fStarMod (relPPrimeCore 3 H) H) (relPPrimeCore 3 H : Set Q)
        (fun X _ => IsL2 X (2 * n)) ∨
     HasQuotShape (fStarMod (relPPrimeCore 3 H) H) (relPPrimeCore 3 H : Set Q)
        (fun X _ => IsU3 X (2 * n))))

@[expose] def Asch5_4 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (H T : Subgroup Q),
    CFSG.Open.IsKGroup ↥H → IsSylowIn 2 T H → T < H → ¬ HasCompFactor H IsCalL0 →
    H = lGen IsCalL0 H T ∨
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 < CFSG.Open.pRank p (perfectCore H) ∧
        1 < CFSG.Open.pRank p (lGen IsCalL0 H T)) ∨
    (calNIn H T = {lGen IsCalL0 H T} ∧
      (IsSolvable ↥H ∨ ∃ L : Subgroup Q, IsComponentModN (OInf H) H L ∧ L ⊔ T = H ∧
        Shape54 H T L))

@[expose] def Asch5_12 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (H T : Subgroup Q),
    CFSG.Open.IsKGroup ↥H → IsSylowIn 2 T H → T < H → CFSG.Open.pRank 3 H ≤ 1 →
    ¬ HasCompFactor H IsCalL1 → H ≠ lGen IsCalL1 H T →
    calNIn H T = {lGen IsCalL1 H T} ∧
      (IsSolvable ↥H ∨
        (IsSolvable ↥(relPPrimeCore 3 H) ∧ relPPrimeCore 3 H ≤ lGen IsCalL1 H T ∧ Shape512 H))

@[expose] def Asch5_PSp4Three : Prop :=
  ∀ (L₀ : Type) [Group L₀] [Finite L₀], LieModel L₀ .PSp 2 3 1 →
    ∀ A S : Subgroup (MulAut L₀), AlmostSimpleData L₀ A S →
      ∃ X₁ X₂ : Subgroup (MulAut L₀), S ≤ X₁ ∧ S ≤ X₂ ∧ X₁ ≤ A ∧ X₂ ≤ A ∧
        ¬ innAutOf L₀ ≤ X₁ ∧ ¬ innAutOf L₀ ≤ X₂ ∧
          (X₁ ⊓ innAutOf L₀) ⊔ (X₂ ⊓ innAutOf L₀) = innAutOf L₀

@[expose] def Asch5_SimpOutSolv : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    ((∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 < p ^ e ∧ F6.IsL2 p e X) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ (LieModel X .PSL 3 p f ∨ LieModel X .PSU 3 p f)) →
    IsSimpleGroup X ∧ (∃ a b : X, a * b ≠ b * a) ∧ OutSolvable X

end CFSG.LocalAnalysis.WeakClosure81
