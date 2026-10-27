module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGTypeACompatFar
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarConfig

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def GGTableBOrderRest (lab : LargeEvenLabel) (N : ℕ) : Prop :=
  (lab.tag = .C ∧ N = 2 ^ lab.rank * lab.rank.factorial) ∨
  (lab.tag = .D ∧ N = 2 ^ (lab.rank - 1) * lab.rank.factorial) ∨
  (lab.tag = .E6 ∧ N = 51840) ∨ (lab.tag = .E7 ∧ N = 2903040) ∨
  (lab.tag = .E8 ∧ N = 696729600)

@[expose] def GGTorusAutCardDvdSCr (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R))
    (N : ℕ) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
    GGTorusTBGroup p r R I L' ψ A →
      N ∣ Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A)

theorem GGTorusAutCardSCr.toDvd {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {N : ℕ}
    (h : GGTorusAutCardSCr p r R I N) : GGTorusAutCardDvdSCr p r R I N :=
  fun L' _ _ ψ A hA => dvd_of_eq (h L' ψ A hA).symm

@[expose] def GGNbrTableBOrderRestInput : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (lab : LargeEvenLabel) (N : ℕ), LargeEvenInLambda2 lab →
    GGNbrSplitLabel p lab → GGTableBOrderRest lab N →
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusAutCardDvdSCr p r R I N

@[expose] def GGTorusFrame (p : ℕ) {L' : Type} [Group L'] (A : Subgroup (MulAut L')) : Prop :=
  ∃ a₁ ∈ ggTorusReflSet p A, ∃ a₂ ∈ ggTorusReflSet p A, 4 ∣ orderOf (a₁ * a₂)

@[expose] def GGTorusOrderNine (p : ℕ) {L' : Type} [Group L'] (A : Subgroup (MulAut L')) : Prop :=
  ∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
    GGTorusWeylElt p A n ∧ 9 ∣ orderOf (ggConjAut A hn)

@[expose] def GGFrameLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .twD ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1) ∨
  (lab.tag = .A ∧ 5 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1) ∨
  (lab.tag = .twA ∧ lab.rank = 5 ∧ p ∣ 2 ^ lab.n - 1)

@[expose] def GGNbrFrameInput : Prop :=
  (∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    GGFrameLabel p lab →
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → GGTorusFrame p A) ∧
  (LargeEvenLabelAll ⟨.A, 8, 1⟩ fun R _ I _ => ∃ r, GGTorusLift 7 r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup 7 r R I L' ψ A → GGTorusOrderNine 7 A)

@[expose] def GGTypeANbrTablePInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGTypeANbrCfg p B Bs x L D J n f y K →
    GGNbrTablePConfig p B Bs x L D J

section CompatDiag

open CFSG.LieType.Universal.SpecialLinear Matrix

@[expose] def GGTypeACompatDiagBInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGTypeANbrCfg p B Bs x L D J n f y K →
    ∃ φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, φ₁.range = L ∧
      φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) ∧
      φ₂.range = K ∧
      φ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) ∧
      (φ₁.comp (slLowerBlockHom n (GaloisField 2 f))).range = J ∧
      φ₁.comp (slLowerBlockHom n (GaloisField 2 f)) =
        φ₂.comp (slUpperBlockHom n (GaloisField 2 f)) ∧
      ∀ b ∈ Bs, GGActsDiag φ₁ b ∧ GGActsDiag φ₂ b

end CompatDiag

end CFSG.StandardType

end
