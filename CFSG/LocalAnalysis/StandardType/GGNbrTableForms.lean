module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
public import CFSG.LocalAnalysis.StandardType.GGFixSub

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

@[expose] def GGHasLabel (lab : LargeEvenLabel) (R : Type) [Group R] : Prop :=
  CFSG.StandardType.LargeEvenRawDatum lab fun R' _ _ _ => Nonempty (R ≃* R')

@[expose] def GGLabelIso (lab lab' : LargeEvenLabel) : Prop :=
  lab = lab' ∨
    ((lab.tag = .B ∨ lab.tag = .C) ∧ (lab'.tag = .B ∨ lab'.tag = .C) ∧ lab.rank = lab'.rank ∧
      lab.n = lab'.n) ∨
    (lab = ⟨.D, 3, lab.n⟩ ∧ lab' = ⟨.A, 3, lab.n⟩) ∨
    (lab = ⟨.A, 3, lab.n⟩ ∧ lab' = ⟨.D, 3, lab.n⟩) ∨
    (lab = ⟨.twD, 3, lab.n⟩ ∧ lab' = ⟨.twA, 3, lab.n⟩) ∨
    (lab = ⟨.twA, 3, lab.n⟩ ∧ lab' = ⟨.twD, 3, lab.n⟩) ∨
    (lab = ⟨.twD, 2, lab.n⟩ ∧ lab' = ⟨.A, 1, 2 * lab.n⟩) ∨
    (lab' = ⟨.twD, 2, lab'.n⟩ ∧ lab = ⟨.A, 1, 2 * lab'.n⟩)

@[expose] def GGLabelRigidInput : Prop :=
  ∀ (lab lab' : LargeEvenLabel) (R : Type) [Group R], LargeEvenInLambda2 lab →
    LargeEvenInLambda2 lab' → GGHasLabel lab R → GGHasLabel lab' R → GGLabelIso lab lab'

@[expose] def GGNbrSplitLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  LargeEvenUntwisted lab.tag ∧ 2 ≤ lab.n ∧ p ∣ 2 ^ lab.n - 1

theorem GGNbrSplitLabel.halfSplit {p : ℕ} {lab : LargeEvenLabel} {c : Prop}
    (h : GGNbrSplitLabel p lab) : LargeEvenHalfSplit p lab c :=
  Or.inl (Or.inl ⟨h.1, h.2.2⟩)

@[expose] def GGTablePRow (p : ℕ) (J X : LargeEvenLabel) : Prop :=
  (J.tag = .A ∧ p ∣ 2 ^ J.n - 1 ∧ 2 ≤ J.rank ∧
    (X = ⟨.A, J.rank + 1, J.n⟩ ∨ (X = ⟨.A, J.rank + 2, J.n⟩ ∧ p ∣ J.rank + 3) ∨
      X = ⟨.C, J.rank + 1, J.n⟩ ∨ X = ⟨.D, J.rank + 1, J.n⟩ ∨ X = ⟨.twD, J.rank + 2, J.n⟩ ∨
      (J.rank = 5 ∧ X = ⟨.E6, 0, J.n⟩) ∨ (J.rank = 6 ∧ X = ⟨.E7, 0, J.n⟩) ∨
      (J.rank = 7 ∧ p ≠ 3 ∧ X = ⟨.E8, 0, J.n⟩) ∨ (J.rank = 8 ∧ p = 3 ∧ X = ⟨.E8, 0, J.n⟩) ∨
      (J.rank = 2 ∧ X.tag = .twA ∧ X.rank = 5 ∧ 2 * X.n = J.n ∧ p ∣ 2 ^ X.n - 1) ∨
      (X.tag = .A ∧ (X.rank = 2 * J.rank + 1 ∨ X.rank = 2 * J.rank + 2) ∧
        2 * X.n = J.n ∧ p ∣ 2 ^ X.n + 1))) ∨
  (J.tag = .A ∧ p ∣ 2 ^ J.n + 1 ∧ 3 ≤ J.rank ∧
    (X = ⟨.A, J.rank + 2, J.n⟩ ∨ (J.rank = 5 ∧ X = ⟨.E6, 0, J.n⟩))) ∨
  (J = ⟨.A, 2, 3⟩ ∧ p = 7 ∧ X = ⟨.A, 8, 1⟩) ∨ (J = ⟨.A, 2, 4⟩ ∧ p = 5 ∧ X = ⟨.A, 5, 2⟩) ∨
  (J = ⟨.A, 8, 1⟩ ∧ p = 7 ∧ X = ⟨.A, 11, 1⟩) ∨
  (J = ⟨.A, 5, 1⟩ ∧ p = 7 ∧ X = ⟨.A, 8, 1⟩) ∨
  (J.tag = .twA ∧ p ∣ 2 ^ J.n - 1 ∧ 3 ≤ J.rank ∧
    (X = ⟨.twA, J.rank + 2, J.n⟩ ∨ (J.rank = 3 ∧ X = ⟨.twD, 4, J.n⟩) ∨
      (J.rank = 5 ∧ X = ⟨.twE6, 0, J.n⟩))) ∨
  (J.tag = .twA ∧ p ∣ 2 ^ J.n + 1 ∧ 2 ≤ J.rank ∧
    (X = ⟨.twA, J.rank + 1, J.n⟩ ∨ (X = ⟨.twA, J.rank + 2, J.n⟩ ∧ p ∣ J.rank + 3) ∨
      X = ⟨.C, J.rank + 1, J.n⟩ ∨ (Odd J.rank ∧ X = ⟨.D, J.rank + 1, J.n⟩) ∨
      (Odd J.rank ∧ X = ⟨.D, J.rank + 2, J.n⟩) ∨ (Even J.rank ∧ X = ⟨.twD, J.rank + 1, J.n⟩) ∨
      (Even J.rank ∧ X = ⟨.twD, J.rank + 2, J.n⟩) ∨ (J.rank = 5 ∧ X = ⟨.twE6, 0, J.n⟩) ∨
      (X.tag = .twE6 ∧ 3 * X.n = J.n) ∨ (J.rank = 6 ∧ X = ⟨.E7, 0, J.n⟩) ∨
      (J.rank = 8 ∧ p = 3 ∧ X = ⟨.E8, 0, J.n⟩) ∨ (J.rank = 7 ∧ p ≠ 3 ∧ X = ⟨.E8, 0, J.n⟩))) ∨
  ((J.tag = .B ∨ J.tag = .C) ∧ (p ∣ 2 ^ J.n - 1 ∨ p ∣ 2 ^ J.n + 1) ∧ 2 ≤ J.rank ∧
    (X = ⟨.C, J.rank + 1, J.n⟩ ∨ (J.rank = 3 ∧ X = ⟨.F4, 0, J.n⟩))) ∨
  (J = ⟨.B2der, 0, 1⟩ ∧ p = 3 ∧ X = ⟨.C, 3, 1⟩) ∨
  (J.tag = .D ∧ p ∣ 2 ^ J.n - 1 ∧
    (X = ⟨.D, J.rank + 1, J.n⟩ ∨ (J.rank = 5 ∧ X = ⟨.E6, 0, J.n⟩) ∨
      (J.rank = 6 ∧ X = ⟨.E7, 0, J.n⟩) ∨ (J.rank = 7 ∧ X = ⟨.E8, 0, J.n⟩) ∨
      (J.rank = 4 ∧ p = 3 ∧ X = ⟨.E6, 0, J.n⟩))) ∨
  (J.tag = .D ∧ p ∣ 2 ^ J.n + 1 ∧
    (X = ⟨.twD, J.rank + 1, J.n⟩ ∨ (J.rank = 4 ∧ p = 3 ∧ X = ⟨.twE6, 0, J.n⟩) ∨
      (J.rank = 6 ∧ X = ⟨.E7, 0, J.n⟩))) ∨
  (J.tag = .twD ∧ p ∣ 2 ^ J.n - 1 ∧ 3 ≤ J.rank ∧
    (X = ⟨.twD, J.rank + 1, J.n⟩ ∨ (J.rank = 4 ∧ X = ⟨.twE6, 0, J.n⟩))) ∨
  (J.tag = .twD ∧ p ∣ 2 ^ J.n + 1 ∧ 3 ≤ J.rank ∧
    (X = ⟨.D, J.rank + 1, J.n⟩ ∨ (J.rank = 4 ∧ X = ⟨.E6, 0, J.n⟩) ∨
      (J.rank = 5 ∧ X = ⟨.twE6, 0, J.n⟩) ∨ (J.rank = 7 ∧ X = ⟨.E8, 0, J.n⟩))) ∨
  (J.tag = .triD4 ∧ p = 3 ∧ X = ⟨.D, 4, 3 * J.n⟩) ∨
  (J.tag = .triD4 ∧ p = 3 ∧ 3 ∣ 2 ^ J.n + 1 ∧ X = ⟨.twE6, 0, J.n⟩) ∨
  (J.tag = .triD4 ∧ p ∣ 2 ^ (2 * J.n) + 2 ^ J.n + 1 ∧ X = ⟨.E6, 0, J.n⟩ ∧ p = 7 ∧ J.n = 1) ∨
  (J.tag = .triD4 ∧ p ∣ 2 ^ (2 * J.n) - 2 ^ J.n + 1 ∧ X = ⟨.twE6, 0, J.n⟩ ∧ p = 7 ∧ J.n = 1) ∨
  (J.tag = .E6 ∧ p ∣ 2 ^ J.n - 1 ∧ X = ⟨.E7, 0, J.n⟩) ∨
  (J.tag = .E6 ∧ p ∣ 2 ^ (2 * J.n) + 2 ^ J.n + 1 ∧ X = ⟨.E8, 0, J.n⟩) ∨
  (J.tag = .twE6 ∧ p ∣ 2 ^ J.n + 1 ∧ X = ⟨.E7, 0, J.n⟩) ∨
  (J.tag = .E7 ∧ (p ∣ 2 ^ J.n - 1 ∨ p ∣ 2 ^ J.n + 1) ∧ X = ⟨.E8, 0, J.n⟩) ∨
  (J.tag = .G2 ∧ (p ∣ 2 ^ J.n - 1 ∨ p ∣ 2 ^ J.n + 1) ∧ p = 3 ∧ X = ⟨.D, 4, J.n⟩)

section TableP

variable {G : Type} [Group G] [Finite G]

@[expose] def GGNbrTablePConfig (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) : Prop :=
  GGConfig p B Bs x L D J → GGInnerDiagAll p B Bs x L D J →
    ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ∀ labJ labK : LargeEvenLabel, LargeEvenInLambda2 labJ → LargeEvenInLambda2 labK →
        GGHasLabel labJ (J ⧸ Subgroup.center J) → GGHasLabel labK (K ⧸ Subgroup.center K) →
        ∃ labJ' labK' : LargeEvenLabel, LargeEvenInLambda2 labJ' ∧ LargeEvenInLambda2 labK' ∧
          GGTablePRow p labJ' labK' ∧
          GGHasLabel labJ' (J ⧸ Subgroup.center J) ∧ GGHasLabel labK' (K ⧸ Subgroup.center K)

end TableP

@[expose] def GGTCJKnown : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ e : MulAut L', e ^ p = 1 → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (e l)) →
          ∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) →
            ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧ lab.n ∣ labJ.n ∧
              GGHasLabel labJ (J ⧸ Subgroup.center J)

@[expose] def ggTorusReflSet (p : ℕ) {L' : Type} [Group L'] (A : Subgroup (MulAut L')) :
    Set (MulAut ↥A) :=
  {φ | ∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
    GGTorusWeylElt p A n ∧ φ = ggConjAut A hn ∧ GGIsReflection p φ}

section TorusForms

variable (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R))

@[expose] def GGTorusTBGroup (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R)
    (A : Subgroup (MulAut L')) : Prop :=
  Function.Surjective ψ ∧ ψ.ker ≤ Subgroup.center L' ∧ commutator L' = ⊤ ∧ IsElemAbelian p A ∧
    (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) ∧ p ^ r ≤ Nat.card A ∧
    p ^ 3 ≤ Nat.card A ∧ GGTorusSelfCent p A

@[expose] def GGTorusReflGenSCr : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
    GGTorusTBGroup p r R I L' ψ A →
      GGReflGenerated p (ggAutomizer (MulAut.conj : L' →* MulAut L').range A)

@[expose] def GGTorusReflGenW : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
    GGTorusTBGroup p r R I L' ψ A →
      ggAutomizer (MulAut.conj : L' →* MulAut L').range A ≤ Subgroup.closure (ggTorusReflSet p A)

@[expose] def GGTorusTypeASCr : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
    GGTorusTBGroup p r R I L' ψ A → ∀ m : ℕ,
      GGWeylOfType p (CoxeterMatrix.A m) (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) →
      ∃ lab : LargeEvenLabel, (lab.tag = .A ∨ lab.tag = .twA) ∧ lab.rank = m ∧ GGHasLabel lab R

@[expose] def GGTorusAutCardSCr (N : ℕ) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
    GGTorusTBGroup p r R I L' ψ A →
      Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) = N

end TorusForms

theorem GGTorusReflGenW.toSCr {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (h : GGTorusReflGenW p r R I) : GGTorusReflGenSCr p r R I := by
  intro L' _ _ ψ A hA
  refine le_antisymm ((h L' ψ A hA).trans (Subgroup.closure_mono ?_)) ?_
  · rintro φ ⟨n, hn, -, rfl, hrefl⟩
    exact show _ ∧ _ from
      ⟨ggConjAut_mem_ggAutomizer (H := (MulAut.conj : L' →* MulAut L').range)
        (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn, hrefl⟩
  · exact (Subgroup.closure_le _).mpr fun φ hφ => hφ.1

theorem ggNbrLabelAll_mono {lab : LargeEvenLabel} {P₁ P₂ : LargeEvenRawCont}
    (h : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), P₁ R I F → P₂ R I F)
    (h₁ : LargeEvenLabelAll lab P₁) : LargeEvenLabelAll lab P₂ := by
  intro Q hQ
  exact largeEvenRawDatum_mono (fun R _ I F h' => ⟨h'.1, h R I F h'.2⟩) (h₁ Q hQ)

@[expose] def GGNbrTableBWeylInput : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    LargeEvenHalfSplit p lab True → GGNbrSplitLabel p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusReflGenW p r R I

theorem GGNbrTableBWeylInput.toTableB (h : GGNbrTableBWeylInput) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
      LargeEvenHalfSplit p lab True → GGNbrSplitLabel p lab →
        LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusReflGenSCr p r R I :=
  fun p hp hp2 lab hlab hhs hsp =>
    ggNbrLabelAll_mono (fun _ _ _ _ ⟨r, hl, hW⟩ => ⟨r, hl, hW.toSCr⟩)
      (h p hp hp2 lab hlab hhs hsp)

@[expose] def GGNbrTableBCardInput : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ n f : ℕ, LargeEvenInLambda2 ⟨.A, n, f⟩ → p ∣ 2 ^ f - 1 →
    LargeEvenLabelAll ⟨.A, n, f⟩ fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGTorusAutCardSCr p r R I (n + 1).factorial

end CFSG.StandardType
