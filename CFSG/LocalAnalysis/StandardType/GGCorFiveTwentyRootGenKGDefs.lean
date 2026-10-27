module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGen
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeADvd

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def ggHypCent {L' : Type} [Group L'] (A : Subgroup (MulAut L')) (n : L') :
    Subgroup L' :=
  ⨅ (a : MulAut L') (_ : a ∈ A ∧ MulAut.conj n * a = a * MulAut.conj n), ggFix a

@[expose] def ggTorusWeylAut (p : ℕ) {L' : Type} [Group L'] (A : Subgroup (MulAut L')) :
    Set (MulAut ↥A) :=
  {φ | ∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
    GGTorusWeylElt p A n ∧ φ = ggConjAut A hn}

@[expose] def GGTorusWeylReflGen (p : ℕ) {L' : Type} [Group L'] (A : Subgroup (MulAut L')) :
    Prop :=
  ggTorusWeylAut p A ⊆ Subgroup.closure {φ | φ ∈ ggTorusWeylAut p A ∧ GGIsReflection p φ}

@[expose] def GGTorusRootGenAvoid (p : ℕ) {L' : Type} [Group L'] (A : Subgroup (MulAut L')) :
    Prop :=
  ∀ ρ : MulAut ↥A,
    (⨆ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')))
      (J : Subgroup L') (_ : GGTorusWeylElt p A n ∧ GGIsReflection p (ggConjAut A hn) ∧
        ggConjAut A hn ≠ ρ ∧ n ∈ J ∧ IsComponentOf J (ggHypCent A n) ∧ p ∣ Nat.card J), J) = ⊤

@[expose] def GGTorusRootGen (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      GGTorusWeylReflGen p A → GGTorusRootGenAvoid p A

theorem ggTorusRootGen_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') {I : Set (MulAut R)} {I' : Set (MulAut R')}
    (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I') (h : GGTorusRootGen p r R' I') :
    GGTorusRootGen p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc hwr
  refine h L' (e.toMonoidHom.comp ψ) (e.surjective.comp hψ) ?_ hperf A hA ?_ hr h3 hsc hwr
  · intro l hl
    exact hker (by simpa [MonoidHom.mem_ker] using hl)
  · intro a ha
    obtain ⟨φ, hφ, hφa⟩ := hAI a ha
    exact ⟨MulAut.congr e φ, hI φ hφ, fun l => by simp [MulAut.congr_apply, hφa]⟩

@[expose] def GGRootGenLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  2 ≤ lab.n ∧ p ∣ 4 ^ lab.n - 1

@[expose] def GGRootGenNbrLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGLabNbrOk p lab ∧ p ∣ 4 ^ lab.n - 1

@[expose] def GGRootGenResLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p = 3 ∧ (lab.tag = .twE6 ∨ (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1))

@[expose] def GGRootGenKGOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab → S p lab →
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusRootGen p r R I

@[expose] def GGRootGenSplitLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ 2 ^ lab.n - 1 ∧ lab.tag ≠ .A ∧ ¬ (lab.tag = .D ∧ lab.rank = 3) ∧
    ¬ (lab.tag = .twD ∧ lab.rank = 2) ∧ ¬ GGRootGenResLabel p lab

@[expose] def GGRootGenUnitaryLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ 2 ^ lab.n + 1 ∧ 2 ≤ lab.n ∧ (lab.tag = .twA ∨ (lab.tag = .twD ∧ lab.rank = 3))

@[expose] def GGRootGenSympLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ 2 ^ lab.n + 1 ∧ 2 ≤ lab.n ∧ (lab.tag = .B ∨ lab.tag = .C)

@[expose] def GGRootGenOrthLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ 2 ^ lab.n + 1 ∧ 2 ≤ lab.n ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank

@[expose] def GGRootGenLinPhiTwoLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ 2 ^ lab.n + 1 ∧ 2 ≤ lab.n ∧ (lab.tag = .A ∨ (lab.tag = .D ∧ lab.rank = 3))

@[expose] def GGRootGenExcPhiTwoLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ 2 ^ lab.n + 1 ∧ 2 ≤ lab.n ∧
    (lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4 ∨ lab.tag = .twE6 ∨
      lab.tag = .triD4 ∨ lab.tag = .G2 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4) ∧
    ¬ GGRootGenResLabel p lab

@[expose] def GGRootGenRowNineLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∧ lab.n = 1 ∧ p = 3 ∧ 5 ≤ lab.rank

@[expose] def GGRootGenKGSplitInput : Prop := GGRootGenKGOn GGRootGenSplitLabel

@[expose] def GGRootGenLInputOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGNbrLabelsOk p B Bs x D J → GGCorFiveTwentyWeylDom p B Bs x L D J →
        GGInnerDiagOnLabel S p Bs L → GGRootCompGenAvoiding p Bs L

@[expose] def GGRootGenNbrInputOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGNbrLabelsOk p B Bs x D J → GGCorFiveTwentyWeylDom p B Bs x L D J →
        ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → GGInnerDiagOnLabel S p Bs K →
          GGRootCompGenAvoiding p Bs K

@[expose] def GGRootGenOpenLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGLabPhiOneTwo p lab ∧ ¬ GGTypeALabel p lab

end CFSG.StandardType

end
