module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FSqIndex
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {W : Type} [CommGroup W]

@[expose] def InducesGraphAutL35 {A : Type} [Group A] (a : A) (L : Subgroup A) : Prop :=
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  a ∈ Subgroup.normalizer (L : Set A) ∧
    ∀ ha : a ∈ Subgroup.normalizer (L : Set A),
      ∃ e : ↥L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 5),
        ∀ x : ↥L,
          e ⟨a * (x : A) * a⁻¹,
              (Subgroup.mem_normalizer_iff.mp ha (x : A)).mp x.2⟩ =
            CFSG.ComponentClassification.CatalogueBGraphForm.pslGraphAut 3 (ZMod 5) (e x)

@[expose] def W4Lem3_6 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y L : Subgroup (MulAut W), ∀ n : ℕ,
      L ≤ Y → (L.subgroupOf Y).Normal → Fstar Y = L →
      IsSU3 ↥L n → 2 < n →
      IsIrrOn Y ⊤ ⊥ →
      E3.mParam Y ≤ 2 * n + 2 →
      NatSUn L ⊤ ⊥ 3 n ∧ E3.mParam Y = 2 * n

@[expose] def W4Lem4_10 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], ∀ (L T : Subgroup Q), ∀ q : ℕ,
    L.Normal → Fstar (⊤ : Subgroup Q) = L →
    (∃ (p e : ℕ), p.Prime ∧ p ≠ 2 ∧ q = p ^ e ∧ F6.IsL2 p e ↥L) → 3 < q → Odd q →
    IsSylowIn 2 T ⊤ → L ⊔ T = ⊤ →
    InFGroup 1 Q ∨
      IsAlt ↥L 5 ∨
      ((F6.IsL2 7 1 Q ∨ F6.IsL2 3 2 Q ∨ IsSymGp Q 6) ∧ InEGroup 1 Q)

@[expose] def W4Lem4_11 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], ∀ (L T : Subgroup Q), ∀ q : ℕ,
    L.Normal → Fstar (⊤ : Subgroup Q) = L →
    (IsCoverL3OddOver ↥L q ∨ IsCoverU3OddOver ↥L q) → Odd q →
    ∀ (Ω : Set (Subgroup Q)),
      IsSylowIn 2 T ⊤ → IsOmegaColl Ω → L ⊔ T = ⊤ →
      InFGroup 1 Q ∨
        ((LieModel ↥L .PSL 3 5 1 ∨ LieModel ↥L .PSU 3 3 1) ∧
          InEGroup 1 Q ∧
          (LieModel ↥L .PSL 3 5 1 → IsAutOf Q ↥L ∧ InFGroup 2 Q) ∧
          (LieModel ↥L .PSL 3 5 1 → ¬ InFOmega 1 T Ω →
            ∀ A ∈ Ω, ∃ a ∈ A, InducesGraphAutL35 a L))

@[expose] def W4Lem4_16 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y L T : Subgroup (MulAut W), ∀ (Δ : Set (Subgroup (MulAut W))) (k : ℕ),
      L ≤ Y → T ≤ Y → L ⊔ T = Y →
      IsComponentOf L Y →
      IsSylowIn 2 T Y →
      O2Trivial Y →
      Δ.Finite →
      (∀ H ∈ Δ, H ≤ Y ∧ T ≤ H) →
      (⨆ H ∈ Δ, H) = Y →
      fIndexSum Δ = (k : ℕ∞) →
      (∀ Ω : Set (Subgroup (MulAut W)), Ω.Nonempty →
        (∀ A ∈ Ω, ∀ g ∈ Y, A.map (MulAut.conj g).toMonoidHom ∈ Ω) →
        (∀ A ∈ Ω, A ∈ E3.aSet (k + 1) Y) →
          commSub (fixV (Wk k T Ω)) L = ⊥) ∧
      (fixV T ≠ fixV Y → E3.aParam Y ≤ k)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
