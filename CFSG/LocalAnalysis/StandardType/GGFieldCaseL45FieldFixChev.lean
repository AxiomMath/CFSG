module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixModel
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley

@[expose] def ChevFixOn (K : Type) [Field K] (τ : Tag) (S : (Fin τ.rank → ℤ) → Prop) (p : ℕ) :
    Prop :=
  ∀ I : Set (MulAut (LargeEvenCenterQuot (MarkChev.chevH τ.cartan S K false))),
    GGL45FieldFixTorsion p (LargeEvenCenterQuot (MarkChev.chevH τ.cartan S K false)) I
      (RecipeFieldExcInn.markFieldImage S K (MarkChev.chevH τ.cartan S K false))

theorem ChevFixOn.of_eq {K : Type} [Field K] {τ : Tag} {S S' : (Fin τ.rank → ℤ) → Prop}
    {p : ℕ} (hS : S = S') (h : ChevFixOn K τ S p) : ChevFixOn K τ S' p :=
  hS ▸ h

section Chev

theorem chevFixOn_isRoot {τ : Tag} (hτ : τ = .F4 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    {n p : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) (hp : p.Prime) (hp2 : p ≠ 2) :
    ChevFixOn K τ (IsRoot τ) p := by
  intro I
  suffices key : ∀ H : Subgroup (MarkChev.GLS (IsRoot τ) K), H = adjointGroup τ K →
      ∀ I : Set (MulAut (LargeEvenCenterQuot H)),
        GGL45FieldFixTorsion p (LargeEvenCenterQuot H) I
          (RecipeFieldExcInn.markFieldImage (IsRoot τ) K H) from
    key _ (chevH_false_eq_adjointGroup K τ) I
  intro H hH I
  subst hH
  exact gff_torsion_model hτ hn hK hp hp2 I

theorem gff_torsion_chev {τ : Tag} (hτ : τ = .F4 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    {n p : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) (hp : p.Prime) (hp2 : p ≠ 2) :
    GGL45FieldFixTorsion p (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false))
      (LargeEvenChevIDImage τ.cartan K _) (LargeEvenChevFieldImage τ.cartan K _) := by
  have h := (chevFixOn_isRoot hτ hn hK hp hp2).of_eq (largeEvenIsRoot_eq_isRoot τ).symm
  suffices key : ∀ H : Subgroup (LargeEvenChevGL τ.cartan K),
      H = MarkChev.chevH τ.cartan (LargeEvenIsRoot τ.cartan) K false →
      GGL45FieldFixTorsion p (LargeEvenCenterQuot H) (LargeEvenChevIDImage τ.cartan K H)
        (LargeEvenChevFieldImage τ.cartan K H) from
    key _ (largeEvenChevH_eq τ.cartan K false)
  intro H hH
  subst hH
  exact h _

theorem ggL45FieldFixLabelAll_chev {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hS : lab.tag = .F4 ∨ lab.tag = .E8) :
    LargeEvenLabelAll lab fun R _ I F => GGL45FieldFixTorsion p R I F := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  rcases hS with ht | ht <;> dsimp only at ht <;> subst ht
  · exact recipeChevalley_and (fun K _ _ hK =>
      gff_torsion_chev (τ := .F4) (Or.inl rfl) hn hK hp hp2) hQ
  · exact recipeChevalley_and (fun K _ _ hK =>
      gff_torsion_chev (τ := .E8) (Or.inr rfl) hn hK hp hp2) hQ

end Chev

end CFSG.StandardType
