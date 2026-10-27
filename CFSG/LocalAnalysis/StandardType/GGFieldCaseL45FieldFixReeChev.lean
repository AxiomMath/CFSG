module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixReeModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Ree

@[expose] def TwF4FixOn (K : Type) [Field K] (a : ℕ) (S : (Fin 4 → ℤ) → Prop) (p : ℕ) : Prop :=
  ∀ I : Set (MulAut (LargeEvenCenterQuot (MarkChev.twF4H S a K))),
    GGL45FieldFixTorsion p (LargeEvenCenterQuot (MarkChev.twF4H S a K)) I
      (RecipeFieldExcInn.markFieldImage S K (MarkChev.twF4H S a K))

theorem TwF4FixOn.of_eq {K : Type} [Field K] {a : ℕ} {S S' : (Fin 4 → ℤ) → Prop} {p : ℕ}
    (hS : S = S') (h : TwF4FixOn K a S p) : TwF4FixOn K a S' p :=
  hS ▸ h

section Chev

variable {K : Type} [Field K] [Finite K] {a : ℕ}

theorem twF4H_isRoot_eq_reeGamma' [CharP K ReeTag.F4.prime] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    MarkChev.twF4H (IsRoot .F4) a K = ReeTag.F4.reeGamma K a :=
  (twF4H_eq_commutator K a).trans (gff_commutator_reeFixedGroup ha hK)

theorem twF4FixOn_isRoot [CharP K ReeTag.F4.prime] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    TwF4FixOn K a (IsRoot .F4) p := by
  intro I
  suffices key : ∀ H : Subgroup (MarkChev.GLS (IsRoot .F4) K), H = ReeTag.F4.reeGamma K a →
      ∀ I : Set (MulAut (LargeEvenCenterQuot H)),
        GGL45FieldFixTorsion p (LargeEvenCenterQuot H) I
          (RecipeFieldExcInn.markFieldImage (IsRoot .F4) K H) from
    key _ (twF4H_isRoot_eq_reeGamma' ha hK) I
  intro H hH I
  subst hH
  exact gff_torsion_reeGamma ha hK hp hp2 I

theorem gff_torsion_twF4 (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    GGL45FieldFixTorsion p (LargeEvenCenterQuot (LargeEvenTwF4H a K))
      (LargeEvenChevIDImage LargeEvenCartanF4 K _)
      (LargeEvenChevFieldImage LargeEvenCartanF4 K _) := by
  have : CharP K ReeTag.F4.prime := charP_two_of_card hK
  have h := (twF4FixOn_isRoot ha hK hp hp2).of_eq (largeEvenIsRoot_eq_isRoot .F4).symm
  suffices key : ∀ H : Subgroup (LargeEvenChevGL LargeEvenCartanF4 K),
      H = MarkChev.twF4H (LargeEvenIsRoot LargeEvenCartanF4) a K →
      GGL45FieldFixTorsion p (LargeEvenCenterQuot H) (LargeEvenChevIDImage LargeEvenCartanF4 K H)
        (LargeEvenChevFieldImage LargeEvenCartanF4 K H) from
    key _ (largeEvenTwF4H_eq a K)
  intro H hH
  subst hH
  exact h _

theorem ggL45FieldFixLabelAll_twF4 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twF4) :
    LargeEvenLabelAll lab fun R _ I F => GGL45FieldFixTorsion p R I F := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  have hn3 : 3 ≤ n := hlab.2.2.2
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  exact ⟨K, inferInstance, inferInstance, hK, hQ', gff_torsion_twF4 (by omega) hK hp hp2⟩

end Chev

end CFSG.StandardType
