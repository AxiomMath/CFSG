module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofChevTwo
public import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofUnitary

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank (StatedSU)
open Res417Three Res417Five

namespace Res417Six

@[expose] def K417G2OddCentSU3 : Prop :=
  ∀ (X : Type) [Group X] (f : ℕ), Odd f → ChevalleyExceptionalModel X .G2 2 f →
    ∀ e : X, orderOf e = 3 → ∃ (K : Type) (_ : Field K)
      (ι : Subgroup.centralizer ({e} : Set X) →* GL (Fin 3) K), Function.Injective ι ∧
        PiField false 2 f K ∧ ∀ x, ι x ∈ StatedSU 3 (2 ^ f) K

@[expose] def K417NoDatumD4Odd : Prop :=
  ∀ (X : Type) [Group X] (f : ℕ), Odd f → ChevalleyExceptionalModel X .trialityD4 2 f →
    ∀ D : Subgroup X, ¬ IsDatum417 X D

theorem modThree_false_of_odd {f : ℕ} (hf : Odd f) : ModThree false (2 ^ f) := by
  show 2 ^ f % 3 = 2
  exact (two_pow_mod_three f).2 hf

theorem finite_of_G2_model {X : Type} [Group X] {f : ℕ}
    (hX : ChevalleyExceptionalModel X .G2 2 f) : Finite X := by
  obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := hX
  have : Finite (ModGL .G2 K) := finite_modGL
  have : Finite (adjointGroup .G2 K) := Subtype.finite
  have : Finite (AdjointQuotient .G2 K) := QuotientGroup.finite
  exact Finite.of_equiv _ e.symm.toEquiv

theorem not_isDatum417_of_G2_odd (hG : K417G2OddCentSU3)
    {X : Type} [Group X] {f : ℕ} (hf : Odd f) (hX : ChevalleyExceptionalModel X .G2 2 f)
    (D : Subgroup X) : ¬ IsDatum417 X D := by
  rintro ⟨hDe, -, F, hFD, hF9, T, hT2, hFT, hTF⟩
  have : Finite X := finite_of_G2_model hX
  have hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hDe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hFe : CFSG.Assembly.IsElemAbelian 3 F :=
    ⟨⟨⟨fun x y => Subtype.ext (hDcomm _ (hFD x.2) _ (hFD y.2))⟩⟩, fun x hx => hDe.2 x (hFD hx)⟩
  apply hTF
  refine le_centralizer_of_unitary hFe hF9 hT2 hFT fun e heF he1 => ?_
  obtain ⟨K, hKf, ι, hι, hK, hιSU⟩ := hG X f hf hX e (orderOf_eq_prime (hFe.2 e heF) he1)
  refine ⟨Subgroup.centralizer ({e} : Set X), Subgroup.le_normalizer, fun r hr => ?_, f, K, hKf,
    ι, hι, hK, modThree_false_of_odd hf, hιSU⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr (hDcomm r (hFD hr) e (hFD heF))

theorem k417NoDatumG2D4Odd_of (hG : K417G2OddCentSU3)
    (hD4 : K417NoDatumD4Odd) : K417NoDatumG2D4Odd := by
  intro X _ f hf hX D
  rcases hX with hG2 | hT
  · exact not_isDatum417_of_G2_odd hG hf hG2 D
  · exact hD4 X f hf hT D

@[expose] def K417DatumG2Even : Prop :=
  ∀ (X : Type) [Group X] (f : ℕ), Even f → ChevalleyExceptionalModel X .G2 2 f →
    ∀ D : Subgroup X, IsDatum417 X D →
      Nat.card D = 9 ∧ Nonempty (autIn ⊤ D ≃* DihedralGroup 6)

@[expose] def K417DatumD4Even : Prop :=
  ∀ (X : Type) [Group X] (f : ℕ), Even f → ChevalleyExceptionalModel X .trialityD4 2 f →
    ∀ D : Subgroup X, IsDatum417 X D →
      Nat.card D = 9 ∧ Nonempty (autIn ⊤ D ≃* DihedralGroup 6)

theorem k417DatumG2D4Even_of (hG : K417DatumG2Even) (hD4 : K417DatumD4Even) :
    K417DatumG2D4Even := by
  intro X _ f hf hX D hD
  rcases hX with hG2 | hT
  · exact hG X f hf hG2 D hD
  · exact hD4 X f hf hT D hD

end Res417Six

end CFSG.RankThree.PartTwo.Sec4
