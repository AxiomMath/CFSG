module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniModel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeKnownSix
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthShapeR
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeRLeaf
public import CFSG.LocalAnalysis.StandardType.GGTorsionQuotComp
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.RankThree.Classical2

private lemma orthShape_induced_range
    {X : Type} [Group X] [Finite X] {R : Type} [Group R]
    {A : Subgroup (MulAut X)} {θ : X ⧸ Subgroup.center X ≃* R}
    {I : Set (MulAut R)} {Ā : Subgroup (MulAut R)}
    (hperf : commutator X = ⊤) (hinn : GGInducedInn A θ I)
    (hmem : ∀ a ∈ A, ggInducedAut θ a ∈ Ā) (hcardĀ : Nat.card Ā = Nat.card A) :
    ∀ a ∈ Ā, a ∈ I := by
  intro a ha
  have hf : Function.Injective (ggInducedAut θ) :=
    ggInducedAut_injective_of_perfect hperf θ
  have hcardMap : Nat.card (A.map (ggInducedAut θ)) = Nat.card A :=
    Subgroup.card_map_of_injective hf
  have hle : A.map (ggInducedAut θ) ≤ Ā := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    rcases hx with ⟨y, hy, rfl⟩
    exact hmem y hy
  have hAne : Nat.card A ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  haveI : Finite Ā := Nat.finite_of_card_ne_zero (by rw [hcardĀ]; exact hAne)
  have hEq : A.map (ggInducedAut θ) = Ā :=
    Subgroup.eq_of_le_of_card_ge hle (hcardĀ.trans hcardMap.symm).le
  rw [← hEq] at ha
  rw [Subgroup.mem_map] at ha
  rcases ha with ⟨y, hy, hya⟩
  rw [← hya]
  exact hinn y hy

private lemma orthShape_transfer
    {X : Type} [Group X] {R : Type} [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R)
    {A : Subgroup (MulAut X)} {Ā : Subgroup (MulAut R)}
    {J : Subgroup X} {J' : Subgroup R}
    (hcardĀ : Nat.card Ā = Nat.card A) (hJ' : J' = J.map (proj θ))
    (hJperf : commutator ↥J = ⊤)
    (hcen : Subgroup.center J = ⊥ → Subgroup.center J' = ⊥)
    {n r : ℕ} (hconcl : OrthShapeConcl n r Ā J') :
    OrthShapeConcl n r A J := by
  unfold OrthShapeConcl at hconcl ⊢
  obtain ⟨lab, hlab, hhas', hcases⟩ := hconcl
  have hquot : Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ↥J' ⧸ Subgroup.center ↥J') := by
    obtain ⟨e⟩ := ggTorsion_centerQuot_image_equiv θ hJperf
    rw [← hJ'] at e
    exact ⟨e⟩
  have hhas : GGHasLabel lab (↥J ⧸ Subgroup.center ↥J) := by
    obtain ⟨e⟩ := hquot
    exact ggHasLabel_of_mulEquiv e.symm hhas'
  refine ⟨lab, hlab, hhas, ?_⟩
  rcases hcases with ⟨htagA, hA1, hA2⟩ | ⟨htagA', hrank⟩ | htagB | htagC |
    ⟨htagD, hrank, hn, hD4⟩
  · left
    refine ⟨htagA, ?_, ?_⟩
    · intro hr1
      rw [← hcardĀ]
      exact hA1 hr1
    · intro hr2 hbot
      exact hA2 hr2 (hcen hbot)
  · right; left; exact ⟨htagA', hrank⟩
  · right; right; left; exact htagB
  · right; right; right; left; exact htagC
  · right; right; right; right; exact ⟨htagD, hrank, hn, hD4⟩

theorem orthShape_holds :
    ∀ (K : Type) [Field K] [Finite K], CharP K 2 → ∀ n r : ℕ, Nat.card K = 2 ^ n → 4 ≤ r →
      (3 ∣ 2 ^ n - 1 ∨ n = 1) →
      (IsSimpleGroup (POmPlusG r K) ∧ ∃ a b : POmPlusG r K, a * b ≠ b * a) →
      ∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
        ∀ (θ : X ⧸ Subgroup.center X ≃* POmPlusG r K) (A : Subgroup (MulAut X)) (δ : MulAut X)
          (J : Subgroup X), GGKLocal A δ J →
          (∀ Q : Subgroup X, IsComponentOf Q (ggAutFixedSubgroup δ) → Q = J) → 3 ^ 3 ≤ Nat.card A →
          GGInducedInn A θ (LargeEvenInnSet (POmPlusG r K)) →
          OrthShapeConcl n r A J := by
  intro K _ _ hchar n r hK hr hsplit hsimple X _ _ hperf θ A δ J hKloc huniq hcard hinn
  haveI : CharP K 2 := hchar
  obtain ⟨Ā, δ', J', hR, hcardĀ, _hδ', hmem, hJ', hcen⟩ :=
    leafR_holds X hperf (POmPlusG r K) θ A δ J hKloc huniq hcard
  have hĀI : ∀ a ∈ Ā, a ∈ LargeEvenInnSet (POmPlusG r K) :=
    orthShape_induced_range hperf hinn hmem hcardĀ
  have hJperf : commutator ↥J = ⊤ := by
    have hcomp : IsComponentOf J (ggAutFixedSubgroup δ) := hKloc.1.2.2.2.1
    obtain ⟨-, -, hqs⟩ := hcomp
    exact hqs.1
  exact orthShape_transfer θ hcardĀ hJ' hJperf (fun hbot => (hcen.1 hbot).1)
    (orthR_shape hK hr hsplit hR hĀI)

end CFSG.StandardType.TablePThreeKG

end
