module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniModel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeKnownSix
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthMinusShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthMinusShapeR
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeRLeaf
import CFSG.LocalAnalysis.StandardType.GGTorsionQuotComp
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.RankThree.Classical2

private lemma orthMinusShape_ggInducedAut_map_mem_of_GGInducedInn
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

private lemma orthMinusShape_concl_transfer
    {X : Type} [Group X] {R : Type} [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R)
    {A : Subgroup (MulAut X)} {Ā : Subgroup (MulAut R)}
    {J : Subgroup X} {J' : Subgroup R}
    (hcardĀ : Nat.card Ā = Nat.card A) (hJ' : J' = J.map (proj θ))
    (hJperf : commutator ↥J = ⊤)
    (hcen : Subgroup.center J = ⊥ → Subgroup.center J' = ⊥)
    {n r : ℕ} (hconcl : OrthMinusShapeConcl n r Ā J') :
    OrthMinusShapeConcl n r A J := by
  unfold OrthMinusShapeConcl at hconcl ⊢
  obtain ⟨lab, hlab, hGG, hcases⟩ := hconcl
  have hquot : Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ↥J' ⧸ Subgroup.center ↥J') := by
    obtain ⟨e⟩ := ggTorsion_centerQuot_image_equiv θ hJperf
    rw [← hJ'] at e
    exact ⟨e⟩
  obtain ⟨e⟩ := hquot
  have hGG' : GGHasLabel lab (J ⧸ Subgroup.center J) :=
    ggHasLabel_of_mulEquiv e.symm hGG
  refine ⟨lab, hlab, hGG', ?_⟩
  rcases hcases with ⟨hA, h1, h2⟩ | ⟨htwA, h2⟩ | hB | hC | ⟨hD, hr, hn, hclause⟩
  · left
    refine ⟨hA, ?_, ?_⟩
    · intro hrk
      rw [← hcardĀ]
      exact h1 hrk
    · intro hrk
      exact fun hbot => h2 hrk (hcen hbot)
  · right; left
    refine ⟨htwA, ?_⟩
    intro hrk
    exact ⟨fun hbot => (h2 hrk).1 (hcen hbot), (h2 hrk).2⟩
  · right; right; left
    exact hB
  · right; right; right; left
    exact hC
  · right; right; right; right
    exact ⟨hD, hr, hn, hclause⟩

theorem orthMinusShape_holds :
    ∀ (K : Type) [Field K] [Finite K], CharP K 2 → ∀ n r : ℕ, Nat.card K = 2 ^ n → 4 ≤ r →
      ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      (IsSimpleGroup (POmMinusG (r - 1) K b c) ∧ ∃ x y : POmMinusG (r - 1) K b c, x * y ≠ y * x) →
      ∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
        ∀ (θ : X ⧸ Subgroup.center X ≃* POmMinusG (r - 1) K b c) (A : Subgroup (MulAut X)) (δ : MulAut X)
          (J : Subgroup X), GGKLocal A δ J →
          (∀ Q : Subgroup X, IsComponentOf Q (ggAutFixedSubgroup δ) → Q = J) → 3 ^ 3 ≤ Nat.card A →
          GGInducedInn A θ (LargeEvenInnSet (POmMinusG (r - 1) K b c)) →
          OrthMinusShapeConcl n r A J := by
  intro K _ _ hchar n r hK hr b c hbc _hsimple X _ _ hperf θ A δ J hKloc huniq hcard hinn
  haveI : CharP K 2 := hchar
  obtain ⟨Ā, δ', J', hR, hcardĀ, _hδ', hmem, hJ', hcen⟩ :=
    leafR_holds X hperf (POmMinusG (r - 1) K b c) θ A δ J hKloc huniq hcard
  have hĀI : ∀ a ∈ Ā, a ∈ LargeEvenInnSet (POmMinusG (r - 1) K b c) :=
    orthMinusShape_ggInducedAut_map_mem_of_GGInducedInn hperf hinn hmem hcardĀ
  have hJperf : commutator ↥J = ⊤ := hKloc.1.2.2.2.1.2.2.1
  exact orthMinusShape_concl_transfer θ hcardĀ hJ' hJperf (fun hbot => (hcen.1 hbot).1)
    (orthMinusR_shape hK hr hbc hR hĀI)

end CFSG.StandardType.TablePThreeKG

end
