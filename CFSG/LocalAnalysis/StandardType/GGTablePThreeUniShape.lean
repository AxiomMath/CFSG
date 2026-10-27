module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniShapeDefs
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniShapeR
import CFSG.LocalAnalysis.StandardType.GGTablePThreeRLeaf
import CFSG.LocalAnalysis.StandardType.GGTorsionQuotComp

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

private lemma uniShape_ggInducedAut_map_mem_of_GGInducedInn
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

private lemma uniShape_uniShapeConcl_transfer
    {X : Type} [Group X] {R : Type} [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R)
    {A : Subgroup (MulAut X)} {Ā : Subgroup (MulAut R)}
    {J : Subgroup X} {J' : Subgroup R}
    (hcardĀ : Nat.card Ā = Nat.card A) (hJ' : J' = J.map (proj θ))
    (hJperf : commutator ↥J = ⊤)
    (hcen : Subgroup.center J = ⊥ → Subgroup.center J' = ⊥)
    {q N : ℕ} (hconcl : UniShapeConcl q N Ā J') :
    UniShapeConcl q N A J := by
  unfold UniShapeConcl at hconcl
  unfold UniShapeConcl
  have hquot : Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ↥J' ⧸ Subgroup.center ↥J') := by
    obtain ⟨e⟩ := ggTorsion_centerQuot_image_equiv θ hJperf
    rw [← hJ'] at e
    exact ⟨e⟩
  rcases hconcl with
    ⟨F, hF, hFF, j, hj, hFcard, hF4, hequiv, hj1, hj3⟩ |
      ⟨E, hE, hFE, m, j, hj, hEcard, hm3, hmq, hequiv, hj1, hj3, hm3j1⟩
  · left
    letI : Field F := hF
    letI : Finite F := hFF
    obtain ⟨e⟩ := hquot
    obtain ⟨e2⟩ := hequiv
    exact ⟨F, hF, hFF, j, hj, hFcard, hF4, ⟨e.trans e2⟩,
      fun h1 => by rw [← hcardĀ]; exact hj1 h1,
      fun h3 => ⟨(hj3 h3).1, by rw [← hcardĀ]; exact (hj3 h3).2⟩⟩
  · right
    letI : Field E := hE
    letI : Finite E := hFE
    obtain ⟨e⟩ := hquot
    obtain ⟨e2⟩ := hequiv
    refine ⟨E, hE, hFE, m, j, hj, hEcard, hm3, hmq, ⟨e.trans e2⟩, hj1, hj3, ?_⟩
    intro hm3' hj1'
    obtain ⟨hZ', hAle, hN5⟩ := hm3j1 hm3' hj1'
    exact ⟨fun hbot => hZ' (hcen hbot), by rw [← hcardĀ]; exact hAle, hN5⟩

theorem uniShape_holds :
    ∀ (K : Type) [Field K] [Finite K], CharP K 2 → ∀ q N : ℕ, Nat.card K = q ^ 2 → 3 ∣ q + 1 → 3 ≤ N →
      (IsSimpleGroup (PSUg N K q) ∧ ∃ a b : PSUg N K q, a * b ≠ b * a) →
      ∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
        ∀ (θ : X ⧸ Subgroup.center X ≃* PSUg N K q) (A : Subgroup (MulAut X)) (δ : MulAut X)
          (J : Subgroup X), GGKLocal A δ J →
          (∀ Q : Subgroup X, IsComponentOf Q (ggAutFixedSubgroup δ) → Q = J) → 3 ^ 3 ≤ Nat.card A →
          GGInducedInn A θ
            (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K q))
              (LargeEvenGUSet (Fin N) K q)) →
          UniShapeConcl q N A J := by
  intro K _ _ hchar q N hK hq3 hN _ X _ _ hperf θ A δ J hKloc huniq hcard hinn
  haveI : CharP K 2 := hchar
  obtain ⟨Ā, δ', J', hR, hcardĀ, _hδ', hmem, hJ', hcen⟩ :=
    leafR_holds X hperf (PSUg N K q) θ A δ J hKloc huniq hcard
  have hĀI : ∀ a ∈ Ā, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K q))
      (LargeEvenGUSet (Fin N) K q) :=
    uniShape_ggInducedAut_map_mem_of_GGInducedInn hperf hinn hmem hcardĀ
  have hJperf : commutator ↥J = ⊤ := hKloc.1.2.2.2.1.2.2.1
  exact uniShape_uniShapeConcl_transfer θ hcardĀ hJ' hJperf (fun hbot => (hcen.1 hbot).1)
    (uniR_shape hK hq3 hN hR hĀI)

end CFSG.StandardType.TablePThreeKG

end
