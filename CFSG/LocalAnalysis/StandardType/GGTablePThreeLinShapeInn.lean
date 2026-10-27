module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeRLeaf

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

theorem linShape_induced_range
    {K : Type} [Field K] [Finite K]
    {N : ℕ}
    {X : Type} [Group X] [Finite X]
    {A : Subgroup (MulAut X)}
    {θ : X ⧸ Subgroup.center X ≃* PSLg N K}
    {Ā : Subgroup (MulAut (PSLg N K))} (hperf : commutator X = ⊤)
    (hinn : GGInducedInn A θ
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)) Set.univ))
    (hmem : ∀ a ∈ A, ggInducedAut θ a ∈ Ā) (hcardĀ : Nat.card Ā = Nat.card A) :
    ∀ a ∈ Ā, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)) Set.univ := by
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

end CFSG.StandardType.TablePThreeKG

end
