module

public import CFSG.LocalAnalysis.StandardType.GGTBWNorm
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNinePGL

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggTorusWNormSC_of_card_lt {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hbound : ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X →
      Nat.card X < p ^ 3) : GGTorusWNormSC p R I := by
  apply ggTorusWNormSC_of_lift_card_lt
  intro L' _ _ ψ hψ hker hperf A hA hAI
  have hAI' : ∀ a ∈ A, ∃ φ : MulAut R, ∀ l : L', φ (ψ l) = ψ (a l) := by
    intro a ha
    obtain ⟨φ, -, hφ⟩ := hAI a ha
    exact ⟨φ, hφ⟩
  have hcard := TypeA.card_inducedSub hψ hker hperf hAI'
  rw [← hcard]
  apply hbound _ ?_ (TypeA.isElemAbelian_inducedSub hψ hA)
  rintro φ ⟨a, ha, hφ⟩
  obtain ⟨φ', hφ'I, hφ'⟩ := hAI a ha
  rw [TypeA.induced_unique ψ hψ hφ hφ']
  exact hφ'I

theorem ggTorusWNormSC_linear_of_le_three {K : Type} [Field K] [Finite K] [CharP K 2]
    {d p : ℕ} (hd : 0 < d) (hd3 : d ≤ 3) (hp : p.Prime) (hp2 : p ≠ 2) :
    GGTorusWNormSC p (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ) := by
  apply ggTorusWNormSC_of_card_lt
  intro X hXI hX
  exact StdSubRestThree.card_lt_of_congr (TypeA.recipeEquiv d K)
    (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
    (fun _ hX'I hX' => TypeA.card_lt_cube_pgl_of_le_three hd hd3 hp hp2 hX' hX'I) hXI hX

theorem largeEvenLabelAll_wnorm_A_le_two {lab : LargeEvenLabel} (ht : lab.tag = .A)
    (hl : lab.rank ≤ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  obtain ⟨tag, rank, n⟩ := lab
  dsimp only at ht hl ⊢
  subst ht
  intro Q hQ
  obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
  exact ggTorusWNormSC_linear_of_le_three (d := rank + 1) (by omega) (by omega) hp hp2

theorem largeEvenLabelAll_wnorm_twD_two {lab : LargeEvenLabel} (ht : lab.tag = .twD)
    (hl : lab.rank = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  obtain ⟨tag, rank, n⟩ := lab
  dsimp only at ht hl ⊢
  subst ht hl
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  simp only [↓reduceIte] at hQ ⊢
  obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
  have : CharP K 2 := charP_two_of_card (m := 2 * n) (by
    rw [hK, ← pow_mul, mul_comm])
  refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
  exact ggTorusWNormSC_linear_of_le_three (by norm_num) (by norm_num) hp hp2

theorem largeEvenLabelAll_wnorm_twA_two {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twA) (hl : lab.rank = 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I :=
  (largeEvenLabelAll_lift_card_lt_unitaryThree_all hp hp2 hlab ht hl).mono
    fun _ _ _ _ h => ggTorusWNormSC_of_lift_card_lt h

theorem largeEvenLabelAll_wnorm_low_rank {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab)
    (hlow : (lab.tag = .A ∧ lab.rank ≤ 2) ∨
      ((lab.tag = .twA ∨ lab.tag = .twD) ∧ lab.rank = 2))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  rcases hlow with ⟨ht, hl⟩ | ⟨ht | ht, hl⟩
  · exact largeEvenLabelAll_wnorm_A_le_two ht hl hp hp2
  · exact largeEvenLabelAll_wnorm_twA_two hlab ht hl hp hp2
  · exact largeEvenLabelAll_wnorm_twD_two ht hl hp hp2

end CFSG.StandardType
