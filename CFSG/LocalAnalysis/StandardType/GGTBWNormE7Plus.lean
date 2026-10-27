module

public import CFSG.LocalAnalysis.StandardType.GGTorusE7PlusToral
public import CFSG.LocalAnalysis.StandardType.GGTBTorE7Cover
public import CFSG.LocalAnalysis.StandardType.GGTBWNormWeylCoord

public noncomputable section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar


theorem ggTorusWNormSC_recipe_E7_plus {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hq : p ∣ Nat.card K + 1) :
    GGTorusWNormSC p (TableBExc.RecipeGroup .E7 K) (TableBExc.RecipeID .E7 K) := by
  have hp2 : p ≠ 2 := by omega
  intro L _ _ ψ hψ hker hperf A hA hAI h3 hsc _ Λ _ _ M C V _ _ ι φ h α _ _ _ _ hgen s hs
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨e, -, E, hE, -, hSC, hAE⟩ :=
    exists_e7_model_of_tbGroup ψ A ⟨hψ, hker, hperf, hA, hAI, h3, h3, hsc⟩
  obtain ⟨-, -, -, -, t, n, -, -, -, -, ht, htr, -, -, hns, hN⟩ :=
    exists_e7_scalar_frame_of_sc hp hp5 hq E hE hSC
  let Λ0 : adjointGroup .E7 K →* MulAut L :=
    (MulAut.congr e.symm).toMonoidHom.comp MulAut.conj
  have hΛ0 : Function.Injective Λ0 :=
    (MulAut.congr e.symm).injective.comp mulAut_conj_injective_adjointGroup
  have hΛψ : ∀ l, Λ0 (e l) = MulAut.conj l := by
    intro l
    ext x
    simp [Λ0, MulAut.congr_apply, MulAut.conj_apply]
  have hEA : E.map Λ0 = A := by
    have hcomp : (MulAut.congr e.symm).toMonoidHom.comp (MulAut.congr e).toMonoidHom =
        MonoidHom.id (MulAut L) := by
      ext a x
      simp [MulAut.congr_apply, MulEquiv.trans_apply]
    change E.map ((MulAut.congr e.symm).toMonoidHom.comp MulAut.conj) = A
    rw [← Subgroup.map_map, ← hAE, Subgroup.map_map, hcomp, Subgroup.map_id]
  exact ExcWeylCoord.wNormConcl_of_centralCover_weylFrame_E7E8 (Or.inl rfl) hp2 e.toMonoidHom
    e.surjective Λ0 hΛ0 hΛψ E A hEA t ht htr n hns hN ι φ h α hgen hs

theorem largeEvenLabelAll_wnorm_E7_plus {lab : LargeEvenLabel} (htag : lab.tag = .E7) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hq : p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  obtain ⟨t, r, f⟩ := lab
  dsimp only at htag hq ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQK⟩ := hQ
  let : CharP K 2 := charP_two_of_card hK
  refine ⟨K, i1, i2, hK, hQK, ?_⟩
  exact ggTorusWNormSC_recipe_E7_plus hp hp5 (by rw [hK]; exact hq)

end CFSG.StandardType
