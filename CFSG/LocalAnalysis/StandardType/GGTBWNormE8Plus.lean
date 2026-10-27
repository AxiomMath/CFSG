module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormWeylCoord
public import CFSG.LocalAnalysis.StandardType.GGTBTorE8Cover
public import CFSG.LocalAnalysis.StandardType.GGTorusE8Scalar
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfSylow

public section

namespace CFSG.StandardType.E8PlusWNorm

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar


theorem ggTorusWNormSC_recipe_E8_plus {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp11 : 11 ≤ p) (hq : p ∣ Nat.card K + 1) :
    GGTorusWNormSC p (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K) := by
  have hp2 : p ≠ 2 := by omega
  intro L _ _ ψ hψ hker hperf A hA hAI h3 hsc _ Λ _ _ M C V _ _ ι φ h α hM hC hpair hlin hgen s hs
  let : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨e, -, E, hE, -, hSC, hAE⟩ :=
    exists_e8_model_of_tableB ψ A ⟨hψ, hker, hperf, hA, hAI, h3, h3, hsc⟩
  have : Finite (adjointGroup .E8 K) := Finite.of_equiv L e.toEquiv
  have h8 : p ^ 8 ≤ Nat.card E :=
    ExcFramesHalf.pow_le_card_of_sylowTorus (ExcFramesHalf.sylowTorus_E8_half K hp hp11 hq)
      (MonoidHom.id _) Function.injective_id (fun x _ => ⟨x, rfl⟩) hE
      (fun g hg hgp => hSC g (fun x hx => (Subgroup.mem_centralizer_iff.mp hg x hx).symm) hgp)
  obtain ⟨-, -, -, -, t, n, -, -, -, -, ht, htr, -, -, hns, hN⟩ :=
    E8ScalarTorus.exists_frame_of_selfCentralizing hp hp2 hq E hE
      (le_trans (Nat.pow_le_pow_right hp.pos (by norm_num)) h8) hSC
  let Λ0 : adjointGroup .E8 K →* MulAut L :=
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
  exact ExcWeylCoord.wNormConcl_of_centralCover_weylFrame_E7E8 (Or.inr rfl) hp2 e.toMonoidHom
    e.surjective Λ0 hΛ0 hΛψ E A hEA t ht htr n hns hN ι φ h α hgen hs

theorem largeEvenLabelAll_wnorm_E8_plus {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    {lab : LargeEvenLabel} (htag : lab.tag = .E8) (hpq : p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  have hp11 : 11 ≤ p :=
    ExcFramesHalf.eleven_le_of_dvd_two_pow_add_one hp (by omega) hpq (by omega) (by omega)
  rcases lab with ⟨tag, r, n⟩
  dsimp only at htag hpq ⊢
  subst htag
  intro Q hQ
  obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
  refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
  have : CharP K 2 := charP_two_of_card hK
  exact ggTorusWNormSC_recipe_E8_plus hp hp11 (by rw [hK]; exact hpq)

end CFSG.StandardType.E8PlusWNorm

end
