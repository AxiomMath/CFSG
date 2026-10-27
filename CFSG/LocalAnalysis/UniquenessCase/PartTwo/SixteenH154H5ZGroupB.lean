module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ZGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16h_zcondGroup_of_ker_le {G P Y : Type} [Group G] [Group P] [Group Y] (ρ : G →* P)
    (κ : G →* Y) (hκ : Function.Surjective κ) (hker : ρ.ker ≤ κ.ker)
    (h : s16h_ZCondGroup ↥ρ.range) : s16h_ZCondGroup Y := by
  have hQ : s16h_ZCondGroup (G ⧸ ρ.ker) :=
    s16h_zcondGroup_of_surjective (QuotientGroup.quotientKerEquivRange ρ).symm.toMonoidHom
      (QuotientGroup.quotientKerEquivRange ρ).symm.surjective h
  exact s16h_zcondGroup_of_surjective (QuotientGroup.lift ρ.ker κ hker)
    (QuotientGroup.lift_surjective_of_surjective ρ.ker κ hκ hker) hQ

theorem s16h_zcondGroup_of_embed_perm_fintype {Y ι : Type} [Group Y] [Fintype ι]
    (hι : Fintype.card ι ≤ 3) (ψ : Y →* Equiv.Perm ι) (hψ : Function.Injective ψ) :
    s16h_ZCondGroup Y := by
  classical
  have hcomp : Function.Injective
      (((Fintype.equivFin ι).permCongrHom.toMonoidHom).comp ψ) :=
    (Fintype.equivFin ι).permCongrHom.injective.comp hψ
  refine s16h_zcondGroup_of_embed_perm_three
    ((Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb hι)).comp
      (((Fintype.equivFin ι).permCongrHom.toMonoidHom).comp ψ)) ?_
  exact (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb hι)).comp hcomp

theorem s16h_zcondGroup_of_transitive_gl3
    (K : Subgroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)))
    (htrans : ∀ u v : Fin 3 → ZMod 2, u ≠ 0 → v ≠ 0 →
      ∃ a ∈ K, ((a : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec u = v) :
    s16h_ZCondGroup ↥K := by
  have h7 : 7 ∣ Nat.card ↥K := by
    rcases s16t3_gl3_transitive_card K htrans with h | h | h
    · exact ⟨1, by rw [h]⟩
    · rw [h]; exact ⟨3, by norm_num⟩
    · rw [h, Subgroup.card_top, CFSG.ComponentClassification.GHarris.card_GL32_gh]
      exact ⟨24, by norm_num⟩
  exact s16h_zcondGroup_of_embed_gl3 K.subtype K.subtype_injective h7

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
