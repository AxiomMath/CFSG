module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwo
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Kit
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434OmegaMinusCheck
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeAut
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.RankThreeEven (projOmegaMinus)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.EvenSmallLie.OmegaEightMinus
open Item434Kit Item434Alt Subgroup

namespace Item434OmegaMinus

theorem statedClassicalModel_of_mulEquiv {X : Type} [Group X] {b c : GaloisField 2 1}
    (hbc : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0)
    (e : X ≃* projOmegaMinus 3 (GaloisField 2 1) b c) :
    StatedClassicalModel X .POmegaMinus 4 2 1 :=
  ⟨⟨Nat.prime_two, le_rfl, le_refl 4⟩, GaloisField 2 1, inferInstance, inferInstance,
    GaloisField.card 2 1 one_ne_zero, b, c, hbc,
    ⟨e.trans (Census.statedProjEquivProjImage _
      (CFSG.RankThree.PartOne.projImage_statedOmegaMinus_eq_projOmegaMinus 4 _ b c)).symm⟩⟩


theorem false_of_omegaMinus {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}
    (h : Ctx434Core G A M Q) {b c : GaloisField 2 1}
    (hbc : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projOmegaMinus 3 (GaloisField 2 1) b c) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hC := statedClassicalModel_of_mulEquiv hbc e₀
  obtain ⟨θ⟩ := nonempty_mulEquiv_omegaT (Or.inl ⟨by decide, hC⟩)
  have hodd : Odd (Nat.card (Subgroup.center (layer G))) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.isPGroup_center_layer
    rw [hk]
    exact Odd.pow (by decide)
  have hZ := (CFSG.SectionRank.EvenCover.even_nonsplit_orthogonal_odd_cover_catalog_step
    h.isQuasisimple hodd hC).1
  have hf := wreathFacts_omegaT
  have hCA := Item434Kit.inf_centralizer_layer_eq_bot h hZ θ (isElemAbelian_baseA hf)
    (card_baseA hf)
  have hA27 := card_map_quotConj h hCA θ
  have hout : ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer omegaT) := by
    rw [card_outer_omegaT]
    norm_num
  set P := (A.map (quotConj θ)).comap (MulAut.conj : omegaT →* MulAut omegaT) with hP
  have hPmap : P.map MulAut.conj = A.map (quotConj θ) := map_comap_conj_eq h θ hout
  have hinj := conj_injective_of_center_eq_bot center_omegaT
  have hP27 : Nat.card P = 27 := by
    rw [← Subgroup.card_map_of_injective hinj, hPmap, hA27]
  have hPe : CFSG.Assembly.IsElemAbelian 3 P :=
    isElemAbelian_of_map_injective hinj (hPmap ▸ isElemAbelian_map_quotConj h θ)
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 3) (by rw [hP27]; norm_num)
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card (P₀ := wreathW zT tT)
    (by rw [card_wreathW_omegaT, factorization_card_omegaT]; norm_num) hPp
  have hPg : P.map (MulAut.conj g⁻¹).toMonoidHom = baseA zT :=
    eq_baseA_of_le_wreathW hf card_wreathW_omegaT (Item434AltPerm.map_conj_inv_le hg)
      (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ P hPe)
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hP27])
  have hPeq : P = (baseA zT).map (MulAut.conj g).toMonoidHom := by
    rw [← hPg, Item434AltPerm.map_conj_map_conj_inv]
  refine false_of_fixed_gens h θ (S := Set.range fun k : Fin 3 => g * sT k * g⁻¹) ?_ ?_
  · have hcl : Subgroup.closure (Set.range fun k : Fin 3 => g * sT k * g⁻¹) =
        (Subgroup.closure (Set.range sT)).map (MulAut.conj g).toMonoidHom := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      rfl
    rw [hcl, closure_range_sT, ← MonoidHom.range_eq_map]
    exact (MonoidHom.range_eq_top.mpr (MulAut.conj g).surjective).ge
  · rintro _ ⟨k, rfl⟩
    refine ⟨?_, ((hypT k).map (MulAut.conj g).toMonoidHom).map MulAut.conj, ?_, ?_, ?_⟩
    · change Nat.Coprime (orderOf (MulAut.conj g (sT k))) 3
      rw [MulEquiv.orderOf_eq]
      exact orderOf_sT_coprime k
    · rw [← hPmap, hPeq]
      exact Subgroup.map_mono (Subgroup.map_mono (hypT_le_baseA k))
    · rw [Subgroup.card_map_of_injective hinj,
        Subgroup.card_map_of_injective (MulAut.conj g).injective, card_hypT]
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      have hxs : x * sT k = sT k * x :=
        Subgroup.mem_centralizer_singleton_iff.mp (hypT_le_centralizer k hx)
      change g * x * g⁻¹ * (g * sT k * g⁻¹) * (g * x * g⁻¹)⁻¹ = g * sT k * g⁻¹
      calc g * x * g⁻¹ * (g * sT k * g⁻¹) * (g * x * g⁻¹)⁻¹ = g * (x * sT k) * x⁻¹ * g⁻¹ := by
            group
        _ = g * (sT k * x) * x⁻¹ * g⁻¹ := by rw [hxs]
        _ = g * sT k * g⁻¹ := by group

end Item434OmegaMinus

section Families


theorem item434OmegaMinusEight : Item434OmegaMinusEight := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  obtain ⟨b, c, hbc, ⟨e₀⟩⟩ := hL
  exact (Item434OmegaMinus.false_of_omegaMinus hc hbc e₀).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
