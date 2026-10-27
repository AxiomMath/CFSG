module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU48Aux
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Kit

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores Item434Kit Item434Alt

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem false_of_inner (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* SU4)
    (hA27 : Nat.card (A.map (quotConj e)) = 27)
    (hin : ∀ α ∈ A.map (quotConj e), α ∈ (MulAut.conj : SU4 →* MulAut SU4).range) : False := by
  have hAe := isElemAbelian_map_quotConj h e
  have hinj := conj_injective_of_center_eq_bot center_SU4
  set P : Subgroup SU4 := (A.map (quotConj e)).comap (MulAut.conj : SU4 →* MulAut SU4) with hP
  have hAP : A.map (quotConj e) = P.map MulAut.conj := (Subgroup.map_comap_eq_self hin).symm
  have hPe : CFSG.Assembly.IsElemAbelian 3 P := isElemAbelian_of_map_injective hinj (hAP ▸ hAe)
  have hPcard : Nat.card P = 27 := by
    rw [← hA27, hAP, Subgroup.card_map_of_injective hinj]
  obtain ⟨g, hg⟩ := exists_map_conj_Dstd hPe hPcard
  refine false_of_fixed_gens h e (S := (MulAut.conj g : SU4 ≃* SU4) ''
    {x : SU4 | Nat.Coprime (orderOf x) 3 ∧ ∃ i : Fin 3, ∀ b ∈ Bsub i, b * x = x * b})
    (closure_map_conj_eq_top g).ge ?_
  rintro _ ⟨s, ⟨hs3, i, hsi⟩, rfl⟩
  refine ⟨?_, ((Bsub i).map (MulAut.conj g).toMonoidHom).map MulAut.conj, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact hs3
  · rw [hAP, hg]
    exact Subgroup.map_mono (Subgroup.map_mono (Bsub_le_Dstd i))
  · rw [Subgroup.card_map_of_injective hinj,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact card_Bsub i
  · rintro φ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    have hbs := hsi b hb
    change (g * b * g⁻¹) * (g * s * g⁻¹) * (g * b * g⁻¹)⁻¹ = g * s * g⁻¹
    calc (g * b * g⁻¹) * (g * s * g⁻¹) * (g * b * g⁻¹)⁻¹ = g * (b * s) * b⁻¹ * g⁻¹ := by group
      _ = g * (s * b) * b⁻¹ * g⁻¹ := by rw [hbs]
      _ = g * s * g⁻¹ := by group

end CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48
