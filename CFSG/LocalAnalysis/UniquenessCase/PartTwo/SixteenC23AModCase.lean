module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AModPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AModMap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23ABlockW
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23ASwap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23ACaseFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.FFC CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c23a_modPair_of_case (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Case167_2 D V₀ V hV L) (h : Hyp151 D V₀ V L)
    (h0 : V₀ = ⊥) (hne : v1Sub D.M V₀ V hV L ≠ ⊥) :
    ∃ x ∈ D.M, C23AModPair (Mbar D.M V₀ V hV) (barSub V₀ V hV L)
      (barSub V₀ V hV (conjSubgroup L x)) (wTil V₀ V hV L) (wTil V₀ V hV (conjSubgroup L x))
      (wTil V₀ V hV L ⊓ fixV (barSub V₀ V hV L))
      (wTil V₀ V hV (conjSubgroup L x) ⊓ fixV (barSub V₀ V hV (conjSubgroup L x))) := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  obtain ⟨x, hx, hxn, hall, hperm⟩ := c23a_swap_of_s15 h hc.2.2.1
  have hxs : x ∈ stabTil V₀ V := hMs hx
  obtain ⟨hx1, hx2⟩ := c23a_cross_fix h hx hxn
  have hL₂ : barSub V₀ V hV (conjSubgroup L x) =
      (barSub V₀ V hV L).map (MulAut.conj (actTil V₀ V hV ⟨x, hxs⟩)⁻¹).toMonoidHom :=
    s15_Infra_barSub_conjSubgroup V₀ V hV hxs L
  have hE₂ : wTil V₀ V hV (conjSubgroup L x) =
      (wTil V₀ V hV L).map ((actTil V₀ V hV ⟨x, hxs⟩)⁻¹).toMonoidHom :=
    s15_Infra_wTil_conjSubgroup V₀ V L hV hxs
  have hne₁ : wTil V₀ V hV L ⊓ fixV (barSub V₀ V hV L) ≠ ⊥ := c23a_z_ne_bot h h0 hne
  subst h0
  have hblk₁ := c23a_block_wTil D h1217 h hc.2.1
  have hblk₂ := c23a_block_map hblk₁ (actTil ⊥ V hV ⟨x, hxs⟩)⁻¹
  rw [← hL₂, ← hE₂] at hblk₂
  have hL1 : barSub ⊥ V hV L ≠ ⊥ := fun hb =>
    hxn (by rw [s15_Infra_nBar_eq_of_barSub_eq_bot h.hyp125 hV hb]; exact hx)
  have hsup : wTil ⊥ V hV L ⊔ wTil ⊥ V hV (conjSubgroup L x) = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← s15_Two_iSup_commSub_eq_top D h1217 h hL1]
    refine iSup_le fun m => ?_
    rcases hall m m.2 with h1 | h1
    · exact le_sup_of_le_left (by rw [h1]; exact le_rfl)
    · exact le_sup_of_le_right (by rw [h1]; exact le_rfl)
  refine ⟨x, hx, ?_⟩
  exact
  { exp2 := s15_Infra_vtil_sq_eq_one ⊥ V hV
    blk₁ := hblk₁
    blk₂ := by rw [← hblk₂.fix]; exact hblk₂
    sup := hsup
    inf₁ := fun e he => ⟨he.1, hx2 he.2⟩
    inf₂ := fun e he => ⟨he.2, hx1 he.1⟩
    ne₁ := hne₁
    ne₂ := by
      rw [← hblk₂.fix]
      exact fun hb => hne₁ ((Subgroup.map_eq_bot_iff_of_injective _ (MulEquiv.injective _)).1 hb)
    perm := fun φ hφ => by
      rcases hperm φ hφ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨Subgroup.mem_normalizer_iff_map_conj_eq.2 h1,
          Subgroup.mem_normalizer_iff_map_conj_eq.2 h2,
          fun e he => c23a_apply_mem_commSub_top h1 he,
          fun e he => c23a_apply_mem_commSub_top h2 he⟩
      · exact Or.inr ⟨fun e he => c23a_apply_mem_commSub_top h1 he,
          fun e he => c23a_apply_mem_commSub_top h2 he⟩ }

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
