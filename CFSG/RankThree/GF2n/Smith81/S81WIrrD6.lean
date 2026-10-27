module

public import CFSG.RankThree.GF2n.Smith81.S81D6Ops

public section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule


variable {K : Type} [Field K]

theorem LamW_irreducible_W [CharP K 2] (S : AddSubgroup (W K))
    (hS : ∀ g ∈ LamW K, ∀ s ∈ S, (g : Module.End K (W K)) s ∈ S) : S = ⊥ ∨ S = ⊤ := by
  set S' : AddSubgroup (V K) := S.map (emb K).toAddMonoidHom with hS'
  have hS'V0 : ∀ s ∈ S', s ∈ V0 K := by
    rintro _ ⟨w, -, rfl⟩
    exact emb_mem_V0 w
  have hΛ : ∀ l ∈ Lam K, ∀ s ∈ S', (l : Module.End K (V K)) s ∈ S' := by
    rintro l hl _ ⟨w, hw, rfl⟩
    refine ⟨(resV0 K ⟨l, hl⟩ : Module.End K (W K)) w, hS _ (mem_LamW_iff.mpr ⟨⟨l, hl⟩, rfl⟩) w hw,
      ?_⟩
    exact resV0_induces ⟨l, hl⟩ w
  rcases Lam_irreducible_V0 S' hS'V0 hΛ with h | h
  · left
    refine eq_bot_iff.mpr fun w hw => ?_
    have hmem : emb K w ∈ S' := ⟨w, hw, rfl⟩
    rw [h, AddSubgroup.mem_bot] at hmem
    exact (AddSubgroup.mem_bot).mpr (emb_injective (by rw [hmem, map_zero]))
  · right
    refine eq_top_iff.mpr fun w _ => ?_
    have hmem : emb K w ∈ S' := by
      rw [h]
      exact emb_mem_V0 w
    obtain ⟨w', hw', he⟩ := hmem
    rw [← emb_injective he]
    exact hw'

end CFSG.RankThree.GF2n.Smith81.D6Spin
