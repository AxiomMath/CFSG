module

public import CFSG.Sporadic.Recognition.HSWalesGroup
public import CFSG.Sporadic.Recognition.HSPinnedIdent

public section

namespace CFSG.Sporadic.Recognition.HSWales

open MulAction CFSG.Blueprint

universe u₁ u₂ u₃ u₄

theorem wales_1969_HS_rank_3_graph_uniqueness
    {G : Type u₁} {Ω : Type u₂} [Group G] [Finite G] [Fintype Ω] [MulAction G Ω]
    [FaithfulSMul G Ω] [IsPretransitive G Ω] (hΩ : Nat.card Ω = 100) (a : Ω)
    (hM : Nonempty (stabilizer G a ≃* NativeSporadic.M22)) (Δ Γ : Set Ω)
    (horb : Set.range (orbit (stabilizer G a) : Ω → Set Ω) = {{a}, Δ, Γ})
    (hΔ : Δ.ncard = 22) (hΓ : Γ.ncard = 77) :
    (walesGraph G a Δ).IsSRGWith 100 22 0 6 ∧
    (∀ (G' : Type u₃) (Ω' : Type u₄) [Group G'] [Finite G'] [MulAction G' Ω']
      [FaithfulSMul G' Ω'] [IsPretransitive G' Ω'], Nat.card Ω' = 100 → ∀ a' : Ω',
      Nonempty (stabilizer G' a' ≃* NativeSporadic.M22) → ∀ Δ' Γ' : Set Ω',
      Set.range (orbit (stabilizer G' a') : Ω' → Set Ω') = {{a'}, Δ', Γ'} →
      Δ'.ncard = 22 → Γ'.ncard = 77 →
      Nonempty (walesGraph G a Δ ≃g walesGraph G' a' Δ')) ∧
    Nonempty (G ≃* NativeSporadic.HS) := by
  obtain ⟨b, c, hb, hc, D⟩ := Rank3.of_range_orbit hΩ horb hΔ hΓ
  subst hb hc
  obtain ⟨φ⟩ := hM
  obtain ⟨𝓜⟩ := D.nonempty_model φ
  refine ⟨𝓜.isSRGWith D, ?_, ?_⟩
  · intro G' Ω' _ _ _ _ _ hΩ' a' hM' Δ' Γ' horb' hΔ' hΓ'
    have : Finite Ω' := Nat.finite_of_card_ne_zero (by rw [hΩ']; norm_num)
    obtain ⟨b', c', hb', hc', D'⟩ := Rank3.of_range_orbit hΩ' horb' hΔ' hΓ'
    subst hb' hc'
    obtain ⟨φ'⟩ := hM'
    obtain ⟨𝓜'⟩ := D'.nonempty_model φ'
    exact ⟨(𝓜.graphIso D).trans (𝓜'.graphIso D').symm⟩
  · obtain ⟨e⟩ := 𝓜.nonempty_mulEquiv_range D
    obtain ⟨e'⟩ := HSPinned.nonempty_mulEquiv_hs (𝓜.autHom D).range (𝓜.index_autHom_range D)
    exact ⟨e.trans e'⟩

end CFSG.Sporadic.Recognition.HSWales
