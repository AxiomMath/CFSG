module

public import CFSG.Quasithin.Background.E1Sections

public import CFSG.LocalAnalysis.ComponentClassification.Helpers

public section

namespace CFSG.LocalAnalysis.WeakClosure81

private theorem exists_surjective_of_map_eq_top_cover {B L : Type} [Group B] [Group L]
    {H : Subgroup B} (ψ : H →* L) {K : Subgroup H} (hK : K.map ψ = ⊤) :
    ∃ ψ' : K.map H.subtype →* L, Function.Surjective ψ' := by
  let e : K ≃* K.map H.subtype := K.equivMapOfInjective H.subtype H.subtype_injective
  refine ⟨(ψ.comp K.subtype).comp e.symm.toMonoidHom, fun l => ?_⟩
  obtain ⟨k, hk, rfl⟩ : l ∈ K.map ψ := by rw [hK]; exact Subgroup.mem_top l
  exact ⟨e ⟨k, hk⟩, by simp⟩

private theorem eq_top_of_minimal_cover {B L : Type} [Group B] [Finite B] [Group L]
    {U H : Subgroup B} (hHU : H ≤ U) (ψ : H →* L)
    (hmin : ∀ H' : Subgroup B, H' ≤ U → (∃ ψ' : H' →* L, Function.Surjective ψ') →
      Nat.card H ≤ Nat.card H')
    {K : Subgroup H} (hK : K.map ψ = ⊤) : K = ⊤ := by
  obtain ⟨ψ', hψ'⟩ := exists_surjective_of_map_eq_top_cover ψ hK
  have h1 : Nat.card H ≤ Nat.card (K.map H.subtype) :=
    hmin _ ((Subgroup.map_subtype_le K).trans hHU) ⟨ψ', hψ'⟩
  have h2 : Nat.card (K.map H.subtype) = Nat.card K :=
    (Nat.card_congr (K.equivMapOfInjective H.subtype H.subtype_injective).toEquiv).symm
  have h3 : Nat.card K ≤ Nat.card H := Subgroup.card_le_card_group K
  exact (Subgroup.card_eq_iff_eq_top K).mp (by omega)

theorem exists_perfect_cover_nilpotent_ker {B L : Type} [Group B] [Finite B] [Group L]
    [IsSimpleGroup L] (hL : ∃ a b : L, a * b ≠ b * a) {U : Subgroup B} (φ : U →* L)
    (hφ : Function.Surjective φ) :
    ∃ (H : Subgroup B) (ψ : H →* L), H ≤ U ∧ Function.Surjective ψ ∧ Group.IsPerfect H ∧
      Group.IsNilpotent ψ.ker := by
  obtain ⟨H, ⟨hHU, ψ, hψ⟩, hmin⟩ := Set.exists_min_image
    {H : Subgroup B | H ≤ U ∧ ∃ ψ : H →* L, Function.Surjective ψ} (fun H => Nat.card H)
    (Set.toFinite _) ⟨U, le_rfl, φ, hφ⟩
  have hmin' : ∀ H' : Subgroup B, H' ≤ U → (∃ ψ' : H' →* L, Function.Surjective ψ') →
      Nat.card H ≤ Nat.card H' := fun H' h1 h2 => hmin H' ⟨h1, h2⟩
  refine ⟨H, ψ, hHU, hψ, ?_, ?_⟩
  · rw [Group.isPerfect_def]
    refine eq_top_of_minimal_cover hHU ψ hmin' ?_
    have h1 := Subgroup.map_commutator (⊤ : Subgroup H) ⊤ ψ
    rw [Subgroup.map_top_of_surjective ψ hψ] at h1
    exact h1.trans (CFSG.ComponentClassification.Helpers.commutator_eq_top L hL)
  · have hfr : ψ.ker ≤ frattini H := by
      unfold frattini Order.radical
      refine le_iInf₂ fun W hW => ?_
      have hW : IsCoatom W := hW
      by_contra hnle
      have hlt : W < W ⊔ ψ.ker := lt_of_le_of_ne le_sup_left fun h => hnle (h ▸ le_sup_right)
      have hmapW : W.map ψ = ⊤ := by
        have h1 := congrArg (Subgroup.map ψ) (hW.lt_iff.mp hlt)
        rwa [Subgroup.map_sup, Subgroup.map_ker_self, sup_bot_eq,
          Subgroup.map_top_of_surjective ψ hψ] at h1
      exact hW.ne_top (eq_top_of_minimal_cover hHU ψ hmin' hmapW)
    have : Group.IsNilpotent (frattini H) := frattini_nilpotent
    exact (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hfr)).mp inferInstance

theorem exists_perfect_cover_of_isCompositionFactor {B : Type} [Group B] [Finite B]
    {G : Subgroup B} {L : Type} [Group L] (h : CFSG.Quasithin.E1.IsCompositionFactor G L)
    (hL : ∃ a b : L, a * b ≠ b * a) :
    ∃ (H : Subgroup B) (ψ : H →* L), H ≤ G ∧ Function.Surjective ψ ∧ Group.IsPerfect H ∧
      Group.IsNilpotent ψ.ker ∧ IsSimpleGroup L := by
  obtain ⟨N, M, hNM, -, -, -, hsimple, ⟨e⟩⟩ := h
  have : IsSimpleGroup L := e.symm.isSimpleGroup
  let π : ↥M →* L := (e : (M ⧸ N.subgroupOf M) →* L).comp (QuotientGroup.mk' (N.subgroupOf M))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let eU : ↥M ≃* ↥(M.map G.subtype) := M.equivMapOfInjective G.subtype G.subtype_injective
  obtain ⟨H, ψ, hHU, hψ, hperf, hnil⟩ := exists_perfect_cover_nilpotent_ker hL
    (U := M.map G.subtype) (π.comp eU.symm.toMonoidHom) (hπ.comp eU.symm.surjective)
  exact ⟨H, ψ, hHU.trans (Subgroup.map_subtype_le M), hψ, hperf, hnil, inferInstance⟩

end CFSG.LocalAnalysis.WeakClosure81
