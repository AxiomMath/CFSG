module

public import CFSG.Sporadic.Recognition.HSGraphModel
public import CFSG.Sporadic.Recognition.HSGraphEven

public section

namespace CFSG.Sporadic.Recognition.HSGraph

open CFSG.ComponentClassification.WittDesign MulAction

universe u

theorem higman_sims_1968_graph_automorphism_group
    {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
    (𝓑 : Finset (Finset Ω)) (h : IsSteinerTriple 𝓑) :
    𝓑.card = 77 ∧
    (hsGraph 𝓑).IsSRGWith 100 22 0 6 ∧
    (IsPretransitive (autGroup 𝓑) (Vert 𝓑) ∧ Nat.card (autGroup 𝓑) = 88704000 ∧
      (88704000 : ℕ) = 2 ^ 10 * 3 ^ 2 * 5 ^ 3 * 7 * 11 ∧
      Set.range (orbit (stabilizer (autGroup 𝓑) (vInf : Vert 𝓑)) : Vert 𝓑 → Set (Vert 𝓑)) =
        {{vInf}, Set.range vPt, Set.range vBlk} ∧
      (∀ (g : stabilizer (autGroup 𝓑) (vInf : Vert 𝓑)) (a : Ω),
        g • (vPt a : Vert 𝓑) = vPt (restrictΩ 𝓑 g a)) ∧
      Function.Injective (restrictΩ 𝓑) ∧ (restrictΩ 𝓑).range = blockAut 𝓑 ∧
      Nat.card (blockAut 𝓑) = 887040) ∧
    ((∃! H : Subgroup (autGroup 𝓑), H.index = 2) ∧
      ∀ H : Subgroup (autGroup 𝓑), H.index = 2 →
        IsSimpleGroup H ∧ Nat.card H = 44352000 ∧
        (44352000 : ℕ) = 2 ^ 9 * 3 ^ 2 * 5 ^ 3 * 7 * 11 ∧ IsPretransitive H (Vert 𝓑) ∧
        Nat.card (stabilizer H (vInf : Vert 𝓑)) = 443520 ∧
        Set.range (orbit (stabilizer H (vInf : Vert 𝓑)) : Vert 𝓑 → Set (Vert 𝓑)) =
          {{vInf}, Set.range vPt, Set.range vBlk} ∧
        (Set.range (vPt : Ω → Vert 𝓑)).ncard = 22 ∧
        (Set.range (vBlk : {B // B ∈ 𝓑} → Vert 𝓑)).ncard = 77) := by
  obtain ⟨e, he⟩ := steinerTriple_iso h isSteinerTriple_hexads
  have F : HSFacts 𝓑 := HSFacts.of_equiv e he hsFacts_hexads
  obtain ⟨D⟩ := F.mdata
  have hΩ : Fintype.card Ω = 22 := h.card_points
  have h𝓑 : 𝓑.card = 77 := h.card_blocks
  have hne : 𝓑.Nonempty := by
    rw [← Finset.card_pos, h𝓑]
    norm_num
  have : Nonempty Ω := Fintype.card_pos_iff.1 (by rw [hΩ]; norm_num)
  have hA : Nat.card (autGroup 𝓑) = 88704000 := by
    rw [card_autGroup D F.psi hΩ h𝓑, F.card_aut]
  have hodd : ∃ s ∈ autGroup 𝓑, Equiv.Perm.sign s = -1 :=
    let ⟨s, hs, _, hsign⟩ := F.odd
    ⟨s, hs, hsign⟩
  have hsimple := isSimpleGroup_evenSubgroup D F.psi F.odd hΩ h𝓑 hA
  have hHcard := card_evenSubgroup hodd hA
  have huniq := eq_evenSubgroup_of_index_two hsimple hHcard hA
  refine ⟨h𝓑, F.srg, ⟨isPretransitive_autGroup D F.psi, hA, by norm_num,
    range_orbit_stabilizer hne D, restrictΩ_smul, restrictΩ_injective, range_restrictΩ,
    F.card_aut⟩, ⟨⟨evenSubgroup 𝓑, index_evenSubgroup hodd, huniq⟩, fun K hK => ?_⟩⟩
  obtain rfl := huniq K hK
  refine ⟨hsimple, hHcard, by norm_num, isPretransitive_evenSubgroup D F.psi F.odd,
    card_stabilizer_even D F.psi F.odd hΩ h𝓑 hA, range_orbit_stabilizer_even hne D, ?_, ?_⟩
  · rw [Set.ncard_range_of_injective vPt_injective, Nat.card_eq_fintype_card, hΩ]
  · rw [Set.ncard_range_of_injective vBlk_injective, Nat.card_eq_fintype_card, Fintype.card_coe,
      h𝓑]

end CFSG.Sporadic.Recognition.HSGraph
