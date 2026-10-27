module

public import CFSG.Open.LocalVocabulary
import CFSG.GroupTheory.ElementaryAbelianTransport

@[expose] public section

namespace CFSG.SylowOfUniqueSubgroup

open CFSG.Open

theorem eq_of_isPGroup_of_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {S W : Subgroup G} (hS : IsPGroup p S) (hWS : W ≤ S) (hW : IsElemAbelian p W)
    (huniq : ∀ U : Subgroup G, U ≤ S → IsElemAbelian p U → Nat.card U = Nat.card W → U = W)
    (hSN : S ≤ Subgroup.normalizer (W : Set G))
    (hmax : ∀ R : Subgroup G, R ≤ Subgroup.normalizer (W : Set G) → IsPGroup p R → S ≤ R →
      R = S)
    {R : Subgroup G} (hR : IsPGroup p R) (hSR : S ≤ R) : R = S := by
  have _hS := hS
  by_contra hne
  have hSRlt : S < R := lt_of_le_of_ne hSR (Ne.symm hne)
  have hnil : Group.IsNilpotent ↥R := hR.isNilpotent
  have hsub_lt : S.subgroupOf R < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    exact not_le_of_gt hSRlt (Subgroup.subgroupOf_eq_top.mp htop)
  obtain ⟨x, hxN, hxS⟩ :=
    SetLike.exists_of_lt
      (Group.normalizerCondition_of_isNilpotent (G := ↥R) (h := hnil)
        (S.subgroupOf R) hsub_lt)
  let xG : G := (x : G)
  have hxGR : xG ∈ R := x.2
  have hxGS : xG ∉ S := fun h => hxS (Subgroup.mem_subgroupOf.2 h)
  have hconjS : ∀ s ∈ S, xG * s * xG⁻¹ ∈ S := by
    intro s hs
    have h1 := (Subgroup.mem_normalizer_iff.1 hxN ⟨s, hSR hs⟩).1 (Subgroup.mem_subgroupOf.2 hs)
    have h2 : ((x * ⟨s, hSR hs⟩ * x⁻¹ : ↥R) : G) = xG * s * xG⁻¹ := by
      simp [xG]
    rw [← h2]
    exact Subgroup.mem_subgroupOf.1 h1
  let W' : Subgroup G := W.map (MulAut.conj xG)
  have hW'leS : W' ≤ S := by
    intro y hy
    rcases Subgroup.mem_map.1 hy with ⟨w, hw, rfl⟩
    simpa [MulAut.conj_apply, xG] using hconjS w (hWS hw)
  have hW'elem : IsElemAbelian p W' := by
    have := hW.map (MulAut.conj xG).toMonoidHom
    simpa [W'] using this
  have hW'card : Nat.card W' = Nat.card W := by
    have := Subgroup.card_map_of_injective (K := W) (f := (MulAut.conj xG).toMonoidHom)
      (MulAut.conj xG).injective
    simpa [W'] using this
  have hW'eq : W' = W := huniq W' hW'leS hW'elem hW'card
  have hxNW : xG ∈ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simpa [W'] using hW'eq
  let T : Subgroup G := S ⊔ Subgroup.zpowers xG
  have hTR : T ≤ R := sup_le hSR (Subgroup.zpowers_le.mpr hxGR)
  have hTN : T ≤ Subgroup.normalizer (W : Set G) :=
    sup_le hSN (Subgroup.zpowers_le.mpr hxNW)
  have hTp : IsPGroup p T := hR.to_le hTR
  have hTeq : T = S := hmax T hTN hTp le_sup_left
  have hxT : xG ∈ T := Subgroup.mem_sup_right (Subgroup.mem_zpowers xG)
  rw [hTeq] at hxT
  exact hxGS hxT

end CFSG.SylowOfUniqueSubgroup

end
