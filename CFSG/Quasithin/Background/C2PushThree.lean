module

public import CFSG.Quasithin.Background.C2PushLift

public section

namespace CFSG.Quasithin.C2Push

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem isTwoRadicalIn_sup_of_le_normalizer {M R L : Subgroup G} (hR : IsTwoRadicalIn M R)
    (hL : L ∈ cComp M) (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hRL : R ≤ Subgroup.normalizer (L : Set G)) : IsTwoRadicalIn (L ⊔ R) R := by
  have hRp : IsPGroup 2 R := hR.isPGroup
  refine ⟨le_sup_right, hR.2.1, le_antisymm (le_pCoreOf_inf_normalizer le_sup_right hRp) ?_⟩
  set S : Subgroup G := pCoreOf 2 ((L ⊔ R) ⊓ Subgroup.normalizer (R : Set G)) with hS
  have hRS : R ≤ S := le_pCoreOf_inf_normalizer le_sup_right hRp
  have hSle : S ≤ (L ⊔ R) ⊓ Subgroup.normalizer (R : Set G) := pCoreOf_le 2 _
  intro s hs
  have hsLR : s ∈ L ⊔ R := (hSle hs).1
  have hsN : s ∈ Subgroup.normalizer (R : Set G) := (hSle hs).2
  have hsLR' : s ∈ (↑(L ⊔ R) : Set G) := hsLR
  rw [Subgroup.coe_mul_of_right_le_normalizer_left L R hRL] at hsLR'
  obtain ⟨l, hl, r, hr, hsr⟩ := hsLR'
  have hlsr : l = s * r⁻¹ := by rw [← hsr]; group
  have hlS : l ∈ S := by
    rw [hlsr]
    exact S.mul_mem hs (S.inv_mem (hRS hr))
  have hlN : l ∈ Subgroup.normalizer (R : Set G) := by
    rw [hlsr]
    exact Subgroup.mul_mem _ hsN (Subgroup.inv_mem _ (Subgroup.le_normalizer hr))
  have hSL : S ⊓ L ≤ pCoreOf 2 (L ⊓ Subgroup.normalizer (R : Set G)) := by
    refine le_pCoreOf_of_le_normalizer 2
      (fun x hx => ⟨hx.2, (hSle hx.1).2⟩) ?_ ((pCoreOf_isPGroup 2 _).to_le inf_le_left)
    intro x hx
    have hxS : x ∈ Subgroup.normalizer (S : Set G) :=
      le_normalizer_pCoreOf 2 _ ⟨Subgroup.mem_sup_left hx.1, hx.2⟩
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hxS, Subgroup.le_normalizer hx.1⟩
  have hlR : l ∈ R := pCoreOf_inf_normalizer_le hR hL hLq (hSL ⟨hlS, hl⟩)
  rw [← hsr]
  exact R.mul_mem hlR hr

end CFSG.Quasithin.C2Push
