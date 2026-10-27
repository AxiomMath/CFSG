module

public import CFSG.Quasithin.Background.S1549DBr

public section

namespace CFSG.Quasithin

namespace S1549D

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
  CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom CFSG.Quasithin.S1549C
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem overgroup_le_M_of_minimal (cx : Ctx49 G T Mc M V₁ V₂ t) {H : Subgroup G} (hb : InspBase cx H)
    {K : Subgroup (MulAut (UTil T M V₁ H))}
    (hK : starOfSub hb.hF98.toHypF91 (Y0 T Mc M ⊔ T) ≤ K)
    (hKH : K ≤ starOfSub hb.hF98.toHypF91 H) (hne : K ≠ starOfSub hb.hF98.toHypF91 H) :
    K ≤ starOfSub hb.hF98.toHypF91 (M ⊓ H) := by
  classical
  have h := hb.hF98.toHypF91
  by_contra hnot
  let H₁ : Subgroup G := preStar h K
  have hH₁H : H₁ ≤ H := preStar_le h K
  have hH₁M : ¬ H₁ ≤ M := by
    intro hM
    apply hnot
    intro y hy
    obtain ⟨x, hx, hxy⟩ := (mem_starOfSub h).mp (hKH hy)
    have hxH₁ : (x : G) ∈ H₁ := (starHom_mem_iff h).mpr (hxy ▸ hy)
    exact (mem_starOfSub h).mpr ⟨x, ⟨hM hxH₁, x.2⟩, hxy⟩
  have hTH₁ : T ≤ H₁ := by
    intro t' ht'
    have htH : t' ∈ H := h.T_le_H ht'
    refine (mem_preStar_iff h).mpr ⟨htH, hK ((mem_starOfSub h).mpr ⟨⟨t', htH⟩, (le_sup_right : T ≤ Y0 T Mc M ⊔ T) ht', rfl⟩)⟩
  have hY0H₁ : Y0 T Mc M ⊔ T ≤ H₁ := by
    refine sup_le ?_ hTH₁
    intro y hy
    have hyH : y ∈ H := hb.adm.hY0 ((le_sup_left : Y0 T Mc M ≤ Y0 T Mc M ⊔ T) hy)
    exact (mem_preStar_iff h).mpr
      ⟨hyH, hK ((mem_starOfSub h).mpr ⟨⟨y, hyH⟩, (le_sup_left : Y0 T Mc M ≤ Y0 T Mc M ⊔ T) hy, rfl⟩)⟩
  have hP2 : pCoreOf 2 H₁ ≠ ⊥ := by
    intro hbot
    apply hb.adm.hH.1.2
    have hle : pCoreOf 2 H ≤ pCoreOf 2 H₁ := by
      refine le_pCoreOf_of_le_normalizer 2 (pCoreOf_le_preStar h K) ?_ (pCoreOf_isPGroup 2 H)
      exact hH₁H.trans (le_normalizer_pCoreOf 2 H)
    exact le_bot_iff.mp (hbot ▸ hle)
  have hadm : Adm T Mc M H₁ := ⟨⟨⟨hTH₁, hP2⟩, hH₁M⟩, hY0H₁⟩
  have hEq : H₁ = H := hb.min H₁ hadm hH₁H
  apply hne
  refine le_antisymm hKH (fun y hy => ?_)
  obtain ⟨x, hx, hxy⟩ := (mem_starOfSub h).mp hy
  have hxH₁ : (x : G) ∈ H₁ := by
    rw [hEq]
    exact x.2
  rw [← hxy]
  exact (starHom_mem_iff h).mp hxH₁

end S1549D

end CFSG.Quasithin
