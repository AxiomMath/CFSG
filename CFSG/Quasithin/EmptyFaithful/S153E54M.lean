module

public import CFSG.Quasithin.EmptyFaithful.S153E54L

public section

namespace CFSG.Quasithin

namespace S153E

open CFSG.Open CFSG.QuasithinUnique
open CFSG.Quasithin.S153E54
open scoped commutatorElement Pointwise

section Final

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem exists_15_3_54 (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} (c : Chain15353 cx N₁ N₂) :
    ∃ g : G, g ∈ Y153 Mc M ∧ NotOrth153 cx.c g := by
  by_contra hcon
  push Not at hcon
  have hperp := isPerp_Zp cx c
  have hVL := conjClosure_Z_Y h113 cx c
  have hle : VZ T M ≤ Zp54 T M V₁ Mc := by
    rw [← hVL]
    refine conjClosure_le fun y hy z hz => ?_
    have hy' : y⁻¹ ∈ Y153 Mc M := (Y153 Mc M).inv_mem hy
    have hNO := hcon y⁻¹ hy'
    have hmem : y * z * y⁻¹ ∈ conjSubgroup (quasithinOmegaOneCenter T) y⁻¹ :=
      mem_conjSubgroup_iff.2 (by simpa [mul_assoc] using hz)
    have hyV : y * z * y⁻¹ ∈ VZ T M := by
      have hyN := cx.c.hyp.le_normalizer (Y153_le Mc M hy)
      exact (Subgroup.mem_normalizer_iff.1 hyN z).1 (cx.c.hyp.Z_le_VZ hz)
    refine ((hperp _).2 ⟨hyV, fun a ha => ?_⟩)
    exact (not_not.1 hNO) a ha _ hmem
  have h1 : (Zp54 T M V₁ Mc).relIndex (VZ T M) = 1 := Subgroup.relIndex_eq_one.2 hle
  rw [relIndex_Zp cx c] at h1
  omega

theorem lemma_15_3_54 (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} (c : Chain15353 cx N₁ N₂) {g : G}
    (hg : g ∈ Y153 Mc M) (hgZ : NotOrth153 cx.c g) : ∃ s : ℕ, Concl15354 cx N₁ N₂ g s := by
  obtain ⟨s, hf⟩ := four_exists h113 cx c hg hgZ
  obtain ⟨-, h2, -, h4, -⟩ := g26_all h113 cx c hg hgZ
  obtain ⟨h51, h52⟩ := five_54 h113 cx c hg hgZ
  exact ⟨s, ⟨I_eq_54 h113 cx c hg hgZ, h4, h2, three_eq_54 h113 cx c hg hgZ,
    three_perp_54 h113 cx c hg hgZ, three_klein_54 h113 cx c hg hgZ, hf.sup, hf.inf, hf.cent₁,
    hf.cent₂, hf.nat₁, hf.nat₂, h51, h52⟩⟩

end Final

end S153E

end CFSG.Quasithin
