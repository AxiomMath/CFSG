module

public import CFSG.Quasithin.Background.S1549CInsp
public import CFSG.Quasithin.Background.S1549CAlpha
public import CFSG.Quasithin.Background.S1549CFClaims

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
  CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

namespace S1549C

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem exists_offData (h11 : StageLemma14111) (h113 : StageLemma14113)
    (cx : Ctx49 G T Mc M V₁ V₂ t) {H : Subgroup G} (hb : InspBase cx H)
    {γ γ' : F8.Geom T (Y153 Mc M) H} {g : ↥(((Y153 Mc M) ⊔ T) ⊔ H)}
    (s : F8Setup T (VZ T M) (Y153 Mc M) H γ γ' g)
    (hpos : 0 < mIdx (F8.Uγ (ZS153 T M V₁) H (g : G))
      (F8.Dγ (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)))
    (hle : mIdx (UH T M V₁ H) (F8.DH (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)) ≤
      mIdx (F8.Uγ (ZS153 T M V₁) H (g : G))
        (F8.Dγ (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G))) :
    ∃ c : G, c ∈ H ∧ ∃ B : Subgroup (MulAut (UTil T M V₁ H)),
      OffData hb (conjSub c (F8.Uγ (VZ T M) H (g : G))) B := by
  obtain ⟨c, hcH, hcW⟩ := exists_alpha_Y0 h11 h113 cx.c.hyp hb.hF98 s
  have hF91 := hb.hF98.toHypF91
  obtain ⟨-, hA2, -, hr⟩ := claim_h_full h113 cx hb.adm hb.hF98 hb.claimC s hpos hle
  have hV : ∀ v : ↥(tildeOf (quasithinOmegaOneCenter T) (conjClosure (ZS153 T M V₁) H)),
      v ^ 2 = 1 := fun w => by
    apply Subtype.ext
    have := hF91.isElemAbelian_tilde.2
      (w : SecQuot (Subgroup.normalizer ((quasithinOmegaOneCenter T : Subgroup G) : Set G))
        (quasithinOmegaOneCenter T)) w.2
    simpa using this
  obtain ⟨B₀, hB₀le, hB₀off, -⟩ := @B1_4_4_le _ (modInst hF91) _ hV _ _ hA2 hr
  have hρc : starHom hF91 ⟨c, hcH⟩ ∈ StarOf T M V₁ H H := by
    have hmap := autOn_tilde_eq_map_starHom hF91 (le_refl H)
    show starHom hF91 ⟨c, hcH⟩ ∈ autOn (tildeOf (quasithinOmegaOneCenter T) H)
      (tildeOf (quasithinOmegaOneCenter T) (conjClosure (ZS153 T M V₁) H))
    rw [hmap]
    exact ⟨⟨c, hcH⟩, Subgroup.mem_subgroupOf.mpr hcH, rfl⟩
  refine ⟨c, hcH, @B1.conjAut _ (modInst hF91) (starHom hF91 ⟨c, hcH⟩) B₀, ?_⟩
  refine ⟨hcW, ?_, ?_⟩
  · intro (x : MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (conjClosure (ZS153 T M V₁) H))) hx
    have hconj := autOn_tilde_conjSub hF91 (hb.hF98.Vγ_le_H s) hcH
    show x ∈ autOn (tildeOf (quasithinOmegaOneCenter T)
      (conjSub c (F8.Uγ (VZ T M) H (g : G))))
      (tildeOf (quasithinOmegaOneCenter T) (conjClosure (ZS153 T M V₁) H))
    rw [hconj]
    have hx' := @B1.mem_conjAut _ (modInst hF91) _ _ _ |>.mp hx
    refine ⟨(starHom hF91 ⟨c, hcH⟩)⁻¹ * x * starHom hF91 ⟨c, hcH⟩, hB₀le hx', ?_⟩
    show starHom hF91 ⟨c, hcH⟩ * ((starHom hF91 ⟨c, hcH⟩)⁻¹ * x * starHom hF91 ⟨c, hcH⟩) *
      (starHom hF91 ⟨c, hcH⟩)⁻¹ = x
    group
  · exact @B1.isFFStarOffender_conjAut _ (modInst hF91) _ _ hB₀off _ hρc

end S1549C

end CFSG.Quasithin
