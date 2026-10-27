module

public import CFSG.Quasithin.Background.RAVBounds
public import CFSG.Quasithin.Background.S1549CInsp
public import CFSG.Quasithin.Background.S1549CFClaims
public import CFSG.Quasithin.Background.S1549CAlpha

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
  CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

namespace S1549C

theorem claimN_rAV_conjAut {W : Type*} [CommGroup W] (g : MulAut W) (A : Subgroup (MulAut W)) :
    rAV (B1.conjAut g A) = rAV A :=
  CFSG.Quasithin.RAV.rAV_conjAut g A

theorem claimN_eq_of_rank_chain {W : Type*} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {X A B : Subgroup (MulAut W)} (hA : IsA2 X A) (hB : IsA2 X B) (hAB : A ≤ B)
    (hno : ∀ C, C ≤ B → ¬ IsStrongFFStarOffender X C) {a : ℕ}
    (h1 : rkIdx (fixV B) ≤ a) (h2 : a ≤ rk A) (h3 : rk A ≤ rk B) :
    A = B ∧ a = rk A := by
  have hr : ¬ rAV B < 1 := fun hlt => by
    obtain ⟨C, hCB, hC, hrC⟩ := B1_4_4_lt hW hB hlt
    exact hno C hCB ⟨hC, hrC⟩
  have hBpos : (0 : ℚ) < (rk B : ℚ) := by exact_mod_cast hB.rk_pos
  have h4 : rk B ≤ rkIdx (fixV B) := by
    have h5 : (1 : ℚ) ≤ rAV B := not_lt.mp hr
    unfold rAV at h5
    rw [le_div_iff₀ hBpos, one_mul] at h5
    exact_mod_cast h5
  have hrk : rk A = rk B := by omega
  have hcard : Nat.card A = Nat.card B := by
    rw [B1.card_elemAbelian hA.2.2, B1.card_elemAbelian hB.2.2, hrk]
  exact ⟨Subgroup.eq_of_le_of_card_ge hAB hcard.ge, by omega⟩

section Gen

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}

theorem claimN_le_sup_inf_pCoreOf (h : HypF91 T V L V₁ Vp H) {A B : Subgroup G} (hAB : A ≤ B)
    (hBH : B ≤ H)
    (hS : autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure Vp H)) ≤
      autOn (tildeOf V₁ A) (tildeOf V₁ (conjClosure Vp H))) :
    B ≤ A ⊔ (B ⊓ pCoreOf 2 H) := by
  intro v hv
  have hAH : A ≤ H := hAB.trans hBH
  have hmem : starHom h ⟨v, hBH hv⟩ ∈ autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure Vp H)) := by
    rw [autOn_tilde_eq_map_starHom h hBH]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hv)
  have hmemA := hS hmem
  rw [autOn_tilde_eq_map_starHom h hAH] at hmemA
  obtain ⟨a, ha, hav⟩ := Subgroup.mem_map.mp hmemA
  rw [Subgroup.mem_subgroupOf] at ha
  have hq : ((a : G))⁻¹ * v ∈ pCoreOf 2 H := by
    have h1 : starHom h (a⁻¹ * ⟨v, hBH hv⟩) = 1 := by
      rw [map_mul, map_inv, hav, inv_mul_cancel]
    exact (starHom_eq_one_iff h _).mp h1
  have hqB : ((a : G))⁻¹ * v ∈ B := B.mul_mem (B.inv_mem (hAB ha)) hv
  have e : v = (a : G) * ((a : G)⁻¹ * v) := by group
  rw [e]
  exact Subgroup.mul_mem_sup ha ⟨hqB, hq⟩

omit [Finite G] in
theorem claimN_starHom_mem_autOn (h : HypF91 T V L V₁ Vp H) {c : G} (hcH : c ∈ H) :
    starHom h ⟨c, hcH⟩ ∈ autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H)) := by
  rw [autOn_tilde_eq_map_starHom h (le_refl H)]
  exact ⟨⟨c, hcH⟩, Subgroup.mem_subgroupOf.mpr hcH, rfl⟩

theorem claimN_conjAut_le (h : HypF91 T V L V₁ Vp H) {X Y : Subgroup G} (hXH : X ≤ H) {c : G}
    (hcH : c ∈ H) (hcXY : conjSub c X ≤ Y)
    {C : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))}
    (hC : C ≤ autOn (tildeOf V₁ X) (tildeOf V₁ (conjClosure Vp H))) :
    @B1.conjAut _ (modInst h) (starHom h ⟨c, hcH⟩) C ≤
      autOn (tildeOf V₁ Y) (tildeOf V₁ (conjClosure Vp H)) := by
  have hconj := autOn_tilde_conjSub h hXH hcH
  have hle : autOn (tildeOf V₁ (conjSub c X)) (tildeOf V₁ (conjClosure Vp H)) ≤
      autOn (tildeOf V₁ Y) (tildeOf V₁ (conjClosure Vp H)) :=
    autOn_le_autOn _ (secImg_mono hcXY)
  refine le_trans ?_ hle
  intro x hx
  rw [hconj]
  have hx' := (@B1.mem_conjAut _ (modInst h) _ _ _).mp hx
  refine ⟨(starHom h ⟨c, hcH⟩)⁻¹ * x * starHom h ⟨c, hcH⟩, hC hx', ?_⟩
  show starHom h ⟨c, hcH⟩ * ((starHom h ⟨c, hcH⟩)⁻¹ * x * starHom h ⟨c, hcH⟩) *
    (starHom h ⟨c, hcH⟩)⁻¹ = x
  group

end Gen

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem claimN_no_strong_le_Vstar (h11 : StageLemma14111) (h113 : StageLemma14113)
    (cx : Ctx49 G T Mc M V₁ V₂ t) {H : Subgroup G} (hb : InspBase cx H)
    (hno : ¬ ∃ A, @IsStrongFFStarOffender (UTil T M V₁ H) (modInst hb.hF98.toHypF91)
      (StarOf T M V₁ H H) A ∧ A ≤ StarOf T M V₁ H (pCoreOf 2 (Y0 T Mc M ⊔ T)))
    {γ γ' : F8.Geom T (Y153 Mc M) H} {g : ↥(((Y153 Mc M) ⊔ T) ⊔ H)}
    (s : F8Setup T (VZ T M) (Y153 Mc M) H γ γ' g)
    {C : Subgroup (MulAut (UTil T M V₁ H))}
    (hC : C ≤ StarOf T M V₁ H (F8.Uγ (VZ T M) H (g : G))) :
    ¬ @IsStrongFFStarOffender (UTil T M V₁ H) (modInst hb.hF98.toHypF91) (StarOf T M V₁ H H) C := by
  intro hCs
  obtain ⟨c, hcH, hcW⟩ := exists_alpha_Y0 h11 h113 cx.c.hyp hb.hF98 s
  have hF91 := hb.hF98.toHypF91
  refine hno ⟨@B1.conjAut _ (modInst hF91) (starHom hF91 ⟨c, hcH⟩) C, ⟨?_, ?_⟩, ?_⟩
  · exact @B1.isFFStarOffender_conjAut _ (modInst hF91) _ _ hCs.1 _
      (claimN_starHom_mem_autOn hF91 hcH)
  · exact lt_of_eq_of_lt (@claimN_rAV_conjAut _ (modInst hF91) (starHom hF91 ⟨c, hcH⟩) C) hCs.2
  · exact claimN_conjAut_le hF91 (hb.hF98.Vγ_le_H s) hcH hcW hC

theorem claim_n1 (h11 : StageLemma14111) (h113 : StageLemma14113) (cx : Ctx49 G T Mc M V₁ V₂ t)
    {H : Subgroup G} (hb : InspBase cx H)
    (hno : ¬ ∃ A, @IsStrongFFStarOffender (UTil T M V₁ H) (modInst hb.hF98.toHypF91)
      (StarOf T M V₁ H H) A ∧ A ≤ StarOf T M V₁ H (pCoreOf 2 (Y0 T Mc M ⊔ T)))
    {γ γ' : F8.Geom T (Y153 Mc M) H} {g : ↥(((Y153 Mc M) ⊔ T) ⊔ H)}
    (s : F8Setup T (VZ T M) (Y153 Mc M) H γ γ' g)
    (hpos : 0 < mIdx (F8.Uγ (ZS153 T M V₁) H (g : G))
      (F8.Dγ (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)))
    (hle : mIdx (UH T M V₁ H) (F8.DH (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)) ≤
      mIdx (F8.Uγ (ZS153 T M V₁) H (g : G))
        (F8.Dγ (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G))) :
    mIdx (UH T M V₁ H) (F8.DH (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)) =
        mIdx (F8.Uγ (ZS153 T M V₁) H (g : G))
          (F8.Dγ (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)) ∧
      StarOf T M V₁ H (F8.Uγ (ZS153 T M V₁) H (g : G)) =
        StarOf T M V₁ H (F8.Uγ (VZ T M) H (g : G)) ∧
      F8.Uγ (VZ T M) H (g : G) =
        F8.Uγ (ZS153 T M V₁) H (g : G) ⊔
          F9.Eγ (VZ T M) (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G) := by
  have h98 := hb.hF98
  have hF91 := h98.toHypF91
  obtain ⟨hUA2, hVA2⟩ := claim_h_isA2 h113 cx hb.adm h98 hb.claimC s hpos hle
  obtain ⟨hUV, h2, h3, h4, -⟩ := claim_h_chain h113 cx hb.adm h98 hb.claimC s hpos hle
  have hW : ∀ w : ↥(tildeOf (quasithinOmegaOneCenter T) (UH T M V₁ H)), w ^ 2 = 1 := by
    let _ : CommGroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH T M V₁ H)) := modInst hF91
    exact fun w => Subtype.ext (by simpa using hF91.isElemAbelian_tilde.2 w w.2)
  obtain ⟨hAB, hrk⟩ := @claimN_eq_of_rank_chain _ (modInst hF91) _ hW _ _ _ hUA2 hVA2 hUV
    (fun C hC => claimN_no_strong_le_Vstar h11 h113 cx hb hno s hC) _ h2 h3 h4
  have hUγVγ := h98.Uγ_le_Vγ (g := g)
  have hVγH := h98.Vγ_le_H s
  refine ⟨hrk.trans (claim_rk_Ustar h98 s), hAB, ?_⟩
  have hsup := claimN_le_sup_inf_pCoreOf hF91 hUγVγ hVγH hAB.ge
  rw [← Eγ_eq_inf_pCoreOf h98 s] at hsup
  exact le_antisymm hsup (sup_le hUγVγ (centralizerMod_le_left _ _ _))

end S1549C

end CFSG.Quasithin
