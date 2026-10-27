module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFiveTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsNoO2Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeNormalCoreTwo
public import CFSG.GroupTheory.E3Params

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem aParam_le_autSub {W : Type} [CommGroup W] [Finite W]
    {X : Subgroup (MulAut W)} {U : Subgroup W} (hstab : X ≤ stabSub U)
    (hfaith : ∀ g ∈ X, (∀ u ∈ U, g u = u) → g = 1) :
    E3.aParam X ≤ E3.aParam (autSub X U) := by
  by_cases h0 : 0 < E3.aParam X
  · obtain ⟨E, hE⟩ := CFSG.GroupTheory.aSet_aParam_nonempty h0
    have hAnc : ¬ E ≤ centSub U := by
      intro hc
      obtain ⟨g, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE.2.1
      exact hg1 (Subtype.ext (hfaith (g : MulAut W) (hE.1 g.2) fun u hu => hc g.2 u hu))
    exact E3.le_aParam_of_mem_aSet h0
      (CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.aSet_autSub hE.1 hstab hE hAnc)
  · have hz : E3.aParam X = 0 := Nat.eq_zero_of_not_pos h0
    rw [hz]
    exact Nat.zero_le _

private theorem conjClosure_eq_iSup_translates (H S : Subgroup G) :
    conjClosure H S = ⨆ l : ↥H, S.map (MulAut.conj (l : G)).toMonoidHom := by
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun K hK => ?_
    obtain ⟨l, hl, rfl⟩ := hK
    exact le_iSup_of_le ⟨l, hl⟩ le_rfl
  · refine iSup_le fun l => ?_
    exact le_iSup₂_of_le _ ⟨(l : G), l.2, rfl⟩ le_rfl

private theorem actTriv_of_fix_imgTil {W₁ W₂ : Subgroup G} (hW₁ : IsElemAbelian 2 W₁)
    (hW₂ : IsElemAbelian 2 W₂) (h12 : W₁ ≤ W₂) {x : G} (hx : x ∈ stabTil (⊥ : Subgroup G) W₂)
    (hfix : ∀ u ∈ imgTil (⊥ : Subgroup G) W₂ hW₂ W₁,
      actTil (⊥ : Subgroup G) W₂ hW₂ ⟨x, hx⟩ u = u) :
    ∀ w ∈ W₁, x * w * x⁻¹ = w := by
  intro w hw
  let y : IntMod W₂ hW₂ := IntMod.mk hW₂ ⟨w, h12 hw⟩
  have hyv : y.val = w := rfl
  have hyU : mkTil (⊥ : Subgroup G) W₂ hW₂ y ∈ imgTil (⊥ : Subgroup G) W₂ hW₂ W₁ :=
    Subgroup.mem_map_of_mem (mkTil (⊥ : Subgroup G) W₂ hW₂)
      ((mem_intSub W₂ hW₂ W₁ y).2 (by rw [hyv]; exact hw))
  have h2 := hfix (mkTil (⊥ : Subgroup G) W₂ hW₂ y) hyU
  rw [actTil_mk] at h2
  have h3 : (actStab (⊥ : Subgroup G) W₂ hW₂ ⟨x, hx⟩ y).val * y.val⁻¹ = 1 := by
    have h4 := (mkTil_eq_iff ⊥ W₂ hW₂ (actStab ⊥ W₂ hW₂ ⟨x, hx⟩ y) y).1 h2
    simpa using h4
  rw [mul_inv_eq_one] at h3
  have h5 : x * y.val * x⁻¹ = y.val := by
    rw [← actStab_apply_val (⊥ : Subgroup G) W₂ hW₂ ⟨x, hx⟩ y]
    exact h3
  rwa [hyv] at h5

theorem aBar_le_of_le_of_faithful {M W₁ W₂ : Subgroup G}
    (hW₁ : IsElemAbelian 2 W₁) (hW₂ : IsElemAbelian 2 W₂) (h12 : W₁ ≤ W₂)
    (hM₁ : M ≤ Subgroup.normalizer (W₁ : Set G))
    (hM₂ : M ≤ Subgroup.normalizer (W₂ : Set G))
    (hfaith : ∀ x ∈ M, (∀ w ∈ W₁, x * w * x⁻¹ = w) → (∀ w ∈ W₂, x * w * x⁻¹ = w)) :
    aBar M ⊥ W₂ hW₂ ≤ aBar M ⊥ W₁ hW₁ := by
  classical
  set U : Subgroup (Vtil (⊥ : Subgroup G) W₂ hW₂) := imgTil ⊥ W₂ hW₂ W₁ with hU
  have hstab : barSub (⊥ : Subgroup G) W₂ hW₂ M ≤ stabSub U := by
    intro φ hφ
    obtain ⟨x, hxM, rfl⟩ := (mem_barSub (⊥ : Subgroup G) W₂ hW₂ M φ).1 hφ
    exact actTil_mem_stabSub_imgTil hW₂ hW₁ h12 x.2
      (Subgroup.mem_inf.mpr ⟨hM₁ hxM, by
        rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top x.1⟩)
  have hfaithX : ∀ g ∈ barSub (⊥ : Subgroup G) W₂ hW₂ M, (∀ u ∈ U, g u = u) → g = 1 := by
    intro φ hφ hfix
    obtain ⟨x, hxM, rfl⟩ := (mem_barSub (⊥ : Subgroup G) W₂ hW₂ M φ).1 hφ
    rw [hU] at hfix
    have hx₁ : ∀ w ∈ W₁, x * w * x⁻¹ = w :=
      actTriv_of_fix_imgTil hW₁ hW₂ h12 x.2 hfix
    exact (actTil_eq_one_iff ⊥ W₂ hW₂ x).2 fun v hv => by
      rw [Subgroup.mem_bot, hfaith x hxM hx₁ v hv]
      group
  have h1 : E3.aParam (barSub (⊥ : Subgroup G) W₂ hW₂ M) ≤
      E3.aParam (autSub (barSub (⊥ : Subgroup G) W₂ hW₂ M) U) :=
    aParam_le_autSub hstab hfaithX
  obtain ⟨e, he⟩ := Mbar_eq_autSub_map hW₂ hW₁ h12 hM₂ hM₁
  have h2 : E3.aParam (Mbar M ⊥ W₁ hW₁) =
      E3.aParam (autSub (barSub (⊥ : Subgroup G) W₂ hW₂ M) U) := by
    rw [he, CFSG.Quasithin.H.aParam_map_congrHom]
  unfold aBar
  rw [h2]
  exact h1

private theorem isPGroup_of_inf_pCoreOf {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {R : Subgroup G} (hRH : R ≤ D.T ⊔ c.L0)
    (hHnR : D.T ⊔ c.L0 ≤ Subgroup.normalizer (R : Set G))
    (hR0le : R ⊓ c.L0 ≤ CFSG.Open.pCoreOf 2 c.L0) : IsPGroup 2 ↥R := by
  have hHnL0 : (D.T ⊔ c.L0 : Subgroup G) ≤ Subgroup.normalizer (c.L0 : Set G) :=
    sup_le c.hL0.1.1 Subgroup.le_normalizer
  haveI hRn : (R.subgroupOf (D.T ⊔ c.L0)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRH).mpr hHnR
  have hR0p : IsPGroup 2 ↥(R ⊓ c.L0) :=
    IsPGroup.to_le (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L0) hR0le
  have hR0p' : IsPGroup 2 ((R ⊓ c.L0).subgroupOf R) :=
    hR0p.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
  haveI hL0nH : ((c.L0).subgroupOf (D.T ⊔ c.L0)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hHnL0
  have hRN : R ≤ Subgroup.normalizer ((R ⊓ c.L0 : Subgroup G) : Set G) :=
    (le_inf (hRH.trans hHnR) (hRH.trans hHnL0)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  haveI hR0n : ((R ⊓ c.L0).subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hRN
  have hHL : IsPGroup 2 (↥(D.T ⊔ c.L0) ⧸ (c.L0).subgroupOf (D.T ⊔ c.L0)) :=
    CFSG.GroupTheory.isPGroup_quotient_sup_left (p := 2) (T := D.T) (C := c.L0)
      (CFSG.ABGLocalTools.IsSylowOf.isPGroup D.sylowG)
  have hRR0 : IsPGroup 2 (↥R ⧸ (R ⊓ c.L0).subgroupOf R) :=
    isPGroup_quotient_inf_of_isPGroup_quotient (p := 2) le_sup_right hRH hHL
  exact IsPGroup.of_subgroup_of_quotient hR0p' hRR0

private theorem le_centralizer_W23_1_of_isPGroup {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {R : Subgroup G} (hRH : R ≤ D.T ⊔ c.L0)
    (hHnR : D.T ⊔ c.L0 ≤ Subgroup.normalizer (R : Set G)) (hR2 : IsPGroup 2 ↥R) :
    R ≤ Subgroup.centralizer (W23_1 c : Set G) := by
  have hpR : R ≤ CFSG.Open.pCoreOf 2 (D.T ⊔ c.L0) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) hRH hHnR hR2
  have hTsyl : IsSylowIn 2 D.T (D.T ⊔ c.L0) := by
    have hTN : D.T ≤ Subgroup.normalizer ((D.T ⊔ c.L0 : Subgroup G) : Set G) :=
      (le_inf Subgroup.le_normalizer c.hL0.1.1).trans
        (Subgroup.inf_normalizer_le_normalizer_sup D.T c.L0)
    have h := Ctx23L.isSylowIn_inf_of_le_normalizer (D := D) (N := D.T ⊔ c.L0) hTN
    rwa [inf_eq_left.mpr le_sup_left] at h
  have hRZ : R ≤ Subgroup.centralizer (D.Z : Set G) :=
    (hpR.trans (CFSG.Quasithin.E1.pCoreOf_two_le_of_isSylowIn hTsyl)).trans
      (uc22main1_T_le_centralizer D)
  rw [show W23_1 c = ⨆ l : ↥c.L0, D.Z.map (MulAut.conj (l : G)).toMonoidHom from
    conjClosure_eq_iSup_translates c.L0 D.Z]
  refine CFSG.subgroup_le_centralizer_iSup_of_le_centralizer _ fun l => ?_
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hw
  change ((l : G) * z * (l : G)⁻¹) * r = r * ((l : G) * z * (l : G)⁻¹)
  have hconj : (l : G)⁻¹ * r * (l : G) ∈ R := by
    have hl : (l : G)⁻¹ ∈ D.T ⊔ c.L0 :=
      (D.T ⊔ c.L0).inv_mem ((le_sup_right : c.L0 ≤ D.T ⊔ c.L0) l.2)
    have h := (Subgroup.mem_normalizer_iff.mp (hHnR hl) r).1 hr
    simpa using h
  have hz' : ((l : G)⁻¹ * r * (l : G)) * z = z * ((l : G)⁻¹ * r * (l : G)) :=
    (Subgroup.mem_centralizer_iff.mp (hRZ hconj) z hz).symm
  calc ((l : G) * z * (l : G)⁻¹) * r
      = (l : G) * (z * ((l : G)⁻¹ * r * (l : G))) * (l : G)⁻¹ := by group
    _ = (l : G) * (((l : G)⁻¹ * r * (l : G)) * z) * (l : G)⁻¹ := by rw [hz']
    _ = r * ((l : G) * z * (l : G)⁻¹) := by group

theorem Ctx23L.le_centralizer_W23_1 {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {A : Subgroup G} (hAN : c.L0 ⊔ D.T ≤ Subgroup.normalizer (A : Set G))
    (hCA : c.L0 ⊓ Subgroup.centralizer (A : Set G) ≤ CFSG.Open.pCoreOf 2 c.L0) :
    (c.L0 ⊔ D.T) ⊓ Subgroup.centralizer (A : Set G) ≤
      Subgroup.centralizer (W23_1 c : Set G) := by
  have hH : (c.L0 ⊔ D.T : Subgroup G) = D.T ⊔ c.L0 := sup_comm ..
  rw [hH]
  set R : Subgroup G := (D.T ⊔ c.L0) ⊓ Subgroup.centralizer (A : Set G) with hRdef
  have hAN' : (D.T ⊔ c.L0 : Subgroup G) ≤ Subgroup.normalizer (A : Set G) := by
    rw [sup_comm]
    exact hAN
  have hHnR : (D.T ⊔ c.L0 : Subgroup G) ≤ Subgroup.normalizer (R : Set G) := by
    rw [hRdef]
    exact (le_inf Subgroup.le_normalizer
      (hAN'.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer A))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hRH : R ≤ D.T ⊔ c.L0 := hRdef.le.trans inf_le_left
  have hR0le : R ⊓ c.L0 ≤ CFSG.Open.pCoreOf 2 c.L0 :=
    fun x hx => hCA ⟨hx.2, hx.1.2⟩
  exact le_centralizer_W23_1_of_isPGroup c hRH hHnR (isPGroup_of_inf_pCoreOf c hRH hHnR hR0le)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
