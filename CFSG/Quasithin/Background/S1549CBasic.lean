module

public import CFSG.Quasithin.Background.C1PackS15349

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement Pointwise

namespace S1549C

section Vocabulary

variable {G : Type} [Group G]

@[expose] def Y0 (T Mc M : Subgroup G) : Subgroup G :=
  oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G))

@[expose] def UH (T M V₁ H : Subgroup G) : Subgroup G := conjClosure (ZS153 T M V₁) H

@[expose] def VH (T M H : Subgroup G) : Subgroup G := conjClosure (VZ T M) H

structure Adm (T Mc M H : Subgroup G) : Prop where
  hH : IsHTM153 T M H
  hY0 : Y0 T Mc M ⊔ T ≤ H

end Vocabulary

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

omit [Finite G] in
theorem Y0_le (T Mc M : Subgroup G) :
    Y0 T Mc M ≤ Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G) :=
  oTwoUpper_le _

theorem pCoreOf_Y153_le (h113 : StageLemma14113) (h : Hyp153 G T Mc M) :
    pCoreOf 2 (Y153 Mc M) ≤ T ⊓ Subgroup.centralizer (VZ T M : Set G) := by
  rw [← h.lemma_15_3_7_pCore h113]
  refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_left) ?_
    (pCoreOf_isPGroup 2 _)
  exact sup_le (le_normalizer_pCoreOf 2 _)
    (h.T_le.trans ((le_normalizer_Y153 Mc M).trans (normalizer_le_normalizer_pCoreOf 2 _)))

theorem inf_le_sup_Y0 (h113 : StageLemma14113) (h : Hyp153 G T Mc M) :
    Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ pCoreOf 2 (Y153 Mc M) ⊔ Y0 T Mc M := by
  intro c hc
  have hYM := Y153_le Mc M
  obtain ⟨φ, -⟩ := exists_mulEquiv_imageOTwoQuot hYM (le_normalizer_Y153 Mc M)
  have hexp : ∀ q : OTwoQuot (Y153 Mc M), q ^ 3 = 1 := fun q => by
    have := (Hyp153.Ystar_structure h113 h).1.2.2 (φ q)
    apply φ.injective
    rw [map_pow, map_one]
    exact Subtype.ext (by simpa using congrArg Subtype.val this)
  set q : OTwoQuot (Y153 Mc M) := QuotientGroup.mk (⟨c, hc.1⟩ : ↥(Y153 Mc M)) with hq
  have hcfin : orderOf c ≠ 0 := (orderOf_pos c).ne'
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hcfin
  set c' : G := c ^ 2 ^ k with hc'
  have hdvd : 2 ^ k ∣ orderOf c := by rw [hkm]; exact dvd_mul_right _ _
  have hc'o : orderOf c' = m := by
    rw [hc', orderOf_pow_of_dvd (by positivity) hdvd, hkm,
      Nat.mul_div_cancel_left _ (by positivity)]
  have hc'K : c' ∈ Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G) :=
    Subgroup.pow_mem _ hc _
  have hc'Y0 : c' ∈ Y0 T Mc M := mem_oTwoUpper_of_odd hc'K (hc'o ▸ hm)
  have hcop : Nat.Coprime (2 ^ k) (orderOf q) := by
    have h3 : orderOf q ∣ 3 := orderOf_dvd_of_pow_eq_one (hexp q)
    exact Nat.Coprime.pow_left k (Nat.Coprime.coprime_dvd_right h3 (by norm_num))
  have hmem := A4.mem_zpowers_pow_of_coprime hcop
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hqc : q ^ 2 ^ k =
      QuotientGroup.mk (⟨c', Subgroup.pow_mem _ hc.1 _⟩ : ↥(Y153 Mc M)) := by
    rw [hq, ← QuotientGroup.mk_pow]; rfl
  have hjq : (QuotientGroup.mk (⟨c', Subgroup.pow_mem _ hc.1 _⟩ : ↥(Y153 Mc M)) :
      OTwoQuot (Y153 Mc M)) ^ j = q := by
    rw [← hqc]; exact hj
  have hjc : (QuotientGroup.mk ((⟨c', Subgroup.pow_mem _ hc.1 _⟩ : ↥(Y153 Mc M)) ^ j) :
      OTwoQuot (Y153 Mc M)) = q := by
    rw [QuotientGroup.mk_zpow]; exact hjq
  have hel : ((⟨c', Subgroup.pow_mem _ hc.1 _⟩ : ↥(Y153 Mc M)) ^ j)⁻¹ * ⟨c, hc.1⟩ ∈
      CFSG.Open.pCore 2 ↥(Y153 Mc M) := by
    rw [← QuotientGroup.eq]
    exact hjc
  have hc'j : c' ^ j ∈ Y0 T Mc M := Subgroup.zpow_mem _ hc'Y0 j
  have ho : (c' ^ j)⁻¹ * c ∈ pCoreOf 2 (Y153 Mc M) := ⟨_, hel, by simp⟩
  have : c = c' ^ j * ((c' ^ j)⁻¹ * c) := by group
  rw [this, sup_comm]
  exact Subgroup.mul_mem_sup hc'j ho

structure Ctx49 (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ : Subgroup G) (t : G) : Prop where
  c : Ctx153 G T Mc M V₁ V₂ t
  r45 : Res15345 T Mc M V₁ V₂
  r46 : Res15346 T M V₁ V₂
  r47 : Res15347 T M V₁
  case2 : Case157Two T Mc M
  hF : ∀ H : Subgroup G, IsHTM153 T M H →
    Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ H →
      HypF91 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H

theorem not_Y0_le_pCoreOf (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    (hc2 : Case157Two T Mc M) : ¬ Y0 T Mc M ≤ pCoreOf 2 (Y153 Mc M) := by
  intro hle
  have hK : Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ pCoreOf 2 (Y153 Mc M) :=
    (inf_le_sup_Y0 h113 h).trans (sup_le le_rfl hle)
  have hcenter : Subgroup.center (OTwoQuot (Y153 Mc M)) = ⊥ := by
    refine eq_bot_iff.mpr fun z hz => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    have hyO : (y : G) ∈ O2Z (Y153 Mc M) := mem_O2Z_iff.mpr ⟨y.2, hz⟩
    rw [hc2.2] at hyO
    have := hK hyO
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff _).mpr
      ((Subgroup.mem_map_iff_mem (Y153 Mc M).subtype_injective).mp this)
  have h3 := hc2.1.1.center_order_p
  rw [hcenter, Subgroup.card_bot] at h3
  omega

theorem inf_le_of_adm (h113 : StageLemma14113) (h : Hyp153 G T Mc M) {H : Subgroup G}
    (hH : Adm T Mc M H) : Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ H := by
  refine (inf_le_sup_Y0 h113 h).trans (sup_le ?_ (le_sup_left.trans hH.hY0))
  exact ((pCoreOf_Y153_le h113 h).trans inf_le_left).trans (le_sup_right.trans hH.hY0)

theorem adm_mc (h11 : StageLemma14111) (h : Hyp153 G T Mc M) : Adm T Mc M Mc := by
  refine ⟨C1Pack153.isHTM153_mc h, sup_le ?_ h.qtfe.t_le_mc⟩
  intro y hy
  have hyC : y ∈ Subgroup.centralizer (VZ T M : Set G) := (Y0_le T Mc M hy).2
  have : y ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    Subgroup.centralizer_le h.Z_le_VZ hyC
  exact (h.lemma_15_3_4 h11) ▸ this

theorem Ctx49.hF91 (cx : Ctx49 G T Mc M V₁ V₂ t) (h113 : StageLemma14113) {H : Subgroup G}
    (hH : Adm T Mc M H) :
    HypF91 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H :=
  cx.hF H hH.hH (inf_le_of_adm h113 cx.c.hyp hH)

theorem exists_minimal_adm (h11 : StageLemma14111) (h : Hyp153 G T Mc M) :
    ∃ H : Subgroup G, Adm T Mc M H ∧ ∀ H' : Subgroup G, Adm T Mc M H' → H' ≤ H → H' = H := by
  obtain ⟨H, hH, hmin⟩ := (wellFounded_lt (α := Subgroup G)).has_min {H | Adm T Mc M H}
    ⟨Mc, adm_mc h11 h⟩
  refine ⟨H, hH, fun H' hH' hle => ?_⟩
  by_contra hne
  exact hmin H' hH' (lt_of_le_of_ne hle hne)

end S1549C

end CFSG.Quasithin
