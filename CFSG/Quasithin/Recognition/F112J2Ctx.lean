module

public import CFSG.Quasithin.Recognition.F112J2Setup
public import CFSG.Quasithin.Recognition.F112J2Reduce
public import CFSG.Quasithin.Recognition.F112WLocal2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F112W CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace F112J2

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem hyp111R_of_setting (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs) :
    Hyp111R K1 L2 S :=
  Hyp111R.of_hyp111 hRO h.hyp

theorem S_le_centralizer_Z (h : R1SettingLegacyBare K1 L2 S Zs) :
    S ≤ Subgroup.centralizer (Zs : Set G) :=
  Subgroup.le_centralizer_iff.mp h.Z_cent_S

theorem zs_le_omegaOneCenter (h : R1SettingLegacyBare K1 L2 S Zs) : Zs ≤ quasithinOmegaOneCenter S := by
  intro z hz
  apply Subgroup.subset_closure
  have hO2 : pCoreOf 2 L2 ≤ S :=
    (isSylowTwoOf_pCoreOf_le h.hyp.h2.sylow).trans inf_le_left
  refine ⟨⟨hO2 (h.Z_le hz), h.Z_cent_S hz⟩, ?_⟩
  have h1 : (⟨z, hz⟩ : ↥Zs) ^ Nat.card ↥Zs = 1 := pow_card_eq_one'
  rw [h.card_Z] at h1
  simpa using congrArg Subtype.val h1

theorem amalgamHypV_of_setting (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs) :
    AmalgamHypV (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) S (conjClosure Zs L2) := by
  have := amalgamHypV_thesis (hyp111R_of_setting hRO h) (zs_le_omegaOneCenter h) h.s3
    h.Z_not_norm
  rwa [conjClosure_sup_S h.hyp.h2.normalizes (S_le_centralizer_Z h)] at this

theorem isNaturalS3_of_setting (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs) :
    IsNaturalS3 (L2 ⊔ S) (conjClosure Zs L2) := by
  have hc := conjClosure_sup_S h.hyp.h2.normalizes (S_le_centralizer_Z h)
  have := isNaturalS3_thesis (hyp111R_of_setting hRO h) (zs_le_omegaOneCenter h) h.s3
    h.Z_not_norm (by rw [hc]; exact h.V_card)
  rwa [hc] at this

theorem V_ne_bot (h : R1SettingLegacyBare K1 L2 S Zs) : conjClosure Zs L2 ≠ ⊥ := by
  intro hV
  have := h.V_card
  rw [hV, Subgroup.card_bot] at this
  omega

theorem two_le_critDist_of_setting (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs) :
    2 ≤ critDist (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) (conjClosure Zs L2) :=
  two_le_critDist_of_le_pCoreOf (amalgamHypV_of_setting hRO h) (V_ne_bot h) h.V_le

theorem critDist_eq_two_of_setting (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs)
    (hna : ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥) :
    critDist (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) (conjClosure Zs L2) = 2 :=
  critDist_eq_two_of_commutator_ne_bot (amalgamHypV_of_setting hRO h) (V_ne_bot h) h.V_le hna

end F112J2

end CFSG.Quasithin
