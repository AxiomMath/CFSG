module

public import CFSG.Monster.AxisCount.HSCount
public import CFSG.Monster.B.Cbar.FourGroupBar
public import CFSG.Monster.B.Cbar.Simple
public import CFSG.Monster.B.TwoA.Census.CentralSqrt
public import CFSG.Monster.Existence.DLevelRank
public import CFSG.Monster.Existence.GMSBridge
public import CFSG.Monster.Existence.InvolutionClasses
public import CFSG.Monster.GMS.Defs
public import Certificates.Certificate3014
public import Certificates.Certificate3015
public import Certificates.Certificate3016
public import Certificates.Certificate3017
public import Certificates.Certificate3018
public import Certificates.Certificate3019
public import Certificates.Certificate3020
public import Certificates.Certificate3021
public import Certificates.Certificate3022
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3053
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate6006
public import Certificates.Certificate6007
public import Certificates.Certificate6009
public import Certificates.Certificate6010
public import Certificates.Certificate6011
public import Certificates.Certificate6012
public import Certificates.Certificate6013
public import Certificates.Certificate6014
public import Certificates.Certificate6015
public import Certificates.Certificate6016
public import Certificates.Certificate6017
public import Certificates.Certificate6018
public import Certificates.Certificate16018
public import Certificates.Certificate3024
public import Certificates.Certificate3027
public import Certificates.Certificate8955

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Tri

open CFSG.Monster CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.Existence CFSG.Monster.GMS CFSG.Blueprint

theorem commutator_eq_top_of_central_sqrt {Γ : Type*} [Group Γ] {t c : Γ} (Z : Subgroup Γ)
    [Z.Normal] (hZ : Z = Subgroup.zpowers t) (hc : c * c = t) (ht : t * t = 1)
    (htc : t ∈ Subgroup.center Γ) (hQ : commutator (Γ ⧸ Z) = ⊤) : commutator Γ = ⊤ := by
  have hmap : (commutator Γ).map (QuotientGroup.mk' Z) = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Z), ← commutator_def, hQ]
  set N := commutator Γ
  have hsup : N ⊔ Z = ⊤ := by
    rw [← QuotientGroup.ker_mk' Z, ← Subgroup.comap_map_eq, hmap, Subgroup.comap_top]
  have htN : t ∈ N := by
    have hc' : c ∈ N ⊔ Z := hsup ▸ Subgroup.mem_top c
    rw [Subgroup.mem_sup_of_normal_right] at hc'
    obtain ⟨n, hn, z, hz, hnz⟩ := hc'
    rw [hZ] at hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have hcomm : Commute n (t ^ k) :=
      (show Commute n t from Subgroup.mem_center_iff.1 htc n).zpow_right k
    have hzz : t ^ k * t ^ k = 1 := by
      rw [← (Commute.refl t).mul_zpow, ht, one_zpow]
    have : t = n * n := by
      calc t = c * c := hc.symm
        _ = (n * t ^ k) * (n * t ^ k) := by rw [hnz]
        _ = n * n * (t ^ k * t ^ k) := by
          rw [mul_assoc, ← mul_assoc (t ^ k), ← hcomm.eq, mul_assoc, mul_assoc]
        _ = n * n := by rw [hzz, mul_one]
    rw [this]
    exact N.mul_mem hn hn
  rw [eq_top_iff, ← hsup]
  exact sup_le le_rfl (hZ ▸ Subgroup.zpowers_le.2 htN)

theorem taubar_not_commute_xbar : taubar * xbar ≠ xbar * taubar := by
  intro h
  have h1 : taubar * xbar * taubar⁻¹ = xbar := by rw [h, mul_inv_cancel_right]
  rw [taubar_conj_xbar] at h1
  exact xbar_ne_ybar h1.symm

theorem commutator_Cbar :
    commutator Cbar = ⊤ := by
  have : IsSimpleGroup Cbar := short_centralizer_generated_quotient_simple.2.2.1
  have hn : (commutator Cbar).Normal := inferInstance
  rcases hn.eq_bot_or_eq_top with h | h
  · exfalso
    have hc := (commutator_eq_bot_iff_center_eq_top Cbar).1 h
    apply taubar_not_commute_xbar
    have hx : xbar ∈ Subgroup.center Cbar := hc ▸ Subgroup.mem_top _
    exact Subgroup.mem_center_iff.1 hx taubar
  · exact h

@[expose] noncomputable def cSqrtC :
    Cgen :=
  ⟨B.TwoA.Census.cSqrt, Jstar_le_Cgen B.TwoA.Census.cSqrt_mem_Jstar⟩

theorem cSqrtC_sq :
    cSqrtC * cSqrtC = tStarC := Subtype.ext B.TwoA.Census.cSqrt_sq

theorem commutator_Cgen :
    commutator Cgen = ⊤ :=
  commutator_eq_top_of_central_sqrt Zstar rfl cSqrtC_sq (Subtype.ext tStar_mul_self)
    tStarC_mem_center commutator_Cbar

theorem orderOf_tGmat : orderOf tGmat = 2 := by
  rw [tGmat, Subgroup.orderOf_mk]
  exact orderOf_tStar

theorem map_cent_tGmat :
    (cent tGmat).map Gmat.subtype = Cgen := by
  rw [← AxisCount.HS.centralizer_tStar_eq_Cgen]
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨h.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hh)
  · rintro ⟨hg, hc⟩
    refine ⟨⟨g, hg⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hc)

@[expose] noncomputable def centEquivCgen :
    cent tGmat ≃* Cgen :=
  ((cent tGmat).equivMapOfInjective Gmat.subtype Gmat.subtype_injective).trans
    (MulEquiv.subgroupCongr map_cent_tGmat)

theorem centEquivCgen_self :
    centEquivCgen ⟨tGmat, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ = tStarC := rfl

@[expose] noncomputable def centToCbar :
    cent tGmat →* Cbar :=
  kappa.comp centEquivCgen.toMonoidHom

theorem centToCbar_surjective :
    Function.Surjective centToCbar :=
  kappa_surjective.comp centEquivCgen.surjective

theorem map_ker_centToCbar :
    centToCbar.ker.map (cent tGmat).subtype = Subgroup.zpowers tGmat := by
  have h : centToCbar.ker = Subgroup.zpowers
      (⟨tGmat, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ : cent tGmat) := by
    ext x
    rw [MonoidHom.mem_ker]
    change kappa (centEquivCgen x) = 1 ↔ _
    rw [← MonoidHom.mem_ker, ker_kappa, Zstar, ← centEquivCgen_self]
    simp only [Subgroup.mem_zpowers_iff, ← map_zpow, EmbeddingLike.apply_eq_iff_eq]
  rw [h, MonoidHom.map_zpowers]
  rfl

theorem gmsF2Type_Cbar :
    GMSF2Type (phiB Existence.uBar) Cbar :=
  ⟨short_centralizer_generated_quotient_simple.2.2.1, Existence.uBar, orderOf_uBar,
    ⟨@Existence.centralizerMulEquiv Cbar NativeSporadic.B _ Units.instGroup phiB
      Existence.uBar⟩⟩

theorem gmsDoubleF2Centralizer_tGmat :
    GMSDoubleF2Centralizer (phiB Existence.uBar) tGmat := by
  have : Group.IsPerfect Cgen := Group.isPerfect_def.2 commutator_Cgen
  refine ⟨orderOf_tGmat, ?_, Cbar, inferInstance, centToCbar, centToCbar_surjective,
    map_ker_centToCbar, gmsF2Type_Cbar⟩
  exact (Group.IsPerfect.ofSurjective (f := centEquivCgen.symm.toMonoidHom)
    centEquivCgen.symm.surjective).commutator_eq_top

theorem xmat_mem_Gmat : xmat ∈ Gmat := Hmat_le_Gmat (Qmat_le_Hmat xmat_mem_Qmat)

theorem gmsF1Type_Gmat :
    GMSF1Type (phiB Existence.uBar) (⟨tStar, tStar_mem_Gmat⟩ : Gmat)
      (⟨xmat, xmat_mem_Gmat⟩ : Gmat) :=
  ⟨gmsDoubleF2Centralizer_tGmat, gmsLeechCentralizer_xGmat⟩

end CFSG.Monster.Tri
