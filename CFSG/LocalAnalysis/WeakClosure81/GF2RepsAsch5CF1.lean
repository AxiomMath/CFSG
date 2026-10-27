module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CFa
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CFb
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CFc

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
  (OInf BarInf uc22p20bSimpSec uc22p20bCj uc22p20b_simpSec_of_cf uc22p20b_simpSec_restrict
    uc22p20b_simpSec_of_surjective uc22p20b_simpSec_comm)

theorem cfShape_of_isComponentModN {Q : Type} [Group Q] [Finite Q] {H T L : Subgroup Q}
    {P : ∀ (X : Type) [Group X], Prop} (hP : IsoInvPred P)
    (hL : IsComponentModN (OInf H) H L) (hLT : L ⊔ T = H) (hT : IsPGroup 2 T)
    (hLP : HasQuotShape L (OInf H : Set Q) P) : CFShape ↥H P := by
  obtain ⟨C, hC, hCL, hCN⟩ := exists_cComp_of_isComponentModN hL
  obtain ⟨X, hXg, hPX, ⟨eX⟩⟩ := exists_mulEquiv_barInf_of_hasQuotShape hC hCL hCN hLP
  have hOI : OInf H = solvRad H := (solvRad_eq_map_solvableRadical H).symm
  have hTH : T ≤ H := hLT ▸ le_sup_right
  have hCH : C ≤ H := le_of_mem_cComp hC
  have hNH : OInf H ≤ H := hOI ▸ solvRad_le H
  haveI : Group.IsSolvable ↥T := by
    haveI := hT.isNilpotent
    infer_instance
  have hNsolv : Group.IsSolvable ↥(OInf H) := by
    have h := solvRad_isSolvable H
    rwa [← hOI] at h
  have hN : ((OInf H).subgroupOf H).Normal := hL.1
  have hNs : Group.IsSolvable ↥((OInf H).subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hNH).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNH).injective
  have hnormN : H ≤ normalizer (OInf H : Set Q) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mp hN
  have hCTH : C ⊔ T ≤ H := sup_le hCH hTH
  have hHeq : (C ⊔ T) ⊔ OInf H = H := by
    rw [sup_right_comm, hCN, hLT]
  intro Λ _ hcf hnc
  have h1 : uc22p20bSimpSec ↥H Λ := uc22p20b_simpSec_of_cf hcf
  haveI := hN
  rcases uc22p20b_simpSec_restrict ((OInf H).subgroupOf H) h1 with h2 | h2
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (uc22p20b_simpSec_comm h2 a b)
  · have hsurj : Function.Surjective
        ((QuotientGroup.mk' ((OInf H).subgroupOf H)).comp (Subgroup.inclusion hCTH)) := by
      intro q
      obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective ((OInf H).subgroupOf H) q
      have hx' : x ∈ (((C ⊔ T) ⊔ OInf H : Subgroup Q) : Set Q) := by
        rw [hHeq]
        exact hx
      rw [Subgroup.coe_mul_of_left_le_normalizer_right (C ⊔ T) (OInf H)
        ((hCTH).trans hnormN)] at hx'
      obtain ⟨a, ha, n, hn, rfl⟩ := hx'
      refine ⟨⟨a, ha⟩, ?_⟩
      simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using hn
    have h3 : uc22p20bSimpSec ↥(C ⊔ T) Λ := uc22p20b_simpSec_of_surjective _ hsurj h2
    obtain ⟨t, ht, ⟨e1⟩⟩ := exists_conj_barInf_of_simpSec hC hTH inferInstance hnc h3
    obtain ⟨e2⟩ := nonempty_mulEquiv_barInf_conj t C
    exact hP X Λ ⟨eX.symm.trans (e2.symm.trans e1)⟩ hPX

end CFSG.LocalAnalysis.WeakClosure81
