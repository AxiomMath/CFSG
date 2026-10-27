module

public import CFSG.Quasithin.Background.SimsF5Asm
public import CFSG.Quasithin.Background.SimsF5Model7
public import CFSG.Quasithin.Background.SimsF5USTransport

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open scoped Pointwise
open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF CFSG.Quasithin.H13.F431.U42Aut
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

theorem a7_M0Dot_le_MDot : M0Dot ≤ MDot := inf_le_left

theorem a7_M1Dot_le_MDot : M1Dot ≤ MDot := inf_le_left

theorem a7_M2Dot_le_MDot : M2Dot ≤ MDot := inf_le_left


theorem model_hsup : MulAction.stabilizer ↥MDot xDot ⊔ HDot = ⊤ := by
  obtain ⟨R, hR, hTR⟩ := exists_R modelCtx
  obtain ⟨-, -, -, h56⟩ := autCtx_conf modelCtx hR hTR
  have hinj := MDot.subtype_injective
  have hf : ((modelCtx.iso.toG fhB : ↥MDot) : GL6) = fDot := by
    rw [modelCtx_toG]
    exact lamA_fhatA
  have hA : (aOf (M2Dot.subgroupOf MDot) (modelCtx.iso.toG fhB)).map MDot.subtype = ADot M2Dot := by
    rw [aOf, ← br_pCoreOf_map hinj, tr_map_inf hinj, cenOf, tr_map_centralizer_singleton hinj,
      MDot.range_subtype, Subgroup.subtype_apply, hf, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 a7_M2Dot_le_MDot, ← inf_assoc,
      inf_eq_left.2 a7_M2Dot_le_MDot]
    rfl
  have h1 : (MulAction.stabilizer ↥MDot xDot ⊔ HDot).map MDot.subtype =
      M0Dot ⊔ (MDot ⊓ MulAction.stabilizer GL6 V3plus) := by
    rw [Subgroup.map_sup, stabilizer_xDot, HDot, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.2 a7_M0Dot_le_MDot,
      inf_eq_left.2 (inf_le_left : MDot ⊓ MulAction.stabilizer GL6 V3plus ≤ MDot)]
  have h2 : ((M1Dot.subgroupOf MDot ⊔ M2Dot.subgroupOf MDot) ⊔
      Subgroup.normalizer (aOf (M2Dot.subgroupOf MDot) (modelCtx.iso.toG fhB) : Set ↥MDot)).map
        MDot.subtype = M0Dot ⊔ (MDot ⊓ MulAction.stabilizer GL6 V3plus) := by
    rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, tr_map_normalizer hinj, MDot.range_subtype, hA,
      ← f57Model.2.2.2.2, inf_eq_left.2 a7_M1Dot_le_MDot,
      inf_eq_left.2 a7_M2Dot_le_MDot, M1Dot_sup_M2Dot]
  rw [← h56]
  apply Subgroup.map_injective hinj
  rw [h1, h2]

theorem f57 : F57 := by
  refine ⟨f57Model, ?_⟩
  intro E _ Gp M₁ M₂ Y _ β M _ ε z Tb fb R h hR r hr hrT
  obtain ⟨Θ, zb, Φ, hz, hC, hμ, hΦ⟩ := exists_std h
  have hinj := psiOf_injective Φ
  have hM0 := tr_M0Of hμ.1 hΦ
  set e : ↥(M0Of β ε) ≃* ↥M0Dot :=
    ((M0Of β ε).equivMapOfInjective (psiOf Φ) hinj).trans (MulEquiv.subgroupCongr hM0) with he
  have he_apply : ∀ x : ↥(M0Of β ε), ((e x : ↥M0Dot) : GL6) = psiOf Φ x := fun x => rfl
  have hσ : ∀ g0 : ↥M0Dot, psiOf Φ ((e.symm g0 : ↥(M0Of β ε)) : M) = g0 := fun g0 => by
    rw [← he_apply, MulEquiv.apply_symm_apply]
  have hmem0 : ∀ g : M, g ∈ M0Of β ε ↔ ((Φ g : ↥MDot) : GL6) ∈ M0Dot := fun g => by
    rw [← hM0, ← psiOf_apply, tr_mem_map_iff hinj]
  have hHDot : ∀ g : ↥MDot, g ∈ HDot ↔
      (g : GL6) ∈ MDot ⊓ Subgroup.normalizer ((ADot M2Dot : Subgroup GL6) : Set GL6) := by
    intro g
    rw [← f57Model.2.2.2.2]
    exact Subgroup.mem_subgroupOf
  have hmemH : ∀ g : M, g ∈ HOf β ε fb ↔ Φ g ∈ HDot := fun g => by
    rw [hHDot, ← tr_HOf hμ.1 hΦ, ← psiOf_apply, tr_mem_map_iff hinj]
  obtain ⟨-, hRM0, -⟩ := R_facts h hR
  have hRcond : ∀ r' ∈ R, r' ∉ TfOf β ε Tb fb →
      ((Φ r' : ↥MDot) : GL6) * fDot = fDot * ((Φ r' : ↥MDot) : GL6) ∧
        ((Φ r' : ↥MDot) : GL6) ∉ M0Dot := by
    intro r' hr' hr'T
    refine ⟨?_, fun h0 => hr'T (hRM0 ⟨hr', (hmem0 r').2 h0⟩)⟩
    have hc' : psiOf Φ r' ∈ (Subgroup.centralizer ({fOf β ε fb} : Set M)).map (psiOf Φ) :=
      ⟨r', hR.1.1 hr', rfl⟩
    rw [tr_cen_f hμ.1 hΦ] at hc'
    exact Subgroup.mem_centralizer_singleton_iff.1 hc'.2
  obtain ⟨hfaith, hUS, β', ζ, hβ', hζ, hstab, hequiv⟩ :=
    us_transport Φ hmem0 hmemH hRcond hr hrT stabilizer_xDot
      (fun g hg hg0 => smul_xDot_of_cen hg hg0) (fun P hP => exists_M0Dot_smul_yDot hP)
      faithfulSMul_PtX (isUniquenessSystem_model model_hsup)
  refine ⟨muOfIso Θ h.f431.amalgam.gen, zb, hz, hμ, e.symm, ⟨?_, ?_, ?_⟩, ζ, ⟨?_, hstab⟩,
    ⟨hfaith, hUS⟩, ⟨faithfulSMul_PtX, isUniquenessSystem_model model_hsup⟩, β', ?_, hequiv⟩
  · intro a
    apply hinj
    rw [hσ]
    exact (tr_phi1 hΦ a).symm
  · intro a
    apply hinj
    rw [hσ]
    exact (tr_phi2 hΦ a).symm
  · intro a
    apply hinj
    rw [hσ]
    exact (tr_bM hΦ a).symm
  · intro g g0 hg
    apply hinj
    rw [hσ, hζ, psiOf_apply, MulEquiv.apply_symm_apply]
    exact hg
  · intro g g0 hg
    apply hinj
    rw [hσ, hβ', psiOf_apply, MulEquiv.apply_symm_apply]
    exact hg

end CFSG.Quasithin.SimsF5
