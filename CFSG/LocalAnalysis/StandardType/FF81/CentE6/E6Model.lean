module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoModel
public import CFSG.LocalAnalysis.SeitzReduction.EPilotCentralizerHigh
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviHom
public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.RadSetting
public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.E6Module
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClasses
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour

public section

namespace CFSG.StandardType.FF81.CentE6

open scoped MatrixGroups
open CFSG CFSG.Open CFSG.SeitzReduction CFSG.StandardType.GGSixE6Two CFSG.StandardType.GGHalf
open CFSG.Timmesfeld.LieEmbed
open CFSG.RankThree.GF2n.Smith81
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem a5Root_two_one :
    a5Root (2 : Fin 6) (1 : Fin 6) = -a5Root (1 : Fin 6) (2 : Fin 6) := by
  decide +kernel

private noncomputable def weylRepElt
    (w : WeylGroup .E6) : EC :=
  ⟨canonicalRep (coxeterSystem .E6) F2 w,
    canonicalRep_mem_adjointGroup (coxeterSystem .E6) F2 w⟩

private theorem weylRepElt_conj
    (w : WeylGroup .E6) {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) :
    weylRepElt w * xr α * (weylRepElt w)⁻¹ = xr (w • α) := by
  apply Subtype.ext
  show canonicalRep (coxeterSystem .E6) F2 w * pinnedX .E6 F2 α 1 *
      (canonicalRep (coxeterSystem .E6) F2 w)⁻¹ = pinnedX .E6 F2 (w • α) 1
  exact E6Pilot.canonicalRep_mul_pinnedX_mul_inv_of_charTwo w hα 1

theorem exists_radGeom_model :
    ∃ (eL : ↥lE ≃* SL(6, ZMod 2))
      (π : ↥(EPilot.highRadical .E6 F2) →* Multiplicative (A5Cube.Cube (ZMod 2))),
      RadGeom (xr (highRoot .E6)) (EPilot.highRadical .E6 F2) lE eL π (eL.symm bStd : EC) ∧
      EPilot.highRadical .E6 F2 ⊔ lE = Subgroup.centralizer ({xr (highRoot .E6)} : Set EC) ∧
      ∃ c : EC, c * zE * c⁻¹ = (eL.symm bStd : EC) := by
  obtain ⟨eL, π, heL, hsurj, hker, hequiv⟩ := exists_radModule
  obtain ⟨hQ, hsup, hinf, hnorm⟩ :=
    EPilot.isTwoRadicalDecomp_highRoot (τ := .E6) (K := F2) (Or.inl rfl) (c := 1) one_ne_zero
  have hlE : lE = EPilot.perpLevi .E6 F2 := rfl
  have hsup' : EPilot.highRadical .E6 F2 ⊔ lE =
      Subgroup.centralizer ({xr (highRoot .E6)} : Set EC) := by
    rw [hlE]
    simpa [xr, EPilot.pinnedElt] using hsup
  have ht_mem : xr (highRoot .E6) ∈ EPilot.highRadical .E6 F2 := by
    have hθ : highRoot .E6 ∈ parabolicRadicalRoots .E6 (EPilot.perpNodes .E6) :=
      (EPilot.mem_parabolicRadicalRoots_perpNodes_iff_iform (Or.inl rfl)).2
        ⟨isRoot_highRoot _, iform_self_pos_of_isRoot (isRoot_highRoot _)⟩
    exact Subgroup.mem_subgroupOf.2 (pinnedX_mem_rootSpan hθ 1)
  have ht_mul_self : xr (highRoot .E6) * xr (highRoot .E6) = 1 := by
    apply Subtype.ext
    change pinnedX .E6 F2 (highRoot .E6) 1 * pinnedX .E6 F2 (highRoot .E6) 1 = 1
    rw [← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]
  have ht_ne_one : xr (highRoot .E6) ≠ 1 := by
    intro h
    have h2 : ((xr (highRoot .E6) : EC) : ModGL .E6 F2) = ((1 : EC) : ModGL .E6 F2) :=
      congrArg Subtype.val h
    have h3 : pinnedX .E6 F2 (highRoot .E6) (1 : F2) =
        pinnedX .E6 F2 (highRoot .E6) 0 := by
      rw [pinnedX_zero]
      exact h2
    exact one_ne_zero (pinnedX_injective (τ := .E6) (R := F2) (highRoot .E6) h3)
  have hb_eq : (eL.symm bStd : EC) = xr (a5Root 1 2) * xr (a5Root 2 1) := by
    obtain ⟨h12mem, h12eq⟩ := heL 1 2 (by decide)
    obtain ⟨h21mem, h21eq⟩ := heL 2 1 (by decide)
    have hsymm12 : eL.symm (elem 1 2) = (⟨xr (a5Root 1 2), h12mem⟩ : ↥lE) := by
      rw [← h12eq, eL.symm_apply_apply]
    have hsymm21 : eL.symm (elem 2 1) = (⟨xr (a5Root 2 1), h21mem⟩ : ↥lE) := by
      rw [← h21eq, eL.symm_apply_apply]
    rw [bStd, map_mul, Subgroup.coe_mul, hsymm12, hsymm21]
  obtain ⟨w, hw⟩ := EPilot.exists_smul_highRoot_eq (τ := .E6) (Or.inl rfl)
    (isRoot_a5Root (show (1 : Fin 6) ≠ 2 by decide))
  have hwneg : w • (-highRoot .E6) = a5Root 2 1 := by
    rw [smul_neg, hw, ← a5Root_two_one]
  have hcθ : weylRepElt w * xr (highRoot .E6) * (weylRepElt w)⁻¹ = xr (a5Root 1 2) := by
    rw [weylRepElt_conj w (isRoot_highRoot .E6), hw]
  have hcnegθ : weylRepElt w * xr (-highRoot .E6) * (weylRepElt w)⁻¹ = xr (a5Root 2 1) := by
    rw [weylRepElt_conj w (IsRoot.neg (isRoot_highRoot .E6)), hwneg]
  have hconj : weylRepElt w * zE * (weylRepElt w)⁻¹ = (eL.symm bStd : EC) := by
    rw [hb_eq]
    calc weylRepElt w * zE * (weylRepElt w)⁻¹
        = (weylRepElt w * xr (highRoot .E6) * (weylRepElt w)⁻¹) *
          (weylRepElt w * xr (-highRoot .E6) * (weylRepElt w)⁻¹) := by
            rw [zE]; group
      _ = xr (a5Root 1 2) * xr (a5Root 2 1) := by rw [hcθ, hcnegθ]
  refine ⟨eL, π, ?_, hsup', ?_⟩
  · refine ⟨ht_mul_self, ht_ne_one, ht_mem, hQ, ?_, ?_, ?_, ?_, hsurj, hker, hequiv, ?_, ?_⟩
    · exact le_trans le_sup_left (le_of_eq hsup')
    · exact le_trans le_sup_right (le_of_eq hsup')
    · intro l hl q hq
      have hl' : l ∈ EPilot.perpLevi .E6 F2 := by rw [hlE] at hl; exact hl
      exact (Subgroup.mem_normalizer_iff.mp (hnorm hl') q).mp hq
    · rw [hlE, inf_comm]; exact hinf
    · exact (eL.symm bStd).2
    · change eL (eL.symm bStd) = bStd
      exact eL.apply_symm_apply bStd
  · exact ⟨weylRepElt w, hconj⟩

end CFSG.StandardType.FF81.CentE6
