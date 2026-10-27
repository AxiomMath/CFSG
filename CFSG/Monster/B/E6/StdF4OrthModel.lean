module

public import CFSG.Monster.B.E6.StdF4Cells
public import CFSG.Monster.B.E6.StdF4ResModel
public import CFSG.Monster.B.Geometry.OrthResidue
public import CFSG.LieType.Chevalley.C2E6FourthResiduePanels

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4

open Module CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FourthResidue
open CFSG.LieType.Chevalley.C2E6Overlap (K)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def phiO : V0 ≃ₗ[ZMod 2] OV where
  toFun v := ![v.1 (.inl 0), v.1 (.inl 1), v.1 (.inl 2), v.1 (.inr 0), v.1 (.inr 1),
    v.1 (.inr 2), v.2 0, v.2 1]
  invFun w := (Sum.elim ![w 0, w 1, w 2] ![w 3, w 4, w 5], ![w 6, w 7])
  map_add' v w := by funext i; fin_cases i <;> rfl
  map_smul' c v := by funext i; fin_cases i <;> rfl
  left_inv v := by
    refine Prod.ext (funext fun c => ?_) (funext fun i => ?_)
    · rcases c with i | i <;> fin_cases i <;> rfl
    · fin_cases i <;> rfl
  right_inv w := by funext i; fin_cases i <;> rfl

theorem phiO_apply (v : V0) :
    phiO v = ![v.1 (.inl 0), v.1 (.inl 1), v.1 (.inl 2), v.1 (.inr 0), v.1 (.inr 1),
      v.1 (.inr 2), v.2 0, v.2 1] := rfl

theorem oQ_phiO (v : V0) : oQ (phiO v) = Qminus v := by
  rw [oQ_apply, Qminus_apply, Fin.sum_univ_three, phiO_apply]
  simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

@[expose] def flagO (W : singularFlags Qminus 3) : PFlag OData where
  V₁ := (W.1 0).map (phiO : V0 →ₗ[ZMod 2] OV)
  V₂ := (W.1 1).map (phiO : V0 →ₗ[ZMod 2] OV)
  V₃ := (W.1 2).map (phiO : V0 →ₗ[ZMod 2] OV)
  finrank₁ := by rw [LinearEquiv.finrank_map_eq]; exact W.2.1 0
  finrank₂ := by rw [LinearEquiv.finrank_map_eq]; exact W.2.1 1
  finrank₃ := by rw [LinearEquiv.finrank_map_eq]; exact W.2.1 2
  le₁₂ := Submodule.map_mono (W.2.2.1 (by decide : (0 : Fin 3) ≤ 1))
  le₂₃ := Submodule.map_mono (W.2.2.1 (by decide : (1 : Fin 3) ≤ 2))
  isTI v hv := by
    obtain ⟨u, hu, rfl⟩ := hv
    change oQ (phiO u) = 0
    rw [oQ_phiO]
    exact W.2.2.2 2 u hu

@[expose] def unflagSub (x : PFlag OData) : Fin 3 → Submodule (ZMod 2) V0 :=
  ![x.V₁.map (phiO.symm : OV →ₗ[ZMod 2] V0), x.V₂.map (phiO.symm : OV →ₗ[ZMod 2] V0),
    x.V₃.map (phiO.symm : OV →ₗ[ZMod 2] V0)]

theorem fin3_cases : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide

theorem unflagSub_mem (x : PFlag OData) : unflagSub x ∈ singularFlags Qminus 3 := by
  refine ⟨fun k => ?_, fun a b hab => ?_, fun k v hv => ?_⟩
  · rcases fin3_cases k with rfl | rfl | rfl
    · exact (LinearEquiv.finrank_map_eq _ _).trans x.finrank₁
    · exact (LinearEquiv.finrank_map_eq _ _).trans x.finrank₂
    · exact (LinearEquiv.finrank_map_eq _ _).trans x.finrank₃
  · have h12 := Submodule.map_mono (f := (phiO.symm : OV →ₗ[ZMod 2] V0)) x.le₁₂
    have h23 := Submodule.map_mono (f := (phiO.symm : OV →ₗ[ZMod 2] V0)) x.le₂₃
    rcases fin3_cases a with rfl | rfl | rfl <;> rcases fin3_cases b with rfl | rfl | rfl
    all_goals first
      | exact le_rfl
      | exact absurd hab (by decide)
      | exact h12
      | exact h23
      | exact h12.trans h23
  · have hv3 : v ∈ x.V₃.map (phiO.symm : OV →ₗ[ZMod 2] V0) := by
      rcases fin3_cases k with rfl | rfl | rfl
      · exact Submodule.map_mono (x.le₁₂.trans x.le₂₃) hv
      · exact Submodule.map_mono x.le₂₃ hv
      · exact hv
    obtain ⟨w, hw, rfl⟩ := hv3
    rw [← oQ_phiO]
    change oQ (phiO (phiO.symm w)) = 0
    rw [LinearEquiv.apply_symm_apply]
    exact x.isTI w hw

theorem map_phiO_map_symm (U : Submodule (ZMod 2) OV) :
    (U.map (phiO.symm : OV →ₗ[ZMod 2] V0)).map (phiO : V0 →ₗ[ZMod 2] OV) = U := by
  ext v
  simp only [Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    rwa [LinearEquiv.apply_symm_apply]
  · intro hv
    exact ⟨phiO.symm v, ⟨v, hv, rfl⟩, LinearEquiv.apply_symm_apply _ _⟩

theorem map_symm_map_phiO (U : Submodule (ZMod 2) V0) :
    (U.map (phiO : V0 →ₗ[ZMod 2] OV)).map (phiO.symm : OV →ₗ[ZMod 2] V0) = U := by
  ext v
  simp only [Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    rwa [LinearEquiv.symm_apply_apply]
  · intro hv
    exact ⟨phiO v, ⟨v, hv, rfl⟩, LinearEquiv.symm_apply_apply _ _⟩

@[expose] def flagEquivO : singularFlags Qminus 3 ≃ PFlag OData where
  toFun := flagO
  invFun x := ⟨unflagSub x, unflagSub_mem x⟩
  left_inv W := by
    refine Subtype.ext (funext fun k => ?_)
    rcases fin3_cases k with rfl | rfl | rfl <;> exact map_symm_map_phiO _
  right_inv x := PFlag.ext (map_phiO_map_symm _) (map_phiO_map_symm _) (map_phiO_map_symm _)

theorem flagEquivO_apply (W : singularFlags Qminus 3) : flagEquivO W = flagO W := rfl

theorem flagO_sub_eq_iff (W W' : singularFlags Qminus 3) (k : Fin 3) :
    (W.1 k).map (phiO : V0 →ₗ[ZMod 2] OV) = (W'.1 k).map (phiO : V0 →ₗ[ZMod 2] OV) ↔
      W.1 k = W'.1 k :=
  ⟨fun h => by rw [← map_symm_map_phiO (W.1 k), h, map_symm_map_phiO], fun h => by rw [h]⟩

theorem phiO_hypVec_inl (j : Fin 3) :
    phiO (hypVec (ZMod 2) (Fin 2 → ZMod 2) (.inl j)) = Pi.single (Fin.castLE (by omega) j) 1 := by
  funext i
  fin_cases j <;> fin_cases i <;> rfl

theorem map_baseFlag (k : Fin 3) :
    (baseFlag k).map (phiO : V0 →ₗ[ZMod 2] OV) =
      cspan (ZMod 2) ((Finset.univ.filter fun j : Fin 3 => j ≤ k).map
        ⟨Fin.castLE (by omega), Fin.castLE_injective _⟩) := by
  rw [baseFlag_eq_span, Submodule.map_span, cspan, Set.image_image]
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_ofPred_eq, LinearEquiv.coe_coe, phiO_hypVec_inl,
    Finset.coe_map, Function.Embedding.coeFn_mk, Finset.coe_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨_, ⟨j, hj, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨j, hj, rfl⟩

theorem flagO_baseFlag : flagO ⟨baseFlag, baseFlag_mem⟩ = oC0 := by
  refine PFlag.ext ?_ ?_ ?_
  · exact (map_baseFlag 0).trans (congrArg (cspan (ZMod 2)) (by decide))
  · exact (map_baseFlag 1).trans (congrArg (cspan (ZMod 2)) (by decide))
  · exact (map_baseFlag 2).trans (congrArg (cspan (ZMod 2)) (by decide))

theorem stdDistance_eq_simple_iff
    (g h : stdGroup) (i : Fin 4) :
    stdDistance (g : stdChamber) (h : stdChamber) = ncs.simple i ↔
      (g : stdChamber) ≠ (h : stdChamber) ∧
        ((g⁻¹ * h : stdGroup) : ModGL Tag.E6 K) ∈ nativeParabolic {i} := by
  rw [← Subgroup.mem_subgroupOf, mem_parabolicG_iff, ← stdDistance_mk_mk,
    mem_parabolic_singleton_iff]
  constructor
  · intro e
    refine ⟨fun e' => ncs.simple_ne_one i ?_, Or.inr e⟩
    rw [← e, e']
    exact (hδ.eq_one_iff _ _).2 rfl
  · rintro ⟨hne, h1 | h1⟩
    · exact absurd ((hδ.eq_one_iff _ _).1 h1) hne
    · exact h1

abbrev ResK :
    Type := residue ncs stdDistance FourthResidue.fourthJ c₀

@[expose] def cosetEquivK :
    ParabolicCosets FourthResidue.fourthJ ≃ ResK :=
  (Equiv.ofInjective _ (chamberOf_injective FourthResidue.fourthJ)).trans
    (Set.equivOfEq (range_chamberOf FourthResidue.fourthJ))

theorem coe_cosetEquivK_mk
    (p : nativeParabolic FourthResidue.fourthJ) :
    (cosetEquivK (QuotientGroup.mk p) : stdChamber) =
      ((⟨p, nativeParabolic_le_stdGroup _ p.2⟩ : stdGroup) : stdChamber) := rfl

@[expose] def modelO
    (y : ResK) : PFlag OData :=
  flagEquivO (FourthResidue.residueFlag (cosetEquivK.symm y))

theorem modelO_bijective :
    Function.Bijective modelO :=
  (flagEquivO.bijective.comp FourthResidue.residueFlag.bijective).comp cosetEquivK.symm.bijective

theorem c₀_mem_ResK :

    c₀ ∈ residue ncs stdDistance FourthResidue.fourthJ c₀ := self_mem_residue _ _

theorem modelO_c₀ :
    modelO ⟨c₀, c₀_mem_ResK⟩ = oC0 := by
  have e : cosetEquivK.symm ⟨c₀, c₀_mem_ResK⟩ = QuotientGroup.mk 1 := by
    rw [Equiv.symm_apply_eq]
    exact Subtype.ext rfl
  rw [modelO, e, flagEquivO_apply]
  convert flagO_baseFlag using 2
  exact Subtype.ext FourthResidue.residueFlag_one

theorem resDist_eq_simple_iff
    (p q : nativeParabolic FourthResidue.fourthJ) (i : Fin 4) :
    resDist ncs stdDistance FourthResidue.fourthJ c₀ (cosetEquivK (QuotientGroup.mk p))
        (cosetEquivK (QuotientGroup.mk q)) = ncs.simple i ↔
      cosetEquivK (QuotientGroup.mk p) ≠ cosetEquivK (QuotientGroup.mk q) ∧
        ((p⁻¹ * q : nativeParabolic FourthResidue.fourthJ) : ModGL Tag.E6 K) ∈
          nativeParabolic {i} := by
  rw [resDist, coe_cosetEquivK_mk, coe_cosetEquivK_mk, stdDistance_eq_simple_iff]
  refine and_congr (not_congr ?_) Iff.rfl
  rw [Subtype.ext_iff, coe_cosetEquivK_mk, coe_cosetEquivK_mk]

theorem not_resDistK_eq_simple_three
    (y z : ResK) :
    resDist ncs stdDistance FourthResidue.fourthJ c₀ y z ≠ ncs.simple 3 := by
  intro h
  have hmem := mem_parabolic_of_mem_residue hδ y.2 z.2
  rw [show stdDistance y.1 z.1 = ncs.simple 3 from h, simple_mem_parabolic_iff] at hmem
  rcases hmem with h0 | h1 | h2
  · exact absurd h0 (by decide)
  · exact absurd h1 (by decide)
  · exact absurd h2 (by decide)

theorem isChamberModel_modelO :
    IsChamberModel ncs (resDist ncs stdDistance FourthResidue.fourthJ c₀)
      (polarChamber OData 0 1 2) modelO := by
  refine ⟨modelO_bijective, fun y z i => ?_⟩
  obtain ⟨y, rfl⟩ := cosetEquivK.surjective y
  obtain ⟨z, rfl⟩ := cosetEquivK.surjective z
  induction y using QuotientGroup.induction_on with | H p => ?_
  induction z using QuotientGroup.induction_on with | H q => ?_
  have hm : ∀ p : nativeParabolic FourthResidue.fourthJ,
      modelO (cosetEquivK (QuotientGroup.mk p)) =
        flagO (FourthResidue.residueFlag (QuotientGroup.mk p)) := fun p => by
    rw [modelO, Equiv.symm_apply_apply]
    rfl
  rw [resDist_eq_simple_iff, hm, hm]
  rcases fin4_cases i with rfl | rfl | rfl | rfl
  · rw [polarChamber_adj_p, show (0 : Fin 4) = (0 : Fin 3).castSucc from rfl,
      FourthResidue.mem_nativeParabolic_singleton_iff]
    refine and_congr_right fun _ => ?_
    simp only [flagO, flagO_sub_eq_iff]
    constructor
    · intro h
      exact ⟨h 1 (by decide), h 2 (by decide)⟩
    · rintro ⟨h1, h2⟩ k hk
      rcases fin3_cases k with rfl | rfl | rfl
      · exact absurd rfl hk
      · exact h1
      · exact h2
  · rw [polarChamber_adj_l (by decide), show (1 : Fin 4) = (1 : Fin 3).castSucc from rfl,
      FourthResidue.mem_nativeParabolic_singleton_iff]
    refine and_congr_right fun _ => ?_
    simp only [flagO, flagO_sub_eq_iff]
    constructor
    · intro h
      exact ⟨h 0 (by decide), h 2 (by decide)⟩
    · rintro ⟨h0, h2⟩ k hk
      rcases fin3_cases k with rfl | rfl | rfl
      · exact h0
      · exact absurd rfl hk
      · exact h2
  · rw [polarChamber_adj_π (by decide) (by decide),
      show (2 : Fin 4) = (2 : Fin 3).castSucc from rfl,
      FourthResidue.mem_nativeParabolic_singleton_iff]
    refine and_congr_right fun _ => ?_
    simp only [flagO, flagO_sub_eq_iff]
    constructor
    · intro h
      exact ⟨h 0 (by decide), h 1 (by decide)⟩
    · rintro ⟨h0, h1⟩ k hk
      rcases fin3_cases k with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact absurd rfl hk
  · constructor
    · intro h
      exact absurd ((resDist_eq_simple_iff p q 3).2 h) (not_resDistK_eq_simple_three _ _)
    · rintro ⟨hne, hadj⟩
      exfalso
      apply hne
      have hEq : (polarChamber OData (0 : Fin 4) 1 2).adj 3 = Eq := by
        simp [polarChamber, ChamberSystem.ofThree]
      rw [hEq] at hadj
      exact modelO_bijective.1 ((hm p).trans (hadj.trans (hm q).symm))

theorem isQuadrangleFlagResidue_c₀ :
    IsQuadrangleFlagResidue ncs stdDistance 1 2 c₀ := by
  have h := isQuadrangleFlagResidue_oC0 (cs := ncs) (by decide : (0 : Fin 4) ≠ 1)
    (by decide : (1 : Fin 4) ≠ 2) (by decide : (0 : Fin 4) ≠ 2) isChamberModel_modelO modelO_c₀
  exact IsQuadrangleFlagResidue.ofResidue (by
    intro i hi
    rcases hi with rfl | rfl <;> simp [FourthResidue.fourthJ]) h

theorem isPlaneFlagResidue_two_c₀ :
    IsPlaneFlagResidue ncs stdDistance (ZMod 2) 0 1 c₀ := by
  have h := isPlaneFlagResidue_oC0 (cs := ncs) (by decide : (0 : Fin 4) ≠ 1)
    (by decide : (1 : Fin 4) ≠ 2) (by decide : (0 : Fin 4) ≠ 2) isChamberModel_modelO modelO_c₀
  exact IsPlaneFlagResidue.ofResidue (by
    intro i hi
    rcases hi with rfl | rfl <;> simp [FourthResidue.fourthJ]) h

end CFSG.Monster.B.E6.StdF4
