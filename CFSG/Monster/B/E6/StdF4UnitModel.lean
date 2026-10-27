module

public import CFSG.Monster.B.E6.StdF4OrthModel
public import CFSG.Monster.B.Geometry.UnitaryModel

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4

open Module CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Overlap (K bar)
open CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem uHerm_eq_nativeHerm (v w : Fin 6 → K) : uHerm v w = nativeHerm v w := by
  rw [uHerm, nativeHerm, Fin.sum_univ_three]
  simp only [add_assoc]
  rfl

abbrev sigmaL : (Fin 6 → K) →ₗ[K] (Fin 6 → K) := (nativeCoord : (Fin 6 → K) →ₗ[K] (Fin 6 → K))

abbrev sigmaInvL : (Fin 6 → K) →ₗ[K] (Fin 6 → K) :=
  (nativeCoord.symm : (Fin 6 → K) →ₗ[K] (Fin 6 → K))

theorem map_sigma_map_symm (U : Submodule K (Fin 6 → K)) : (U.map sigmaInvL).map sigmaL = U := by
  ext v
  simp only [Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    rwa [LinearEquiv.apply_symm_apply]
  · intro hv
    exact ⟨nativeCoord.symm v, ⟨v, hv, rfl⟩, LinearEquiv.apply_symm_apply _ _⟩

theorem map_symm_map_sigma (U : Submodule K (Fin 6 → K)) : (U.map sigmaL).map sigmaInvL = U := by
  ext v
  simp only [Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    rwa [LinearEquiv.symm_apply_apply]
  · intro hv
    exact ⟨nativeCoord v, ⟨v, hv, rfl⟩, LinearEquiv.symm_apply_apply _ _⟩

@[expose] def flagU (F : IsoFlag6) : PFlag UData where
  V₁ := (F.sub 0).map sigmaL
  V₂ := (F.sub 1).map sigmaL
  V₃ := (F.sub 2).map sigmaL
  finrank₁ := by rw [LinearEquiv.finrank_map_eq]; exact F.finrank_sub 0
  finrank₂ := by rw [LinearEquiv.finrank_map_eq]; exact F.finrank_sub 1
  finrank₃ := by rw [LinearEquiv.finrank_map_eq]; exact F.finrank_sub 2
  le₁₂ := Submodule.map_mono (F.mono (by decide : (0 : Fin 3) ≤ 1))
  le₂₃ := Submodule.map_mono (F.mono (by decide : (1 : Fin 3) ≤ 2))
  isTI v hv := by
    obtain ⟨u, hu, rfl⟩ := hv
    change uHerm (nativeCoord u) (nativeCoord u) = 0
    rw [uHerm_eq_nativeHerm, nativeHerm_nativeCoord]
    exact F.isotropic u hu u hu

@[expose] def unflagUSub (x : PFlag UData) : Fin 3 → Submodule K (Fin 6 → K) :=
  ![x.V₁.map sigmaInvL, x.V₂.map sigmaInvL, x.V₃.map sigmaInvL]

@[expose] def unflagU (x : PFlag UData) : IsoFlag6 where
  sub := unflagUSub x
  finrank_sub k := by
    rcases fin3_cases k with rfl | rfl | rfl
    · exact (LinearEquiv.finrank_map_eq _ _).trans x.finrank₁
    · exact (LinearEquiv.finrank_map_eq _ _).trans x.finrank₂
    · exact (LinearEquiv.finrank_map_eq _ _).trans x.finrank₃
  mono a b hab := by
    have h12 := Submodule.map_mono (f := sigmaInvL) x.le₁₂
    have h23 := Submodule.map_mono (f := sigmaInvL) x.le₂₃
    rcases fin3_cases a with rfl | rfl | rfl <;> rcases fin3_cases b with rfl | rfl | rfl
    all_goals first
      | exact le_rfl
      | exact absurd hab (by decide)
      | exact h12
      | exact h23
      | exact h12.trans h23
  isotropic v hv w hw := by
    obtain ⟨a, ha, rfl⟩ := hv
    obtain ⟨b, hb, rfl⟩ := hw
    rw [← nativeHerm_nativeCoord]
    change nativeHerm (nativeCoord (nativeCoord.symm a)) (nativeCoord (nativeCoord.symm b)) = 0
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, ← uHerm_eq_nativeHerm]
    exact UData.pair_eq_zero_of_isTI x.V₃ x.isTI b hb a ha

@[expose] def flagEquivU : IsoFlag6 ≃ PFlag UData where
  toFun := flagU
  invFun := unflagU
  left_inv F := by
    refine IsoFlag6.ext (funext fun k => ?_)
    rcases fin3_cases k with rfl | rfl | rfl <;> exact map_symm_map_sigma _
  right_inv x := PFlag.ext (map_sigma_map_symm _) (map_sigma_map_symm _) (map_sigma_map_symm _)

theorem flagEquivU_apply (F : IsoFlag6) : flagEquivU F = flagU F := rfl

theorem flagU_sub_eq_iff (F F' : IsoFlag6) (k : Fin 3) :
    (F.sub k).map sigmaL = (F'.sub k).map sigmaL ↔ F.sub k = F'.sub k :=
  ⟨fun h => by rw [← map_symm_map_sigma (F.sub k), h, map_symm_map_sigma], fun h => by rw [h]⟩

abbrev ResJ :
    Type := residue ncs stdDistance firstJ c₀

@[expose] def cosetEquivJ :
    ParabolicCosets firstJ ≃ ResJ :=
  (Equiv.ofInjective _ (FourthResidue.chamberOf_injective firstJ)).trans
    (Set.equivOfEq (FourthResidue.range_chamberOf firstJ))

theorem coe_cosetEquivJ_mk
    (p : nativeParabolic firstJ) :
    (cosetEquivJ (QuotientGroup.mk p) : stdChamber) =
      ((⟨p, nativeParabolic_le_stdGroup _ p.2⟩ : stdGroup) : stdChamber) := rfl

@[expose] def modelU
    (y : ResJ) : PFlag UData :=
  flagEquivU (C2E6Std.residueFlag (cosetEquivJ.symm y))

theorem modelU_bijective :
    Function.Bijective modelU :=
  (flagEquivU.bijective.comp C2E6Std.residueFlag.bijective).comp cosetEquivJ.symm.bijective

theorem c₀_mem_ResJ :
    c₀ ∈ residue ncs stdDistance firstJ c₀ := self_mem_residue _ _

theorem modelU_c₀ :
    modelU ⟨c₀, c₀_mem_ResJ⟩ = flagU baseFlag := by
  have e : cosetEquivJ.symm ⟨c₀, c₀_mem_ResJ⟩ = QuotientGroup.mk 1 := by
    rw [Equiv.symm_apply_eq]
    exact Subtype.ext rfl
  rw [modelU, e, flagEquivU_apply, C2E6Std.residueFlag_one]

theorem resDistJ_eq_simple_iff
    (p q : nativeParabolic firstJ) (i : Fin 4) :
    resDist ncs stdDistance firstJ c₀ (cosetEquivJ (QuotientGroup.mk p))
        (cosetEquivJ (QuotientGroup.mk q)) = ncs.simple i ↔
      cosetEquivJ (QuotientGroup.mk p) ≠ cosetEquivJ (QuotientGroup.mk q) ∧
        ((p⁻¹ * q : nativeParabolic firstJ) : ModGL Tag.E6 K) ∈ nativeParabolic {i} := by
  rw [resDist, coe_cosetEquivJ_mk, coe_cosetEquivJ_mk, stdDistance_eq_simple_iff]
  refine and_congr (not_congr ?_) Iff.rfl
  rw [Subtype.ext_iff, coe_cosetEquivJ_mk, coe_cosetEquivJ_mk]

theorem not_resDistJ_eq_simple_zero
    (y z : ResJ) :
    resDist ncs stdDistance firstJ c₀ y z ≠ ncs.simple 0 := by
  intro h
  have hmem := mem_parabolic_of_mem_residue hδ y.2 z.2
  rw [show stdDistance y.1 z.1 = ncs.simple 0 from h, simple_mem_parabolic_iff] at hmem
  rcases hmem with h1 | h2 | h3
  · exact absurd h1 (by decide)
  · exact absurd h2 (by decide)
  · exact absurd h3 (by decide)

theorem one_mem_firstJ : (1 : Fin 4) ∈ firstJ := by simp [firstJ]

theorem three_mem_firstJ : (3 : Fin 4) ∈ firstJ := by simp [firstJ]

theorem isChamberModel_modelU :
    IsChamberModel ncs (resDist ncs stdDistance firstJ c₀) (polarChamber UData 3 2 1) modelU := by
  refine ⟨modelU_bijective, fun y z i => ?_⟩
  obtain ⟨y, rfl⟩ := cosetEquivJ.surjective y
  obtain ⟨z, rfl⟩ := cosetEquivJ.surjective z
  induction y using QuotientGroup.induction_on with | H p => ?_
  induction z using QuotientGroup.induction_on with | H q => ?_
  have hm : ∀ p : nativeParabolic firstJ,
      modelU (cosetEquivJ (QuotientGroup.mk p)) =
        flagU (C2E6Std.residueFlag (QuotientGroup.mk p)) := fun p => by
    rw [modelU, Equiv.symm_apply_apply]
    rfl
  rw [resDistJ_eq_simple_iff, hm, hm]
  rcases fin4_cases i with rfl | rfl | rfl | rfl
  · constructor
    · intro h
      exact absurd ((resDistJ_eq_simple_iff p q 0).2 h) (not_resDistJ_eq_simple_zero _ _)
    · rintro ⟨hne, hadj⟩
      exfalso
      apply hne
      have hEq : (polarChamber UData (3 : Fin 4) 2 1).adj 0 = Eq := by
        simp [polarChamber, ChamberSystem.ofThree]
      rw [hEq] at hadj
      exact modelU_bijective.1 ((hm p).trans (hadj.trans (hm q).symm))
  · rw [polarChamber_adj_π (by decide) (by decide),
      C2E6Std.mem_nativeParabolic_singleton_iff one_mem_firstJ]
    refine and_congr_right fun _ => ?_
    simp only [flagU, flagU_sub_eq_iff]
    constructor
    · intro h
      exact ⟨h 0 (by decide), h 1 (by decide)⟩
    · rintro ⟨h0, h1⟩ k hk
      rcases fin3_cases k with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact absurd rfl hk
  · rw [polarChamber_adj_l (by decide),
      C2E6Std.mem_nativeParabolic_singleton_iff two_mem_firstJ]
    refine and_congr_right fun _ => ?_
    simp only [flagU, flagU_sub_eq_iff]
    constructor
    · intro h
      exact ⟨h 0 (by decide), h 2 (by decide)⟩
    · rintro ⟨h0, h2⟩ k hk
      rcases fin3_cases k with rfl | rfl | rfl
      · exact h0
      · exact absurd rfl hk
      · exact h2
  · rw [polarChamber_adj_p, C2E6Std.mem_nativeParabolic_singleton_iff three_mem_firstJ]
    refine and_congr_right fun _ => ?_
    simp only [flagU, flagU_sub_eq_iff]
    constructor
    · intro h
      exact ⟨h 1 (by decide), h 2 (by decide)⟩
    · rintro ⟨h1, h2⟩ k hk
      rcases fin3_cases k with rfl | rfl | rfl
      · exact absurd rfl hk
      · exact h1
      · exact h2

@[expose] def rhoU : (Fin 6 → K) →ₗ[K] (Fin 3 → K) where
  toFun v := ![v 0, v 1, v 2]
  map_add' v w := by funext i; fin_cases i <;> rfl
  map_smul' c v := by funext i; fin_cases i <;> rfl

theorem rhoU_injOn :
    Set.InjOn rhoU (modelU ⟨c₀, c₀_mem_ResJ⟩).V₃ := by
  intro v hv w hw h
  rw [modelU_c₀] at hv hw
  change v ∈ (baseFlag.sub 2).map sigmaL at hv
  change w ∈ (baseFlag.sub 2).map sigmaL at hw
  rw [nativeCoord_baseFlag] at hv hw
  change v ∈ cspan K ({0, 1, 2} : Finset (Fin 6)) at hv
  change w ∈ cspan K ({0, 1, 2} : Finset (Fin 6)) at hw
  rw [mem_cspan] at hv hw
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  all_goals
    simp only [Fin.reduceFinMk, Fin.isValue]
    rw [hv _ (by decide), hw _ (by decide)]

theorem isPlaneFlagResidue_four_c₀ :
    IsPlaneFlagResidue ncs stdDistance K 2 3 c₀ := by
  have h := isPlaneFlagResidue_polar (cs := ncs) isChamberModel_modelU
    (by decide : (3 : Fin 4) ≠ 2) (by decide : (2 : Fin 4) ≠ 1) (by decide : (3 : Fin 4) ≠ 1)
    rhoU rhoU_injOn
  exact IsPlaneFlagResidue.ofResidue (by
    intro i hi
    rcases hi with rfl | rfl <;> simp [firstJ]) h.swap

end CFSG.Monster.B.E6.StdF4
