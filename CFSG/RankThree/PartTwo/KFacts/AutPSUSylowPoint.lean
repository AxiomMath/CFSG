module

public import CFSG.RankThree.PartTwo.KFacts.AutPSU
public import CFSG.ClassicalGroups.UnitaryFlag.PointSylow
public import CFSG.ClassicalGroups.UnitaryFlag.StatedBridge

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LinearGroups CFSG.Quasithin Matrix
open scoped Pointwise

variable {n : ℕ} {K : Type} [Field K]

theorem isometry_of_mem_unitaryIsom3 (hu : UnitaryFieldData 2 n K) (A : unitaryIsom3 hu)
    (x y : Fin 3 → K) :
    stdHermForm hu 3 ((A : GL (Fin 3) K) • x) ((A : GL (Fin 3) K) • y) =
      stdHermForm hu 3 x y := by
  rw [stdHermForm_eq_gramForm hu 3]
  exact ((gramForm_isometry_iff hu (1 : Matrix (Fin 3) (Fin 3) K)
    ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).mpr (by
      simpa only [Matrix.mul_one] using (mem_unitaryIsom3 (h := hu)).mp A.2)) x y

private theorem smul_mem_isotropicLines (hu : UnitaryFieldData 2 n K) (A : unitaryIsom3 hu)
    {L : Submodule K (Fin 3 → K)} (hL : L ∈ isotropicLines hu 3) :
    (A : GL (Fin 3) K) • L ∈ isotropicLines hu 3 := by
  refine ⟨?_, ?_⟩
  · rw [smul_eq_map, ← hL.1]
    exact LinearEquiv.finrank_map_eq
      (DistribMulAction.toLinearEquiv K (Fin 3 → K) (A : GL (Fin 3) K)) L
  · rintro a ⟨b, hb, rfl⟩
    exact (isometry_of_mem_unitaryIsom3 hu A b b).trans (hL.2 b hb)

private theorem mulVecLin_conj_hermTransvection_of_isom (hu : UnitaryFieldData 2 n K)
    (A : unitaryIsom3 hu) (x : unitarySU 2 n K 3) {a : Fin 3 → K} {c : K}
    (hx : mulVecLin ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      hermTransvection (stdHermForm hu 3) a c) :
    mulVecLin (((suConj hu A x : unitarySU 2 n K 3) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) =
      hermTransvection (stdHermForm hu 3) ((A : GL (Fin 3) K) • a) c := by
  refine LinearMap.ext fun v => ?_
  change (((suConj hu A x : unitarySU 2 n K 3) : GL (Fin 3) K) • v) =
    hermTransvection (stdHermForm hu 3) ((A : GL (Fin 3) K) • a) c v
  have hgi : (A : GL (Fin 3) K) • ((A : GL (Fin 3) K)⁻¹ • v) = v := smul_inv_smul _ v
  have hiso := isometry_of_mem_unitaryIsom3 hu A a ((A : GL (Fin 3) K)⁻¹ • v)
  rw [hgi] at hiso
  have hxv : (x : GL (Fin 3) K) • ((A : GL (Fin 3) K)⁻¹ • v) =
      hermTransvection (stdHermForm hu 3) a c ((A : GL (Fin 3) K)⁻¹ • v) := by
    change ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (((A : GL (Fin 3) K)⁻¹) • v) =
      hermTransvection (stdHermForm hu 3) a c ((A : GL (Fin 3) K)⁻¹ • v)
    simpa only [Matrix.mulVecLin_apply] using
      LinearMap.congr_fun hx ((A : GL (Fin 3) K)⁻¹ • v)
  rw [coe_suConj, mul_smul, mul_smul]
  change (A : GL (Fin 3) K) • ((x : GL (Fin 3) K) •
    (((A : GL (Fin 3) K)⁻¹) • v)) = _
  rw [hxv, hermTransvection_apply, smul_add,
    smul_comm (A : GL (Fin 3) K)
      (c * stdHermForm hu 3 a ((A : GL (Fin 3) K)⁻¹ • v)) a,
    hgi, hermTransvection_apply, ← hiso]

theorem suConj_isotropicTransvectionGroup (hu : UnitaryFieldData 2 n K) (A : unitaryIsom3 hu)
    {L : Submodule K (Fin 3 → K)} (hL : L ∈ isotropicLines hu 3) :
    (isotropicTransvectionGroup hu 3 L).map (suConj hu A).toMonoidHom =
      isotropicTransvectionGroup hu 3 ((A : GL (Fin 3) K) • L) := by
  rw [isotropicTransvectionGroup, MonoidHom.map_closure, isotropicTransvectionGroup]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨b, hb, c, hc, hx⟩, rfl⟩
    exact ⟨(A : GL (Fin 3) K) • b, Submodule.smul_mem_pointwise_smul b (A : GL (Fin 3) K) L hb,
      c, hc, mulVecLin_conj_hermTransvection_of_isom hu A x hx⟩
  · rintro ⟨b', hb', c, hc, hy⟩
    obtain ⟨b, hb, rfl⟩ :=
      (Submodule.mem_smul_pointwise_iff_exists b' (A : GL (Fin 3) K) L).mp hb'
    refine ⟨suConj hu A⁻¹ y, ⟨b, hb, c, hc, ?_⟩, ?_⟩
    · rw [mulVecLin_conj_hermTransvection_of_isom hu A⁻¹ y hy]
      rw [show ((A⁻¹ : unitaryIsom3 hu) : GL (Fin 3) K) = (A : GL (Fin 3) K)⁻¹ from rfl,
        inv_smul_smul]
    · change (suConj hu A * suConj hu A⁻¹) y = y
      rw [← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

private theorem eq_of_isPGroup_map_eq_of_odd_central_ker {G X : Type*} [Group G] [Finite G]
    [Group X] [Finite X] (φ : G →* X) (hcen : φ.ker ≤ Subgroup.center G)
    (hodd : Odd (Nat.card φ.ker)) {A B : Subgroup G} (hA : IsPGroup 2 A) (hB : IsPGroup 2 B)
    (hmap : A.map φ = B.map φ) : A = B := by
  have hle : ∀ {A B : Subgroup G}, IsPGroup 2 A → IsPGroup 2 B → A.map φ = B.map φ → A ≤ B := by
    intro A B hA hB hmap a ha
    have hφa : φ a ∈ B.map φ := hmap ▸ Subgroup.mem_map_of_mem φ ha
    obtain ⟨b, hb, hbφ⟩ := Subgroup.mem_map.mp hφa
    set k : G := b⁻¹ * a with hk
    have hkker : k ∈ φ.ker := by
      rw [MonoidHom.mem_ker, hk, map_mul, map_inv, hbφ, inv_mul_cancel]
    have hkcen : k ∈ Subgroup.center G := hcen hkker
    have hkodd : Odd (orderOf k) :=
      Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard φ.ker hkker)
    have hcomm : Commute b k := Subgroup.mem_center_iff.mp hkcen b
    have ha2 : ∃ m, orderOf a = 2 ^ m := by
      simpa [Subgroup.orderOf_mk] using hA.exists_orderOf_eq_pow ⟨a, ha⟩
    have hb2 : ∃ m, orderOf b = 2 ^ m := by
      simpa [Subgroup.orderOf_mk] using hB.exists_orderOf_eq_pow ⟨b, hb⟩
    have haeq : a = b * k := by rw [hk]; group
    have hk1 : k = 1 := eq_one_of_mul_eq_of_two_pow_of_odd hcomm haeq ha2 hb2 hkodd
    rw [haeq, hk1, mul_one]
    exact hb
  exact le_antisymm (hle hA hB hmap) (hle hB hA hmap.symm)

private theorem eq_of_omegaOneOf_sylow_eq_psu (hu : UnitaryFieldData 2 n K)
    {S S' : Sylow 2 (unitaryPSU hu 3)}
    (hΩ : omegaOneOf (S : Subgroup (unitaryPSU hu 3)) =
      omegaOneOf (S' : Subgroup (unitaryPSU hu 3))) : S = S' := by
  haveI : Finite K := hu.finite
  haveI : Finite ↥(unitarySU 2 n K 3) := Subtype.finite
  haveI : Finite (unitaryPSU hu 3) :=
    Finite.of_surjective (unitaryProj hu 3) (unitaryProj_surjective hu 3)
  obtain ⟨R, hR⟩ := (sylowMapUnitaryProj_bijective hu).2 S
  obtain ⟨R', hR'⟩ := (sylowMapUnitaryProj_bijective hu).2 S'
  have hΩR : (omegaOneOf (R : Subgroup ↥(unitarySU 2 n K 3))).map (unitaryProj hu 3) =
      omegaOneOf (S : Subgroup (unitaryPSU hu 3)) := by
    rw [omegaOneOf_map_sylowMapUnitaryProj hu R, hR]
  have hΩR' : (omegaOneOf (R' : Subgroup ↥(unitarySU 2 n K 3))).map (unitaryProj hu 3) =
      omegaOneOf (S' : Subgroup (unitaryPSU hu 3)) := by
    rw [omegaOneOf_map_sylowMapUnitaryProj hu R', hR']
  have himg : (omegaOneOf (R : Subgroup ↥(unitarySU 2 n K 3))).map (unitaryProj hu 3) =
      (omegaOneOf (R' : Subgroup ↥(unitarySU 2 n K 3))).map (unitaryProj hu 3) :=
    hΩR.trans (hΩ.trans hΩR'.symm)
  have h2R : IsPGroup 2 (omegaOneOf (R : Subgroup ↥(unitarySU 2 n K 3))) :=
    R.isPGroup'.to_le (by
      rw [omegaOneOf]
      exact (Subgroup.closure_le _).mpr (fun x hx => hx.1))
  have h2R' : IsPGroup 2 (omegaOneOf (R' : Subgroup ↥(unitarySU 2 n K 3))) :=
    R'.isPGroup'.to_le (by
      rw [omegaOneOf]
      exact (Subgroup.closure_le _).mpr (fun x hx => hx.1))
  have hΩeq : omegaOneOf (R : Subgroup ↥(unitarySU 2 n K 3)) =
      omegaOneOf (R' : Subgroup ↥(unitarySU 2 n K 3)) :=
    eq_of_isPGroup_map_eq_of_odd_central_ker (unitaryProj hu 3)
      (by rw [ker_unitaryProj]; exact unitaryScalars_le_center hu 3)
      (ker_unitaryProj_odd hu) h2R h2R' himg
  have hRR' : R = R' := eq_of_omegaOneOf_sylow_eq hu hΩeq
  rw [← hR, ← hR', hRR']

theorem smul_eq_of_normalizes_sylow (hu : UnitaryFieldData 2 n K) (hn : 2 ≤ n)
    (A : unitaryIsom3 hu) (S : Sylow 2 (unitaryPSU hu 3))
    (hS : ∀ x ∈ (S : Subgroup (unitaryPSU hu 3)),
      psuConj hu A x ∈ (S : Subgroup (unitaryPSU hu 3))) :
    ∃ L ∈ isotropicLines hu 3, (A : GL (Fin 3) K) • L = L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite K := hu.finite
  haveI : Finite ↥(unitarySU 2 n K 3) := Subtype.finite
  haveI : Finite (unitaryPSU hu 3) :=
    Finite.of_surjective (unitaryProj hu 3) (unitaryProj_surjective hu 3)
  obtain ⟨R, hR⟩ := (sylowMapUnitaryProj_bijective hu).2 S
  let T : Sylow 2 ↥(unitarySU 2 n K 3) :=
    Sylow.mapSurjective (f := (suConj hu A).toMonoidHom) (suConj hu A).surjective R
  have hT : (T : Subgroup ↥(unitarySU 2 n K 3)) =
      (R : Subgroup ↥(unitarySU 2 n K 3)).map (suConj hu A).toMonoidHom :=
    Sylow.coe_mapSurjective (f := (suConj hu A).toMonoidHom) (suConj hu A).surjective R
  have hcomp : (unitaryProj hu 3).comp (suConj hu A).toMonoidHom =
      (psuConj hu A).toMonoidHom.comp (unitaryProj hu 3) := by
    ext g
    exact (psuConj_mk A g).symm
  have hker : Odd (Nat.card (suConj hu A).toMonoidHom.ker) := by
    rw [(MonoidHom.ker_eq_bot_iff (suConj hu A).toMonoidHom).mpr (suConj hu A).injective,
      Subgroup.card_bot]
    exact ⟨0, by norm_num⟩
  have hΩR : (omegaOneOf (R : Subgroup ↥(unitarySU 2 n K 3))).map (unitaryProj hu 3) =
      omegaOneOf (S : Subgroup (unitaryPSU hu 3)) := by
    rw [omegaOneOf_map_sylowMapUnitaryProj hu R, hR]
  have hSmap : S.map (psuConj hu A).toMonoidHom = (S : Subgroup (unitaryPSU hu 3)) := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro y ⟨x, hx, rfl⟩
      exact hS x hx
    · exact (Subgroup.card_map_of_injective (psuConj hu A).injective).symm.le
  have hkerP : Odd (Nat.card (psuConj hu A).toMonoidHom.ker) := by
    rw [(MonoidHom.ker_eq_bot_iff (psuConj hu A).toMonoidHom).mpr (psuConj hu A).injective,
      Subgroup.card_bot]
    exact ⟨0, by norm_num⟩
  have hΩS : (omegaOneOf (S : Subgroup (unitaryPSU hu 3))).map
      (psuConj hu A).toMonoidHom = omegaOneOf (S : Subgroup (unitaryPSU hu 3)) := by
    rw [omegaOneOf_map_of_odd_ker (psuConj hu A).toMonoidHom hkerP S.isPGroup', hSmap]
  have hΩT : omegaOneOf (sylowMapUnitaryProj hu T : Subgroup (unitaryPSU hu 3)) =
      omegaOneOf (S : Subgroup (unitaryPSU hu 3)) := by
    rw [← omegaOneOf_map_sylowMapUnitaryProj hu T, hT,
      ← omegaOneOf_map_of_odd_ker (suConj hu A).toMonoidHom hker R.isPGroup',
      Subgroup.map_map, hcomp, ← Subgroup.map_map, hΩR, hΩS, ← hΩR]
  have hTS : sylowMapUnitaryProj hu T = S := eq_of_omegaOneOf_sylow_eq_psu hu hΩT
  have hTR : T = R := (sylowMapUnitaryProj_bijective hu).1 (hTS.trans hR.symm)
  have hRm : (R : Subgroup ↥(unitarySU 2 n K 3)).map (suConj hu A).toMonoidHom =
      (R : Subgroup ↥(unitarySU 2 n K 3)) := by
    rw [← hT]
    exact congrArg (fun S : Sylow 2 ↥(unitarySU 2 n K 3) =>
      (S : Subgroup ↥(unitarySU 2 n K 3))) hTR
  obtain ⟨L, hL, hΩ⟩ := omegaOneOf_sylow_eq_isotropicTransvectionGroup R
  have hmapΩ : (omegaOneOf (R : Subgroup ↥(unitarySU 2 n K 3))).map
      (suConj hu A).toMonoidHom = omegaOneOf (R : Subgroup ↥(unitarySU 2 n K 3)) := by
    rw [omegaOneOf_map_of_odd_ker (suConj hu A).toMonoidHom hker R.isPGroup', hRm]
  have hAL : (A : GL (Fin 3) K) • L ∈ isotropicLines hu 3 :=
    smul_mem_isotropicLines hu A hL
  have hU : isotropicTransvectionGroup hu 3 ((A : GL (Fin 3) K) • L) =
      isotropicTransvectionGroup hu 3 L := by
    rw [← suConj_isotropicTransvectionGroup hu A hL, ← hΩ, hmapΩ, hΩ]
  exact ⟨L, hL, eq_of_isotropicTransvectionGroup_eq hAL hL hU⟩

end CFSG.RankThree.PartTwo.KFacts

end
