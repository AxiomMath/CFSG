module

public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613C3Frame

public section

namespace CFSG.StandardType

open Module CFSG.StandardType.Triality CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin
  CFSG.RankThree.PartOne.AUTSL CFSG.StandardType.D4Rank CFSG.StandardType.L613KG QuadraticMap
open scoped Matrix

namespace L613C3

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem castSucc_ne_three (i : Fin 3) : Fin.castSucc i ≠ (3 : Fin 4) := by
  fin_cases i <;> decide

omit [Finite K] [CharP K 2] in
theorem last_eq_three : (Fin.last 3 : Fin 4) = 3 := rfl

theorem act_zStd_pvec_true (ω : Kˣ) (k : Fin 4) :
    act (zStd ω) (AutOm.pvec k true) =
      ((if k = 3 then 1 else ω : Kˣ) : K) • AutOm.pvec k true := by
  rw [AutOm.pvec_true, zStd, act_dg_single, twHom_ie]

theorem act_zStd_pvec_false (ω : Kˣ) (k : Fin 4) :
    act (zStd ω) (AutOm.pvec k false) =
      (((if k = 3 then 1 else ω : Kˣ)⁻¹ : Kˣ) : K) • AutOm.pvec k false := by
  rw [AutOm.pvec_false, zStd, act_dg_single, twHom_jf]

omit [Finite K] [CharP K 2] in
theorem omega_sq_add_of_orderOf {ω : Kˣ} (hω : orderOf ω = 3) : (ω : K) ^ 2 + ω + 1 = 0 := by
  obtain ⟨hω1, -, -⟩ := units_facts hω
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have h3 : (ω : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  have hne : (ω : K) - 1 ≠ 0 := sub_ne_zero.mpr fun h => hω1 (Units.ext h)
  have h0 : ((ω : K) - 1) * ((ω : K) ^ 2 + ω + 1) = 0 := by linear_combination h3
  exact (mul_eq_zero.mp h0).resolve_left hne

omit [Finite K] [CharP K 2] in
theorem isHypTriple_std :
    IsHypTriple (fun i : Fin 3 => (AutOm.pvec (Fin.castSucc i) true : Fin (2 * 4) → K))
      (fun i : Fin 3 => AutOm.pvec (Fin.castSucc i) false) := by
  refine ⟨fun i => AutOm.form_pvec _ _, fun i => AutOm.form_pvec _ _, fun i j => ?_,
    fun i j => ?_, fun i j => ?_⟩ <;> rw [AutOm.polar_pvec] <;> simp

theorem exists_conj_zStd {ω : Kˣ} (hω : orderOf ω = 3) {z : Om8 K} (hz3 : z ^ 3 = 1)
    (hd : omFixDim z = 2) : ∃ h : Om8 K, z = h * zStd ω * h⁻¹ := by
  have hw := omega_sq_add_of_orderOf hω
  have hinv : ((ω⁻¹ : Kˣ) : K) = (ω : K) ^ 2 := by
    rw [Units.val_inv_eq_inv_val, omega_inv hw]
  have hnd := (regular_coordinateQuadPlus 4 K (by norm_num)).1
  have hT := (regular_coordinateQuadPlus 4 K (by norm_num)).2
  obtain ⟨u, w, hf⟩ := exists_eframe hz3 hd hw 3 le_rfl
  have hzt := hf.isHypTriple hw
  obtain ⟨g, hgO, hg⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq
    hnd _ (Fin.append u w) isHypTriple_std.linIndep hzt.linIndep
    (fun i => by rw [hzt.Q_append, isHypTriple_std.Q_append])
    (isHypTriple_std.polar_append_eq hzt)
  have hgu : ∀ i : Fin 3, g (AutOm.pvec (Fin.castSucc i) true) = u i := fun i => by
    have h := hg (Fin.castAdd 3 i)
    rwa [Fin.append_left, Fin.append_left] at h
  have hgw : ∀ i : Fin 3, g (AutOm.pvec (Fin.castSucc i) false) = w i := fun i => by
    have h := hg (Fin.natAdd 3 i)
    rwa [Fin.append_right, Fin.append_right] at h
  have hgpol : ∀ a b, polar (coordinateQuadPlus 4 K) (g a) (g b) =
      polar (coordinateQuadPlus 4 K) a b :=
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO
  have hfix3 : ∀ r, act z (g (AutOm.pvec (Fin.last 3) r)) = g (AutOm.pvec (Fin.last 3) r) :=
    fun r => fixed_of_orth_eframe hz3 hd hw hf
      (fun i => by
        rw [← hgu i, hgpol]
        exact AutOm.polar_pvec_of_ne (Fin.castSucc_lt_last i).ne' r true)
      (fun i => by
        rw [← hgw i, hgpol]
        exact AutOm.polar_pvec_of_ne (Fin.castSucc_lt_last i).ne' r false)
  have hbasis : ∀ (k : Fin 4) (r : Bool),
      act z (g (AutOm.pvec k r)) = g (act (zStd ω) (AutOm.pvec k r)) := by
    intro k r
    induction k using Fin.lastCases with
    | last =>
      cases r
      · rw [act_zStd_pvec_false, ite_eq_left last_eq_three, inv_one, Units.val_one, one_smul]
        exact hfix3 false
      · rw [act_zStd_pvec_true, ite_eq_left last_eq_three, Units.val_one, one_smul]
        exact hfix3 true
    | cast i =>
      cases r
      · rw [act_zStd_pvec_false, ite_eq_right (castSucc_ne_three i), hgw, map_smul, hgw,
          hf.2.1 i, hinv]
      · rw [act_zStd_pvec_true, ite_eq_right (castSucc_ne_three i), hgu, map_smul, hgu, hf.1 i]
  have key : ∀ y, act z (g y) = g (act (zStd ω) y) := by
    have hW : LinearMap.ker ((omRep z).comp (g : (Fin (2 * 4) → K) →ₗ[K] (Fin (2 * 4) → K)) -
        (g : (Fin (2 * 4) → K) →ₗ[K] (Fin (2 * 4) → K)).comp (omRep (zStd ω))) = ⊤ :=
      AutOm.eq_top_of_pvec_mem fun k r => by
        rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
          sub_eq_zero, LinearEquiv.coe_coe, omRep_apply, omRep_apply]
        exact hbasis k r
    intro y
    have hy : y ∈ LinearMap.ker ((omRep z).comp (g : (Fin (2 * 4) → K) →ₗ[K] (Fin (2 * 4) → K)) -
        (g : (Fin (2 * 4) → K) →ₗ[K] (Fin (2 * 4) → K)).comp (omRep (zStd ω))) := by
      rw [hW]
      exact Submodule.mem_top
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      sub_eq_zero, LinearEquiv.coe_coe, omRep_apply, omRep_apply] at hy
    exact hy
  set G := matrixLinearIso.symm g with hG
  have hGI := symm_mem_isometries hgO
  have hunit : ((z : Om8 K) : GL (Fin (2 * 4)) K) * G =
      G * ((zStd ω : Om8 K) : GL (Fin (2 * 4)) K) := by
    refine gl_eq_of_mulVec fun y => ?_
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, symm_mulVec,
      symm_mulVec]
    exact key y
  set u₀ : Fin (2 * 4) → K := AutOm.pvec (Fin.last 3) true + AutOm.pvec (Fin.last 3) false
    with hu₀
  have hu : coordinateQuadPlus 4 K u₀ = 1 := by
    have h := AutOm.polar_pvec_not (K := K) (n := 4) (Fin.last 3) true
    rw [polar, AutOm.form_pvec, AutOm.form_pvec, sub_zero, sub_zero] at h
    exact h
  have hu0 : coordinateQuadPlus 4 K u₀ ≠ 0 := by
    rw [hu]
    exact one_ne_zero
  have hzu : act (zStd ω) u₀ = u₀ := by
    rw [hu₀, act_add, act_zStd_pvec_true, act_zStd_pvec_false, ite_eq_left last_eq_three, inv_one,
      Units.val_one, one_smul, one_smul]
  rcases mem_or_mul_reflMat_mem hnd hT hGI u₀ hu0 with hGΩ | hGrΩ
  · refine ⟨⟨G, hGΩ⟩, Subtype.ext ?_⟩
    change ((z : Om8 K) : GL (Fin (2 * 4)) K) = G * ((zStd ω : Om8 K) : GL (Fin (2 * 4)) K) * G⁻¹
    exact eq_mul_inv_of_mul_eq hunit
  · refine ⟨⟨G * reflMat (coordinateQuadPlus 4 K) u₀ hu0, hGrΩ⟩, Subtype.ext ?_⟩
    change ((z : Om8 K) : GL (Fin (2 * 4)) K) = G * reflMat (coordinateQuadPlus 4 K) u₀ hu0 *
      ((zStd ω : Om8 K) : GL (Fin (2 * 4)) K) * (G * reflMat (coordinateQuadPlus 4 K) u₀ hu0)⁻¹
    calc ((z : Om8 K) : GL (Fin (2 * 4)) K) =
          G * ((zStd ω : Om8 K) : GL (Fin (2 * 4)) K) * G⁻¹ := eq_mul_inv_of_mul_eq hunit
      _ = G * (reflMat (coordinateQuadPlus 4 K) u₀ hu0 * ((zStd ω : Om8 K) : GL (Fin (2 * 4)) K)) *
          (G * reflMat (coordinateQuadPlus 4 K) u₀ hu0)⁻¹ := by
          rw [reflMat_comm hu hu0 hzu, mul_inv_rev]
          group
      _ = _ := by group

end L613C3

open L613C3

theorem ggD4ClassThreeConjInput_holds : GGD4ClassThreeConjInput := by
  intro K _ _ _ hK3 z z' hz3 hz'3 hz2 hz'2
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ : ∃ ω : Kˣ, orderOf ω = 3 :=
    exists_prime_orderOf_dvd_card' 3 (by rw [Nat.card_units]; exact hK3)
  obtain ⟨h, rfl⟩ := exists_conj_zStd hω hz3 hz2
  obtain ⟨h', rfl⟩ := exists_conj_zStd hω hz'3 hz'2
  exact ⟨h' * h⁻¹, by group⟩

end CFSG.StandardType
