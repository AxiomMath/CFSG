module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section3.corollary_1_b
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.claim_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.proposition
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.claim_H4_b
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_6_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.corollary
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.AppendixIInput
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.lemma_5
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter3section3.proposition
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CoprimeHall

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section4

open PFchapter1section1 PFchapter1section3 PFAppendixIII
open PFchapter3section1 PFchapter3section3 PFchapter4section2 PFchapter4section3

/-! # Peterfalvi, Part II, Chapter IV, Section 4 endpoint -/

universe u v

private theorem fixed_point_card_ge_three_of_centralizer_Q
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [Finite Omega]
    (H D Q X : Subgroup G) (t q : G)
    (hA1 : HypothesisA1 G Omega H D Q t)
    (hX_le_D : X ≤ D)
    (hqQ : q ∈ Q) (hq_ne : q ≠ 1)
    (hqC : q ∈ Subgroup.centralizer (X : Set G)) :
    3 ≤ Nat.card {omega : Omega //
      omega ∈ fixedPointsOfSubgroup G Omega X} := by
  classical
  obtain ⟨base, hHbase⟩ := hA1.point_stabilizer
  let beta : Omega := t⁻¹ • base
  have hbase_fixed : base ∈ fixedPointsOfSubgroup G Omega X := by
    intro x hx
    have hxH : x ∈ H := hA1.D_le_H (hX_le_D hx)
    rw [hHbase] at hxH
    simpa using hxH
  have hright_stabilizer :
      rightConjugate H t = MulAction.stabilizer G beta := by
    rw [hHbase]
    exact rightConjugate_stabilizer base t
  have hbeta_fixed : beta ∈ fixedPointsOfSubgroup G Omega X := by
    intro x hx
    have hxD : x ∈ D := hX_le_D hx
    rw [hA1.D_eq] at hxD
    have hxstab : x ∈ MulAction.stabilizer G beta := by
      simpa [hright_stabilizer] using hxD.2
    simpa using hxstab
  have hqbeta_fixed : q • beta ∈ fixedPointsOfSubgroup G Omega X := by
    intro x hx
    have hcomm : x * q = q * x :=
      (Subgroup.mem_centralizer_iff.mp hqC) x hx
    calc
      x • (q • beta) = (x * q) • beta := by rw [mul_smul]
      _ = (q * x) • beta := by rw [hcomm]
      _ = q • (x • beta) := by rw [mul_smul]
      _ = q • beta := by rw [hbeta_fixed x hx]
  have hbase_ne_beta : base ≠ beta := by
    intro hbase
    apply hA1.t_not_mem_H
    have htinv_stab : t⁻¹ ∈ MulAction.stabilizer G base := by
      change t⁻¹ • base = base
      simpa [beta] using hbase.symm
    have htinv_H : t⁻¹ ∈ H := by simpa [hHbase] using htinv_stab
    simpa using H.inv_mem htinv_H
  have hq_fixes_base : q • base = base := by
    have hqH : q ∈ H := hA1.Q_le_H hqQ
    rw [hHbase] at hqH
    simpa using hqH
  have hbase_ne_qbeta : base ≠ q • beta := by
    intro hbase
    apply hbase_ne_beta
    calc
      base = q⁻¹ • base := by
        simpa [smul_smul] using congrArg (fun z : Omega => q⁻¹ • z) hq_fixes_base
      _ = q⁻¹ • (q • beta) := by rw [← hbase]
      _ = beta := by simp [smul_smul]
  have hbeta_ne_qbeta : beta ≠ q • beta := by
    intro hfix
    have hq_stab : q ∈ MulAction.stabilizer G beta := by
      change q • beta = beta
      exact hfix.symm
    have hq_right : q ∈ rightConjugate H t := by
      rw [hright_stabilizer]
      exact hq_stab
    have hqD : q ∈ D := by
      rw [hA1.D_eq]
      exact ⟨hA1.Q_le_H hqQ, hq_right⟩
    have hqbot : q ∈ (⊥ : Subgroup G) :=
      hA1.Q_disjoint_D.le_bot ⟨hqQ, hqD⟩
    exact hq_ne (by simpa using hqbot)
  let p0 : {omega : Omega // omega ∈ fixedPointsOfSubgroup G Omega X} :=
    ⟨base, hbase_fixed⟩
  let p1 : {omega : Omega // omega ∈ fixedPointsOfSubgroup G Omega X} :=
    ⟨beta, hbeta_fixed⟩
  let p2 : {omega : Omega // omega ∈ fixedPointsOfSubgroup G Omega X} :=
    ⟨q • beta, hqbeta_fixed⟩
  let e : Fin 3 →
      {omega : Omega // omega ∈ fixedPointsOfSubgroup G Omega X} :=
    ![p0, p1, p2]
  have he : Function.Injective e := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (hbase_ne_beta (by simpa [e, p0, p1] using hij))
    · exact False.elim (hbase_ne_qbeta (by simpa [e, p0, p2] using hij))
    · exact False.elim (hbase_ne_beta (by simpa [e, p0, p1] using hij.symm))
    · rfl
    · exact False.elim (hbeta_ne_qbeta (by simpa [e, p1, p2] using hij))
    · exact False.elim (hbase_ne_qbeta (by simpa [e, p0, p2] using hij.symm))
    · exact False.elim (hbeta_ne_qbeta (by simpa [e, p1, p2] using hij.symm))
    · rfl
  simpa using Nat.card_le_card_of_injective e he

end PFchapter4section4
end CFSG.BenderSuzuki

namespace CFSG.BenderSuzuki
namespace PFchapter4section4

universe u v

public theorem equation_10_forces_ringAut_one
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (F : Subfield E) (mu : F ≃+* F) (zeta : E) (exceptional : F)
    (hodd : Odd (orderOf mu))
    (h10 : ∀ X : F, X ≠ 0 → X ≠ exceptional →
      (zeta + zeta⁻¹ + ((mu X : F) : E)) * (X : E) =
        (zeta + zeta⁻¹ + ((mu (mu X) : F) : E)) * ((mu X : F) : E)) :
    mu = 1 := by
  classical
  by_cases hmu_one : mu = 1
  · exact hmu_one
  letI : Fintype F := Fintype.ofFinite F
  haveI : Finite (F ≃+* F) :=
    Finite.of_injective (fun e : F ≃+* F => (e : F → F)) (by
      intro e₁ e₂ h
      apply RingEquiv.ext
      intro x
      exact congr_fun h x)
  have horder_ge_three : 3 ≤ orderOf mu := by
    rcases hodd with ⟨k, hk⟩
    have hk_ne_zero : k ≠ 0 := by
      intro hkzero
      apply hmu_one
      apply orderOf_eq_one_iff.mp
      omega
    omega
  have horder_le_aut_card :
      orderOf mu ≤ Nat.card (F ≃+* F) := by
    exact Nat.le_of_dvd (Nat.card_pos (α := F ≃+* F))
      (orderOf_dvd_natCard mu)
  letI : Module (ZMod 2) F :=
    { (ZMod.castHom dvd_rfl F : ZMod 2 →+* _).toModule with }
  letI : Algebra (ZMod 2) F := ZMod.algebraOfModule 2 F
  let toAlg : (F ≃+* F) → (F ≃ₐ[ZMod 2] F) := fun e =>
    AlgEquiv.ofRingEquiv (R := ZMod 2) (A₁ := F) (A₂ := F) (f := e) (by
      intro x
      have h :
          (e.toRingHom.comp (algebraMap (ZMod 2) F) :
              ZMod 2 →+* F) = algebraMap (ZMod 2) F :=
        RingHom.ext_zmod _ _
      exact DFunLike.congr_fun h x)
  have htoAlg_injective : Function.Injective toAlg := by
    intro e₁ e₂ he
    ext x
    have hx : (toAlg e₁) x = (toAlg e₂) x := DFunLike.congr_fun he x
    rw [show (toAlg e₁) x = e₁ x by rfl,
      show (toAlg e₂) x = e₂ x by rfl] at hx
    exact congrArg Subtype.val hx
  have hAut_card_le :
      Nat.card (F ≃+* F) ≤ Module.finrank (ZMod 2) F := by
    calc
      Nat.card (F ≃+* F) ≤ Nat.card (F ≃ₐ[ZMod 2] F) :=
        Nat.card_le_card_of_injective toAlg htoAlg_injective
      _ ≤ Module.finrank (ZMod 2) F := by
        simpa [Nat.card_eq_fintype_card] using
          (AlgEquiv.card_le (F := ZMod 2) (K := F))
  have hfinrank : 3 ≤ Module.finrank (ZMod 2) F :=
    horder_ge_three.trans (horder_le_aut_card.trans hAut_card_le)
  have hcard8 : 8 ≤ Fintype.card F := by
    calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ Module.finrank (ZMod 2) F :=
        Nat.pow_le_pow_right (by norm_num) hfinrank
      _ = Nat.card F := FiniteField.pow_finrank_eq_natCard 2 F
      _ = Fintype.card F := Nat.card_eq_fintype_card
  have hmu2_good : ∀ X : F,
      X ≠ 0 → X ≠ exceptional → X ≠ exceptional + 1 → mu (mu X) = X := by
    intro X hX0 hXexc hXexc1
    by_cases hXone : X = 1
    · simp [hXone]
    have hX1zero : X + 1 ≠ 0 := by
      intro hzero
      have : X = 1 := CharTwo.add_eq_zero.mp hzero
      exact hXone this
    have hX1exc : X + 1 ≠ exceptional := by
      intro heq
      apply hXexc1
      calc
        X = (X + 1) + 1 := by simp [add_assoc, CharTwo.add_self_eq_zero]
        _ = exceptional + 1 := by rw [heq]
    have hbase := h10 X hX0 hXexc
    have hshift := h10 (X + 1) hX1zero hX1exc
    simp only [map_add, map_one, Subfield.coe_add, Subfield.coe_one] at hshift
    apply F.subtype.injective
    have hsum := congrArg (fun y : E => y +
      ((zeta + zeta⁻¹ + ((mu X : F) : E)) * (X : E))) hshift
    have hbase' := hbase
    have htwo : (2 : E) = 0 := CharP.cast_eq_zero E 2
    linear_combination
      (norm := (ring_nf; simp [htwo, CharTwo.neg_eq,
        CharTwo.add_self_eq_zero])) hshift + hbase'
  have hmu2 : mu * mu = 1 := by
    apply RingEquiv.ext
    intro X
    let forbidden : Finset F :=
      [0, exceptional, exceptional + 1, X, X + exceptional,
        X + exceptional + 1].toFinset
    have hforbidden_card : forbidden.card ≤ 6 := by
      simpa [forbidden] using List.toFinset_card_le
        [0, exceptional, exceptional + 1, X, X + exceptional,
          X + exceptional + 1]
    have hy : ∃ Y : F, Y ∉ forbidden := by
      by_contra hnone
      push Not at hnone
      have huniv_le : (Finset.univ : Finset F) ⊆ forbidden := by
        intro Y _hY
        exact hnone Y
      have hle := Finset.card_le_card huniv_le
      rw [Finset.card_univ] at hle
      omega
    obtain ⟨Y, hY⟩ := hy
    have hY0 : Y ≠ 0 := by
      intro h
      apply hY
      simp [forbidden, h]
    have hYexc : Y ≠ exceptional := by
      intro h
      apply hY
      simp [forbidden, h]
    have hYexc1 : Y ≠ exceptional + 1 := by
      intro h
      apply hY
      simp [forbidden, h]
    have hYX0 : Y + X ≠ 0 := by
      intro h
      have hYX : Y = X := CharTwo.add_eq_zero.mp h
      apply hY
      simp [forbidden, hYX]
    have hYXexc : Y + X ≠ exceptional := by
      intro h
      have hYeq : Y = X + exceptional := by
        calc
          Y = (Y + X) + X := by simp [add_assoc, CharTwo.add_self_eq_zero]
          _ = exceptional + X := by rw [h]
          _ = X + exceptional := add_comm _ _
      apply hY
      simp [forbidden, hYeq]
    have hYXexc1 : Y + X ≠ exceptional + 1 := by
      intro h
      have hYeq : Y = X + exceptional + 1 := by
        calc
          Y = (Y + X) + X := by simp [add_assoc, CharTwo.add_self_eq_zero]
          _ = (exceptional + 1) + X := by rw [h]
          _ = X + exceptional + 1 := by ring
      apply hY
      simp [forbidden, hYeq]
    have hYfix := hmu2_good Y hY0 hYexc hYexc1
    have hYXfix := hmu2_good (Y + X) hYX0 hYXexc hYXexc1
    change mu (mu X) = X
    have hadd : mu (mu (Y + X)) = mu (mu Y) + mu (mu X) := by simp
    rw [hYXfix, hYfix] at hadd
    exact (add_left_cancel hadd).symm
  have horder_dvd_two : orderOf mu ∣ 2 := by
    exact orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hmu2)
  have horder_one : orderOf mu = 1 :=
    Nat.eq_one_of_dvd_coprimes hodd.coprime_two_right
      (dvd_refl (orderOf mu)) horder_dvd_two
  exact orderOf_eq_one_iff.mp horder_one

public theorem equation10_of_semilinear_relations
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (F : Subfield E) (theta mu : F ≃+* F) (muE : E ≃+* E)
    (T : E ≃+ E)
    (z omegaBar : E) (alpha c : F) (phi : Fˣ → E)
    (hthetaOdd : Odd (orderOf theta))
    (hzeta_not_mem : z ∉ F) (homegaBar_ne : omegaBar ≠ 0)
    (hc : (c : E) = z + z⁻¹)
    (hmu_coe : ∀ x : F, muE (x : E) = ((mu x : F) : E))
    (hmu_zeta : muE z = z)
    (hT_semilinear : ∀ lambda y : E, T (lambda * y) = muE lambda * T y)
    (hT_omega : T omegaBar = omegaBar)
    (h3 : ∀ a b : Fˣ,
      (b : F) * theta (b : F) =
          alpha + (a : F)⁻¹ * theta ((a : F)⁻¹) →
        phi a = z * (((a : F) : E)⁻¹ ^ 2) * phi b)
    (h4 : ∀ a : Fˣ,
      (((a : F) : E) ^ 2) * phi a =
        z⁻¹ * T (phi a) + omegaBar) :
    ∃ exceptional : F, ∀ X : F, X ≠ 0 → X ≠ exceptional →
      ((c : E) + ((mu X : F) : E)) * (X : E) =
        ((c : E) + ((mu (mu X) : F) : E)) * ((mu X : F) : E) := by
  classical
  have hzeta_ne : z ≠ 0 := by
    intro hz
    apply hzeta_not_mem
    simp [hz]
  let normEquiv : F ≃ F :=
    Equiv.ofBijective (fun x : F => x * theta x)
      (PFchapter4section2.norm_bijective_of_odd_order theta hthetaOdd)
  let tau : F → F := normEquiv.symm
  have hnorm_tau (x : F) : tau x * theta (tau x) = x := by
    exact normEquiv.apply_symm_apply x
  have htau_ne_zero (x : F) (hx : x ≠ 0) : tau x ≠ 0 := by
    intro htau
    apply hx
    rw [← hnorm_tau x, htau]
    simp
  let exceptional : F := mu ((tau alpha) ^ 2)
  refine ⟨exceptional, ?_⟩
  intro X hXzero hXexceptional
  let y : F := mu.symm X
  have hy_ne : y ≠ 0 := by
    intro hy
    apply hXzero
    calc
      X = mu y := (mu.apply_symm_apply X).symm
      _ = 0 := by rw [hy, map_zero]
  obtain ⟨r, hr⟩ :=
    (Finite.injective_iff_surjective.mp CharTwo.sq_injective) y
  have hr_ne : r ≠ 0 := by
    intro hrzero
    apply hy_ne
    rw [← hr, hrzero]
    simp
  let a : Fˣ := Units.mk0 r⁻¹ (inv_ne_zero hr_ne)
  have ha_inv : (a : F)⁻¹ = r := by
    simp [a]
  have hmu_r_sq : mu (r ^ 2) = X := by
    rw [show r ^ 2 = y from hr]
    exact mu.apply_symm_apply X
  let target : F := alpha + r * theta r
  have htarget_ne : target ≠ 0 := by
    intro htarget
    have hrnorm : r * theta r = alpha := by
      exact (CharTwo.add_eq_zero.mp htarget).symm
    have hr_tau : r = tau alpha := by
      apply normEquiv.injective
      change r * theta r = tau alpha * theta (tau alpha)
      rw [hrnorm, hnorm_tau]
    apply hXexceptional
    calc
      X = mu (r ^ 2) := hmu_r_sq.symm
      _ = mu ((tau alpha) ^ 2) := by rw [hr_tau]
      _ = exceptional := rfl
  let b0 : F := tau target
  have hb0_ne : b0 ≠ 0 := htau_ne_zero target htarget_ne
  let b : Fˣ := Units.mk0 b0 hb0_ne
  have hnorm :
      (b : F) * theta (b : F) =
        alpha + (a : F)⁻¹ * theta ((a : F)⁻¹) := by
    simp only [b, b0, a, Units.val_mk0, inv_inv]
    rw [hnorm_tau]
  have h3ab := h3 a b hnorm
  have h4a := h4 a
  have h4b := h4 b
  let x : F := mu ((a : F)⁻¹ ^ 2)
  let B : F := (b : F) ^ 2
  have hx_ne : x ≠ 0 := by
    simp [x]
  have hX_eq : x = X := by
    change mu ((a : F)⁻¹ ^ 2) = X
    rw [ha_inv]
    exact hmu_r_sq
  have h5 : z * phi b = ((x : F) : E) * T (phi b) + omegaBar := by
    rw [h3ab] at h4a
    rw [hT_semilinear] at h4a
    simp only [map_mul, hmu_zeta] at h4a
    have hcoe_inv_sq :
        ((((a : F)⁻¹ ^ 2 : F) : E)) = (((a : F) : E)⁻¹ ^ 2) := by
      norm_cast
    rw [← hcoe_inv_sq, hmu_coe] at h4a
    have hcoef :
        ((x : F) : E) = ((((mu (a : F) : F) : E) ^ 2)⁻¹) := by
      simp [x, map_inv₀, map_pow]
    calc
      z * phi b = (((a : F) : E) ^ 2) *
          (z * ((((a : F)⁻¹ ^ 2 : F) : E)) * phi b) := by
        rw [hcoe_inv_sq]
        field_simp [Units.ne_zero a]
      _ = z⁻¹ *
            (z * (((mu ((a : F)⁻¹ ^ 2) : F) : E) * T (phi b))) +
          omegaBar := by simpa [mul_assoc] using h4a
      _ = ((x : F) : E) * T (phi b) + omegaBar := by
        simp only [x]
        field_simp [hzeta_ne]
  have h6 : ((B : F) : E) * phi b = z⁻¹ * T (phi b) + omegaBar := by
    simpa [B] using h4b
  have hxE_ne : ((x : F) : E) ≠ 0 := by
    exact_mod_cast hx_ne
  have hden : (1 : E) + ((B : F) : E) * ((x : F) : E) ≠ 0 := by
    intro hden_zero
    have hprod : (1 : E) = ((B : F) : E) * ((x : F) : E) :=
      CharTwo.add_eq_zero.mp hden_zero
    have hB_eq : ((B : F) : E) = ((x : F) : E)⁻¹ := by
      calc
        ((B : F) : E) =
            (((B : F) : E) * ((x : F) : E)) * ((x : F) : E)⁻¹ := by
          field_simp [hxE_ne]
        _ = ((x : F) : E)⁻¹ := by rw [← hprod]; simp
    have hrhs :
        T (phi b) + ((x : F) : E)⁻¹ * omegaBar =
          T (phi b) + z * omegaBar := by
      calc
        T (phi b) + ((x : F) : E)⁻¹ * omegaBar =
            ((x : F) : E)⁻¹ * (z * phi b) := by
          rw [h5]
          field_simp [hxE_ne]
        _ = z * (((x : F) : E)⁻¹ * phi b) := by ring
        _ = z * (((B : F) : E) * phi b) := by rw [hB_eq]
        _ = z * (z⁻¹ * T (phi b) + omegaBar) := by rw [h6]
        _ = T (phi b) + z * omegaBar := by
          field_simp [hzeta_ne]
    have hxz : ((x : F) : E)⁻¹ = z := by
      apply mul_right_cancel₀ homegaBar_ne
      exact add_left_cancel hrhs
    apply hzeta_not_mem
    rw [← hxz]
    exact F.inv_mem x.property
  have htwo : (2 : E) = 0 := CharP.cast_eq_zero E 2
  have hPlinear :
      z * ((1 : E) + ((B : F) : E) * ((x : F) : E)) * phi b =
        ((1 : E) + z * ((x : F) : E)) * omegaBar := by
    calc
      z * ((1 : E) + ((B : F) : E) * ((x : F) : E)) * phi b =
          z * phi b + z * ((x : F) : E) * (((B : F) : E) * phi b) := by
        ring
      _ = (((x : F) : E) * T (phi b) + omegaBar) +
          z * ((x : F) : E) * (z⁻¹ * T (phi b) + omegaBar) := by
        rw [h5, h6]
      _ = ((1 : E) + z * ((x : F) : E)) * omegaBar := by
        field_simp [hzeta_ne]
        ring_nf
        simp [htwo]
  have hPlinear' :
      ((1 : E) + ((B : F) : E) * ((x : F) : E)) * phi b =
        (z⁻¹ + ((x : F) : E)) * omegaBar := by
    calc
      ((1 : E) + ((B : F) : E) * ((x : F) : E)) * phi b =
          z⁻¹ *
            (z * ((1 : E) + ((B : F) : E) * ((x : F) : E)) * phi b) := by
        field_simp [hzeta_ne]
      _ = z⁻¹ * ((1 : E) + z * ((x : F) : E)) * omegaBar := by
        rw [hPlinear]
        ring
      _ = (z⁻¹ + ((x : F) : E)) * omegaBar := by
        field_simp [hzeta_ne]
  have hP :
      phi b =
        (z⁻¹ + ((x : F) : E)) /
            ((1 : E) + ((B : F) : E) * ((x : F) : E)) * omegaBar := by
    calc
      phi b =
          ((z⁻¹ + ((x : F) : E)) * omegaBar) /
            ((1 : E) + ((B : F) : E) * ((x : F) : E)) := by
        apply (eq_div_iff hden).2
        calc
          phi b * ((1 : E) + ((B : F) : E) * ((x : F) : E)) =
              ((1 : E) + ((B : F) : E) * ((x : F) : E)) * phi b :=
            mul_comm _ _
          _ = (z⁻¹ + ((x : F) : E)) * omegaBar := hPlinear'
      _ = (z⁻¹ + ((x : F) : E)) /
            ((1 : E) + ((B : F) : E) * ((x : F) : E)) * omegaBar := by
        ring
  have hM :
      T (phi b) =
        (((B : F) : E) + z) /
            ((1 : E) + ((B : F) : E) * ((x : F) : E)) * omegaBar := by
    calc
      T (phi b) = z * (((B : F) : E) * phi b + omegaBar) := by
        rw [h6]
        field_simp [hzeta_ne]
        ring_nf
        simp [htwo]
      _ = z * (((B : F) : E) *
            ((z⁻¹ + ((x : F) : E)) /
              ((1 : E) + ((B : F) : E) * ((x : F) : E)) * omegaBar) +
            omegaBar) := by rw [hP]
      _ = (((B : F) : E) + z) /
            ((1 : E) + ((B : F) : E) * ((x : F) : E)) * omegaBar := by
        field_simp [hzeta_ne, hden]
        ring_nf
        simp [htwo]
  let denF : F := 1 + B * x
  have hdenF : denF ≠ 0 := by
    intro hdenFzero
    apply hden
    exact_mod_cast hdenFzero
  have hPden :
      phi b =
        (z⁻¹ + ((x : F) : E)) / ((denF : F) : E) * omegaBar := by
    simpa [denF] using hP
  have hMden :
      T (phi b) =
        (((B : F) : E) + z) / ((denF : F) : E) * omegaBar := by
    simpa [denF] using hM
  have hPmu :
      T (phi b) =
        (z⁻¹ + ((mu x : F) : E)) / ((mu denF : F) : E) * omegaBar := by
    rw [hPden]
    rw [hT_semilinear, hT_omega]
    simp only [map_div₀, map_add, map_inv₀, hmu_zeta, hmu_coe]
  have hratios :
      (z⁻¹ + ((mu x : F) : E)) / ((mu denF : F) : E) =
        (((B : F) : E) + z) / ((denF : F) : E) := by
    apply mul_right_cancel₀ homegaBar_ne
    exact hPmu.symm.trans hMden
  let lambda : F := mu denF / denF
  have h9 :
      z⁻¹ + ((mu x : F) : E) =
        ((lambda : F) : E) * (((B : F) : E) + z) := by
    dsimp only [lambda]
    have hmu_denF : mu denF ≠ 0 := (map_ne_zero mu).2 hdenF
    have hdenFE : ((denF : F) : E) ≠ 0 := by exact_mod_cast hdenF
    have hmu_denFE : ((mu denF : F) : E) ≠ 0 := by
      exact_mod_cast hmu_denF
    have hcross :=
      (div_eq_div_iff hmu_denFE hdenFE).mp hratios
    change z⁻¹ + ((mu x : F) : E) =
      (((mu denF : F) : E) / ((denF : F) : E)) *
        (((B : F) : E) + z)
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hdenFE).2
    calc
      (z⁻¹ + ((mu x : F) : E)) * ((denF : F) : E) =
          (((B : F) : E) + z) * ((mu denF : F) : E) := hcross
      _ = ((mu denF : F) : E) * (((B : F) : E) + z) := mul_comm _ _
  have hlin :
      ((1 : E) + ((lambda : F) : E)) * z =
        ((c : F) : E) + ((mu x : F) : E) +
          ((lambda : F) : E) * ((B : F) : E) := by
    calc
      ((1 : E) + ((lambda : F) : E)) * z =
          z + ((lambda : F) : E) * z := by ring
      _ = z +
          (((lambda : F) : E) * (((B : F) : E) + z) +
            ((lambda : F) : E) * ((B : F) : E)) := by
        congr 1
        ring_nf
        simp [htwo]
      _ = z +
          ((z⁻¹ + ((mu x : F) : E)) +
            ((lambda : F) : E) * ((B : F) : E)) := by
        rw [← h9]
      _ = (z + z⁻¹) + ((mu x : F) : E) +
          ((lambda : F) : E) * ((B : F) : E) := by ring
      _ = ((c : F) : E) + ((mu x : F) : E) +
          ((lambda : F) : E) * ((B : F) : E) := by rw [← hc]
  have hlambda : lambda = 1 := by
    by_contra hlambda_ne
    have hcoeff_ne : (1 : F) + lambda ≠ 0 := by
      intro hzero
      apply hlambda_ne
      exact (CharTwo.add_eq_zero.mp hzero).symm
    have hcoeffE_ne : (((1 : F) + lambda : F) : E) ≠ 0 := by
      exact_mod_cast hcoeff_ne
    let q : F :=
      (c + mu x + lambda * B) / ((1 : F) + lambda)
    have hz_eq : z = ((q : F) : E) := by
      change z =
        (((c + mu x + lambda * B : F) : E) /
          ((((1 : F) + lambda : F) : E)))
      apply (eq_div_iff hcoeffE_ne).2
      calc
        z * ((((1 : F) + lambda : F) : E)) =
            ((((1 : F) + lambda : F) : E)) * z := mul_comm _ _
        _ = ((c : F) : E) + ((mu x : F) : E) +
              ((lambda : F) : E) * ((B : F) : E) := by
          simpa only [Subfield.coe_add, Subfield.coe_one] using hlin
        _ = ((c + mu x + lambda * B : F) : E) := by norm_cast
    apply hzeta_not_mem
    rw [hz_eq]
    exact q.property
  have hmu_c : mu c = c := by
    apply F.subtype.injective
    calc
      ((mu c : F) : E) = muE ((c : F) : E) := (hmu_coe c).symm
      _ = muE (z + z⁻¹) := by rw [← hc]
      _ = z + z⁻¹ := by simp only [map_add, map_inv₀, hmu_zeta]
      _ = ((c : F) : E) := hc.symm
  have h9one :
      z⁻¹ + ((mu x : F) : E) = ((B : F) : E) + z := by
    simpa [hlambda] using h9
  have hB_mu_E :
      ((B : F) : E) + ((mu x : F) : E) = ((c : F) : E) := by
    calc
      ((B : F) : E) + ((mu x : F) : E) =
          (((B : F) : E) + z) + (z + ((mu x : F) : E)) := by
        ring_nf
        simp [htwo]
      _ = (z⁻¹ + ((mu x : F) : E)) +
          (z + ((mu x : F) : E)) := by rw [← h9one]
      _ = z⁻¹ + z := by
        ring_nf
        simp [htwo]
      _ = ((c : F) : E) := by simpa only [add_comm] using hc.symm
  have hB_mu : B + mu x = c := by
    apply F.subtype.injective
    change ((B : F) : E) + ((mu x : F) : E) = (c : E)
    exact hB_mu_E
  have hB_eq : B = c + mu x := by
    calc
      B = c - mu x := (eq_sub_iff_add_eq).2 hB_mu
      _ = c + mu x := CharTwo.sub_eq_add _ _
  have hmu_denF : mu denF = denF := by
    have h := hlambda
    dsimp only [lambda] at h
    exact (div_eq_one_iff_eq hdenF).mp h
  have hmuB_eq : mu B = c + mu (mu x) := by
    rw [hB_eq, map_add, hmu_c]
  have hmu_den_expanded :
      1 + mu B * mu x = 1 + B * x := by
    simpa [denF] using hmu_denF
  have hprod : B * x = mu B * mu x :=
    add_left_cancel hmu_den_expanded.symm
  have h10F :
      (c + mu x) * x = (c + mu (mu x)) * mu x := by
    rw [← hB_eq, ← hmuB_eq]
    exact hprod
  have h10E := congrArg (fun y : F => ((y : F) : E)) h10F
  simpa [hX_eq] using h10E

private theorem subring_closure_eq_top_of_quadratic_generator
    {E : Type*} [Field E] (F : Subfield E)
    (hfinrank : Module.finrank F E = 2)
    (scalarSet : Set E) (z : E)
    (hF : ∀ a : F, (a : E) ∈ Subring.closure scalarSet)
    (hz : z ∈ Subring.closure scalarSet) (hz_not_mem : z ∉ F) :
    Subring.closure scalarSet = ⊤ := by
  let R : Subring E := Subring.closure scalarSet
  let A : Subalgebra F E :=
    { carrier := R
      zero_mem' := R.zero_mem
      add_mem' := fun hx hy => R.add_mem hx hy
      one_mem' := R.one_mem
      mul_mem' := fun hx hy => R.mul_mem hx hy
      algebraMap_mem' := hF }
  have hprime : Nat.Prime (Module.finrank F E) :=
    hfinrank.symm ▸ Nat.prime_two
  letI : IsSimpleOrder (Subalgebra F E) :=
    Subalgebra.isSimpleOrder_of_finrank_prime F E hprime
  have hA_ne_bot : A ≠ ⊥ := by
    intro hA
    have hzbot : z ∈ (⊥ : Subalgebra F E) := by
      rw [← hA]
      exact hz
    rcases hzbot with ⟨a, ha⟩
    apply hz_not_mem
    rw [← ha]
    exact a.property
  have hA_top : A = ⊤ := (eq_bot_or_eq_top A).resolve_left hA_ne_bot
  ext x
  constructor
  · intro _
    trivial
  · intro _
    have hxA : x ∈ A := by rw [hA_top]; trivial
    exact hxA

private theorem semilinear_hom_of_normal_scalar_action
    {A U E : Type*} [Group A] [Group U] [Field E] [Finite E]
    (T : Subgroup U) [T.Normal]
    (qadd : A ≃* Multiplicative E)
    (rho : U →* (A ≃* A))
    (scalar : T →* Eˣ)
    (hscalar : ∀ (t : T) (x : A),
      qadd (rho (t : U)⁻¹ x) =
        Multiplicative.ofAdd
          ((scalar t : E) * Multiplicative.toAdd (qadd x)))
    (scalarSet : Set E)
    (hscalarSet : scalarSet = Set.range (fun t : T => (scalar t : E)))
    (hclosure : Subring.closure scalarSet = ⊤)
    (s : A) (hs : s ≠ 1) :
    ∃ sigmaHom : U →* (E ≃+* E),
      (∀ (u : U) (lambda : E) (x : A),
          rho u
              (qadd.symm
                (Multiplicative.ofAdd
                  (lambda * Multiplicative.toAdd (qadd x)))) =
            qadd.symm
              (Multiplicative.ofAdd
                (sigmaHom u lambda *
                  Multiplicative.toAdd (qadd (rho u x))))) ∧
        ∀ (u : U) (t : T),
          sigmaHom u (scalar t : E) =
            (scalar
              ⟨u * (t : U) * u⁻¹,
                (inferInstance : T.Normal).conj_mem
                  (t : U) t.property u⟩ : E) := by
  classical
  let q0add : (⊤ : Subgroup A) ≃* Multiplicative E :=
    Subgroup.topEquiv.trans qadd
  let liftTop (f : A ≃* A) : (⊤ : Subgroup A) ≃* (⊤ : Subgroup A) :=
    Subgroup.topEquiv.trans (f.trans Subgroup.topEquiv.symm)
  let uadd : U →* ((⊤ : Subgroup A) ≃* (⊤ : Subgroup A)) :=
    { toFun := fun u => liftTop (rho u)
      map_one' := by
        ext x
        simp [liftTop]
      map_mul' := by
        intro u v
        ext x
        simp [liftTop] }
  have hscalar_eq_action (t : T) (x : (⊤ : Subgroup A)) :
      q0add.symm
          (Multiplicative.ofAdd
            ((scalar t : E) * Multiplicative.toAdd (q0add x))) =
        uadd (t : U)⁻¹ x := by
    apply Subtype.ext
    change qadd.symm
        (Multiplicative.ofAdd
          ((scalar t : E) * Multiplicative.toAdd (qadd (x : A)))) =
      rho (t : U)⁻¹ (x : A)
    apply qadd.injective
    rw [qadd.apply_symm_apply]
    exact (hscalar t (x : A)).symm
  have hconjT : ∀ (u : U) (lambda : E), lambda ∈ scalarSet →
      ∃ c : E, ∀ x : (⊤ : Subgroup A),
        uadd u
            (q0add.symm
              (Multiplicative.ofAdd
                (lambda * Multiplicative.toAdd (q0add x)))) =
          q0add.symm
            (Multiplicative.ofAdd
              (c * Multiplicative.toAdd (q0add (uadd u x)))) := by
    intro u lambda hlambda
    rw [hscalarSet] at hlambda
    rcases hlambda with ⟨t, rfl⟩
    let t' : T :=
      ⟨u * (t : U) * u⁻¹,
        (inferInstance : T.Normal).conj_mem (t : U) t.property u⟩
    refine ⟨(scalar t' : E), ?_⟩
    intro x
    rw [hscalar_eq_action, hscalar_eq_action]
    calc
      uadd u (uadd (t : U)⁻¹ x) = uadd (u * (t : U)⁻¹) x := by
        rw [map_mul]
        rfl
      _ = uadd ((t' : U)⁻¹ * u) x := by
        congr 2
        simp [t', mul_assoc]
      _ = uadd (t' : U)⁻¹ (uadd u x) := by
        rw [map_mul]
        rfl
  let sTop : (⊤ : Subgroup A) := ⟨s, trivial⟩
  have hsTop : (sTop : A) ≠ 1 := hs
  rcases PFAppendixI.peterfalvi_appendixI_proposition_2_b_semilinear_hom
      (⊤ : Subgroup A) q0add uadd sTop hsTop scalarSet hclosure hconjT with
    ⟨sigmaHom, hsemi⟩
  refine ⟨sigmaHom, ?_, ?_⟩
  · intro u lambda x
    let xTop : (⊤ : Subgroup A) := ⟨x, trivial⟩
    have h := hsemi u lambda xTop
    simpa [q0add, uadd, liftTop, xTop] using congrArg Subtype.val h
  · intro u t
    let t' : T :=
      ⟨u * (t : U) * u⁻¹,
        (inferInstance : T.Normal).conj_mem (t : U) t.property u⟩
    have haction :
        uadd u
            (q0add.symm
              (Multiplicative.ofAdd
                ((scalar t : E) * Multiplicative.toAdd (q0add sTop)))) =
          q0add.symm
            (Multiplicative.ofAdd
              ((scalar t' : E) *
                Multiplicative.toAdd (q0add (uadd u sTop)))) := by
      rw [hscalar_eq_action, hscalar_eq_action]
      calc
        uadd u (uadd (t : U)⁻¹ sTop) =
            uadd (u * (t : U)⁻¹) sTop := by
          rw [map_mul]
          rfl
        _ = uadd ((t' : U)⁻¹ * u) sTop := by
          congr 2
          simp [t', mul_assoc]
        _ = uadd (t' : U)⁻¹ (uadd u sTop) := by
          rw [map_mul]
          rfl
    have hsemis := hsemi u (scalar t : E) sTop
    have hprod :
        sigmaHom u (scalar t : E) *
            Multiplicative.toAdd (q0add (uadd u sTop)) =
          (scalar t' : E) *
            Multiplicative.toAdd (q0add (uadd u sTop)) := by
      have heq := q0add.symm.injective (hsemis.symm.trans haction)
      exact congrArg Multiplicative.toAdd heq
    have hu_s_ne : uadd u sTop ≠ 1 := by
      intro hu
      apply hsTop
      have hback := congrArg (fun x => uadd u⁻¹ x) hu
      simpa using hback
    have hq_ne : q0add (uadd u sTop) ≠ 1 := by
      simpa using hu_s_ne
    have hv_ne : Multiplicative.toAdd (q0add (uadd u sTop)) ≠ 0 := by
      intro hv
      apply hq_ne
      apply Multiplicative.toAdd.injective
      simpa using hv
    exact mul_right_cancel₀ hv_ne hprod

private theorem quotient_mulEquiv_multiplicative_of_additive_coordinate
    {G E : Type*} [Group G] [Finite G] [Field E] [Finite E]
    (Q Q0 : Subgroup G) (_hQ0Q : Q0 ≤ Q)
    (bar : G → E)
    (hbar_mul : ∀ x : G, x ∈ Q → ∀ y : G, y ∈ Q →
      bar (x * y) = bar x + bar y)
    (hbar_Q0 : ∀ x : G, x ∈ Q → (bar x = 0 ↔ x ∈ Q0))
    [hQ0Q_normal : (Q0.subgroupOf Q).Normal]
    (hcard : Nat.card (Q ⧸ Q0.subgroupOf Q) = Nat.card E) :
    ∃ qbar : (Q ⧸ Q0.subgroupOf Q) ≃* Multiplicative E,
      ∀ q : Q,
        Multiplicative.toAdd
            (qbar (QuotientGroup.mk' (Q0.subgroupOf Q) q)) =
          bar (q : G) := by
  classical
  let Q0Q : Subgroup Q := Q0.subgroupOf Q
  letI : Q0Q.Normal := hQ0Q_normal
  let barHom : Q →* Multiplicative E :=
    { toFun := fun q => Multiplicative.ofAdd (bar (q : G))
      map_one' := by
        change Multiplicative.ofAdd (bar (1 : G)) = 1
        rw [(hbar_Q0 1 Q.one_mem).2 Q0.one_mem]
        rfl
      map_mul' := by
        intro x y
        change Multiplicative.ofAdd (bar ((x : G) * (y : G))) =
          Multiplicative.ofAdd (bar (x : G)) *
            Multiplicative.ofAdd (bar (y : G))
        rw [hbar_mul (x : G) x.property (y : G) y.property]
        rfl }
  have hbarHom_ker : barHom.ker = Q0Q := by
    ext q
    change Multiplicative.ofAdd (bar (q : G)) = 1 ↔ (q : G) ∈ Q0
    rw [← (hbar_Q0 (q : G) q.property)]
    rfl
  have hQ0Q_le_ker : Q0Q ≤ barHom.ker := by rw [hbarHom_ker]
  let qbarHom : (Q ⧸ Q0Q) →* Multiplicative E :=
    QuotientGroup.lift Q0Q barHom hQ0Q_le_ker
  have hqbarHom_ker : qbarHom.ker = ⊥ := by
    change (QuotientGroup.lift Q0Q barHom hQ0Q_le_ker).ker = ⊥
    rw [QuotientGroup.ker_lift, hbarHom_ker,
      QuotientGroup.map_mk'_self]
  have hqbarHom_injective : Function.Injective qbarHom :=
    (MonoidHom.ker_eq_bot_iff qbarHom).mp hqbarHom_ker
  have hcard' : Nat.card (Multiplicative E) = Nat.card (Q ⧸ Q0Q) := by
    rw [Nat.card_congr Multiplicative.toAdd]
    exact hcard.symm
  have hqbarHom_bijective : Function.Bijective qbarHom :=
    hqbarHom_injective.bijective_of_nat_card_le (by rw [hcard'])
  let qbar : (Q ⧸ Q0Q) ≃* Multiplicative E :=
    MulEquiv.ofBijective qbarHom hqbarHom_bijective
  refine ⟨qbar, ?_⟩
  intro q
  rfl

open PFchapter1section1 PFchapter1section3 PFAppendixIII
open PFchapter3section1 PFchapter3section3 PFchapter4section2 PFchapter4section3

set_option maxHeartbeats 800000

/--
The V != W endpoint of Chapter IV.

Peterfalvi first obtains a prime-order subgroup from failure of the
fixed-point-free quotient alternative, conjugates it into V, and proves it
disjoint from W. That selection is internal rather than data supplied by
Suzuki's theorem.
-/
public theorem case_v_ne_w
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [Finite Omega]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G) (f g h : G → G)
    (hsection3 : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA
      G Omega H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧
      _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔
                x = 1 ∨ (x ∈ H ∧
                  _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q,
                      S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ a : G, a ∈ S → ∀ b : G, b ∈ Q1 →
                            a * b = b * a) ∧
                            S ⊔ Q1 = Q) ∧
      s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
        ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hC1 : HypothesisC1 G V) (hC2 : HypothesisC2 G S W t s)
    (hC3 : TypeBChapter3Data G K Q0 S W s)
    (hind :
      ∀ (L : Type u) [Group L] [Finite L],
        ∀ (OmegaL : Type v) [MulAction L OmegaL] [Finite OmegaL]
          (HL DL QL : Subgroup L) (tL : L),
          Nat.card L < Nat.card G →
            HypothesisA L OmegaL HL DL QL tL →
              suzukiConclusion.{u, v} L OmegaL)
    (hQ_two : IsPGroup 2 Q)
    (hf_mem : ∀ x : G, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : G, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : G, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : G, x ∈ Q → x ≠ 1 →
      t * x * t = g x * h x * t * f x)
    (_hV_ne_W : V ≠ W) :
    suzukiConclusion.{u, v} G Omega := by
  classical
  by_cases hD_fixed_point_free :
      ∀ d : G, d ∈ D → d ≠ 1 →
        ∀ x : G, x ∈ Q → x ∉ Q0 →
          rightConjugateElem x d * x⁻¹ ∉ Q0
  · obtain ⟨L, hL, q, _hL_eq, hodd, hq, hq_gt, hunitary⟩ :=
      PFchapter4section3.corollary_1_of_fixed_point_free
        H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2 hC3 hQ_two
          hf_mem hg_mem hh_mem hcanonical_eq hD_fixed_point_free
    exact ⟨L, hL, q, hodd, hq, hq_gt, Or.inr (Or.inr hunitary)⟩
  · push Not at hD_fixed_point_free
    obtain ⟨d, hdD, hd_ne, x, hxQ, hx_not_Q0, hdx⟩ :=
      hD_fixed_point_free
    have hA1 := hsection3.section2.hA.A1
    have hQ0_commutes_Q : ∀ z : G, z ∈ Q0 → ∀ y : G, y ∈ Q →
        z * y = y * z :=
      PFchapter4section2.Q0_commutes_Q
        H D Q K V W Q0 S Q1 t s hsection3 hC2
    have hQ0_stable_D : ∀ a : D, ∀ z : Q0,
        rightConjugateElem (z : G) (a : G)⁻¹ ∈ Q0 := by
      intro a z
      rcases (hsection3.section2.Q0_def (z : G)).1 z.property with
        hz_one | ⟨hzH, hzI⟩
      · rw [hz_one]
        simp [rightConjugateElem]
      · apply (hsection3.section2.Q0_def _).2
        refine Or.inr ⟨?_, isInvolution_rightConjugateElem hzI⟩
        have haH : (a : G) ∈ H := hA1.D_le_H a.property
        exact H.mul_mem
          (H.mul_mem (H.inv_mem (H.inv_mem haH)) hzH) (H.inv_mem haH)
    let Q0Q : Subgroup Q := Q0.subgroupOf Q
    have hQ0Q_normal : Q0Q.Normal := by
      apply (Subgroup.normal_subgroupOf_iff_le_normalizer
        hsection3.section2.Q0_le_Q).2
      intro q hqQ
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hzQ0
        have hcomm := hQ0_commutes_Q z hzQ0 q hqQ
        have hconj : q * z * q⁻¹ = z := by
          rw [← hcomm]
          simp
        simpa [hconj] using hzQ0
      · intro hzQ0
        have hcomm := hQ0_commutes_Q (q * z * q⁻¹) hzQ0 q hqQ
        have hz_eq : z = q * z * q⁻¹ := by
          calc
            z = q⁻¹ * (q * z * q⁻¹) * q := by group
            _ = q⁻¹ * ((q * z * q⁻¹) * q) := by rw [mul_assoc]
            _ = q⁻¹ * (q * (q * z * q⁻¹)) := by rw [hcomm]
            _ = q * z * q⁻¹ := by group
        rwa [hz_eq]
    letI : Q0Q.Normal := hQ0Q_normal
    have hD_normalizes_Q : D ≤ Subgroup.normalizer Q :=
      hA1.D_le_H.trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hA1.Q_le_H).1
          hA1.Q_normal_in_H)
    letI : MulDistribMulAction D Q :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer
        (G := G) D Q hD_normalizes_Q
    have hD_smul_coe : ∀ (a : D) (q : Q),
        ((a • q : Q) : G) = (a : G) * (q : G) * (a : G)⁻¹ := by
      intro a q
      exact Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit
        D Q hD_normalizes_Q a q
    have hQ0Q_invariant_D : IsInvariant D Q Q0Q := by
      refine ⟨?_⟩
      have hforward : ∀ (a : D) (q : Q), q ∈ Q0Q → a • q ∈ Q0Q := by
        intro a q hq
        have hstable := hQ0_stable_D a ⟨q, hq⟩
        change (a : G) * (q : G) * (a : G)⁻¹ ∈ Q0
        simpa [rightConjugateElem, mul_assoc] using hstable
      intro a q
      constructor
      · exact hforward a q
      · intro haq
        have hinv : a⁻¹ • (a • q) ∈ Q0Q := hforward a⁻¹ (a • q) haq
        simpa using hinv
    letI : MulAction.QuotientAction D Q0Q :=
      quotientAction_of_isInvariant (A := D) (G := Q) Q0Q hQ0Q_invariant_D
    letI : MulDistribMulAction D (Q ⧸ Q0Q) :=
      quotientMulDistribMulAction (A := D) (G := Q) Q0Q hQ0Q_invariant_D
    let xQ : Q := ⟨x, hxQ⟩
    let xbar : Q ⧸ Q0Q := QuotientGroup.mk' Q0Q xQ
    have hxbar_ne : xbar ≠ 1 := by
      intro hxbar
      apply hx_not_Q0
      exact (QuotientGroup.eq_one_iff xQ).1 hxbar
    let dD : D := ⟨d⁻¹, D.inv_mem hdD⟩
    have hdD_ne : dD ≠ 1 := by
      intro hdD_one
      apply hd_ne
      have : d⁻¹ = 1 := congrArg Subtype.val hdD_one
      simpa using congrArg Inv.inv this
    have hdD_fix : dD • xbar = xbar := by
      change QuotientGroup.mk' Q0Q (dD • xQ) = QuotientGroup.mk' Q0Q xQ
      apply (QuotientGroup.eq_iff_div_mem).2
      have hcoe := hD_smul_coe dD xQ
      change (((dD • xQ) / xQ : Q) : G) ∈ Q0
      simpa [Subgroup.coe_div, hcoe, dD, xQ, div_eq_mul_inv,
        rightConjugateElem, mul_assoc] using hdx
    let A_D : Subgroup D := MulAction.stabilizer D xbar
    let A : Subgroup G := A_D.map D.subtype
    have hd_mem_A : d⁻¹ ∈ A := by
      refine ⟨dD, ?_, rfl⟩
      simpa [A_D, MulAction.mem_stabilizer_iff] using hdD_fix
    have hA_ne : A ≠ ⊥ := by
      apply Subgroup.ne_bot_iff_exists_ne_one.mpr
      refine ⟨⟨d⁻¹, hd_mem_A⟩, ?_⟩
      intro hd_inv_one
      apply hd_ne
      have hd_inv_one_G : d⁻¹ = 1 := congrArg Subtype.val hd_inv_one
      simpa using congrArg Inv.inv hd_inv_one_G
    let p := (Nat.card A).minFac
    have hp_prime : Nat.Prime p :=
      Nat.minFac_prime (A.one_lt_card_iff_ne_bot.mpr hA_ne).ne'
    letI : Fact (Nat.Prime p) := ⟨hp_prime⟩
    obtain ⟨a, ha_order⟩ :=
      exists_prime_orderOf_dvd_card' (G := A) p
        (Nat.minFac_dvd (Nat.card A))
    let P : Subgroup G := Subgroup.zpowers (a : G)
    have hP_le_A : P ≤ A := Subgroup.zpowers_le.mpr a.property
    have hP_le_D : P ≤ D := by
      intro y hy
      rcases hP_le_A hy with ⟨yD, _hyA, rfl⟩
      exact yD.property
    have hP_card : Nat.card P = p := by
      calc
        Nat.card P = orderOf (a : G) := Nat.card_zpowers (a : G)
        _ = orderOf a := Subgroup.orderOf_coe a
        _ = p := ha_order
    let pToD : P →* D := Subgroup.inclusion hP_le_D
    letI : MulDistribMulAction P Q :=
      MulDistribMulAction.compHom Q pToD
    have hQ0Q_invariant_P : IsInvariant P Q Q0Q := by
      refine ⟨?_⟩
      intro y q
      simpa [MulAction.compHom_smul_def] using
        (IsInvariant.invariant (A := D) (G := Q) (H := Q0Q) (pToD y) q)
    letI : MulAction.QuotientAction P Q0Q :=
      quotientAction_of_isInvariant (A := P) (G := Q) Q0Q hQ0Q_invariant_P
    letI : MulDistribMulAction P (Q ⧸ Q0Q) :=
      quotientMulDistribMulAction (A := P) (G := Q) Q0Q hQ0Q_invariant_P
    have hP_to_stabilizer : ∀ y : P, pToD y ∈ A_D := by
      intro y
      rcases hP_le_A y.property with ⟨z, hzA_D, hz_eq⟩
      have hy_eq : pToD y = z := by
        apply Subtype.ext
        exact hz_eq.symm
      simpa [hy_eq] using hzA_D
    have hxbar_fixed_P : xbar ∈ fixedPointSubgroup P (Q ⧸ Q0Q) := by
      intro y
      have hy_stab := hP_to_stabilizer y
      have hy_fix : pToD y • xbar = xbar := by
        simpa [A_D, MulAction.mem_stabilizer_iff] using hy_stab
      change y • xbar = xbar at hy_fix
      exact hy_fix
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI : Group.IsNilpotent Q := hQ_two.isNilpotent
    have hQ_solvable : Group.IsSolvable Q := by infer_instance
    have hp_dvd_D : p ∣ Nat.card D := by
      rw [← hP_card]
      exact Subgroup.card_dvd_of_le hP_le_D
    have hp_odd : Odd p := hA1.D_odd.of_dvd_nat hp_dvd_D
    have hP_Q_coprime : Nat.Coprime (Nat.card P) (Nat.card Q) := by
      rcases (IsPGroup.iff_card).1 hQ_two with ⟨n, hn⟩
      rw [hP_card, hn]
      exact hp_odd.coprime_two_right.pow_right n
    have hfixed_quotient :=
      fixedPointSubgroup_quotient_eq_map_of_solvable_coprime_action
        (G := Q) (A := P) hQ_solvable hP_Q_coprime
          (∅ : Set Nat.Primes) Q0Q hQ0Q_invariant_P
    have hxbar_map : xbar ∈
        (fixedPointSubgroup P Q).map (QuotientGroup.mk' Q0Q) := by
      rw [← hfixed_quotient]
      exact hxbar_fixed_P
    rcases Subgroup.mem_map.mp hxbar_map with ⟨q, hq_fixed, hq_bar⟩
    have hq_not_Q0 : (q : G) ∉ Q0 := by
      intro hqQ0
      have hqbar_one : QuotientGroup.mk' Q0Q q = 1 :=
        (QuotientGroup.eq_one_iff q).2 hqQ0
      apply hxbar_ne
      calc
        xbar = QuotientGroup.mk' Q0Q q := hq_bar.symm
        _ = 1 := hqbar_one
    have hq_ne : (q : G) ≠ 1 := by
      intro hq_one
      apply hq_not_Q0
      simp [hq_one]
    have hq_centralizer : (q : G) ∈
        Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hyP
      let yP : P := ⟨y, hyP⟩
      have hy_fix : yP • q = q := hq_fixed yP
      have hconj : y * (q : G) * y⁻¹ = (q : G) := by
        calc
          y * (q : G) * y⁻¹ =
              ((pToD yP • q : Q) : G) := by
                symm
                exact hD_smul_coe (pToD yP) q
          _ = (q : G) := congrArg Subtype.val hy_fix
      have hcomm := congrArg (fun z : G => z * y) hconj
      simpa [mul_assoc] using hcomm
    have hfixed_card :
        3 ≤ Nat.card {omega : Omega //
          omega ∈ fixedPointsOfSubgroup G Omega P} :=
      fixed_point_card_ge_three_of_centralizer_Q
        H D Q P t (q : G) hA1 hP_le_D q.property hq_ne hq_centralizer
    obtain ⟨c, hcV⟩ :=
      PFchapter1section1.proposition_6_c H D Q P t hA1 hP_le_D hfixed_card
    let X : Subgroup G := rightConjugate P (c : G)
    have hX_le_V : X ≤ V := by
      rw [hsection3.section2.V_eq]
      exact hcV
    have hX_card : Nat.card X = Nat.card P := by
      change Nat.card (rightConjugate P (c : G)) = Nat.card P
      rw [rightConjugate, Subgroup.conjBy]
      exact Nat.card_congr
        (Subgroup.equivMapOfInjective P
          (MulAut.conj (c : G)⁻¹).toMonoidHom
          (MulAut.conj (c : G)⁻¹).injective).symm.toEquiv
    have hX_card_prime : Nat.card X = p := hX_card.trans hP_card
    have hX_ne : X ≠ ⊥ := by
      intro hX_bot
      apply hp_prime.ne_one
      calc
        p = Nat.card X := hX_card_prime.symm
        _ = 1 := by rw [hX_bot]; simp
    let qX : G := rightConjugateElem (q : G) (c : G)
    have hqX_mem_Q : qX ∈ Q := by
      have hqX_eq : qX = ((c⁻¹ • q : Q) : G) := by
        calc
          qX = (c : G)⁻¹ * (q : G) * (c : G) := by
            rfl
          _ = ((c⁻¹ • q : Q) : G) := by
            simpa only [Subgroup.coe_inv, inv_inv] using
              (hD_smul_coe c⁻¹ q).symm
      rw [hqX_eq]
      exact (c⁻¹ • q : Q).property
    have hqX_not_Q0 : qX ∉ Q0 := by
      intro hqXQ0
      apply hq_not_Q0
      have hback := hQ0_stable_D c ⟨qX, hqXQ0⟩
      simpa [qX, rightConjugateElem, mul_assoc] using hback
    have hqX_ne : qX ≠ 1 := by
      intro hqX_one
      apply hq_ne
      calc
        (q : G) = (c : G) * qX * (c : G)⁻¹ := by
          simp [qX, rightConjugateElem, mul_assoc]
        _ = 1 := by rw [hqX_one]; simp
    have hqX_centralizer : qX ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hyX
      change y ∈ rightConjugate P (c : G) at hyX
      rw [rightConjugate] at hyX
      change y ∈ P.map (MulAut.conj (c : G)⁻¹).toMonoidHom at hyX
      rcases Subgroup.mem_map.mp hyX with ⟨z, hzP, rfl⟩
      have hzq : z * (q : G) = (q : G) * z :=
        (Subgroup.mem_centralizer_iff.mp hq_centralizer) z hzP
      have hconj :=
        congrArg (fun w : G => (c : G)⁻¹ * w * (c : G)) hzq
      simpa [MulAut.conj_apply, qX, rightConjugateElem, mul_assoc] using hconj
    obtain ⟨T, hS_eq⟩ := hsection3.section2.S_sylow_in_Q
    have hT_top : (T : Subgroup Q) = ⊤ :=
      (T.is_maximal' (hQ_two.to_subgroup ⊤) le_top).symm
    have hSQ : S = Q := by
      rw [hS_eq, hT_top]
      ext y
      constructor
      · rintro ⟨y, _hy, rfl⟩
        exact y.property
      · intro hy
        exact ⟨⟨y, hy⟩, trivial, rfl⟩
    have hSuzukiS : IsSuzukiTwoGroup S := by
      rcases PFchapter1section2.corollary
          H D Q K V W Q0 S Q1 t hsection3.section2 with hcomm | hSuzuki
      · exact False.elim
          (typeB_not_isMulCommutative S hC2.S_type_B hcomm)
      · exact hSuzuki
    have hSuzukiQ : IsSuzukiTwoGroup Q := by
      rw [← hSQ]
      exact hSuzukiS
    have hQ_card_cube : Nat.card Q = Nat.card Q0 ^ 3 :=
      PFchapter4section2.natCard_eq_cube_of_isSuzukiTwoTypeB H Q Q0 S
        hC2.S_type_B hsection3.section2.S_le_Q hA1.Q_le_H
        hsection3.section2.Q0_le_Q hsection3.section2.Q0_def hSQ
    have hX_disjoint_W : Disjoint X W := by
      rw [Subgroup.disjoint_def]
      intro y hyX hyW
      by_contra hy_ne
      have hycentral : qX ∈
          Subgroup.centralizer (Subgroup.zpowers y : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
        have hcomm : Commute y qX :=
          (Subgroup.mem_centralizer_iff.mp hqX_centralizer) y hyX
        exact (hcomm.zpow_left n).eq
      have hcentralizer_eq :=
        PFchapter1section3.lemma_5_nontrivial_W_centralizer_eq_Q0
          H D Q K V W Q0 S Q1 t s y hsection3 hind
            hC2.st_order_three hSuzukiQ hQ_card_cube hyW hy_ne
      have hqX_Q0 : qX ∈ Q0 := by
        rw [← hcentralizer_eq]
        exact ⟨hycentral, hqX_mem_Q⟩
      exact hqX_not_Q0 hqX_Q0
    have hX_two_rank :
        TwoRankAtLeastTwo (Subgroup.centralizer (X : Set G)) :=
      hC1.centralizers_two_rank X hX_le_V
        ⟨p, hp_prime, hX_card_prime⟩
    rcases PFchapter1section3.proposition_1_c.{u, v}
        H D Q K V W Q0 S Q1 X t s hsection3
          (by simpa only [suzukiConclusion] using hind) hX_ne hX_le_V
          hX_two_rank with
      ⟨hCQ1, hlocal_kernel, ell, hell_pow, hell_gt, hell_Q0, hlocal_cases⟩
    rcases hlocal_cases with hpsl | hsuzuki | hpsu
    · rcases hpsl with
        ⟨_k, _hk, _hell, _hmodel, _hst, hCX_elementary, _hCX_card⟩
      let CX : Subgroup G := Subgroup.centralizer (X : Set G) ⊓ Q
      letI : IsElementaryAbelian 2 CX := hCX_elementary
      have hqX_sq : qX ^ 2 = 1 :=
        elemPow_eq_one_of_isElementaryAbelian qX
          (show qX ∈ CX from ⟨hqX_centralizer, hqX_mem_Q⟩)
      have hqX_involution : IsInvolution qX := ⟨hqX_ne, hqX_sq⟩
      exact False.elim (hqX_not_Q0
        ((hsection3.section2.Q0_def qX).2
          (Or.inr ⟨hA1.Q_le_H hqX_mem_Q, hqX_involution⟩)))
    · rcases hsuzuki with
        ⟨_k, _hk, _hell, _hmodel, hst_five, _hCX_type, _hCX_card⟩
      have : (3 : ℕ) = 5 := hC2.st_order_three.symm.trans hst_five
      omega
    · rcases hpsu with
        ⟨E0, hE0Field, hE0Finite, J, hJ, hE0card, hfixedCard,
          hlocalPSU, hst_three, hCX_suzuki, hCX_card, hliftedSeed⟩
      let L : Subgroup G := Subgroup.centralizer (X : Set G)
      let F : Subgroup G := (twoPrimeResidual L).map L.subtype
      let CX : Subgroup G := L ⊓ Q
      let CQ0 : Subgroup G := L ⊓ Q0
      change psuCorollaryTwoLiftedSeed F CX CQ0 V t at hliftedSeed
      rcases hliftedSeed with
        ⟨omega, gamma, zeta1, delta, homega_CX, hgamma_CX,
          hzeta1_F, hzeta1_V, hzeta1_ne, hzeta1_centralizes_CQ0,
          hzeta1_not_center, hdelta_center, hdelta_V,
          hdelta_centralizes_CX, homega_sq, hlocal_seed⟩
      have homega_Q : omega ∈ Q := homega_CX.2
      have homega_ne : omega ≠ 1 := by
        intro homega_one
        apply homega_sq
        simp [homega_one]
      have homega_not_Q0 : omega ∉ Q0 := by
        intro homega_Q0
        rcases (hsection3.section2.Q0_def omega).mp homega_Q0 with
          homega_one | homega_inv
        · exact homega_ne homega_one
        · exact homega_sq homega_inv.2.sq_eq_one
      have hfixed_control :=
        PFchapter1section2.proposition_3_V_inf_centralizer_fixed_Q0_le_sup
          H D Q K V W Q0 S Q1 t hsection3.section2 X hX_le_V
      have hzeta1_fixed : zeta1 ∈
          V ⊓ Subgroup.centralizer
            ((Q0 ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) := by
        refine ⟨hzeta1_V, ?_⟩
        rw [Subgroup.mem_centralizer_iff] at hzeta1_centralizes_CQ0
        change zeta1 ∈ Subgroup.centralizer
          ((Q0 ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro q hq
        exact hzeta1_centralizes_CQ0 q ⟨hq.2, hq.1⟩
      have hdelta_fixed : delta ∈
          V ⊓ Subgroup.centralizer
            ((Q0 ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) := by
        refine ⟨hdelta_V, ?_⟩
        rw [Subgroup.mem_centralizer_iff] at hdelta_centralizes_CX
        change delta ∈ Subgroup.centralizer
          ((Q0 ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro q hq
        exact hdelta_centralizes_CX q
          ⟨hq.2, hsection3.section2.Q0_le_Q hq.1⟩
      have hzeta1_sup : zeta1 ∈ X ⊔ W := hfixed_control hzeta1_fixed
      have hdelta_sup : delta ∈ X ⊔ W := hfixed_control hdelta_fixed
      have hprop3 := PFchapter1section2.proposition_3
        H D Q K V W Q0 S Q1 t hsection3.section2
      rcases hprop3.2 with ⟨hWV, _hVmodW_cyclic⟩
      letI : (W.subgroupOf V).Normal := hWV
      have hX_normalizes_W : X ≤ Subgroup.normalizer (W : Set G) :=
        hX_le_V.trans
          (Subgroup.le_normalizer_of_normal_subgroupOf
            hsection3.section2.W_le_V)
      have hdecomp : ∀ y : G, y ∈ X ⊔ W →
          ∃ w x : G, w ∈ W ∧ x ∈ X ∧ y = w * x := by
        intro y hy
        have hy' : y ∈ W ⊔ X := by simpa [sup_comm] using hy
        change y ∈ ((W ⊔ X : Subgroup G) : Set G) at hy'
        rw [Subgroup.coe_mul_of_right_le_normalizer_left
          W X hX_normalizes_W] at hy'
        rcases Set.mem_mul.mp hy' with ⟨w, hw, x, hx, hvalue⟩
        exact ⟨w, x, hw, hx, hvalue.symm⟩
      rcases hdecomp zeta1 hzeta1_sup with
        ⟨zeta, zetaX, hzeta_W, hzetaX_X, hzeta1_eq⟩
      rcases hdecomp delta hdelta_sup with
        ⟨deltaW, deltaX, hdeltaW_W, hdeltaX_X, hdelta_eq⟩
      have hF_le_L : F ≤ L := by
        intro y hy
        rcases hy with ⟨yL, _hyF, rfl⟩
        exact yL.property
      have hzeta1_not_X : zeta1 ∉ X := by
        intro hzeta1_X
        apply hzeta1_not_center
        let zetaF : F := ⟨zeta1, hzeta1_F⟩
        refine ⟨zetaF, ?_, rfl⟩
        change zetaF ∈ Subgroup.center F
        rw [Subgroup.mem_center_iff]
        intro yF
        have hyL : (yF : G) ∈ L := hF_le_L yF.property
        have hcomm :=
          (Subgroup.mem_centralizer_iff.mp hyL) zeta1 hzeta1_X
        apply Subtype.ext
        exact hcomm.symm
      have hzeta_ne : zeta ≠ 1 := by
        intro hzeta_one
        apply hzeta1_not_X
        have hzeta1_eq_X : zeta1 = zetaX := by
          simpa [hzeta_one] using hzeta1_eq
        rw [hzeta1_eq_X]
        exact hzetaX_X
      letI : IsCyclic X := isCyclic_of_prime_card hX_card_prime
      have hzeta1_centralizes_X : zeta1 ∈
          Subgroup.centralizer (X : Set G) := hF_le_L hzeta1_F
      have hzeta_centralizes_X : zeta ∈
          Subgroup.centralizer (X : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hyX
        have htotal :=
          (Subgroup.mem_centralizer_iff.mp hzeta1_centralizes_X) y hyX
        rw [hzeta1_eq] at htotal
        have hxcomm : y * zetaX = zetaX * y :=
          congrArg Subtype.val
            (mul_comm'
              (⟨y, hyX⟩ : X) (⟨zetaX, hzetaX_X⟩ : X))
        calc
          y * zeta = (y * (zeta * zetaX)) * zetaX⁻¹ := by group
          _ = ((zeta * zetaX) * y) * zetaX⁻¹ := by rw [htotal]
          _ = zeta * (zetaX * y) * zetaX⁻¹ := by group
          _ = zeta * (y * zetaX) * zetaX⁻¹ := by rw [← hxcomm]
          _ = zeta * y := by group
      have hdeltaW_centralizes_omega :
          deltaW * omega = omega * deltaW := by
        have htotal :=
          (Subgroup.mem_centralizer_iff.mp hdelta_centralizes_CX)
            omega homega_CX
        rw [hdelta_eq] at htotal
        have hxcomm : deltaX * omega = omega * deltaX :=
          (Subgroup.mem_centralizer_iff.mp homega_CX.1)
            deltaX hdeltaX_X
        calc
          deltaW * omega =
              (deltaW * omega * deltaX) * deltaX⁻¹ := by group
          _ = (deltaW * (omega * deltaX)) * deltaX⁻¹ := by group
          _ = (deltaW * (deltaX * omega)) * deltaX⁻¹ := by rw [← hxcomm]
          _ = ((deltaW * deltaX) * omega) * deltaX⁻¹ := by group
          _ = (omega * (deltaW * deltaX)) * deltaX⁻¹ := by rw [← htotal]
          _ = omega * deltaW := by group
      have hdeltaW_one : deltaW = 1 := by
        by_contra hdeltaW_ne
        have homega_centralizes_zpowers : omega ∈
            Subgroup.centralizer (Subgroup.zpowers deltaW : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
          have hcomm : Commute deltaW omega :=
            hdeltaW_centralizes_omega
          exact (hcomm.zpow_left n).eq
        have hcentralizer_eq :=
          PFchapter1section3.lemma_5_nontrivial_W_centralizer_eq_Q0
            H D Q K V W Q0 S Q1 t s deltaW hsection3 hind
              hC2.st_order_three hSuzukiQ hQ_card_cube
              hdeltaW_W hdeltaW_ne
        apply homega_not_Q0
        rw [← hcentralizer_eq]
        exact ⟨homega_centralizes_zpowers, homega_Q⟩
      have hdelta_X : delta ∈ X := by
        rw [hdelta_eq, hdeltaW_one, one_mul]
        exact hdeltaX_X
      have hzeta1_D : zeta1 ∈ D := by
        have hzeta1_V' := hzeta1_V
        rw [hsection3.section2.V_eq] at hzeta1_V'
        exact hzeta1_V'.1
      have hdelta_D : delta ∈ D := by
        have hdelta_V' := hdelta_V
        rw [hsection3.section2.V_eq] at hdelta_V'
        exact hdelta_V'.1
      have hright_Q : zeta1⁻¹ * omega⁻¹ * zeta1 ∈ Q := by
        have hzeta_inv_normalizes :=
          hD_normalizes_Q (D.inv_mem hzeta1_D)
        have hmem :=
          (Subgroup.mem_normalizer_iff.mp hzeta_inv_normalizes omega⁻¹).mp
            (Q.inv_mem homega_Q)
        simpa [mul_assoc] using hmem
      have hdelta_comm_t : Commute delta t := by
        have hdelta_V' := hdelta_V
        rw [hsection3.section2.V_eq] at hdelta_V'
        exact Subgroup.mem_centralizer_singleton_iff.mp hdelta_V'.2
      have hdelta_comm_zeta1 : Commute delta zeta1 :=
        (Subgroup.mem_centralizer_iff.mp hzeta1_centralizes_X)
          delta hdelta_X
      have hdelta_comm_omega : Commute delta omega :=
        ((Subgroup.mem_centralizer_iff.mp hdelta_centralizes_CX)
          omega homega_CX).symm
      have hright_comm_delta :
          Commute (zeta1⁻¹ * omega⁻¹ * zeta1) delta :=
        ((hdelta_comm_zeta1.inv_right.mul_right
          hdelta_comm_omega.inv_right).mul_right hdelta_comm_zeta1).symm
      have hlocal_canonical :
          t * omega * t =
            gamma * (zeta1 ^ 3 * delta) * t *
              (zeta1⁻¹ * omega⁻¹ * zeta1) := by
        calc
          t * omega * t =
              gamma * zeta1 ^ 3 * t *
                (zeta1⁻¹ * omega⁻¹ * zeta1) * delta := hlocal_seed
          _ = gamma * zeta1 ^ 3 * t *
                ((zeta1⁻¹ * omega⁻¹ * zeta1) * delta) := by group
          _ = gamma * zeta1 ^ 3 * t *
                (delta * (zeta1⁻¹ * omega⁻¹ * zeta1)) := by
              rw [hright_comm_delta.eq]
          _ = gamma * zeta1 ^ 3 * (t * delta) *
                (zeta1⁻¹ * omega⁻¹ * zeta1) := by group
          _ = gamma * zeta1 ^ 3 * (delta * t) *
                (zeta1⁻¹ * omega⁻¹ * zeta1) := by
              rw [← hdelta_comm_t.eq]
          _ = gamma * (zeta1 ^ 3 * delta) * t *
                (zeta1⁻¹ * omega⁻¹ * zeta1) := by group
      have hglobal_local :
          g omega * h omega * t * f omega =
            gamma * (zeta1 ^ 3 * delta) * t *
              (zeta1⁻¹ * omega⁻¹ * zeta1) :=
        (hcanonical_eq omega homega_Q homega_ne).symm.trans hlocal_canonical
      have hcanonical_parts :=
        PFchapter4section1.qd_t_q_unique
          (M := H) (Q := Q) (D := D) (t := t)
          (q₁ := g omega) (d₁ := h omega) (r₁ := f omega)
          (q₂ := gamma) (d₂ := zeta1 ^ 3 * delta)
          (r₂ := zeta1⁻¹ * omega⁻¹ * zeta1)
          hA1.involution_t.inv_eq_self hA1.D_eq hA1.Q_le_H
          (PFchapter4section1.rankOneSplit_D_le_M hA1.D_eq)
          hA1.Q_disjoint_D
          (hg_mem omega homega_Q homega_ne).1
          (hh_mem omega homega_Q homega_ne)
          (hf_mem omega homega_Q homega_ne).1
          hgamma_CX.2
          (D.mul_mem (D.pow_mem hzeta1_D 3) hdelta_D)
          hright_Q hglobal_local
      have hcomm_zeta_zetaX : Commute zeta zetaX :=
        ((Subgroup.mem_centralizer_iff.mp hzeta_centralizes_X)
          zetaX hzetaX_X).symm
      let eta : G := (zetaX ^ 3 * delta)⁻¹
      have heta_X : eta ∈ X := by
        exact X.inv_mem (X.mul_mem (X.pow_mem hzetaX_X 3) hdelta_X)
      have heta_comm_omega : Commute eta omega :=
        ((Subgroup.mem_centralizer_iff.mp homega_CX.1) eta heta_X)
      have heta_comm_zeta : Commute eta zeta :=
        (Subgroup.mem_centralizer_iff.mp hzeta_centralizes_X) eta heta_X
      have hf_omega :
          f omega = rightConjugateElem omega⁻¹ zeta := by
        have hzetaX_comm_omega : Commute zetaX omega :=
          (Subgroup.mem_centralizer_iff.mp homega_CX.1) zetaX hzetaX_X
        have hzetaX_comm_right :
            Commute zetaX (zeta⁻¹ * omega⁻¹ * zeta) :=
          ((hcomm_zeta_zetaX.symm.inv_right.mul_right
            hzetaX_comm_omega.inv_right).mul_right
              hcomm_zeta_zetaX.symm)
        calc
          f omega = zeta1⁻¹ * omega⁻¹ * zeta1 := hcanonical_parts.2.2
          _ = zetaX⁻¹ * (zeta⁻¹ * omega⁻¹ * zeta) * zetaX := by
            rw [hzeta1_eq]
            group
          _ = zetaX⁻¹ *
                ((zeta⁻¹ * omega⁻¹ * zeta) * zetaX) := by group
          _ = zetaX⁻¹ *
                (zetaX * (zeta⁻¹ * omega⁻¹ * zeta)) := by
            rw [← hzetaX_comm_right.eq]
          _ = zeta⁻¹ * omega⁻¹ * zeta := by group
          _ = rightConjugateElem omega⁻¹ zeta := by rfl
      have hh_omega : h omega = zeta ^ 3 * eta⁻¹ := by
        calc
          h omega = zeta1 ^ 3 * delta := hcanonical_parts.2.1
          _ = (zeta * zetaX) ^ 3 * delta := by rw [hzeta1_eq]
          _ = (zeta ^ 3 * zetaX ^ 3) * delta :=
            congrArg (fun y => y * delta) (hcomm_zeta_zetaX.mul_pow 3)
          _ = zeta ^ 3 * eta⁻¹ := by simp [eta, mul_assoc]
      have hK_inter_W : ∀ x : G, x ∈ K → x ∈ W → x = 1 := by
        intro x hxK hxW
        have hxV : x ∈ V := hsection3.section2.W_le_V hxW
        rw [hsection3.section2.V_eq] at hxV
        have hxt : t * x = x * t :=
          (Subgroup.mem_centralizer_iff.mp hxV.2) t (by simp)
        have hfix : rightConjugateElem x t = x := by
          calc
            rightConjugateElem x t = t⁻¹ * x * t := rfl
            _ = t⁻¹ * (x * t) := by rw [mul_assoc]
            _ = t⁻¹ * (t * x) := by rw [hxt]
            _ = x := by simp
        have hinv : rightConjugateElem x t = x⁻¹ :=
          (hsection3.section2.K_def x).1 hxK |>.2
        have hxinverse : x = x⁻¹ := hfix.symm.trans hinv
        have hx_sq : x ^ 2 = 1 := by
          rw [pow_two]
          nth_rw 1 [hxinverse]
          simp
        let xD : D := ⟨x, hsection3.section2.K_le_D hxK⟩
        have hxD_sq : xD ^ 2 = 1 := by
          apply Subtype.ext
          simpa [xD] using hx_sq
        have horder_two : orderOf xD ∣ 2 :=
          orderOf_dvd_of_pow_eq_one hxD_sq
        have horder_card : orderOf xD ∣ Nat.card D :=
          orderOf_dvd_natCard xD
        have horder_one : orderOf xD = 1 :=
          Nat.eq_one_of_dvd_coprimes hA1.D_odd.coprime_two_right
            horder_card horder_two
        have hxD_one : xD = 1 := orderOf_eq_one_iff.mp horder_one
        exact congrArg Subtype.val hxD_one
      have hC3coord := hC3
      rcases hC3coord with
        ⟨E3, hE3Field, hE3Finite, hE3Char, F3, theta, sigma, phi0,
          K1, W1, S1, hS1Group, coord, rho, rho1, sIso, kwIso,
          modelIso, hfinrank, hcardF3, hthetaOdd, hsigmaF, hsigmaFrob,
          hK1, hW1ne, hW1norm, hW1inv, hphiThetaOne, hphiThetaNe,
          hcoordMul, hrho, hrho1, hmodelS, hmodelKW, hmapK, hmapW, hs⟩
      letI : Field E3 := hE3Field
      letI : Finite E3 := hE3Finite
      letI : CharP E3 2 := hE3Char
      letI : Group S1 := hS1Group
      have hphi_zero_left : ∀ x : E3, phi0 0 x = 0 := by
        intro x
        by_cases htheta : theta = 1
        · rw [hphiThetaOne htheta]
          simp
        · have hzero := (hphiThetaNe htheta).2.1 0 0 x
          simpa using hzero
      have hcoord_one :
          ((coord (1 : S1) :
              {p : E3 × E3 //
                (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
                  (theta ≠ 1 ∧ p.2 ∈ F3)}) : E3 × E3) = (0, 0) := by
        let p : E3 × E3 :=
          ((coord (1 : S1) :
              {p : E3 × E3 //
                (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
                  (theta ≠ 1 ∧ p.2 ∈ F3)}) : E3 × E3)
        have hp := hcoordMul (1 : S1) 1
        have hp_eq : p =
            (p.1 + p.1, p.2 + p.2 + phi0 p.1 p.1) := by
          simpa [p] using hp
        have hp_one : p.1 = 0 := by
          have hfirst := congrArg Prod.fst hp_eq
          simpa using hfirst
        have hp_two : p.2 = 0 := by
          have hsecond := congrArg Prod.snd hp_eq
          rw [hp_one, hphi_zero_left] at hsecond
          simpa using hsecond
        exact Prod.ext hp_one hp_two
      have hsIso_rho : ∀ (a : (K ⊔ W : Subgroup G)) (x : S),
          sIso (rho a x) = rho1 (kwIso a) (sIso x) := by
        intro a x
        apply (SemidirectProduct.inl_injective (φ := rho1))
        calc
          SemidirectProduct.inl (sIso (rho a x)) =
              modelIso (SemidirectProduct.inl (rho a x)) :=
            (hmodelS (rho a x)).symm
          _ = modelIso
              (SemidirectProduct.inr a * SemidirectProduct.inl x *
                SemidirectProduct.inr a⁻¹) := by
            rw [← SemidirectProduct.inl_aut]
          _ = modelIso (SemidirectProduct.inr a) *
              modelIso (SemidirectProduct.inl x) *
                modelIso (SemidirectProduct.inr a⁻¹) := by
            rw [map_mul, map_mul]
          _ = SemidirectProduct.inr (kwIso a) *
              SemidirectProduct.inl (sIso x) *
                SemidirectProduct.inr (kwIso a)⁻¹ := by
            rw [hmodelKW a, hmodelS x, hmodelKW a⁻¹, map_inv]
          _ = SemidirectProduct.inl (rho1 (kwIso a) (sIso x)) :=
            (SemidirectProduct.inl_aut (kwIso a) (sIso x)).symm
      let centerCoord (u : F3) :
          {p : E3 × E3 //
            (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
              (theta ≠ 1 ∧ p.2 ∈ F3)} :=
        ⟨(0, (u : E3)), by
          by_cases htheta : theta = 1
          · left
            refine ⟨htheta, ?_⟩
            rw [hsigmaF]
            rw [htheta]
            simpa using CharTwo.add_self_eq_zero (u : E3)
          · exact Or.inr ⟨htheta, u.property⟩⟩
      let centerS (u : F3) : S :=
        sIso.symm (coord.symm (centerCoord u))
      let center (u : F3) : G := (centerS u : G)
      have hcenter_coord : ∀ u : F3,
          ((coord (sIso (centerS u)) :
              {p : E3 × E3 //
                (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
                  (theta ≠ 1 ∧ p.2 ∈ F3)}) : E3 × E3) =
            (0, (u : E3)) := by
        intro u
        simp [centerS, centerCoord]
      have hcenterS_zero : centerS 0 = 1 := by
        apply sIso.injective
        apply coord.injective
        apply Subtype.ext
        simpa [centerS, centerCoord] using hcoord_one.symm
      have hcenter_zero : center 0 = 1 :=
        congrArg Subtype.val hcenterS_zero
      have hcenterS_add : ∀ u v : F3,
          centerS (u + v) = centerS u * centerS v := by
        intro u v
        apply sIso.injective
        rw [map_mul]
        apply coord.injective
        apply Subtype.ext
        rw [hcoordMul]
        simp [hcenter_coord, hphi_zero_left]
      have hcenter_add : ∀ u v : F3,
          center (u + v) = center u * center v := by
        intro u v
        exact congrArg Subtype.val (hcenterS_add u v)
      have hcenter_sq : ∀ u : F3, center u ^ 2 = 1 := by
        intro u
        rw [pow_two, ← hcenter_add, CharTwo.add_self_eq_zero,
          hcenter_zero]
      have hcenter_mem_Q0 : ∀ u : F3, center u ∈ Q0 := by
        intro u
        by_cases hcenter_one : center u = 1
        · simp [hcenter_one]
        · apply (hsection3.section2.Q0_def (center u)).2
          refine Or.inr ⟨?_, hcenter_one, hcenter_sq u⟩
          apply hA1.Q_le_H
          simpa [hSQ, center] using (centerS u).property
      have hcenter_injective : Function.Injective center := by
        intro u v huv
        apply Subtype.ext
        have huvS : centerS u = centerS v := Subtype.ext huv
        have hcoords := congrArg
          (fun x : S =>
            ((coord (sIso x) :
              {p : E3 × E3 //
                (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
                  (theta ≠ 1 ∧ p.2 ∈ F3)}) : E3 × E3)) huvS
        have hsecond := congrArg Prod.snd hcoords
        simpa [hcenter_coord] using hsecond
      let centerToQ0 : F3 → Q0 := fun u =>
        ⟨center u, hcenter_mem_Q0 u⟩
      have hcenterToQ0_injective : Function.Injective centerToQ0 := by
        intro u v huv
        apply hcenter_injective
        exact congrArg (fun q : Q0 => (q : G)) huv
      have hcenterToQ0_bijective : Function.Bijective centerToQ0 :=
        hcenterToQ0_injective.bijective_of_nat_card_le (by rw [hcardF3])
      have hcenter_surjective : ∀ y : G, y ∈ Q0 →
          ∃ u : F3, center u = y := by
        intro y hy
        obtain ⟨u, hu⟩ := hcenterToQ0_bijective.2 ⟨y, hy⟩
        exact ⟨u, congrArg Subtype.val hu⟩
      let coordPair (x : S) : E3 × E3 :=
        ((coord (sIso x) :
          {p : E3 × E3 //
            (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
              (theta ≠ 1 ∧ p.2 ∈ F3)}) : E3 × E3)
      have hcenter_coordPair (u : F3) :
          coordPair (centerS u) = (0, (u : E3)) := by
        simpa [coordPair] using hcenter_coord u
      have hcoordPair_mul (x y : S) :
          coordPair (x * y) =
            ((coordPair x).1 + (coordPair y).1,
              (coordPair x).2 + (coordPair y).2 +
                phi0 (coordPair x).1 (coordPair y).1) := by
        simpa [coordPair] using hcoordMul (sIso x) (sIso y)
      have hcoordPair_one : coordPair 1 = (0, 0) := by
        simpa [coordPair] using hcoord_one
      have hcoordPair_zero_of_mem_Q0 (x : S)
          (hxQ0 : (x : G) ∈ Q0) : (coordPair x).1 = 0 := by
        obtain ⟨u, hu⟩ := hcenter_surjective (x : G) hxQ0
        have hx : x = centerS u := Subtype.ext hu.symm
        rw [hx]
        exact congrArg Prod.fst (hcenter_coord u)
      have hmem_Q0_of_coordPair_zero (x : S)
          (hxzero : (coordPair x).1 = 0) : (x : G) ∈ Q0 := by
        have hx_sq : x * x = 1 := by
          apply sIso.injective
          apply coord.injective
          apply Subtype.ext
          change coordPair (x * x) = coordPair 1
          rw [hcoordPair_mul, hxzero, hphi_zero_left]
          simp [hcoordPair_one, CharTwo.add_self_eq_zero]
        by_cases hxone : (x : G) = 1
        · simp [hxone]
        · exact (hsection3.section2.Q0_def _).2 <|
            Or.inr ⟨hA1.Q_le_H (by simpa [hSQ] using x.property),
              hxone, by simpa [pow_two] using congrArg Subtype.val hx_sq⟩
      let conjS (x : S) (a : (K ⊔ W : Subgroup G)) : S := rho a⁻¹ x
      have hconjS_coe : ∀ (x : S) (a : (K ⊔ W : Subgroup G)),
          ((conjS x a : S) : G) =
            rightConjugateElem (x : G) (a : G) := by
        intro x a
        simpa [conjS, rightConjugateElem] using hrho a⁻¹ x
      have hconjS_coord : ∀ (x : S) (a : (K ⊔ W : Subgroup G)),
          coordPair (conjS x a) =
            ((((kwIso a : (K1 ⊔ W1 : Subgroup E3ˣ)) : E3ˣ) : E3) *
                (coordPair x).1,
              (((kwIso a : (K1 ⊔ W1 : Subgroup E3ˣ)) : E3ˣ) : E3) *
                sigma
                    (((kwIso a : (K1 ⊔ W1 : Subgroup E3ˣ)) : E3ˣ) : E3) *
                  (coordPair x).2) := by
        intro x a
        change
          ((coord (sIso (rho a⁻¹ x)) :
            {p : E3 × E3 //
              (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
                (theta ≠ 1 ∧ p.2 ∈ F3)}) : E3 × E3) = _
        rw [hsIso_rho]
        simpa [map_inv, coordPair] using hrho1 (kwIso a) (sIso x)
      have hconjS_first : ∀ (x : S) (a : (K ⊔ W : Subgroup G)),
          (coordPair (conjS x a)).1 =
            (((kwIso a : (K1 ⊔ W1 : Subgroup E3ˣ)) : E3ˣ) : E3) *
              (coordPair x).1 := by
        intro x a
        exact congrArg Prod.fst (hconjS_coord x a)
      have hkwIso_mem_K1 : ∀ (a : G), ∀ ha : a ∈ K,
          (((kwIso
              (⟨a, Subgroup.mem_sup_left ha⟩ : (K ⊔ W : Subgroup G)) :
                (K1 ⊔ W1 : Subgroup E3ˣ)) : E3ˣ) ∈ K1) := by
        intro a ha
        let aKW : (K ⊔ W : Subgroup G) :=
          ⟨a, Subgroup.mem_sup_left ha⟩
        have ha_sub : aKW ∈ K.subgroupOf (K ⊔ W) := ha
        have ha_map : kwIso aKW ∈
            Subgroup.map kwIso.toMonoidHom (K.subgroupOf (K ⊔ W)) :=
          ⟨aKW, ha_sub, rfl⟩
        rw [hmapK] at ha_map
        exact ha_map
      have hkwIso_mem_W1 : ∀ (a : G), ∀ ha : a ∈ W,
          (((kwIso
              (⟨a, Subgroup.mem_sup_right ha⟩ : (K ⊔ W : Subgroup G)) :
                (K1 ⊔ W1 : Subgroup E3ˣ)) : E3ˣ) ∈ W1) := by
        intro a ha
        let aKW : (K ⊔ W : Subgroup G) :=
          ⟨a, Subgroup.mem_sup_right ha⟩
        have ha_sub : aKW ∈ W.subgroupOf (K ⊔ W) := ha
        have ha_map : kwIso aKW ∈
            Subgroup.map kwIso.toMonoidHom (W.subgroupOf (K ⊔ W)) :=
          ⟨aKW, ha_sub, rfl⟩
        rw [hmapW] at ha_map
        exact ha_map
      have hK_of_scalar : ∀ b : F3ˣ,
          ∃ a : G, ∃ ha : a ∈ K,
            (((kwIso
                (⟨a, Subgroup.mem_sup_left ha⟩ : (K ⊔ W : Subgroup G)) :
                  (K1 ⊔ W1 : Subgroup E3ˣ)) : E3ˣ) : E3) =
              ((b : F3) : E3) := by
        intro b
        let bE : E3ˣ := Units.map F3.subtype.toMonoidHom b
        have hbE_K1 : bE ∈ K1 := by
          apply (hK1 bE).2
          exact ⟨b, by simp [bE]⟩
        let bKW : (K1 ⊔ W1 : Subgroup E3ˣ) :=
          ⟨bE, Subgroup.mem_sup_left hbE_K1⟩
        have hb_sub : bKW ∈ K1.subgroupOf (K1 ⊔ W1) := hbE_K1
        rw [← hmapK] at hb_sub
        obtain ⟨aKW, haK, ha_image⟩ := hb_sub
        refine ⟨(aKW : G), haK, ?_⟩
        have haKW_eq :
            (⟨(aKW : G), Subgroup.mem_sup_left haK⟩ :
                (K ⊔ W : Subgroup G)) = aKW := Subtype.ext rfl
        rw [haKW_eq]
        have himage := congrArg
          (fun z : (K1 ⊔ W1 : Subgroup E3ˣ) => (((z : E3ˣ) : E3)))
          ha_image
        simpa [bKW, bE] using himage
      let kOf (b : F3ˣ) : G := Classical.choose (hK_of_scalar b)
      have hkOf_mem : ∀ b : F3ˣ, kOf b ∈ K := by
        intro b
        exact Classical.choose (Classical.choose_spec (hK_of_scalar b))
      have hkOf_coord : ∀ b : F3ˣ,
          (((kwIso
              (⟨kOf b, Subgroup.mem_sup_left (hkOf_mem b)⟩ :
                (K ⊔ W : Subgroup G)) :
                  (K1 ⊔ W1 : Subgroup E3ˣ)) : E3ˣ) : E3) =
            ((b : F3) : E3) := by
        intro b
        exact Classical.choose_spec
          (Classical.choose_spec (hK_of_scalar b))
      have hcenter_conj_K_exact : ∀ (a : G), ∀ ha : a ∈ K,
          ∀ (b : F3ˣ),
            (((kwIso
                (⟨a, Subgroup.mem_sup_left ha⟩ :
                  (K ⊔ W : Subgroup G)) :
                    (K1 ⊔ W1 : Subgroup E3ˣ)) : E3ˣ) : E3) =
              ((b : F3) : E3) →
            ∀ u : F3, rightConjugateElem (center u) a =
              center ((b : F3) * theta (b : F3) * u) := by
        intro a ha b hb u
        let aKW : (K ⊔ W : Subgroup G) :=
          ⟨a, Subgroup.mem_sup_left ha⟩
        have hsub : conjS (centerS u) aKW =
            centerS ((b : F3) * theta (b : F3) * u) := by
          apply sIso.injective
          apply coord.injective
          apply Subtype.ext
          change coordPair (conjS (centerS u) aKW) =
            coordPair (centerS ((b : F3) * theta (b : F3) * u))
          rw [hconjS_coord, hcenter_coordPair, hcenter_coordPair]
          change
            (((((kwIso aKW :
                (K1 ⊔ W1 : Subgroup E3ˣ)) : E3ˣ) : E3)) * 0,
              ((((kwIso aKW :
                (K1 ⊔ W1 : Subgroup E3ˣ)) : E3ˣ) : E3)) *
                sigma
                    ((((kwIso aKW :
                      (K1 ⊔ W1 : Subgroup E3ˣ)) : E3ˣ) : E3)) *
                  (u : E3)) =
              (0, (((b : F3) * theta (b : F3) * u : F3) : E3))
          rw [hb, hsigmaF]
          simp
        calc
          rightConjugateElem (center u) a =
              ((conjS (centerS u) aKW : S) : G) := by
            rw [hconjS_coe]
          _ = center ((b : F3) * theta (b : F3) * u) :=
            congrArg Subtype.val hsub
      have hcenter_conj_W : ∀ (a : G), a ∈ W → ∀ u : F3,
          rightConjugateElem (center u) a = center u := by
        intro a ha u
        let aKW : (K ⊔ W : Subgroup G) :=
          ⟨a, Subgroup.mem_sup_right ha⟩
        let aUnit : E3ˣ :=
          ((kwIso aKW : (K1 ⊔ W1 : Subgroup E3ˣ)) : E3ˣ)
        have haUnit_W1 : aUnit ∈ W1 := hkwIso_mem_W1 a ha
        have ha_sigma : sigma (aUnit : E3) = (aUnit : E3)⁻¹ :=
          hW1inv aUnit haUnit_W1
        have hsub : conjS (centerS u) aKW = centerS u := by
          apply sIso.injective
          apply coord.injective
          apply Subtype.ext
          change coordPair (conjS (centerS u) aKW) =
            coordPair (centerS u)
          rw [hconjS_coord, hcenter_coordPair]
          change ((aUnit : E3) * 0,
              (aUnit : E3) * sigma (aUnit : E3) * (u : E3)) =
            (0, (u : E3))
          rw [ha_sigma]
          simp
        calc
          rightConjugateElem (center u) a =
              ((conjS (centerS u) aKW : S) : G) := by
            rw [hconjS_coe]
          _ = center u := congrArg Subtype.val hsub
      obtain ⟨hsS, hs_coord⟩ := hs
      have hs_centerS : (⟨s, hsS⟩ : S) = centerS 1 := by
        apply sIso.injective
        apply coord.injective
        apply Subtype.ext
        rw [hs_coord, hcenter_coord]
        simp
      have hs_center : s = center 1 := congrArg Subtype.val hs_centerS
      have hV_le_D : V ≤ D := by
        rw [hsection3.section2.V_eq]
        exact inf_le_left
      have hW_le_D : W ≤ D := hsection3.section2.W_le_V.trans hV_le_D
      have hKW_le_D : K ⊔ W ≤ D :=
        sup_le hsection3.section2.K_le_D hW_le_D
      let bar : G → E3 := fun x =>
        if hx : x ∈ Q then
          (coordPair (⟨x, by simpa [hSQ] using hx⟩ : S)).1
        else 0
      let kcoord : G → E3 := fun a =>
        if ha : a ∈ K ⊔ W then
          (((kwIso (⟨a, ha⟩ : (K ⊔ W : Subgroup G)) :
              (K1 ⊔ W1 : Subgroup E3ˣ)) : E3ˣ) : E3)
        else 0
      have hbar_of_mem_Q (x : G) (hx : x ∈ Q) :
          bar x =
            (coordPair (⟨x, by simpa [hSQ] using hx⟩ : S)).1 := by
        simp [bar, hx]
      have hkcoord_of_mem_KW (a : G) (ha : a ∈ K ⊔ W) :
          kcoord a =
            (((kwIso (⟨a, ha⟩ : (K ⊔ W : Subgroup G)) :
              (K1 ⊔ W1 : Subgroup E3ˣ)) : E3ˣ) : E3) := by
        simp [kcoord, ha]
      have hbar_mul : ∀ x : G, x ∈ Q → ∀ y : G, y ∈ Q →
          bar (x * y) = bar x + bar y := by
        intro x hx y hy
        let xS : S := ⟨x, by simpa [hSQ] using hx⟩
        let yS : S := ⟨y, by simpa [hSQ] using hy⟩
        have hfirst := congrArg Prod.fst (hcoordPair_mul xS yS)
        simpa [bar, hx, hy, Q.mul_mem hx hy, xS, yS] using hfirst
      have hbar_Q0 : ∀ x : G, x ∈ Q → (bar x = 0 ↔ x ∈ Q0) := by
        intro x hx
        let xS : S := ⟨x, by simpa [hSQ] using hx⟩
        rw [hbar_of_mem_Q x hx]
        constructor
        · intro hzero
          simpa [xS] using hmem_Q0_of_coordPair_zero xS hzero
        · intro hxQ0
          exact hcoordPair_zero_of_mem_Q0 xS hxQ0
      have hQ_conj_KW : ∀ x : G, x ∈ Q → ∀ d : G, d ∈ K ⊔ W →
          rightConjugateElem x d ∈ Q := by
        intro x hx d hd
        exact PFchapter4section1.h6_rightConjugateElem_mem_Q_of_mem_M
          (PFchapter4section1.rankOneSplit_Q_le_M hA1.Q_sup_D)
          hA1.Q_normal_in_H hx (hA1.D_le_H (hKW_le_D hd))
      have hbar_conj : ∀ x : G, x ∈ Q → ∀ d : G, d ∈ K ⊔ W →
          bar (rightConjugateElem x d) = kcoord d * bar x := by
        intro x hx d hd
        let xS : S := ⟨x, by simpa [hSQ] using hx⟩
        let dKW : (K ⊔ W : Subgroup G) := ⟨d, hd⟩
        let rS : S :=
          ⟨rightConjugateElem x d,
            by simpa [hSQ] using hQ_conj_KW x hx d hd⟩
        have hrS : rS = conjS xS dKW := by
          apply Subtype.ext
          exact (hconjS_coe xS dKW).symm
        have hscale := hconjS_first xS dKW
        rw [hbar_of_mem_Q _ (hQ_conj_KW x hx d hd),
          hbar_of_mem_Q x hx, hkcoord_of_mem_KW d hd]
        change (coordPair rS).1 =
          (((kwIso dKW : (K1 ⊔ W1 : Subgroup E3ˣ)) : E3ˣ) : E3) *
            (coordPair xS).1
        rw [hrS]
        exact hscale
      have hkcoord_mul : ∀ x : G, x ∈ K ⊔ W →
          ∀ y : G, y ∈ K ⊔ W →
            kcoord (x * y) = kcoord x * kcoord y := by
        intro x hx y hy
        let xKW : (K ⊔ W : Subgroup G) := ⟨x, hx⟩
        let yKW : (K ⊔ W : Subgroup G) := ⟨y, hy⟩
        have hmap := congrArg
          (fun a : (K1 ⊔ W1 : Subgroup E3ˣ) => (((a : E3ˣ) : E3)))
          (kwIso.map_mul xKW yKW)
        simpa [kcoord, hx, hy, (K ⊔ W).mul_mem hx hy, xKW, yKW]
          using hmap
      have hkcoord_inv : ∀ x : G, x ∈ K ⊔ W →
          kcoord x⁻¹ = (kcoord x)⁻¹ := by
        intro x hx
        let xKW : (K ⊔ W : Subgroup G) := ⟨x, hx⟩
        rw [hkcoord_of_mem_KW x⁻¹ ((K ⊔ W).inv_mem hx),
          hkcoord_of_mem_KW x hx]
        have hxinv :
            (⟨x⁻¹, (K ⊔ W).inv_mem hx⟩ :
              (K ⊔ W : Subgroup G)) = xKW⁻¹ := by
          rfl
        rw [hxinv, map_inv]
        simp [xKW]
      have hkcoord_pow : ∀ x : G, x ∈ K ⊔ W → ∀ m : ℕ,
          kcoord (x ^ m) = kcoord x ^ m := by
        intro x hx m
        let xKW : (K ⊔ W : Subgroup G) := ⟨x, hx⟩
        rw [hkcoord_of_mem_KW (x ^ m) ((K ⊔ W).pow_mem hx m),
          hkcoord_of_mem_KW x hx]
        have hxpow :
            (⟨x ^ m, (K ⊔ W).pow_mem hx m⟩ :
              (K ⊔ W : Subgroup G)) = xKW ^ m := by
          rfl
        rw [hxpow, map_pow]
        rfl
      have hkcoord_ne_zero : ∀ x : G, x ∈ K ⊔ W →
          kcoord x ≠ 0 := by
        intro x hx
        simp [kcoord, hx]
      have hkcoord_kOf (a : F3ˣ) :
          kcoord (kOf a) = ((a : F3) : E3) := by
        rw [hkcoord_of_mem_KW (kOf a)
          (Subgroup.mem_sup_left (hkOf_mem a))]
        exact hkOf_coord a
      let omegaS : S := ⟨omega, by simpa [hSQ] using homega_Q⟩
      have homega_sq_first : (coordPair (omegaS ^ 2)).1 = 0 := by
        rw [pow_two, hcoordPair_mul]
        exact CharTwo.add_self_eq_zero (coordPair omegaS).1
      have homega_sq_mem_Q0 : omega ^ 2 ∈ Q0 := by
        have hsquare :=
          hmem_Q0_of_coordPair_zero (omegaS ^ 2) homega_sq_first
        simpa [omegaS] using hsquare
      obtain ⟨alpha, halpha_center⟩ :=
        hcenter_surjective (omega ^ 2) homega_sq_mem_Q0
      have homega_inv_shape : omega⁻¹ = omega * center alpha := by
        apply inv_eq_of_mul_eq_one_right
        calc
          omega * (omega * center alpha) =
              omega ^ 2 * center alpha := by rw [pow_two, mul_assoc]
          _ = center alpha * center alpha := by rw [← halpha_center]
          _ = 1 := by simpa [pow_two] using hcenter_sq alpha
      let omegaBar : E3 := bar omega
      have homegaBar_ne : omegaBar ≠ 0 := by
        intro hzero
        apply homega_not_Q0
        exact (hbar_Q0 omega homega_Q).1 hzero
      let z : E3 := kcoord zeta
      have hz_ne : z ≠ 0 :=
        hkcoord_ne_zero zeta (Subgroup.mem_sup_right hzeta_W)
      have hz_not_mem_F3 : z ∉ F3 := by
        intro hzF
        let zF : F3 := ⟨z, hzF⟩
        let zUnit : F3ˣ := Units.mk0 zF (by
          intro hzFzero
          apply hz_ne
          exact congrArg Subtype.val hzFzero)
        let kKW : (K ⊔ W : Subgroup G) :=
          ⟨kOf zUnit, Subgroup.mem_sup_left (hkOf_mem zUnit)⟩
        let zKW : (K ⊔ W : Subgroup G) :=
          ⟨zeta, Subgroup.mem_sup_right hzeta_W⟩
        have himage : kwIso kKW = kwIso zKW := by
          apply Subtype.ext
          apply Units.ext
          calc
            (((kwIso kKW : (K1 ⊔ W1 : Subgroup E3ˣ)) : E3ˣ) : E3) =
                ((zUnit : F3) : E3) := hkOf_coord zUnit
            _ = z := rfl
            _ = kcoord zeta := rfl
            _ = (((kwIso zKW :
                (K1 ⊔ W1 : Subgroup E3ˣ)) : E3ˣ) : E3) :=
              hkcoord_of_mem_KW zeta
                (Subgroup.mem_sup_right hzeta_W)
        have hk_eq_zeta : kOf zUnit = zeta :=
          congrArg Subtype.val (kwIso.injective himage)
        have hzeta_K : zeta ∈ K := by
          rw [← hk_eq_zeta]
          exact hkOf_mem zUnit
        exact hzeta_ne (hK_inter_W zeta hzeta_K hzeta_W)
      have hmem_F3_of_frobenius_fixed (y : E3)
          (hy : y ^ Nat.card F3 = y) : y ∈ F3 := by
        letI : Fintype F3 := Fintype.ofFinite F3
        let fr : E3 ≃ₐ[F3] E3 :=
          FiniteField.frobeniusAlgEquivOfAlgebraic F3 E3
        have hyfr : fr y = y := by
          simpa [fr, Nat.card_eq_fintype_card] using hy
        have hall_fixed : ∀ tau : E3 ≃ₐ[F3] E3, tau y = y := by
          intro tau
          obtain ⟨j, hj⟩ :=
            (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
              F3 E3).2 tau
          have hjlt : (j : ℕ) < 2 := by
            have hjlt' : (j : ℕ) < Module.finrank F3 E3 := j.isLt
            omega
          have hjcases : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by omega
          rcases hjcases with hjzero | hjone
          · rw [← hj]
            change
              (FiniteField.frobeniusAlgEquivOfAlgebraic F3 E3 ^
                (j : ℕ)) y = y
            rw [hjzero]
            simp
          · rw [← hj]
            change
              (FiniteField.frobeniusAlgEquivOfAlgebraic F3 E3 ^
                (j : ℕ)) y = y
            rw [hjone, pow_one]
            exact hyfr
        have hyrange : y ∈ Set.range (algebraMap F3 E3) :=
          (IsGalois.mem_range_algebraMap_iff_fixed y).2 hall_fixed
        rcases hyrange with ⟨a, ha⟩
        rw [← ha]
        exact a.property
      let zetaKW : (K ⊔ W : Subgroup G) :=
        ⟨zeta, Subgroup.mem_sup_right hzeta_W⟩
      let zetaUnit : E3ˣ :=
        ((kwIso zetaKW : (K1 ⊔ W1 : Subgroup E3ˣ)) : E3ˣ)
      have hzetaUnit_W1 : zetaUnit ∈ W1 := by
        simpa [zetaUnit, zetaKW] using hkwIso_mem_W1 zeta hzeta_W
      have hzeta_coord : z = (zetaUnit : E3) := by
        simpa [z, zetaUnit, zetaKW] using
          hkcoord_of_mem_KW zeta (Subgroup.mem_sup_right hzeta_W)
      have hzeta_coord_norm : z ^ (Nat.card F3 + 1) = 1 := by
        rw [hzeta_coord]
        exact hW1norm zetaUnit hzetaUnit_W1
      have hzeta_coord_frobenius : z ^ Nat.card F3 = z⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        simpa [pow_succ] using hzeta_coord_norm
      have hc_mem_F3 : z + z⁻¹ ∈ F3 := by
        letI : Fintype F3 := Fintype.ofFinite F3
        let fr : E3 ≃ₐ[F3] E3 :=
          FiniteField.frobeniusAlgEquivOfAlgebraic F3 E3
        have hfr_z : fr z = z⁻¹ := by
          calc
            fr z = z ^ Nat.card F3 := by
              simp [fr, Nat.card_eq_fintype_card]
            _ = z⁻¹ := hzeta_coord_frobenius
        apply hmem_F3_of_frobenius_fixed
        calc
          (z + z⁻¹) ^ Nat.card F3 = fr (z + z⁻¹) := by
            simp [fr, Nat.card_eq_fintype_card]
          _ = fr z + fr z⁻¹ := map_add fr z z⁻¹
          _ = z⁻¹ + (z⁻¹)⁻¹ := by rw [map_inv₀, hfr_z]
          _ = z + z⁻¹ := by rw [inv_inv, add_comm]
      let c : F3 := ⟨z + z⁻¹, hc_mem_F3⟩
      have hc : (c : E3) = z + z⁻¹ := rfl
      have hquotient_card :
          Nat.card (Q ⧸ Q0Q) = Nat.card Q0 ^ 2 := by
        have hcardQ0Q : Nat.card Q0Q = Nat.card Q0 :=
          Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe
              (H := Q0) (K := Q) hsection3.section2.Q0_le_Q).toEquiv
        have hprod : Nat.card (Q ⧸ Q0Q) * Nat.card Q0 =
            Nat.card Q0 ^ 2 * Nat.card Q0 := by
          calc
            Nat.card (Q ⧸ Q0Q) * Nat.card Q0 =
                Nat.card (Q ⧸ Q0Q) * Nat.card Q0Q := by rw [hcardQ0Q]
            _ = Nat.card Q :=
              (Subgroup.card_eq_card_quotient_mul_card_subgroup Q0Q).symm
            _ = Nat.card Q0 ^ 3 := hQ_card_cube
            _ = Nat.card Q0 ^ 2 * Nat.card Q0 := by ring
        apply Nat.mul_right_cancel (Nat.card_pos (α := Q0))
        exact hprod
      have hE3_card : Nat.card E3 = Nat.card F3 ^ 2 := by
        have hcard := Module.natCard_eq_pow_finrank (K := F3) (V := E3)
        rw [hfinrank] at hcard
        simpa using hcard
      have hquotient_E3_card : Nat.card (Q ⧸ Q0Q) = Nat.card E3 := by
        rw [hquotient_card, hE3_card, hcardF3]
      obtain ⟨qBarEquiv, hqBarEquiv_mk⟩ :=
        quotient_mulEquiv_multiplicative_of_additive_coordinate
          Q Q0 hsection3.section2.Q0_le_Q bar hbar_mul hbar_Q0
            hquotient_E3_card
      let KW_D : Subgroup D := (K ⊔ W).subgroupOf D
      have hK_normal_D : (K.subgroupOf D).Normal :=
        (PFchapter1section2.proposition_2
          H D Q K V W Q0 S Q1 t hsection3.section2).2
      have hW_normal_D : (W.subgroupOf D).Normal :=
        _root_.CFSG.BenderSuzuki.PFchapter1section2.peterfalvi_chapter1_section2_proposition_3_appendixI_input_W_normal_D
            H D Q K V W t hA1 hsection3.section2.K_def
              hsection3.section2.V_eq hsection3.section2.W_le_V
                hsection3.section2.W_eq hV_le_D
      have hKW_D_eq : KW_D = K.subgroupOf D ⊔ W.subgroupOf D := by
        exact Subgroup.subgroupOf_sup hsection3.section2.K_le_D hW_le_D
      have hKW_D_normal : KW_D.Normal := by
        rw [hKW_D_eq]
        letI : (K.subgroupOf D).Normal := hK_normal_D
        letI : (W.subgroupOf D).Normal := hW_normal_D
        exact Subgroup.sup_normal (K.subgroupOf D) (W.subgroupOf D)
      letI : KW_D.Normal := hKW_D_normal
      let kwDToKW : KW_D ≃* (K ⊔ W : Subgroup G) :=
        Subgroup.subgroupOfEquivOfLe hKW_le_D
      let scalar : KW_D →* E3ˣ :=
        (K1 ⊔ W1).subtype.comp
          (kwIso.toMonoidHom.comp kwDToKW.toMonoidHom)
      have hscalar_value (a : KW_D) :
          (scalar a : E3) = kcoord (a : G) := by
        rw [hkcoord_of_mem_KW (a : G) a.property]
        rfl
      let scalarSet : Set E3 :=
        Set.range (fun a : KW_D => (scalar a : E3))
      have hF3_closure : ∀ a : F3,
          (a : E3) ∈ Subring.closure scalarSet := by
        intro a
        by_cases ha : a = 0
        · rw [ha]
          exact (Subring.closure scalarSet).zero_mem
        · let aUnit : F3ˣ := Units.mk0 a ha
          let kD : KW_D :=
            ⟨⟨kOf aUnit,
                hKW_le_D (Subgroup.mem_sup_left (hkOf_mem aUnit))⟩,
              Subgroup.mem_sup_left (hkOf_mem aUnit)⟩
          apply Subring.subset_closure
          refine ⟨kD, ?_⟩
          calc
            (scalar kD : E3) = kcoord (kOf aUnit) := hscalar_value kD
            _ = ((aUnit : F3) : E3) := hkcoord_kOf aUnit
            _ = (a : E3) := rfl
      have hz_closure : z ∈ Subring.closure scalarSet := by
        let zD : KW_D :=
          ⟨⟨zeta, hKW_le_D (Subgroup.mem_sup_right hzeta_W)⟩,
            Subgroup.mem_sup_right hzeta_W⟩
        apply Subring.subset_closure
        refine ⟨zD, ?_⟩
        calc
          (scalar zD : E3) = kcoord zeta := hscalar_value zD
          _ = z := rfl
      have hscalar_closure : Subring.closure scalarSet = ⊤ :=
        subring_closure_eq_top_of_quadratic_generator F3 hfinrank
          scalarSet z hF3_closure hz_closure hz_not_mem_F3
      let rhoD : D →* ((Q ⧸ Q0Q) ≃* (Q ⧸ Q0Q)) :=
        MulDistribMulAction.toMulAut D (Q ⧸ Q0Q)
      have hscalar_action : ∀ (a : KW_D) (x : Q ⧸ Q0Q),
          qBarEquiv (rhoD (a : D)⁻¹ x) =
            Multiplicative.ofAdd
              ((scalar a : E3) * Multiplicative.toAdd (qBarEquiv x)) := by
        intro a xbar
        obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective Q0Q xbar
        apply Multiplicative.toAdd.injective
        change Multiplicative.toAdd
            (qBarEquiv
              ((a : D)⁻¹ • QuotientGroup.mk' Q0Q q)) =
          (scalar a : E3) *
            Multiplicative.toAdd
              (qBarEquiv (QuotientGroup.mk' Q0Q q))
        change Multiplicative.toAdd
            (qBarEquiv
              (QuotientGroup.mk' Q0Q ((a : D)⁻¹ • q))) =
          (scalar a : E3) *
            Multiplicative.toAdd
              (qBarEquiv (QuotientGroup.mk' Q0Q q))
        rw [hqBarEquiv_mk, hqBarEquiv_mk]
        calc
          bar ((((a : D)⁻¹ • q : Q) : G)) =
              bar (rightConjugateElem (q : G) (a : G)) := by
            congr 1
            rw [hD_smul_coe]
            simp [rightConjugateElem, mul_assoc]
          _ = kcoord (a : G) * bar (q : G) :=
            hbar_conj (q : G) q.property (a : G) a.property
          _ = (scalar a : E3) * bar (q : G) := by
            rw [hscalar_value]
      let omegaQ : Q := ⟨omega, homega_Q⟩
      let omegaQbar : Q ⧸ Q0Q := QuotientGroup.mk' Q0Q omegaQ
      have homegaQbar_ne : omegaQbar ≠ 1 := by
        intro hone
        apply homega_not_Q0
        exact (QuotientGroup.eq_one_iff omegaQ).1 hone
      obtain ⟨sigmaHom, hsemilinear, hsigma_scalar⟩ :=
        semilinear_hom_of_normal_scalar_action KW_D qBarEquiv rhoD
          scalar hscalar_action scalarSet rfl hscalar_closure
            omegaQbar homegaQbar_ne
      have heta_V : eta ∈ V := hX_le_V heta_X
      have heta_D : eta ∈ D := by
        rw [hsection3.section2.V_eq] at heta_V
        exact heta_V.1
      let etaInvD : D := ⟨eta⁻¹, D.inv_mem heta_D⟩
      let muE : E3 ≃+* E3 := sigmaHom etaInvD
      let Tmul : Multiplicative E3 ≃* Multiplicative E3 :=
        qBarEquiv.symm.trans ((rhoD etaInvD).trans qBarEquiv)
      let T : E3 ≃+ E3 :=
        AddEquiv.toMultiplicative.symm Tmul
      have hT_apply (xbar : Q ⧸ Q0Q) :
          T (Multiplicative.toAdd (qBarEquiv xbar)) =
            Multiplicative.toAdd (qBarEquiv (rhoD etaInvD xbar)) := by
        simp [T, Tmul]
      have hT_semilinear : ∀ lambda y : E3,
          T (lambda * y) = muE lambda * T y := by
        intro lambda y
        let xbar : Q ⧸ Q0Q :=
          qBarEquiv.symm (Multiplicative.ofAdd y)
        have hsemi := hsemilinear etaInvD lambda xbar
        have htransport := congrArg
          (fun q : Q ⧸ Q0Q =>
            Multiplicative.toAdd (qBarEquiv q)) hsemi
        simpa [xbar, T, Tmul, muE] using htransport
      have hT_bar : ∀ q : G, ∀ hq : q ∈ Q,
          T (bar q) = bar (rightConjugateElem q eta) := by
        intro q hq
        let qQ : Q := ⟨q, hq⟩
        calc
          T (bar q) =
              T (Multiplicative.toAdd
                (qBarEquiv (QuotientGroup.mk' Q0Q qQ))) := by
            rw [hqBarEquiv_mk]
          _ = Multiplicative.toAdd
              (qBarEquiv
                (rhoD etaInvD (QuotientGroup.mk' Q0Q qQ))) :=
            hT_apply _
          _ = Multiplicative.toAdd
              (qBarEquiv
                (QuotientGroup.mk' Q0Q (etaInvD • qQ))) := by
            rfl
          _ = bar (((etaInvD • qQ : Q) : G)) := hqBarEquiv_mk _
          _ = bar (rightConjugateElem q eta) := by
            congr 1
            rw [hD_smul_coe]
            simp [etaInvD, qQ, rightConjugateElem, mul_assoc]
      have hT_omega : T omegaBar = omegaBar := by
        have hbar_eta := hT_bar omega homega_Q
        change T (bar omega) = bar omega
        rw [hbar_eta]
        congr 1
        calc
          rightConjugateElem omega eta = eta⁻¹ * omega * eta := rfl
          _ = eta⁻¹ * (omega * eta) := by rw [mul_assoc]
          _ = eta⁻¹ * (eta * omega) := by rw [heta_comm_omega.eq]
          _ = omega := by simp
      have hsigma_mem_F3 : ∀ (d : D) (a : F3),
          sigmaHom d (a : E3) ∈ F3 := by
        intro d a
        by_cases ha : a = 0
        · rw [ha]
          simp
        · let aUnit : F3ˣ := Units.mk0 a ha
          let kD : KW_D :=
            ⟨⟨kOf aUnit,
                hKW_le_D (Subgroup.mem_sup_left (hkOf_mem aUnit))⟩,
              Subgroup.mem_sup_left (hkOf_mem aUnit)⟩
          let kConj : KW_D :=
            ⟨d * (kD : D) * d⁻¹,
              (inferInstance : KW_D.Normal).conj_mem
                (kD : D) kD.property d⟩
          have hkConj_K : (kConj : G) ∈ K := by
            exact hK_normal_D.conj_mem (kD : D)
              (show (kD : G) ∈ K from hkOf_mem aUnit) d
          have hscalar_K1 : scalar kConj ∈ K1 := by
            change
              (((kwIso
                (⟨(kConj : G), kConj.property⟩ :
                  (K ⊔ W : Subgroup G)) :
                    (K1 ⊔ W1 : Subgroup E3ˣ)) : E3ˣ) ∈ K1)
            exact hkwIso_mem_K1 (kConj : G) hkConj_K
          obtain ⟨b, hb⟩ := (hK1 (scalar kConj)).1 hscalar_K1
          have ha_scalar : (scalar kD : E3) = (a : E3) := by
            calc
              (scalar kD : E3) = kcoord (kOf aUnit) :=
                hscalar_value kD
              _ = ((aUnit : F3) : E3) := hkcoord_kOf aUnit
              _ = (a : E3) := rfl
          have hcompat := hsigma_scalar d kD
          have hcompat' : sigmaHom d (scalar kD : E3) =
              (scalar kConj : E3) := by
            simpa [kConj] using hcompat
          rw [← ha_scalar, hcompat', hb]
          exact (b : F3).property
      let restrictSigma (d : D) : F3 ≃+* F3 :=
        { toFun := fun a => ⟨sigmaHom d (a : E3), hsigma_mem_F3 d a⟩
          invFun := fun a =>
            ⟨sigmaHom d⁻¹ (a : E3), hsigma_mem_F3 d⁻¹ a⟩
          left_inv := by
            intro a
            apply Subtype.ext
            simp
          right_inv := by
            intro a
            apply Subtype.ext
            simp
          map_mul' := by
            intro a b
            apply Subtype.ext
            simp
          map_add' := by
            intro a b
            apply Subtype.ext
            simp }
      let sigmaFHom : D →* (F3 ≃+* F3) :=
        { toFun := restrictSigma
          map_one' := by
            ext a
            simp [restrictSigma]
          map_mul' := by
            intro d e
            ext a
            simp [restrictSigma] }
      let mu : F3 ≃+* F3 := sigmaFHom etaInvD
      have hmu_coe : ∀ a : F3,
          muE (a : E3) = ((mu a : F3) : E3) := by
        intro a
        rfl
      have hmu_odd : Odd (orderOf mu) := by
        have hetaInvD_odd : Odd (orderOf etaInvD) :=
          hA1.D_odd.of_dvd_nat (orderOf_dvd_natCard etaInvD)
        exact hetaInvD_odd.of_dvd_nat
          (orderOf_map_dvd sigmaFHom etaInvD)
      have hmu_zeta : muE z = z := by
        let zD : KW_D :=
          ⟨⟨zeta, hKW_le_D (Subgroup.mem_sup_right hzeta_W)⟩,
            Subgroup.mem_sup_right hzeta_W⟩
        let zConj : KW_D :=
          ⟨etaInvD * (zD : D) * etaInvD⁻¹,
            (inferInstance : KW_D.Normal).conj_mem
              (zD : D) zD.property etaInvD⟩
        have hzConj : zConj = zD := by
          apply Subtype.ext
          apply Subtype.ext
          dsimp [zConj, zD, etaInvD]
          simp only [inv_inv]
          calc
            eta⁻¹ * zeta * eta = eta⁻¹ * (zeta * eta) := by
              rw [mul_assoc]
            _ = eta⁻¹ * (eta * zeta) := by rw [heta_comm_zeta.eq]
            _ = zeta := by simp
        have hcompat := hsigma_scalar etaInvD zD
        have hcompat' : muE (scalar zD : E3) =
            (scalar zConj : E3) := by
          simpa [muE, zConj] using hcompat
        calc
          muE z = muE (scalar zD : E3) := by
            rw [hscalar_value]
          _ = (scalar zConj : E3) := hcompat'
          _ = (scalar zD : E3) := by rw [hzConj]
          _ = z := by
            rw [hscalar_value]
      have hs_conj_kOf (a : F3ˣ) :
          rightConjugateElem s (kOf a) =
            center ((a : F3) * theta (a : F3)) := by
        rw [hs_center]
        simpa using
          hcenter_conj_K_exact (kOf a) (hkOf_mem a) a
            (hkOf_coord a) 1
      have hs_conj_kOf_inv (a : F3ˣ) :
          rightConjugateElem s (kOf a)⁻¹ =
            center ((a : F3)⁻¹ * theta ((a : F3)⁻¹)) := by
        have ha_inv_mem : (kOf a)⁻¹ ∈ K := K.inv_mem (hkOf_mem a)
        have ha_inv_coord :
            (((kwIso
              (⟨(kOf a)⁻¹, Subgroup.mem_sup_left ha_inv_mem⟩ :
                (K ⊔ W : Subgroup G)) :
                  (K1 ⊔ W1 : Subgroup E3ˣ)) : E3ˣ) : E3) =
              (((a⁻¹ : F3ˣ) : F3) : E3) := by
          calc
            (((kwIso
              (⟨(kOf a)⁻¹, Subgroup.mem_sup_left ha_inv_mem⟩ :
                (K ⊔ W : Subgroup G)) :
                  (K1 ⊔ W1 : Subgroup E3ˣ)) : E3ˣ) : E3) =
                kcoord (kOf a)⁻¹ :=
              (hkcoord_of_mem_KW (kOf a)⁻¹
                (Subgroup.mem_sup_left ha_inv_mem)).symm
            _ = (kcoord (kOf a))⁻¹ :=
              hkcoord_inv (kOf a)
                (Subgroup.mem_sup_left (hkOf_mem a))
            _ = ((((a : F3) : E3))⁻¹) := by rw [hkcoord_kOf]
            _ = (((a⁻¹ : F3ˣ) : F3) : E3) := by simp
        rw [hs_center]
        simpa using
          hcenter_conj_K_exact (kOf a)⁻¹ ha_inv_mem a⁻¹
            ha_inv_coord 1
      have hs_conj_kOf_mem_Q0 (a : F3ˣ) :
          rightConjugateElem s (kOf a) ∈ Q0 := by
        rw [hs_conj_kOf]
        exact hcenter_mem_Q0 _
      have hs_conj_kOf_inv_mem_Q0 (a : F3ˣ) :
          rightConjugateElem s (kOf a)⁻¹ ∈ Q0 := by
        rw [hs_conj_kOf_inv]
        exact hcenter_mem_Q0 _
      have homega_mul_s_mem_Q (a : F3ˣ) :
          omega * rightConjugateElem s (kOf a) ∈ Q :=
        Q.mul_mem homega_Q
          (hsection3.section2.Q0_le_Q (hs_conj_kOf_mem_Q0 a))
      have homega_mul_s_ne_one (a : F3ˣ) :
          omega * rightConjugateElem s (kOf a) ≠ 1 := by
        intro hprod
        apply homega_not_Q0
        have homega_eq :
            omega = (rightConjugateElem s (kOf a))⁻¹ :=
          eq_inv_of_mul_eq_one_left hprod
        rw [homega_eq]
        exact Q0.inv_mem (hs_conj_kOf_mem_Q0 a)
      have hzeta_mem_peterfalviV : zeta ∈ peterfalviV D t := by
        rw [← hsection3.section2.V_eq]
        exact hsection3.section2.W_le_V hzeta_W
      have hzeta_D : zeta ∈ D := hzeta_mem_peterfalviV.1
      have hzeta_comm_t : Commute zeta t :=
        Subgroup.mem_centralizer_singleton_iff.mp
          hzeta_mem_peterfalviV.2
      have hzeta_fixed_t : rightConjugateElem zeta t = zeta := by
        simp [rightConjugateElem, hzeta_comm_t.eq, mul_assoc]
      have hinner_identity (a b : F3ˣ)
          (hnorm :
            (b : F3) * theta (b : F3) =
              alpha + (a : F3)⁻¹ * theta ((a : F3)⁻¹)) :
          f omega * rightConjugateElem s (kOf a)⁻¹ =
            rightConjugateElem
              (omega * rightConjugateElem s (kOf b)) zeta := by
        have homega_center_conj :
            rightConjugateElem (omega * center alpha) zeta =
              rightConjugateElem omega zeta * center alpha := by
          calc
            rightConjugateElem (omega * center alpha) zeta =
                rightConjugateElem omega zeta *
                  rightConjugateElem (center alpha) zeta := by
              simp [rightConjugateElem, mul_assoc]
            _ = rightConjugateElem omega zeta * center alpha := by
              rw [hcenter_conj_W zeta hzeta_W alpha]
        have hprod_conj :
            rightConjugateElem
                (omega * rightConjugateElem s (kOf b)) zeta =
              rightConjugateElem omega zeta *
                rightConjugateElem s (kOf b) := by
          calc
            rightConjugateElem
                (omega * rightConjugateElem s (kOf b)) zeta =
              rightConjugateElem omega zeta *
                  rightConjugateElem
                    (rightConjugateElem s (kOf b)) zeta := by
                simp [rightConjugateElem, mul_assoc]
            _ = rightConjugateElem omega zeta *
                rightConjugateElem s (kOf b) := by
              rw [hs_conj_kOf b, hcenter_conj_W zeta hzeta_W]
        calc
          f omega * rightConjugateElem s (kOf a)⁻¹ =
              rightConjugateElem omega⁻¹ zeta *
                rightConjugateElem s (kOf a)⁻¹ := by rw [hf_omega]
          _ = rightConjugateElem (omega * center alpha) zeta *
                rightConjugateElem s (kOf a)⁻¹ := by
            rw [homega_inv_shape]
          _ = (rightConjugateElem omega zeta * center alpha) *
                center ((a : F3)⁻¹ * theta ((a : F3)⁻¹)) := by
            rw [homega_center_conj, hs_conj_kOf_inv]
          _ = rightConjugateElem omega zeta *
                center
                  (alpha + (a : F3)⁻¹ * theta ((a : F3)⁻¹)) := by
            rw [mul_assoc, ← hcenter_add]
          _ = rightConjugateElem omega zeta *
                center ((b : F3) * theta (b : F3)) := by rw [← hnorm]
          _ = rightConjugateElem omega zeta *
                rightConjugateElem s (kOf b) := by rw [hs_conj_kOf]
          _ = rightConjugateElem
              (omega * rightConjugateElem s (kOf b)) zeta :=
            hprod_conj.symm
      have hf_conj_zeta (b : F3ˣ) :
          f (rightConjugateElem
              (omega * rightConjugateElem s (kOf b)) zeta) =
            rightConjugateElem
              (f (omega * rightConjugateElem s (kOf b))) zeta := by
        have htransport := PFchapter4section1.claim_H3 H Q D t f g h
          hA1.two_transitive hA1.point_stabilizer hA1.involution_t
          hA1.t_not_mem_H hA1.D_eq hA1.Q_normal_in_H
          hA1.Q_disjoint_D hA1.Q_sup_D hf_mem hg_mem hh_mem
          hcanonical_eq
          (omega * rightConjugateElem s (kOf b)) zeta
          (homega_mul_s_mem_Q b) (homega_mul_s_ne_one b) hzeta_D
        simpa [hzeta_fixed_t] using htransport
      let phiF : F3ˣ → E3 := fun a =>
        bar (f (omega * rightConjugateElem s (kOf a)))
      have h3 : ∀ a b : F3ˣ,
          (b : F3) * theta (b : F3) =
              alpha + (a : F3)⁻¹ * theta ((a : F3)⁻¹) →
            phiF a = z * (((a : F3) : E3)⁻¹ ^ 2) * phiF b := by
        intro a b hnorm
        have hsection2_eq := PFchapter4section2.claim_2
          H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
          hA1.two_transitive hA1.point_stabilizer hA1.involution_t
          hA1.t_not_mem_H hA1.D_eq hA1.Q_normal_in_H
          hA1.Q_disjoint_D hA1.Q_sup_D hf_mem hg_mem hh_mem
          hcanonical_eq omega (kOf a) homega_Q homega_not_Q0
          (hkOf_mem a)
        rw [hinner_identity a b hnorm, hf_conj_zeta b] at hsection2_eq
        have hfprod_b_mem_Q :
            f (omega * rightConjugateElem s (kOf b)) ∈ Q :=
          (hf_mem _ (homega_mul_s_mem_Q b)
            (homega_mul_s_ne_one b)).1
        have hzeta_KW : zeta ∈ K ⊔ W := Subgroup.mem_sup_right hzeta_W
        have hconj_zeta_mem_Q :
            rightConjugateElem
                (f (omega * rightConjugateElem s (kOf b))) zeta ∈ Q :=
          hQ_conj_KW _ hfprod_b_mem_Q zeta hzeta_KW
        have ha_inv_KW : (kOf a)⁻¹ ∈ K ⊔ W :=
          (K ⊔ W).inv_mem (Subgroup.mem_sup_left (hkOf_mem a))
        have ha_inv_sq_KW : (kOf a)⁻¹ ^ 2 ∈ K ⊔ W :=
          (K ⊔ W).pow_mem ha_inv_KW 2
        have houter_mem_Q :
            rightConjugateElem
                (rightConjugateElem
                  (f (omega * rightConjugateElem s (kOf b))) zeta)
                ((kOf a)⁻¹ ^ 2) ∈ Q :=
          hQ_conj_KW _ hconj_zeta_mem_Q _ ha_inv_sq_KW
        have hsa_inv_mem_Q0 : rightConjugateElem s (kOf a)⁻¹ ∈ Q0 :=
          hs_conj_kOf_inv_mem_Q0 a
        have hsa_inv_mem_Q : rightConjugateElem s (kOf a)⁻¹ ∈ Q :=
          hsection3.section2.Q0_le_Q hsa_inv_mem_Q0
        have hbar_relation :
            phiF a = (((a : F3) : E3)⁻¹) ^ 2 *
              (z * phiF b) := by
          calc
            phiF a = bar (rightConjugateElem
                  (rightConjugateElem
                    (f (omega * rightConjugateElem s (kOf b))) zeta)
                  ((kOf a)⁻¹ ^ 2) *
                rightConjugateElem s (kOf a)⁻¹) :=
              congrArg bar hsection2_eq
            _ = bar (rightConjugateElem
                    (rightConjugateElem
                      (f (omega * rightConjugateElem s (kOf b))) zeta)
                    ((kOf a)⁻¹ ^ 2)) +
                  bar (rightConjugateElem s (kOf a)⁻¹) :=
              hbar_mul _ houter_mem_Q _ hsa_inv_mem_Q
            _ = kcoord ((kOf a)⁻¹ ^ 2) *
                  bar (rightConjugateElem
                    (f (omega * rightConjugateElem s (kOf b))) zeta) +
                0 := by
              rw [hbar_conj _ hconj_zeta_mem_Q _ ha_inv_sq_KW,
                (hbar_Q0 _ hsa_inv_mem_Q).2 hsa_inv_mem_Q0]
            _ = kcoord ((kOf a)⁻¹ ^ 2) *
                (kcoord zeta * phiF b) := by
              rw [hbar_conj _ hfprod_b_mem_Q zeta hzeta_KW, add_zero]
            _ = (((a : F3) : E3)⁻¹) ^ 2 * (z * phiF b) := by
              rw [hkcoord_pow (kOf a)⁻¹ ha_inv_KW 2,
                hkcoord_inv (kOf a)
                  (Subgroup.mem_sup_left (hkOf_mem a)),
                hkcoord_kOf]
        calc
          phiF a = (((a : F3) : E3)⁻¹) ^ 2 * (z * phiF b) :=
            hbar_relation
          _ = z * (((a : F3) : E3)⁻¹ ^ 2) * phiF b := by ring
      have homega_ne_one : omega ≠ 1 := by
        intro homega
        exact homega_not_Q0 (homega ▸ Q0.one_mem)
      have homega_inv_mem_Q : omega⁻¹ ∈ Q := Q.inv_mem homega_Q
      have homega_inv_ne_one : omega⁻¹ ≠ 1 := by
        simpa using homega_ne_one
      have homega_inv_not_Q0 : omega⁻¹ ∉ Q0 := by
        intro homega_inv_mem
        exact homega_not_Q0 (by simpa using Q0.inv_mem homega_inv_mem)
      have hf_omega_inv :
          f omega⁻¹ = rightConjugateElem omega zeta⁻¹ := by
        have hffomega := PFchapter4section1.claim_H2 H Q D t f g h
          hA1.two_transitive hA1.point_stabilizer hA1.involution_t
          hA1.t_not_mem_H hA1.D_eq hA1.Q_normal_in_H
          hA1.Q_disjoint_D hA1.Q_sup_D hf_mem hg_mem hh_mem
          hcanonical_eq omega homega_Q homega_ne_one
        have htransport := PFchapter4section1.claim_H3 H Q D t f g h
          hA1.two_transitive hA1.point_stabilizer hA1.involution_t
          hA1.t_not_mem_H hA1.D_eq hA1.Q_normal_in_H
          hA1.Q_disjoint_D hA1.Q_sup_D hf_mem hg_mem hh_mem
          hcanonical_eq omega⁻¹ zeta homega_inv_mem_Q
          homega_inv_ne_one hzeta_D
        have hconj : rightConjugateElem (f omega⁻¹) zeta = omega := by
          calc
            rightConjugateElem (f omega⁻¹) zeta =
                rightConjugateElem (f omega⁻¹)
                  (rightConjugateElem zeta t) := by rw [hzeta_fixed_t]
            _ = f (rightConjugateElem omega⁻¹ zeta) := htransport.symm
            _ = f (f omega) := by rw [hf_omega]
            _ = omega := hffomega
        have hback := congrArg
          (fun x : G => rightConjugateElem x zeta⁻¹) hconj
        simpa [rightConjugateElem, mul_assoc] using hback
      have hg_omega_inv :
          g omega⁻¹ = rightConjugateElem omega zeta := by
        have hH1 := PFchapter4section1.claim_H1 H Q D t f g h
          hA1.two_transitive hA1.point_stabilizer hA1.involution_t
          hA1.t_not_mem_H hA1.D_eq hA1.Q_normal_in_H
          hA1.Q_disjoint_D hA1.Q_sup_D hf_mem hg_mem hh_mem
          hcanonical_eq omega⁻¹ homega_inv_mem_Q homega_inv_ne_one
        have hH1' : f omega = (g omega⁻¹)⁻¹ := by simpa using hH1
        calc
          g omega⁻¹ = ((g omega⁻¹)⁻¹)⁻¹ := by simp
          _ = (f omega)⁻¹ := by rw [hH1']
          _ = (rightConjugateElem omega⁻¹ zeta)⁻¹ := by rw [hf_omega]
          _ = rightConjugateElem omega zeta := by
            simp [rightConjugateElem, mul_assoc]
      have heta_mem_peterfalviV : eta ∈ peterfalviV D t := by
        rw [← hsection3.section2.V_eq]
        exact heta_V
      have heta_comm_t : Commute eta t :=
        Subgroup.mem_centralizer_singleton_iff.mp
          heta_mem_peterfalviV.2
      have hzeta_comm_t : Commute zeta t :=
        Subgroup.mem_centralizer_singleton_iff.mp
          hzeta_mem_peterfalviV.2
      have rightConjugateElem_eq_self_of_commute
          {x : G} (hx : Commute x t) :
          rightConjugateElem x t = x := by
        calc
          t⁻¹ * x * t = t⁻¹ * (x * t) := by rw [mul_assoc]
          _ = t⁻¹ * (t * x) := by rw [hx.eq]
          _ = x := by simp
      have heta_fixed_t : rightConjugateElem eta t = eta :=
        rightConjugateElem_eq_self_of_commute heta_comm_t
      have hhomega_fixed_t : rightConjugateElem (h omega) t = h omega := by
        rw [hh_omega]
        calc
          rightConjugateElem (zeta ^ 3 * eta⁻¹) t =
              rightConjugateElem (zeta ^ 3) t *
                rightConjugateElem eta⁻¹ t := by
            simp [rightConjugateElem, mul_assoc]
          _ = zeta ^ 3 * eta⁻¹ := by
            rw [rightConjugateElem_eq_self_of_commute
                  (hzeta_comm_t.pow_left 3),
              rightConjugateElem_eq_self_of_commute
                heta_comm_t.inv_left]
      have hh_omega_inv : h omega⁻¹ = eta * zeta⁻¹ ^ 3 := by
        have hH4b := PFchapter4section1.claim_H4_b H Q D t f g h
          hA1.two_transitive hA1.point_stabilizer hA1.involution_t
          hA1.t_not_mem_H hA1.D_eq hA1.Q_normal_in_H
          hA1.Q_disjoint_D hA1.Q_sup_D hf_mem hg_mem hh_mem
          hcanonical_eq omega homega_Q homega_ne_one
        calc
          h omega⁻¹ = (rightConjugateElem (h omega) t)⁻¹ := hH4b
          _ = (h omega)⁻¹ := by rw [hhomega_fixed_t]
          _ = (zeta ^ 3 * eta⁻¹)⁻¹ := by rw [hh_omega]
          _ = eta * zeta⁻¹ ^ 3 := by group
      have hh_omega_inv_fixed_t :
          rightConjugateElem (h omega⁻¹) t = h omega⁻¹ := by
        rw [hh_omega_inv]
        calc
          rightConjugateElem (eta * zeta⁻¹ ^ 3) t =
              rightConjugateElem eta t *
                rightConjugateElem (zeta⁻¹ ^ 3) t := by
            simp [rightConjugateElem, mul_assoc]
          _ = eta * zeta⁻¹ ^ 3 := by
            rw [heta_fixed_t,
              rightConjugateElem_eq_self_of_commute
                (hzeta_comm_t.inv_left.pow_left 3)]
      have hs_mem_Q : s ∈ Q :=
        hsection3.section2.Q0_le_Q
          ((hsection3.section2.Q0_def s).2
            (Or.inr ⟨hsection3.s_mem_H, hsection3.s_involution⟩))
      have hgroup4 : ∀ a : F3ˣ,
          rightConjugateElem
              (f (omega * rightConjugateElem s (kOf a)))
              (zeta⁻¹ * (kOf a) ^ 2) *
                rightConjugateElem s (kOf a) =
            rightConjugateElem
                (f (omega * rightConjugateElem s (kOf a)))
                (zeta⁻¹ ^ 2 * eta) *
              rightConjugateElem omega zeta⁻¹ := by
        intro a
        have ha_mem_D : kOf a ∈ D :=
          hsection3.section2.K_le_D (hkOf_mem a)
        have ha_mem_H : kOf a ∈ H :=
          PFchapter4section1.rankOneSplit_D_le_M hA1.D_eq ha_mem_D
        have hsa_mem_Q : rightConjugateElem s (kOf a) ∈ Q :=
          PFchapter4section1.h6_rightConjugateElem_mem_Q_of_mem_M
            (PFchapter4section1.rankOneSplit_Q_le_M hA1.Q_sup_D)
            hA1.Q_normal_in_H hs_mem_Q ha_mem_H
        have hsa_involution :
            IsInvolution (rightConjugateElem s (kOf a)) :=
          isInvolution_rightConjugateElem hsection3.s_involution
        have hsa_mem_H : rightConjugateElem s (kOf a) ∈ H :=
          H.mul_mem (H.mul_mem (H.inv_mem ha_mem_H)
            hsection3.s_mem_H) ha_mem_H
        have hsa_mem_Q0 : rightConjugateElem s (kOf a) ∈ Q0 :=
          (hsection3.section2.Q0_def _).2
            (Or.inr ⟨hsa_mem_H, hsa_involution⟩)
        have hprod_mem_Q :
            omega * rightConjugateElem s (kOf a) ∈ Q :=
          Q.mul_mem homega_Q hsa_mem_Q
        have hprod_ne_one :
            omega * rightConjugateElem s (kOf a) ≠ 1 := by
          intro hprod
          apply homega_not_Q0
          have homega_eq :
              omega = (rightConjugateElem s (kOf a))⁻¹ :=
            eq_inv_of_mul_eq_one_left hprod
          rw [homega_eq, hsa_involution.inv_eq_self]
          exact hsa_mem_Q0
        have hzeta_mem_peterfalviW :
            zeta ∈ peterfalviW V (K : Set G) := by
          rw [← hsection3.section2.W_eq]
          exact hzeta_W
        have ha_comm_zeta : Commute (kOf a) zeta :=
          Subgroup.mem_centralizer_iff.mp hzeta_mem_peterfalviW.2
            (kOf a) (hkOf_mem a)
        have hV_eq_s :
            peterfalviV D t =
              D ⊓ Subgroup.centralizer ({s} : Set G) :=
          (PFchapter1section1.proposition_5 H D Q t s hA1
            hsection3.s_mem_H hsection3.s_involution
            hsection3.s_conjugate).1
        have hs_comm_zeta : Commute s zeta := by
          have hzeta_mem_Cs :
              zeta ∈ Subgroup.centralizer ({s} : Set G) := by
            rw [hV_eq_s] at hzeta_mem_peterfalviV
            exact hzeta_mem_peterfalviV.2
          exact
            (Subgroup.mem_centralizer_singleton_iff.mp hzeta_mem_Cs).symm
        have hsa_comm_zeta :
            Commute (rightConjugateElem s (kOf a)) zeta := by
          have hcomm : Commute ((kOf a)⁻¹ * s * kOf a) zeta :=
            (ha_comm_zeta.inv_left.mul_left hs_comm_zeta).mul_left
              ha_comm_zeta
          simpa [rightConjugateElem, mul_assoc] using hcomm
        have hsa_fixed_zeta :
            rightConjugateElem
                (rightConjugateElem s (kOf a)) zeta =
              rightConjugateElem s (kOf a) :=
          hsa_comm_zeta.symm.inv_mul_cancel
        have hsa_fixed_zeta_inv :
            rightConjugateElem
                (rightConjugateElem s (kOf a)) zeta⁻¹ =
              rightConjugateElem s (kOf a) :=
          hsa_comm_zeta.inv_right.symm.inv_mul_cancel
        have hprod_conj_zeta :
            rightConjugateElem
                (omega * rightConjugateElem s (kOf a)) zeta =
              rightConjugateElem omega zeta *
                rightConjugateElem s (kOf a) := by
          calc
            rightConjugateElem
                (omega * rightConjugateElem s (kOf a)) zeta =
              rightConjugateElem omega zeta *
                  rightConjugateElem
                    (rightConjugateElem s (kOf a)) zeta := by
                simp [rightConjugateElem, mul_assoc]
            _ = rightConjugateElem omega zeta *
                rightConjugateElem s (kOf a) := by
              rw [hsa_fixed_zeta]
        have hprod_conj_zeta_inv :
            rightConjugateElem
                (omega * rightConjugateElem s (kOf a)) zeta⁻¹ =
              rightConjugateElem omega zeta⁻¹ *
                rightConjugateElem s (kOf a) := by
          calc
            rightConjugateElem
                (omega * rightConjugateElem s (kOf a)) zeta⁻¹ =
              rightConjugateElem omega zeta⁻¹ *
                  rightConjugateElem
                    (rightConjugateElem s (kOf a)) zeta⁻¹ := by
                simp [rightConjugateElem, mul_assoc]
            _ = rightConjugateElem omega zeta⁻¹ *
                rightConjugateElem s (kOf a) := by
              rw [hsa_fixed_zeta_inv]
        have hf_prod_zeta :
            f (rightConjugateElem omega zeta *
                rightConjugateElem s (kOf a)) =
              rightConjugateElem
                (f (omega * rightConjugateElem s (kOf a))) zeta := by
          have htransport := PFchapter4section1.claim_H3
            H Q D t f g h hA1.two_transitive hA1.point_stabilizer
            hA1.involution_t hA1.t_not_mem_H hA1.D_eq
            hA1.Q_normal_in_H hA1.Q_disjoint_D hA1.Q_sup_D
            hf_mem hg_mem hh_mem hcanonical_eq
            (omega * rightConjugateElem s (kOf a)) zeta
            hprod_mem_Q hprod_ne_one hzeta_D
          rw [hprod_conj_zeta] at htransport
          simpa [hzeta_fixed_t] using htransport
        have hf_prod_zeta_inv :
            f (rightConjugateElem omega zeta⁻¹ *
                rightConjugateElem s (kOf a)) =
              rightConjugateElem
                (f (omega * rightConjugateElem s (kOf a))) zeta⁻¹ := by
          have hzeta_inv_fixed_t :
              rightConjugateElem zeta⁻¹ t = zeta⁻¹ := by
            exact rightConjugateElem_eq_self_of_commute
              hzeta_comm_t.inv_left
          have htransport := PFchapter4section1.claim_H3
            H Q D t f g h hA1.two_transitive hA1.point_stabilizer
            hA1.involution_t hA1.t_not_mem_H hA1.D_eq
            hA1.Q_normal_in_H hA1.Q_disjoint_D hA1.Q_sup_D
            hf_mem hg_mem hh_mem hcanonical_eq
            (omega * rightConjugateElem s (kOf a)) zeta⁻¹
            hprod_mem_Q hprod_ne_one (D.inv_mem hzeta_D)
          rw [hprod_conj_zeta_inv] at htransport
          simpa [hzeta_inv_fixed_t] using htransport
        have hclaim2 := PFchapter4section2.claim_2
          H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
          hA1.two_transitive hA1.point_stabilizer hA1.involution_t
          hA1.t_not_mem_H hA1.D_eq hA1.Q_normal_in_H
          hA1.Q_disjoint_D hA1.Q_sup_D hf_mem hg_mem hh_mem
          hcanonical_eq omega⁻¹ (kOf a)⁻¹ homega_inv_mem_Q
          homega_inv_not_Q0 (K.inv_mem (hkOf_mem a))
        have hclaim3 := PFchapter4section2.claim_3
          H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
          hA1.two_transitive hA1.point_stabilizer hA1.involution_t
          hA1.t_not_mem_H hA1.D_eq hA1.Q_normal_in_H
          hA1.Q_disjoint_D hA1.Q_sup_D hf_mem hg_mem hh_mem
          hcanonical_eq omega⁻¹ (kOf a)⁻¹ homega_inv_mem_Q
          homega_inv_not_Q0 (K.inv_mem (hkOf_mem a))
        have hfirst :
            f (omega⁻¹ * rightConjugateElem s (kOf a)⁻¹) =
              rightConjugateElem
                  (f (omega * rightConjugateElem s (kOf a)))
                  (zeta⁻¹ * (kOf a) ^ 2) *
                rightConjugateElem s (kOf a) := by
          calc
            f (omega⁻¹ * rightConjugateElem s (kOf a)⁻¹) =
                rightConjugateElem
                    (f (f omega⁻¹ *
                      rightConjugateElem s ((kOf a)⁻¹)⁻¹))
                    (((kOf a)⁻¹)⁻¹ ^ 2) *
                  rightConjugateElem s ((kOf a)⁻¹)⁻¹ := hclaim2
            _ = rightConjugateElem
                  (rightConjugateElem
                    (f (omega * rightConjugateElem s (kOf a))) zeta⁻¹)
                  ((kOf a) ^ 2) * rightConjugateElem s (kOf a) := by
              rw [inv_inv, hf_omega_inv, hf_prod_zeta_inv]
            _ = rightConjugateElem
                  (f (omega * rightConjugateElem s (kOf a)))
                  (zeta⁻¹ * (kOf a) ^ 2) *
                rightConjugateElem s (kOf a) := by
              simp [rightConjugateElem, mul_assoc]
        have hactor :
            zeta * (eta * zeta⁻¹ ^ 3) = zeta⁻¹ ^ 2 * eta := by
          calc
            zeta * (eta * zeta⁻¹ ^ 3) =
                (zeta * eta) * zeta⁻¹ ^ 3 := by group
            _ = (eta * zeta) * zeta⁻¹ ^ 3 := by
              rw [← heta_comm_zeta.eq]
            _ = eta * zeta⁻¹ ^ 2 := by group
            _ = zeta⁻¹ ^ 2 * eta :=
              (heta_comm_zeta.inv_right.pow_right 2).eq
        have hsecond :
            f (omega⁻¹ * rightConjugateElem s (kOf a)⁻¹) =
              rightConjugateElem
                  (f (omega * rightConjugateElem s (kOf a)))
                  (zeta⁻¹ ^ 2 * eta) *
                rightConjugateElem omega zeta⁻¹ := by
          calc
            f (omega⁻¹ * rightConjugateElem s (kOf a)⁻¹) =
                rightConjugateElem
                    (f (g omega⁻¹ *
                      rightConjugateElem s ((kOf a)⁻¹)⁻¹))
                    (rightConjugateElem (h omega⁻¹) t) * f omega⁻¹ :=
              hclaim3
            _ = rightConjugateElem
                  (rightConjugateElem
                    (f (omega * rightConjugateElem s (kOf a))) zeta)
                  (eta * zeta⁻¹ ^ 3) *
                rightConjugateElem omega zeta⁻¹ := by
              rw [inv_inv, hg_omega_inv, hf_prod_zeta,
                hh_omega_inv_fixed_t, hh_omega_inv, hf_omega_inv]
            _ = rightConjugateElem
                  (f (omega * rightConjugateElem s (kOf a)))
                  (zeta⁻¹ ^ 2 * eta) *
                rightConjugateElem omega zeta⁻¹ := by
              congr 1
              simp only [rightConjugateElem]
              rw [← hactor]
              group
        exact hfirst.symm.trans hsecond
      have h4 : ∀ a : F3ˣ,
          (((a : F3) : E3) ^ 2) * phiF a =
            z⁻¹ * T (phiF a) + omegaBar := by
        intro a
        let qa : G :=
          f (omega * rightConjugateElem s (kOf a))
        have hqa_Q : qa ∈ Q :=
          (hf_mem _ (homega_mul_s_mem_Q a)
            (homega_mul_s_ne_one a)).1
        have hka_KW : kOf a ∈ K ⊔ W :=
          Subgroup.mem_sup_left (hkOf_mem a)
        have hka_sq_KW : (kOf a) ^ 2 ∈ K ⊔ W :=
          (K ⊔ W).pow_mem hka_KW 2
        have hzeta_KW : zeta ∈ K ⊔ W :=
          Subgroup.mem_sup_right hzeta_W
        have hzeta_inv_KW : zeta⁻¹ ∈ K ⊔ W :=
          (K ⊔ W).inv_mem hzeta_KW
        have hzeta_inv_sq_KW : zeta⁻¹ ^ 2 ∈ K ⊔ W :=
          (K ⊔ W).pow_mem hzeta_inv_KW 2
        have hleft_actor_KW : zeta⁻¹ * (kOf a) ^ 2 ∈ K ⊔ W :=
          (K ⊔ W).mul_mem hzeta_inv_KW hka_sq_KW
        have hleft_Q :
            rightConjugateElem qa (zeta⁻¹ * (kOf a) ^ 2) ∈ Q :=
          hQ_conj_KW qa hqa_Q _ hleft_actor_KW
        have hsa_Q0 : rightConjugateElem s (kOf a) ∈ Q0 :=
          hs_conj_kOf_mem_Q0 a
        have hsa_Q : rightConjugateElem s (kOf a) ∈ Q :=
          hsection3.section2.Q0_le_Q hsa_Q0
        let qz : G := rightConjugateElem qa (zeta⁻¹ ^ 2)
        have hqz_Q : qz ∈ Q :=
          hQ_conj_KW qa hqa_Q _ hzeta_inv_sq_KW
        have hsplit :
            rightConjugateElem qa (zeta⁻¹ ^ 2 * eta) =
              rightConjugateElem qz eta := by
          dsimp only [qz]
          simp only [rightConjugateElem, mul_inv_rev]
          group
        have hright_Q :
            rightConjugateElem qa (zeta⁻¹ ^ 2 * eta) ∈ Q := by
          rw [hsplit]
          exact PFchapter4section1.h6_rightConjugateElem_mem_Q_of_mem_M
            (PFchapter4section1.rankOneSplit_Q_le_M hA1.Q_sup_D)
            hA1.Q_normal_in_H hqz_Q (hA1.D_le_H heta_D)
        have homega_zeta_inv_Q :
            rightConjugateElem omega zeta⁻¹ ∈ Q :=
          hQ_conj_KW omega homega_Q zeta⁻¹ hzeta_inv_KW
        have hleft_bar :
            bar (rightConjugateElem qa
                (zeta⁻¹ * (kOf a) ^ 2)) =
              z⁻¹ * (((a : F3) : E3) ^ 2) * phiF a := by
          rw [hbar_conj qa hqa_Q _ hleft_actor_KW,
            hkcoord_mul zeta⁻¹ hzeta_inv_KW ((kOf a) ^ 2) hka_sq_KW,
            hkcoord_inv zeta hzeta_KW,
            hkcoord_pow (kOf a) hka_KW 2, hkcoord_kOf]
        have hsa_bar : bar (rightConjugateElem s (kOf a)) = 0 :=
          (hbar_Q0 _ hsa_Q).2 hsa_Q0
        have hright_bar :
            bar (rightConjugateElem qa (zeta⁻¹ ^ 2 * eta)) =
              z⁻¹ ^ 2 * T (phiF a) := by
          calc
            bar (rightConjugateElem qa (zeta⁻¹ ^ 2 * eta)) =
                bar (rightConjugateElem qz eta) :=
              congrArg bar hsplit
            _ = T (bar qz) := (hT_bar qz hqz_Q).symm
            _ = T (z⁻¹ ^ 2 * phiF a) := by
              congr 1
              dsimp only [qz]
              rw [hbar_conj qa hqa_Q _ hzeta_inv_sq_KW,
                hkcoord_pow zeta⁻¹ hzeta_inv_KW 2,
                hkcoord_inv zeta hzeta_KW]
            _ = muE (z⁻¹ ^ 2) * T (phiF a) :=
              hT_semilinear (z⁻¹ ^ 2) (phiF a)
            _ = z⁻¹ ^ 2 * T (phiF a) := by
              simp only [map_pow, map_inv₀, hmu_zeta]
        have homega_zeta_inv_bar :
            bar (rightConjugateElem omega zeta⁻¹) =
              z⁻¹ * omegaBar := by
          rw [hbar_conj omega homega_Q zeta⁻¹ hzeta_inv_KW,
            hkcoord_inv zeta hzeta_KW]
        have hbar_eq :
            z⁻¹ * (((a : F3) : E3) ^ 2) * phiF a + 0 =
              z⁻¹ ^ 2 * T (phiF a) + z⁻¹ * omegaBar := by
          calc
            z⁻¹ * (((a : F3) : E3) ^ 2) * phiF a + 0 =
                bar (rightConjugateElem qa
                    (zeta⁻¹ * (kOf a) ^ 2) *
                  rightConjugateElem s (kOf a)) := by
              rw [hbar_mul _ hleft_Q _ hsa_Q, hleft_bar, hsa_bar]
            _ = bar (rightConjugateElem qa (zeta⁻¹ ^ 2 * eta) *
                  rightConjugateElem omega zeta⁻¹) := by
              exact congrArg bar (hgroup4 a)
            _ = z⁻¹ ^ 2 * T (phiF a) + z⁻¹ * omegaBar := by
              rw [hbar_mul _ hright_Q _ homega_zeta_inv_Q,
                hright_bar, homega_zeta_inv_bar]
        calc
          (((a : F3) : E3) ^ 2) * phiF a =
              z * (z⁻¹ * (((a : F3) : E3) ^ 2) * phiF a + 0) := by
            field_simp [hz_ne]
            ring
          _ = z * (z⁻¹ ^ 2 * T (phiF a) + z⁻¹ * omegaBar) := by
            rw [hbar_eq]
          _ = z⁻¹ * T (phiF a) + omegaBar := by
            field_simp [hz_ne]
      obtain ⟨exceptional, h10⟩ :=
        equation10_of_semilinear_relations F3 theta mu muE T z omegaBar
          alpha c phiF hthetaOdd hz_not_mem_F3 homegaBar_ne hc hmu_coe
            hmu_zeta hT_semilinear hT_omega h3 h4
      have hmu_one : mu = 1 := by
        apply equation_10_forces_ringAut_one F3 mu z exceptional hmu_odd
        intro X hXzero hXexceptional
        simpa only [hc] using h10 X hXzero hXexceptional
      have hscalar_injective : Function.Injective scalar := by
        intro a b hab
        apply kwDToKW.injective
        apply kwIso.injective
        apply Subtype.ext
        exact hab
      have heta_centralizes_K : eta ∈
          Subgroup.centralizer (K : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        let kKW : (K ⊔ W : Subgroup G) :=
          ⟨k, Subgroup.mem_sup_left hk⟩
        let kD : KW_D :=
          ⟨⟨k, hKW_le_D (Subgroup.mem_sup_left hk)⟩,
            Subgroup.mem_sup_left hk⟩
        let kUnit : E3ˣ :=
          ((kwIso kKW : (K1 ⊔ W1 : Subgroup E3ˣ)) : E3ˣ)
        have hkUnit_K1 : kUnit ∈ K1 := by
          simpa [kUnit, kKW] using hkwIso_mem_K1 k hk
        obtain ⟨b, hb⟩ := (hK1 kUnit).1 hkUnit_K1
        have hscalar_k : (scalar kD : E3) = ((b : F3) : E3) := by
          calc
            (scalar kD : E3) = kcoord k := hscalar_value kD
            _ = (((kwIso kKW :
                (K1 ⊔ W1 : Subgroup E3ˣ)) : E3ˣ) : E3) := by
              simpa [kKW] using
                hkcoord_of_mem_KW k (Subgroup.mem_sup_left hk)
            _ = (kUnit : E3) := rfl
            _ = ((b : F3) : E3) := hb
        let kConj : KW_D :=
          ⟨etaInvD * (kD : D) * etaInvD⁻¹,
            (inferInstance : KW_D.Normal).conj_mem
              (kD : D) kD.property etaInvD⟩
        have hcompat := hsigma_scalar etaInvD kD
        have hcompat' : muE (scalar kD : E3) =
            (scalar kConj : E3) := by
          simpa [muE, kConj] using hcompat
        have hmu_b : muE ((b : F3) : E3) = ((b : F3) : E3) := by
          calc
            muE ((b : F3) : E3) = ((mu b : F3) : E3) := hmu_coe b
            _ = ((b : F3) : E3) := by rw [hmu_one]; rfl
        have hscalar_values : (scalar kConj : E3) =
            (scalar kD : E3) := by
          calc
            (scalar kConj : E3) = muE (scalar kD : E3) := hcompat'.symm
            _ = muE ((b : F3) : E3) := by rw [hscalar_k]
            _ = ((b : F3) : E3) := hmu_b
            _ = (scalar kD : E3) := hscalar_k.symm
        have hscalar_eq : scalar kConj = scalar kD := by
          apply Units.ext
          exact hscalar_values
        have hkConj_eq : kConj = kD := hscalar_injective hscalar_eq
        have hconj_eq : eta⁻¹ * k * eta = k := by
          have hcoe := congrArg (fun x : KW_D => (x : G)) hkConj_eq
          simpa [kConj, kD, etaInvD] using hcoe
        calc
          k * eta = eta * (eta⁻¹ * k * eta) := by group
          _ = eta * k := by rw [hconj_eq]
      have heta_W : eta ∈ W := by
        rw [hsection3.section2.W_eq]
        exact ⟨heta_V, heta_centralizes_K⟩
      have hh_omega_W : h omega ∈ W := by
        rw [hh_omega]
        exact W.mul_mem (W.pow_mem hzeta_W 3) (W.inv_mem heta_W)
      obtain ⟨L0, hL0, q0, hL0_eq, hodd0, hq0, hq0_gt, hunitary0⟩ :=
        PFchapter4section3.corollary_1_of_seed
          H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2 hC3
            hQ_two hf_mem hg_mem hh_mem hcanonical_eq omega zeta
              homega_Q homega_not_Q0 hzeta_W hzeta_ne hf_omega hh_omega_W
      exact ⟨L0, hL0, q0, hodd0, hq0, hq0_gt,
        Or.inr (Or.inr hunitary0)⟩

end PFchapter4section4
end CFSG.BenderSuzuki
