module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23cNine.Generic
public import CFSG.Quasithin.H13.U4ParPoint

import CFSG.ClassicalGroups.UnitaryFlag.StatedBridge
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SU4Borel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SU4Char
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SU4Act
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SU4Parabolic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSU44.FixedLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.ReduceLine
import CFSG.LocalAnalysis.UniquenessCase.UC22P21c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTab23cNine

open Matrix CFSG.Open CFSG.Quasithin CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin.H13.U4Par
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (flagStabilizer)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
open CFSG.LocalAnalysis.UniquenessCase.UC22.KSUE

private lemma fixed_ie1_of_mem_hypUnitriangular {a : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData 2 a K} {g : ↥(hypSU h 2 0)} (hg : g ∈ hypUnitriangular h 2 0) :
    (((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ
      (Pi.single ie1 1 : HypIndex 2 0 → K)) = Pi.single ie1 1 := by
  have h := (KSUE.fixed_hypUnitriangular_iff h (Pi.single ie1 1 : HypIndex 2 0 → K)).mpr
    ⟨1, by rw [one_smul]⟩
  exact h g hg

private lemma su4Coroot_one {a : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 a K) :
    su4Coroot h (1 : Kˣ) = 1 := by
  have hord := orderOf_su4Coroot h (1 : Kˣ)
  rw [orderOf_one] at hord
  exact orderOf_eq_one_iff.mp hord

private lemma mem_hypBorel_of_mem_hinf_vecStab {a : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 a K) {t : ↥(hypSU h 2 0)}
    (ht : t ∈ Hinf (flagStabilizer h 2 0 {2}) ⊓
      KTabC.vecStab (hypSU h 2 0).subtype (Pi.single ie1 1 : HypIndex 2 0 → K)) :
    t ∈ hypBorel h 2 0 := by
  obtain ⟨htQα, htVec⟩ := Subgroup.mem_inf.mp ht
  have htQα' : t ∈ flagStabilizer h 2 0 {2} := uc22p21c_Hinf_le _ htQα
  have htfix : (((t : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ
      (Pi.single ie1 1 : HypIndex 2 0 → K)) = Pi.single ie1 1 := by
    simpa using KTabC.mem_vecStab.mp htVec
  have htP : t ∈ parP h := by
    rw [mem_parP_iff h t]
    intro c hc
    have hcol := congrFun htfix c
    rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_eq_of_ne hc] at hcol
    exact hcol
  rw [← su4_parP_inf_flagStabilizer_eq_hypBorel h]
  exact ⟨htP, htQα'⟩

theorem su4_eq_one_of_mem_hinf_vecStab {a : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 a K) {t : ↥(hypSU h 2 0)}
    (ht : t ∈ Hinf (flagStabilizer h 2 0 {2}) ⊓
      KTabC.vecStab (hypSU h 2 0).subtype (Pi.single ie1 1 : HypIndex 2 0 → K))
    (hodd : Odd (orderOf t)) : t = 1 := by
  have htB : t ∈ hypBorel h 2 0 := mem_hypBorel_of_mem_hinf_vecStab h ht
  have htfix : (((t : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ
      (Pi.single ie1 1 : HypIndex 2 0 → K)) = Pi.single ie1 1 := by
    simpa using KTabC.mem_vecStab.mp ht.2
  obtain ⟨e, heU, hetor⟩ := su4_exists_conj_mem_hypTorus h htB hodd.not_two_dvd_nat
  have heB : e ∈ hypBorel h 2 0 := hypUnitriangular_le_hypBorel h heU
  have he_mem : e ∈ parP h ⊓ flagStabilizer h 2 0 {2} := by
    rw [su4_parP_inf_flagStabilizer_eq_hypBorel h]
    exact heB
  have hconjHinf : e * t * e⁻¹ ∈ Hinf (flagStabilizer h 2 0 {2}) :=
    suo_conj_mem_hinf he_mem.2 ht.1
  have hdiag := su4_diag_mul_eq_one_of_mem_hinf h hconjHinf (hypTorus_le_hypBorel h hetor)
  obtain ⟨c, hc⟩ := su4_exists_eq_coroot_of_mem_hypTorus h hetor hdiag
  have hefix := fixed_ie1_of_mem_hypUnitriangular heU
  have heinvfix := fixed_ie1_of_mem_hypUnitriangular (Subgroup.inv_mem _ heU)
  have hcmat : (((su4Coroot h c : ↥(hypSU h 2 0)) : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      (((e : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        (((t : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
          (((e⁻¹ : ↥(hypSU h 2 0)) : GL (HypIndex 2 0) K) :
            Matrix (HypIndex 2 0) (HypIndex 2 0) K))) := by
    have h := congrArg (fun g : ↥(hypSU h 2 0) =>
      (((g : GL (HypIndex 2 0) K)) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)) hc.symm
    simpa only [coe_mul_hypSU, mul_assoc] using h
  have hcfix : (((su4Coroot h c : ↥(hypSU h 2 0)) : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ
        (Pi.single ie1 1 : HypIndex 2 0 → K) = Pi.single ie1 1 := by
    simp only [hcmat, ← Matrix.mulVec_mulVec, htfix, heinvfix, hefix]
  have hcval : (c : K) = 1 := by
    have h := congrFun hcfix ie1
    simpa [coe_su4Coroot, Matrix.mulVec_single_one, Matrix.col_apply,
      Matrix.diagonal_apply_eq, Pi.single_eq_same, ie1, torusEntries, Matrix.cons_val_zero] using h
  have hc1 : c = 1 := Units.ext hcval
  have hfin : e * t * e⁻¹ = 1 := by
    rw [hc, hc1, su4Coroot_one h]
  have h2 : e * t = e * 1 := by
    rw [mul_one]
    exact mul_inv_eq_one.mp hfin
  exact mul_left_cancel h2

private lemma conj_matrix {a : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 a K)
    (x γ : ↥(hypSU h 2 0)) :
    ((((x⁻¹ : ↥(hypSU h 2 0)) : GL (HypIndex 2 0) K) :
          Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        (((MulAut.conj x γ : ↥(hypSU h 2 0)) : GL (HypIndex 2 0) K) :
          Matrix (HypIndex 2 0) (HypIndex 2 0) K)) =
      ((((γ : ↥(hypSU h 2 0)) : GL (HypIndex 2 0) K) :
          Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        (((x⁻¹ : ↥(hypSU h 2 0)) : GL (HypIndex 2 0) K) :
          Matrix (HypIndex 2 0) (HypIndex 2 0) K)) := by
  have hψ : ∀ a b : ↥(hypSU h 2 0),
      (((a * b : ↥(hypSU h 2 0)) : GL (HypIndex 2 0) K) :
          Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
        (((a : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
          ((b : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)) := by
    intro a b
    rw [Subgroup.coe_mul, Units.val_mul]
  have hgrp : (x⁻¹ : ↥(hypSU h 2 0)) * MulAut.conj x γ = γ * x⁻¹ := by
    rw [MulAut.conj_apply, mul_assoc x γ x⁻¹]
    exact inv_mul_cancel_left x (γ * x⁻¹)
  calc (((x⁻¹ : ↥(hypSU h 2 0)) : GL (HypIndex 2 0) K) :
          Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        (((MulAut.conj x γ : ↥(hypSU h 2 0)) : GL (HypIndex 2 0) K) : Matrix _ _ K)
      = ((((x⁻¹ : ↥(hypSU h 2 0)) * MulAut.conj x γ : ↥(hypSU h 2 0)) :
            GL (HypIndex 2 0) K) : Matrix _ _ K) := (hψ _ _).symm
    _ = (((γ * x⁻¹ : ↥(hypSU h 2 0)) : GL (HypIndex 2 0) K) : Matrix _ _ K) := by
          rw [hgrp]
    _ = (((γ : ↥(hypSU h 2 0)) : GL (HypIndex 2 0) K) : Matrix _ _ K) *
        (((x⁻¹ : ↥(hypSU h 2 0)) : GL (HypIndex 2 0) K) : Matrix _ _ K) := hψ _ _

private noncomputable def coordAddEquiv {a : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 a K) (x : ↥(hypSU h 2 0)) :
    (HypIndex 2 0 → K) ≃+ (HypIndex 2 0 → K) := by
  let Mx : GL (HypIndex 2 0) K := (x : ↥(hypSU h 2 0))
  let Mxi : GL (HypIndex 2 0) K := (x⁻¹ : ↥(hypSU h 2 0))
  have hMxMxi : Mx * Mxi = 1 := by
    change (x : GL (HypIndex 2 0) K) *
      ((x⁻¹ : ↥(hypSU h 2 0)) : GL (HypIndex 2 0) K) = 1
    rw [← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]
  have hMxiMx : Mxi * Mx = 1 := by
    change ((x⁻¹ : ↥(hypSU h 2 0)) : GL (HypIndex 2 0) K) *
      (x : GL (HypIndex 2 0) K) = 1
    rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
  have hmatMx : (Mx : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (Mxi : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = 1 := by
    rw [← Units.val_mul, hMxMxi, Units.val_one]
  have hmatMxi : (Mxi : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (Mx : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = 1 := by
    rw [← Units.val_mul, hMxiMx, Units.val_one]
  exact
    { toFun := fun v => (Mxi : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v
      invFun := fun v => (Mx : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v
      left_inv := fun v => by
        change (Mx : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ
          ((Mxi : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v) = v
        rw [Matrix.mulVec_mulVec, hmatMx, Matrix.one_mulVec]
      right_inv := fun v => by
        change (Mxi : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ
          ((Mx : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v) = v
        rw [Matrix.mulVec_mulVec, hmatMxi, Matrix.one_mulVec]
      map_add' := fun v w => by
        change (Mxi : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ (v + w) =
          (Mxi : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v +
            (Mxi : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ w
        rw [Matrix.mulVec_add] }

private lemma exists_adapted_coord {W : Type} [CommGroup W] {K : Type} [Field K]
    {a : ℕ} (h : UnitaryFieldData 2 a K) {H : Subgroup (MulAut W)}
    (π : ↥(hypSU h 2 0) ≃* ↥H) (e : W ≃* Multiplicative (HypIndex 2 0 → K))
    (he : ∀ (γ : ↥(hypSU h 2 0)) (w : W),
      Multiplicative.toAdd (e (((π γ : ↥H) : MulAut W) w)) =
        ((γ : GL (HypIndex 2 0) K) : Matrix _ _ K) *ᵥ Multiplicative.toAdd (e w))
    (x : ↥(hypSU h 2 0)) :
    ∃ e' : W ≃* Multiplicative (HypIndex 2 0 → K),
      ∀ (γ : ↥(hypSU h 2 0)) (w : W),
        Multiplicative.toAdd (e' (((((MulAut.conj x).trans π) γ : ↥H) : MulAut W) w)) =
          ((γ : GL (HypIndex 2 0) K) : Matrix _ _ K) *ᵥ Multiplicative.toAdd (e' w) := by
  refine ⟨e.trans (coordAddEquiv h x).toMultiplicative, ?_⟩
  have hE' : ∀ y : W,
      Multiplicative.toAdd ((e.trans (coordAddEquiv h x).toMultiplicative) y) =
        (((x⁻¹ : ↥(hypSU h 2 0)) : GL (HypIndex 2 0) K) :
          Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ Multiplicative.toAdd (e y) :=
    fun y => rfl
  intro γ w
  have hmat := conj_matrix h x γ
  simp only [hE']
  rw [MulEquiv.trans_apply, he (MulAut.conj x γ) w]
  simp only [Matrix.mulVec_mulVec]
  rw [hmat]

private theorem exists_hypNatEquiv {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {K : Type} [Field K] {a : ℕ} (h : UnitaryFieldData 2 a K)
    (hreal : (FFModel.nat (StatedSU 4 (2 ^ a) K)).Realizes H ⊤ ⊥) :
    ∃ (π : ↥(hypSU h 2 0) ≃* ↥H) (e : W ≃* Multiplicative (HypIndex 2 0 → K)),
      ∀ (γ : ↥(hypSU h 2 0)) (w : W),
        Multiplicative.toAdd (e (((π γ : ↥H) : MulAut W) w)) =
          ((γ : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ
            Multiplicative.toAdd (e w) := by
  obtain ⟨π₀, e₀, he₀⟩ := KTabC.exists_natEquiv hreal
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 0) h
  let φ : (Fin (2 * 2 + 0) → K) ≃+ (HypIndex 2 0 → K) :=
    { toFun := fun v => transportInv h R *ᵥ v
      invFun := fun v => R *ᵥ v
      left_inv := fun v => by
        simp only []
        rw [Matrix.mulVec_mulVec, mul_transportInv hR, Matrix.one_mulVec]
      right_inv := fun v => by
        simp only []
        rw [Matrix.mulVec_mulVec, transportInv_mul hR, Matrix.one_mulVec]
      map_add' := fun v w => by rw [Matrix.mulVec_add] }
  refine ⟨(hypTransport h hR).trans π₀, e₀.trans (AddEquiv.toMultiplicative φ), ?_⟩
  intro γ w
  show transportInv h R *ᵥ Multiplicative.toAdd
      (e₀ (((π₀ (hypTransport h hR γ) : ↥H) : MulAut W) w)) =
    ((γ : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ
      (transportInv h R *ᵥ Multiplicative.toAdd (e₀ w))
  have hmat : transportInv h R *
      (((hypTransport h hR γ : unitarySU 2 a K (2 * 2 + 0)) : GL (Fin (2 * 2 + 0)) K) :
        Matrix (Fin (2 * 2 + 0)) (Fin (2 * 2 + 0)) K) =
      ((γ : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        transportInv h R := by
    rw [coe_hypTransport hR γ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, transportInv_mul hR,
      Matrix.one_mul]
  rw [he₀ (hypTransport h hR γ) w]
  simp only [Matrix.mulVec_mulVec]
  rw [hmat]

private theorem exists_adapted_equiv {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {K : Type} [Field K] {a : ℕ} (h : UnitaryFieldData 2 a K)
    (hreal : (FFModel.nat (StatedSU 4 (2 ^ a) K)).Realizes H ⊤ ⊥) (S : Sylow 2 ↥H) :
    ∃ (Φ : ↥(hypSU h 2 0) ≃* ↥H) (e : W ≃* Multiplicative (HypIndex 2 0 → K)),
      (∀ (γ : ↥(hypSU h 2 0)) (w : W),
        Multiplicative.toAdd (e (((Φ γ : ↥H) : MulAut W) w)) =
          ((γ : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ
            Multiplicative.toAdd (e w)) ∧
      (S : Subgroup ↥H) = (hypUnitriangular h 2 0).map Φ.toMonoidHom := by
  obtain ⟨π, e, he⟩ := exists_hypNatEquiv h hreal
  haveI : Finite ↥(hypSU h 2 0) := by
    haveI := h.finite
    infer_instance
  haveI : Finite ↥H := Finite.of_injective π.symm.toEquiv π.symm.toEquiv.injective
  obtain ⟨S₀, hS₀⟩ :=
    (unitary_order_and_Sylow h (r := 2) (ε := 0) (by norm_num) (by norm_num)).2.1
  haveI : Finite (Sylow 2 ↥(hypSU h 2 0)) := Sylow.finite_of_finiteIndex S₀
  let S' : Sylow 2 ↥(hypSU h 2 0) :=
    S.mapSurjective (f := π.symm.toMonoidHom) π.symm.surjective
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq ↥(hypSU h 2 0) S₀ S'
  obtain ⟨e', he'⟩ := exists_adapted_coord h π e he x
  refine ⟨(MulAut.conj x).trans π, e', he', ?_⟩
  have hS'coe : (S' : Subgroup ↥(hypSU h 2 0)) =
      (S : Subgroup ↥H).map π.symm.toMonoidHom :=
    Sylow.coe_mapSurjective (f := π.symm.toMonoidHom) (hf := π.symm.surjective) (P := S)
  have hS'smul : (S' : Subgroup ↥(hypSU h 2 0)) =
      (hypUnitriangular h 2 0).map
        ((MulAut.conj x : MulAut ↥(hypSU h 2 0)) : ↥(hypSU h 2 0) →* ↥(hypSU h 2 0)) := by
    rw [← hx, Sylow.coe_subgroup_smul, hS₀, Subgroup.pointwise_smul_def]
    rfl
  rw [MulEquiv.toMonoidHom_eq_coe, MulEquiv.toMonoidHom_trans, ← Subgroup.map_map,
    ← hS'smul, hS'coe, Subgroup.map_map, MulEquiv.toMonoidHom_eq_coe,
    MulEquiv.toMonoidHom_comp_toMonoidHom_symm, Subgroup.map_id]

theorem su4_exists_mulEquiv_pointStab_fixSub {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {a : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 a K)
    (hreal : (FFModel.nat (StatedSU 4 (2 ^ a) K)).Realizes H ⊤ ⊥) (S : Sylow 2 ↥H) :
    ∃ φ : ↥(hypSU h 2 0) ≃* ↥H,
      (hypUnitriangular h 2 0).map φ.toMonoidHom = (S : Subgroup ↥H) ∧
        KTabD.pointStab H S = (parP h).map φ.toMonoidHom ∧
          KSUE.fixSub H S =
            (KTabC.vecStab (hypSU h 2 0).subtype (Pi.single ie1 1 :
              HypIndex 2 0 → K)).map φ.toMonoidHom := by
  obtain ⟨Φ, e, he, hS⟩ := exists_adapted_equiv h hreal S
  have hfix : ∀ v : HypIndex 2 0 → K,
      (∀ s ∈ (S : Subgroup ↥H),
        (((Φ.symm s : ↥(hypSU h 2 0)) : GL (HypIndex 2 0) K) :
          Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v = v) ↔
        ∃ c : K, v = c • (Pi.single ie1 1 : HypIndex 2 0 → K) := by
    intro v
    rw [← KSUE.fixed_hypUnitriangular_iff h v, hS]
    constructor
    · intro hv g hg
      simpa using hv (Φ g) (Subgroup.mem_map_of_mem Φ.toMonoidHom hg)
    · intro hv s hs
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hs
      simpa using hv g hg
  have hP : KTabD.pointStab H S = (parP h).map Φ.toMonoidHom := by
    rw [← su4_lineStab_eq_parP h]
    exact KTabD.pointStab_eq_map_lineStab Φ e he S hfix
  have hF : KSUE.fixSub H S =
      (KTabC.vecStab (hypSU h 2 0).subtype (Pi.single ie1 1 :
        HypIndex 2 0 → K)).map Φ.toMonoidHom := by
    let ρ : ↥H →* GL (HypIndex 2 0) K := (hypSU h 2 0).subtype.comp Φ.symm.toMonoidHom
    have he' : ∀ (hh : ↥H) (w : W), Multiplicative.toAdd (e ((hh : MulAut W) w)) =
        ((ρ hh : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ
          Multiplicative.toAdd (e w) := by
      intro hh w
      obtain ⟨g, rfl⟩ := Φ.surjective hh
      simpa [ρ] using he g w
    refine (KTabC.fixingSubgroupOf_fixedPointSubgroup_eq_vecStab he' S hfix).trans ?_
    ext g
    rw [Subgroup.mem_map_equiv, KTabC.mem_vecStab, KTabC.mem_vecStab]
    rfl
  exact ⟨Φ, hS.symm, hP, hF⟩

theorem kTab23cNineAt_of_realizes_su4 {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {a : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 a K)
    (hreal : (FFModel.nat (StatedSU 4 (2 ^ a) K)).Realizes H ⊤ ⊥) : KTab23cNineAt W H := by
  haveI : Finite ↥(hypSU h 2 0) := CFSG.ClassicalGroups.UnitaryFlag.finite_hypSU h
  refine kTab23cNineAt_of_model H (hypUnitriangular h 2 0) (flagStabilizer h 2 0 {2})
    (parP h) (KTabC.vecStab (hypSU h 2 0).subtype (Pi.single ie1 1)) ?_
    (su4_isParabolicTwo_flagStabilizer_two h) (su4_hypUnitriangular_le_flagStabilizer_two h)
    (su4_not_flagStabilizer_two_le_parP h)
    (fun P hP hU hnot => su4_flagStabilizer_two_le_of_parabolic h hP hU hnot)
    (fun t ht hodd => su4_eq_one_of_mem_hinf_vecStab h ht hodd)
  exact su4_exists_mulEquiv_pointStab_fixSub h hreal

theorem kTab23cNineAt_su4 {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {a : ℕ} (h : NatSUn H ⊤ ⊥ 4 a) : KTab23cNineAt W H := by
  obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := h
  letI : Field K := hKf
  letI : Finite K := hKfin
  exact kTab23cNineAt_of_realizes_su4 (unitaryFieldDataOfCard hKcard) hreal

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTab23cNine
