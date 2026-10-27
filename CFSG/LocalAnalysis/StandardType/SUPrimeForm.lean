module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.Timmesfeld.LieEmbed.UnitaryForms
import CFSG.LocalAnalysis.StandardType.GGRootDetectSU
import CFSG.Timmesfeld.LieEmbed.UnitaryIsometry
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.StandardType

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Timmesfeld.LieEmbed
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag

private theorem isometry_of_mem_primeFormUnitary {F : Type} [Field F] [Finite F] [CharP F 2]
    {f n : ℕ} (h : UnitaryFieldData 2 f F) {C : Matrix (Fin n) (Fin n) F}
    {A : GL (Fin n) F} (hA : A ∈ primeFormUnitary h C) (hC : C = antidiag n) :
    conjTr (unitaryInvolution F 2 f) (A : Matrix (Fin n) (Fin n) F) * antidiag n *
      (A : Matrix (Fin n) (Fin n) F) = antidiag n := by
  have h1 := mem_primeFormUnitary.1 hA
  rw [hC] at h1
  have h2 : (A : Matrix (Fin n) (Fin n) F).map (unitaryInvolution F 2 f) =
      (A : Matrix (Fin n) (Fin n) F).map h.bar := RootDetectSU.map_eq_map_bar h _
  calc conjTr (unitaryInvolution F 2 f) (A : Matrix (Fin n) (Fin n) F) * antidiag n *
        (A : Matrix (Fin n) (Fin n) F)
      = ((A : Matrix (Fin n) (Fin n) F).map h.bar)ᵀ * antidiag n *
          (A : Matrix (Fin n) (Fin n) F) := by rw [conjTr, h2]
    _ = antidiag n := h1

theorem exists_mulEquiv_primeFormP_range {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (h : UnitaryFieldData 2 f F) {n : ℕ} (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    {C : GL (Fin n) F} (hC : (C : Matrix (Fin n) (Fin n) F) = antidiag n)
    {K : Type} [Group K] {Φ : SU (unitaryInvolution F 2 f) n →* K}
    (hker : Φ.ker = Subgroup.center (SU (unitaryInvolution F 2 f) n)) :
    ∃ e : primeFormP h (C : Matrix (Fin n) (Fin n) F) ≃* Φ.range,
      ∀ (g : gramSU h (C : Matrix (Fin n) (Fin n) F)) (g' : SU (unitaryInvolution F 2 f) n),
        (g : GL (Fin n) F) = (g' : GL (Fin n) F) →
          e (g : primeFormP h (C : Matrix (Fin n) (Fin n) F)) = Φ.rangeRestrict g' := by
  classical
  let σ := unitaryInvolution F 2 f
  have hC' : IsPrimeFormGram C := RootDetectSU.isPrimeFormGram_of_eq_antidiag hC
  have hE : SU σ n = gramSU h (C : Matrix (Fin n) (Fin n) F) := by
    rw [hC]
    exact RootDetectSU.SU_eq_gramSU_antidiag h
  let E : SU σ n ≃* gramSU h (C : Matrix (Fin n) (Fin n) F) := MulEquiv.subgroupCongr hE
  let Φ' : gramSU h (C : Matrix (Fin n) (Fin n) F) →* K := Φ.comp E.symm.toMonoidHom
  have hker' : Φ'.ker = Subgroup.center (gramSU h (C : Matrix (Fin n) (Fin n) F)) := by
    have hmap : (Subgroup.center (gramSU h (C : Matrix (Fin n) (Fin n) F))).map
        E.symm.toMonoidHom = Subgroup.center (SU σ n) := Subgroup.map_center_eq E.symm
    ext x
    constructor
    · intro hx
      change Φ (E.symm x) = 1 at hx
      have h1 : E.symm x ∈ Subgroup.center (SU σ n) := by
        rw [← hker]
        exact hx
      rw [← hmap, Subgroup.mem_map_equiv] at h1
      simpa using h1
    · intro hx
      change Φ (E.symm x) = 1
      have h2 : E.symm x ∈ (Subgroup.center
          (gramSU h (C : Matrix (Fin n) (Fin n) F))).map E.symm.toMonoidHom := by
        rw [Subgroup.mem_map_equiv]
        simpa using hx
      rw [hmap] at h2
      have h3 : E.symm x ∈ Φ.ker := by
        rw [hker]
        exact h2
      exact h3
  have hZ : Subgroup.center (gramSU h (C : Matrix (Fin n) (Fin n) F)) =
      normOneScalars h (gramSU h (C : Matrix (Fin n) (Fin n) F)) n :=
    CFSG.SeitzReduction.F4Pilot.center_gramSU_eq_normOneScalars h hC' hn hq
  have hrange : Φ'.range = Φ.range := by
    have htop : E.symm.toMonoidHom.range = (⊤ : Subgroup (SU σ n)) :=
      MulEquiv.range_eq_top E.symm
    rw [show Φ' = Φ.comp E.symm.toMonoidHom from rfl, MonoidHom.range_comp, htop,
      Subgroup.map_top]
  let e0 : primeFormP h (C : Matrix (Fin n) (Fin n) F) ≃* Φ'.range :=
    (QuotientGroup.quotientMulEquivOfEq (hker'.trans hZ).symm).trans
      (QuotientGroup.quotientKerEquivRange Φ')
  let e : primeFormP h (C : Matrix (Fin n) (Fin n) F) ≃* Φ.range :=
    e0.trans (MulEquiv.subgroupCongr hrange)
  refine ⟨e, ?_⟩
  intro g g' hgg
  have hgE : E.symm g = g' := Subtype.ext (by
    rw [MulEquiv.subgroupCongr_symm_apply, hgg])
  apply Subtype.ext
  change Φ (E.symm g) = Φ g'
  rw [hgE]

theorem eq_of_mk_eq_of_mul_self_eq_one {F : Type} [Field F] [CharP F 2] {f : ℕ}
    (h : UnitaryFieldData 2 f F) {n : ℕ} (hn : 1 ≤ n) {C : Matrix (Fin n) (Fin n) F}
    {a b : gramSU h C} (hab : (a : primeFormP h C) = b) (ha : a * a = 1) (hb : b * b = 1) :
    a = b := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨c, -, -, hc⟩ :=
    (QuotientGroup.eq.mp hab : a⁻¹ * b ∈ normOneScalars h (gramSU h C) n)
  have hM : (a : GL (Fin n) F)⁻¹ * (b : GL (Fin n) F) =
      GeneralLinearGroup.scalar (Fin n) c := by
    rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, hc]
  have ha' : (a : GL (Fin n) F) * (a : GL (Fin n) F) = 1 := by
    rw [← Subgroup.coe_mul, ha, Subgroup.coe_one]
  have hb' : (b : GL (Fin n) F) * (b : GL (Fin n) F) = 1 := by
    rw [← Subgroup.coe_mul, hb, Subgroup.coe_one]
  exact Subtype.ext (RootDetectSU.eq_of_inv_mul_eq_scalar hM ha' hb').symm

theorem exists_mulVec_map_eq_smul_of_primeFormPsi_apply_eq {F : Type} [Field F] [Finite F]
    [CharP F 2] {f : ℕ} (h : UnitaryFieldData 2 f F) {n : ℕ} (hn : 1 ≤ n) {C : GL (Fin n) F}
    (hC : IsPrimeFormGram C) (hCa : (C : Matrix (Fin n) (Fin n) F) = antidiag n)
    (A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) F)) (φ : F ≃+* F) {v : Fin n → F}
    (hvv : uForm (unitaryInvolution F 2 f) v v = 0)
    (t : gramSU h (C : Matrix (Fin n) (Fin n) F))
    (ht : ((t : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      uTrans (unitaryInvolution F 2 f) v 1)
    (hfix : primeFormPsi h hC ⟨A, φ⟩ (t : primeFormP h (C : Matrix (Fin n) (Fin n) F)) = t) :
    ∃ μ : F, ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ (fun i => φ (v i)) = μ • v := by
  classical
  let σ := unitaryInvolution F 2 f
  let Cm : Matrix (Fin n) (Fin n) F := (C : Matrix (Fin n) (Fin n) F)
  have hCm : Cm = antidiag n := hCa
  let tφ : gramSU h Cm := primeFormFieldSU h hC φ t
  let a : gramSU h Cm :=
    ⟨(A : GL (Fin n) F) * (tφ : GL (Fin n) F) * (A : GL (Fin n) F)⁻¹,
      conj_mem_gramSU h Cm A.2 tφ.2⟩
  have hAiso : conjTr σ ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * antidiag n *
      ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = antidiag n :=
    isometry_of_mem_primeFormUnitary h (C := Cm) A.2 hCm
  have hfix' : (a : primeFormP h (C : Matrix (Fin n) (Fin n) F)) =
      (t : primeFormP h (C : Matrix (Fin n) (Fin n) F)) := by
    rw [primeFormPsi_apply, MulAut.mul_apply] at hfix
    rw [show primeFormFieldHom h hC φ = primeFormFieldAut h hC φ from rfl] at hfix
    rw [primeFormFieldAut_mk, primeFormConjHom_mk] at hfix
    simpa only [a, tφ, Cm] using hfix
  have htt : t * t = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one, Units.val_mul, Units.val_one, ht,
      uTrans_mul_uTrans σ hvv, CharTwo.add_self_eq_zero, uTrans_zero]
  have htφ : tφ * tφ = 1 := by
    have h := map_mul_eq_one (primeFormFieldSU h hC φ) htt
    simpa only [tφ] using h
  have haa : a * a = 1 := by
    have haGL : (a : GL (Fin n) F) * (a : GL (Fin n) F) = 1 := by
      change (A : GL (Fin n) F) * (tφ : GL (Fin n) F) * (A : GL (Fin n) F)⁻¹ *
          ((A : GL (Fin n) F) * (tφ : GL (Fin n) F) * (A : GL (Fin n) F)⁻¹) = 1
      have htGL : (tφ : GL (Fin n) F) * (tφ : GL (Fin n) F) = 1 := by
        rw [← Subgroup.coe_mul, htφ, Subgroup.coe_one]
      calc (A : GL (Fin n) F) * (tφ : GL (Fin n) F) * (A : GL (Fin n) F)⁻¹ *
            ((A : GL (Fin n) F) * (tφ : GL (Fin n) F) * (A : GL (Fin n) F)⁻¹)
          = (A : GL (Fin n) F) * ((tφ : GL (Fin n) F) * (tφ : GL (Fin n) F)) *
              (A : GL (Fin n) F)⁻¹ := by group
        _ = 1 := by rw [htGL, mul_one, mul_inv_cancel]
    exact Subtype.ext haGL
  have hat : a = t := eq_of_mk_eq_of_mul_self_eq_one h hn hfix' haa htt
  have hmat : (A : GL (Fin n) F) *
      ((t : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map φ *
      (A : GL (Fin n) F)⁻¹ = uTrans σ v 1 := by
    have h1 := congrArg (fun x : gramSU h (C : Matrix (Fin n) (Fin n) F) =>
      ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) hat
    exact h1.trans ht
  have hφ : ∀ c, φ (σ c) = σ (φ c) := by
    intro c
    rw [show σ c = h.bar c from (RootDetectSU.bar_eq h c).symm,
      show σ (φ c) = h.bar (φ c) from (RootDetectSU.bar_eq h (φ c)).symm]
    exact map_bar_comm h φ c
  have hmap : ((t : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map φ =
      uTrans σ (fun i => φ (v i)) 1 := by
    rw [ht, CFSG.Timmesfeld.LieEmbed.map_uTrans (σ := σ) φ hφ]
    simp
  rw [hmap] at hmat
  have hAA : ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      (((A : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have htrans : uTrans σ ((A : GL (Fin n) F) *ᵥ fun i => φ (v i)) 1 = uTrans σ v 1 := by
    have h := hmat
    rw [CFSG.Timmesfeld.LieEmbed.mul_uTrans_of_isometry (σ := σ) hAiso, Matrix.mul_assoc,
      hAA, Matrix.mul_one] at h
    exact h
  have hnil : uNil σ ((A : GL (Fin n) F) *ᵥ fun i => φ (v i)) = uNil σ v := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) F => M - 1) htrans
    simpa [uTrans, one_smul] using h
  obtain ⟨μ, hμ⟩ := CFSG.Timmesfeld.LieEmbed.exists_eq_smul_of_uNil_eq (σ := σ) (l := 1)
    (by simpa using hnil)
  exact ⟨μ, hμ⟩

end CFSG.StandardType
