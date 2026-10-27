module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23Parab
public import CFSG.Quasithin.Vol2.Ch5Sec2M23GxRho

public section

namespace CFSG.Quasithin.H13

open CFSG.ComponentClassification.WittDesign CFSG.Monster.B.Classical.Plane CFSG.Fischer
  CFSG.EvenSmallLie.UnitarySix.MathieuExt CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups Matrix

variable {G : Type} [Group G]

theorem exists_point_type {G0 L : Subgroup G} [Finite G] {F : Type} [Field F] [Finite F]
    [CharP F 2] (e : ↥G0 ≃* LinearFlag.projectiveSL 3 F)
    (hL : L.subgroupOf G0 ∈ LinearFlag.maximalParabolics ↥G0 2) {t : G} (A : GL (Fin 3) F)
    (σ : F ≃+* F)
    (hrel : ∀ x y : ↥G0, (y : G) = t * x * t⁻¹ →
      e y = LinearFlag.conjAut 3 F A (LinearFlag.fieldAut 3 F σ (e x))) :
    ∃ (e' : ↥G0 ≃* LinearFlag.projectiveSL 3 F) (A' : GL (Fin 3) F)
      (W : Submodule F (Fin 3 → F)),
      Module.finrank F W = 1 ∧ (L.subgroupOf G0).map e'.toMonoidHom = LinearFlag.projStabilizer W ∧
      ∀ x y : ↥G0, (y : G) = t * x * t⁻¹ →
        e' y = LinearFlag.conjAut 3 F A' (LinearFlag.fieldAut 3 F σ (e' x)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP := map_mem_maximalParabolics e hL
  obtain ⟨hM, -, -⟩ := LinearFlag.maximal_parabolics (K := F) 2 (by norm_num : 1 ≤ 3)
  rw [hM] at hP
  obtain ⟨W, ⟨h0, htop⟩, hW⟩ := hP
  obtain ⟨hk1, hk3⟩ := LinearFlag.one_le_finrank_and_lt h0 htop
  by_cases h1 : Module.finrank F W = 1
  · exact ⟨e, A, W, h1, hW.symm, hrel⟩
  have h2 : Module.finrank F W = 2 := by omega
  obtain ⟨-, -, -, hδδ, hδc, hδf, -, -, hδW, -⟩ :=
    LinearFlag.standard_automorphism_transport (n := 3) (K := F)
  refine ⟨e.trans (LinearFlag.dualAut 3 F), Matrix.GeneralLinearGroup.inverseTranspose A,
    LinearFlag.dotOrth W, ?_, ?_, ?_⟩
  · rw [LinearFlag.finrank_dotOrth, h2]
  · rw [← hδW, hW, Subgroup.map_map]
    rfl
  · intro x y hxy
    set δ := LinearFlag.dualAut 3 F with hδ
    have key : δ * LinearFlag.conjAut 3 F A * LinearFlag.fieldAut 3 F σ =
        LinearFlag.conjAut 3 F (Matrix.GeneralLinearGroup.inverseTranspose A) *
          LinearFlag.fieldAut 3 F σ * δ := by
      calc δ * LinearFlag.conjAut 3 F A * LinearFlag.fieldAut 3 F σ =
          δ * LinearFlag.conjAut 3 F A * (δ * δ) * LinearFlag.fieldAut 3 F σ * (δ * δ) := by
            rw [hδδ, mul_one, mul_one]
        _ = δ * LinearFlag.conjAut 3 F A * δ * (δ * LinearFlag.fieldAut 3 F σ * δ) * δ := by
            group
        _ = _ := by rw [hδc A, hδf σ]
    have e1 := congrArg (fun φ : MulAut (LinearFlag.projectiveSL 3 F) => φ (e x)) key
    simp only [MulAut.mul_apply] at e1
    change δ (e y) = _
    rw [hrel x y hxy, e1]
    rfl

theorem exists_fixed_point_of_projStabilizer {F : Type} [Field F] (κ : F ≃+* F4)
    {W : Submodule F (Fin 3 → F)} (hW : Module.finrank F W = 1) :
    ∃ q : Fin 21, ∀ z ∈ LinearFlag.projStabilizer W, pslPerm (pslCoord κ z) q = q := by
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp hW
  set w : Fin 3 → F := (v : Fin 3 → F) with hwdef
  have hw0 : w ≠ 0 := fun h => hv0 (Subtype.ext h)
  set u : Fin 3 → F4 := fun i => κ (w i) with hudef
  have hu0 : u ≠ 0 := by
    intro h
    apply hw0
    funext i
    have := congrFun h i
    simpa [hudef] using this
  refine ⟨normIdx u, ?_⟩
  rintro _ ⟨g, hg, rfl⟩
  rw [pslCoord_proj, pslPerm_mk_apply]
  have hgw : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W := by
    have h := LinearFlag.mem_stabilizer.mp hg
    rw [← h]
    exact ⟨w, v.2, rfl⟩
  obtain ⟨c, hc⟩ := hv ⟨_, hgw⟩
  have hc' : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ w = c • w := (congrArg Subtype.val hc).symm
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc'
    apply hw0
    have h1 : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    rw [← h1, hc', Matrix.mulVec_zero]
  obtain ⟨c', hc'0, hu⟩ := exists_smul_Ω_normIdx u hu0
  have hΩ : Ω (normIdx u) = c'⁻¹ • u := by
    conv_rhs => rw [hu]
    rw [smul_smul, inv_mul_cancel₀ hc'0, one_smul]
  have hκ : ((Matrix.SpecialLinearGroup.map κ.toRingHom g : Matrix.SpecialLinearGroup (Fin 3) F4) :
      Matrix (Fin 3) (Fin 3) F4) *ᵥ u = κ c • u := by
    funext i
    have h1 := RingHom.map_mulVec κ.toRingHom (g : Matrix (Fin 3) (Fin 3) F) w i
    rw [hc'] at h1
    simp only [Pi.smul_apply, smul_eq_mul, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      map_mul] at h1
    rw [Pi.smul_apply, smul_eq_mul, hudef]
    exact h1.symm
  rw [hΩ, Matrix.mulVec_smul, hκ, smul_smul]
  exact normIdx_smul _ u (mul_ne_zero (inv_ne_zero hc'0) (κ.map_ne_zero_iff.mpr hc0))

theorem exists_conj_eq_of_card {X : Type*} [Group X] {P A B : Subgroup X} [Finite ↥P]
    (hP : Nat.card P = 20160) (hA : A ≤ P) (hB : B ≤ P) (hA64 : Nat.card A = 64)
    (hB64 : Nat.card B = 64) :
    ∃ p ∈ P, ∀ y ∈ B, ∃ x ∈ A, y = p * x * p⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl : ∀ C : Subgroup X, C ≤ P → Nat.card C = 64 →
      IsPGroup 2 (C.subgroupOf P) ∧ ¬ 2 ∣ (C.subgroupOf P).index := by
    intro C hC hC64
    have hcard : Nat.card (C.subgroupOf P) = 64 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC).toEquiv, hC64]
    refine ⟨IsPGroup.of_card (n := 6) (by rw [hcard]; norm_num), ?_⟩
    have h := Subgroup.card_mul_index (C.subgroupOf P)
    rw [hcard, hP] at h
    omega
  obtain ⟨hA2, hAi⟩ := hsyl A hA hA64
  obtain ⟨hB2, hBi⟩ := hsyl B hB hB64
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥P (hA2.toSylow hAi) (hB2.toSylow hBi)
  refine ⟨g, g.2, fun y hy => ?_⟩
  have hmem : (⟨y, hB hy⟩ : ↥P) ∈ ((hB2.toSylow hBi : Sylow 2 ↥P) : Subgroup ↥P) :=
    Subgroup.mem_subgroupOf.mpr hy
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨x, hx, hxy⟩ := hmem
  refine ⟨x, Subgroup.mem_subgroupOf.mp hx, ?_⟩
  have := congrArg Subtype.val hxy
  simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at this
  exact this.symm

end CFSG.Quasithin.H13
