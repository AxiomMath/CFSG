module

public import CFSG.RankThree.PartTwo.Sec16.KSL3TwoTailProofKP1Two

public section

namespace CFSG.RankThree.PartTwo.Sec16

namespace ProofKS1624KP1

open CFSG CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.SteinbergBR.BlockPar
open ProofKS1623Parab
open Matrix
open scoped commutatorElement

variable {F : Type} [Field F]

theorem sq_eq_one_of_det_sub_one [CharP F 2] {y : SpecialLinearGroup (Fin 2) F}
    (hy : (y.val - 1).det = 0) : y ^ 2 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hdet : y.val 0 0 * y.val 1 1 - y.val 0 1 * y.val 1 0 = 1 := by
    have := y.prop
    rwa [Matrix.det_fin_two] at this
  have hy' : (y.val 0 0 - 1) * (y.val 1 1 - 1) - y.val 0 1 * y.val 1 0 = 0 := by
    rw [Matrix.det_fin_two] at hy
    simpa using hy
  have htr : y.val 0 0 + y.val 1 1 = 0 := by linear_combination hdet - hy' + h2
  apply Subtype.ext
  show y.val ^ 2 = 1
  rw [sq]
  ext i j
  fin_cases i <;> fin_cases j
  · show (y.val * y.val) 0 0 = (1 : Matrix (Fin 2) (Fin 2) F) 0 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq]
    linear_combination (-1 : F) * hdet + y.val 0 0 * htr - h2
  · show (y.val * y.val) 0 1 = (1 : Matrix (Fin 2) (Fin 2) F) 0 1
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_ne (by decide)]
    linear_combination y.val 0 1 * htr
  · show (y.val * y.val) 1 0 = (1 : Matrix (Fin 2) (Fin 2) F) 1 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_ne (by decide)]
    linear_combination y.val 1 0 * htr
  · show (y.val * y.val) 1 1 = (1 : Matrix (Fin 2) (Fin 2) F) 1 1
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq]
    linear_combination (-1 : F) * hdet + y.val 1 1 * htr - h2

theorem sq_eq_one_of_fix [CharP F 2] {y : SpecialLinearGroup (Fin 2) F} {v : Fin 2 → F}
    (hv : v ≠ 0) (hyv : y.val *ᵥ v = v) : y ^ 2 = 1 :=
  sq_eq_one_of_det_sub_one (Matrix.exists_mulVec_eq_zero_iff.mp
    ⟨v, hv, by rw [Matrix.sub_mulVec, hyv, Matrix.one_mulVec, sub_self]⟩)

theorem exists_sub_one_mulVec_eq [CharP F 2] {y : SpecialLinearGroup (Fin 2) F}
    (hy : y ^ 2 ≠ 1) (w : Fin 2 → F) : ∃ w' : Fin 2 → F, (y.val - 1) *ᵥ w' = w := by
  have hdet : (y.val - 1).det ≠ 0 := fun h => hy (sq_eq_one_of_det_sub_one h)
  refine ⟨(y.val - 1)⁻¹ *ᵥ w, ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]

theorem exists_eq_smul_of_fix {r : SpecialLinearGroup (Fin 2) F} (hr : r ≠ 1) {v w : Fin 2 → F}
    (hv0 : v ≠ 0) (hv : r.val *ᵥ v = v) (hw : r.val *ᵥ w = w) : ∃ c : F, w = c • v := by
  have ev0 := congrFun hv 0
  have ev1 := congrFun hv 1
  have ew0 := congrFun hw 0
  have ew1 := congrFun hw 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at ev0 ev1 ew0 ew1
  by_cases hD : v 0 * w 1 - v 1 * w 0 = 0
  · by_cases h0 : v 0 = 0
    · have h1 : v 1 ≠ 0 := by
        intro h1
        apply hv0
        ext i
        fin_cases i
        · exact h0
        · exact h1
      have hw0 : w 0 = 0 := by
        have : v 1 * w 0 = 0 := by rw [h0] at hD; linear_combination -hD
        exact (mul_eq_zero.mp this).resolve_left h1
      refine ⟨w 1 / v 1, ?_⟩
      ext i
      fin_cases i
      · simp [h0, hw0]
      · simp [h1]
    · refine ⟨w 0 / v 0, ?_⟩
      ext i
      fin_cases i
      · simp [h0]
      · show w 1 = w 0 / v 0 * v 1
        rw [div_mul_eq_mul_div, eq_div_iff h0]
        linear_combination hD
  · exfalso
    apply hr
    have e00 : (r.val 0 0 - 1) * (v 0 * w 1 - v 1 * w 0) = 0 := by
      linear_combination w 1 * ev0 - v 1 * ew0
    have e01 : r.val 0 1 * (v 0 * w 1 - v 1 * w 0) = 0 := by
      linear_combination -(w 0 * ev0) + v 0 * ew0
    have e10 : r.val 1 0 * (v 0 * w 1 - v 1 * w 0) = 0 := by
      linear_combination w 1 * ev1 - v 1 * ew1
    have e11 : (r.val 1 1 - 1) * (v 0 * w 1 - v 1 * w 0) = 0 := by
      linear_combination -(w 0 * ev1) + v 0 * ew1
    apply Subtype.ext
    show r.val = 1
    ext i j
    fin_cases i <;> fin_cases j
    · exact sub_eq_zero.mp ((mul_eq_zero.mp e00).resolve_right hD)
    · exact (mul_eq_zero.mp e01).resolve_right hD
    · exact (mul_eq_zero.mp e10).resolve_right hD
    · exact sub_eq_zero.mp ((mul_eq_zero.mp e11).resolve_right hD)

theorem eq_bot_of_normalized_sl2 [Finite F] [CharP F 2] {Γ : Type*} [Group Γ]
    (hΓ : commutator Γ = ⊤) (φ : Γ →* SpecialLinearGroup (Fin 2) F) {γ : Γ}
    (hγ : φ γ ^ 2 ≠ 1) {R : Subgroup (SpecialLinearGroup (Fin 2) F)} (hR : IsPGroup 2 R)
    (hN : ∀ g : Γ, ∀ r ∈ R, φ g * r * (φ g)⁻¹ ∈ R) : R = ⊥ := by
  by_contra hne
  obtain ⟨⟨r, hrR⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
  obtain ⟨v, hvC, hv0⟩ := exists_ne_zero_mem_fixVec (by norm_num) hR
  have hscal : ∀ g : Γ, ∃ c : F, (φ g).val *ᵥ v = c • v := by
    intro g
    have hmem : (φ g).val *ᵥ v ∈ fixVec R := by
      refine mulVec_mem_fixVec (fun x hx => ?_) hvC
      have := hN g⁻¹ x hx
      rwa [map_inv, inv_inv] at this
    exact exists_eq_smul_of_fix hr1' hv0 (hvC r hrR) (hmem r hrR)
  have hsmul : ∀ g : Γ, ∀ c c' : F, (φ g).val *ᵥ v = c • v → (φ g⁻¹).val *ᵥ v = c' • v →
      c * c' = 1 := by
    intro g c c' hc hc'
    have h1 : (φ g).val *ᵥ ((φ g⁻¹).val *ᵥ v) = v := by
      rw [mulVec_mulVec, show (φ g).val * (φ g⁻¹).val = (φ g * φ g⁻¹).val from rfl, ← map_mul,
        mul_inv_cancel, map_one]
      exact one_mulVec v
    rw [hc', mulVec_smul, hc, smul_smul] at h1
    have h2 : (c' * c - 1) • v = 0 := by rw [sub_smul, one_smul, h1, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · linear_combination h
    · exact absurd h hv0
  set Fx : Subgroup Γ := (MulAction.stabilizer (SpecialLinearGroup (Fin 2) F) v).comap φ
    with hFx
  have hcomm : commutator Γ ≤ Fx := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g _ h _
    obtain ⟨c1, hc1⟩ := hscal g
    obtain ⟨c2, hc2⟩ := hscal h
    obtain ⟨c3, hc3⟩ := hscal g⁻¹
    obtain ⟨c4, hc4⟩ := hscal h⁻¹
    have e13 := hsmul g c1 c3 hc1 hc3
    have e24 := hsmul h c2 c4 hc2 hc4
    show φ ⁅g, h⁆ • v = v
    rw [smul_vec_eq', commutatorElement_def, map_mul, map_mul, map_mul]
    show ((φ g).val * (φ h).val * (φ g⁻¹).val * (φ h⁻¹).val) *ᵥ v = v
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hc4, mulVec_smul, hc3, smul_smul,
      mulVec_smul, hc2, smul_smul, mulVec_smul, hc1, smul_smul,
      show c4 * c3 * c2 * c1 = (c1 * c3) * (c2 * c4) by ring, e13, e24, mul_one, one_smul]
  have hγv : (φ γ).val *ᵥ v = v := by
    have hγF : γ ∈ Fx := hcomm (hΓ ▸ Subgroup.mem_top γ)
    have h1 : φ γ • v = v := hγF
    rwa [smul_vec_eq'] at h1
  exact hγ (sq_eq_one_of_fix hv0 hγv)

@[expose] noncomputable def blockB (F : Type) [Field F] :
    parB F →* SpecialLinearGroup (Fin 2) F :=
  (blockA F).comp (parKEquiv F).symm.toMonoidHom

theorem blockB_eq_one_iff (x : parB F) :
    blockB F x = 1 ↔ (x : projectiveSL 3 F) ∈ radV F := by
  rw [blockB, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, blockA_eq_one_iff]
  constructor
  · intro hx
    rw [← proj_parKEquiv_symm x]
    exact ⟨_, hx, rfl⟩
  · intro hx
    obtain ⟨u, hu, hux⟩ := exists_radU_of_mem_radV hx
    have := eq_of_proj_eq ((parKEquiv F).symm x).2 (radU_le_parK hu)
      ((proj_parKEquiv_symm x).trans hux.symm)
    rw [this]
    exact hu

theorem sq_eq_one_of_mem_radV [CharP F 2] {u : projectiveSL 3 F} (hu : u ∈ radV F) :
    u ^ 2 = 1 := by
  obtain ⟨u0, hu0, rfl⟩ := exists_radU_of_mem_radV hu
  rw [← map_pow, sq, radU_mul_self hu0, map_one]

theorem blockB_sq_ne_one [CharP F 2] {x : parB F} (hx4 : (x : projectiveSL 3 F) ^ 4 ≠ 1) :
    blockB F x ^ 2 ≠ 1 := by
  intro h
  apply hx4
  have h1 : blockB F (x ^ 2) = 1 := by rw [map_pow]; exact h
  rw [blockB_eq_one_iff] at h1
  have h2 := sq_eq_one_of_mem_radV h1
  rw [Subgroup.coe_pow, ← pow_mul] at h2
  exact h2

theorem le_radV_of_normalized [Finite F] [CharP F 2] {K1 R : Subgroup (projectiveSL 3 F)}
    (hK1 : K1 ≤ parB F) (hperf : ⁅K1, K1⁆ = K1) {x : projectiveSL 3 F} (hx : x ∈ K1)
    (hx4 : x ^ 4 ≠ 1) (hR : IsPGroup 2 R) (hRB : R ≤ parB F)
    (hN : K1 ≤ Subgroup.normalizer (R : Set (projectiveSL 3 F))) : R ≤ radV F := by
  set φ : K1 →* SpecialLinearGroup (Fin 2) F := (blockB F).comp (Subgroup.inclusion hK1)
    with hφ
  have hΓ : commutator K1 = ⊤ := ((Subgroup.isPerfect_iff).mpr hperf).commutator_eq_top
  have hγ : φ ⟨x, hx⟩ ^ 2 ≠ 1 := blockB_sq_ne_one (x := ⟨x, hK1 hx⟩) hx4
  set R2 := (R.subgroupOf (parB F)).map (blockB F) with hR2
  have hR2p : IsPGroup 2 R2 :=
    (hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRB).symm).map (blockB F)
  have hR2N : ∀ g : K1, ∀ r ∈ R2, φ g * r * (φ g)⁻¹ ∈ R2 := by
    rintro g _ ⟨r0, hr0, rfl⟩
    refine ⟨Subgroup.inclusion hK1 g * r0 * (Subgroup.inclusion hK1 g)⁻¹, ?_, ?_⟩
    · show (g : projectiveSL 3 F) * r0 * (g : projectiveSL 3 F)⁻¹ ∈ R
      exact (Subgroup.mem_normalizer_iff.mp (hN g.2) _).mp (Subgroup.mem_subgroupOf.mp hr0)
    · rw [map_mul, map_mul, map_inv]
      rfl
  have hR2bot := eq_bot_of_normalized_sl2 hΓ φ hγ hR2p hR2N
  intro r hr
  have h1 : blockB F ⟨r, hRB hr⟩ ∈ R2 := ⟨⟨r, hRB hr⟩, hr, rfl⟩
  rw [hR2bot, Subgroup.mem_bot, blockB_eq_one_iff] at h1
  exact h1

theorem commutator_parK_uVec {M : SpecialLinearGroup (Fin 3) F} (hM : M ∈ parK F)
    (w : Fin 2 → F) : M * uVec w * M⁻¹ * (uVec w)⁻¹ = uVec ((blockAMat M - 1) *ᵥ w) := by
  have hc := conj_mem_radU (parK_le_stabilizer hM) (uVec_mem_radU w)
  have hmem : M * uVec w * M⁻¹ * (uVec w)⁻¹ ∈ radU F (flagSpace 3 F 2) :=
    mul_mem hc (inv_mem (uVec_mem_radU w))
  rw [← uVec_radCoord hmem, radCoord_mul hc (inv_mem (uVec_mem_radU w)),
    radCoord_conj hM (uVec_mem_radU w), radCoord_inv (uVec_mem_radU w), radCoord_uVec,
    Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_add_neg]

theorem conj_mem_inSubgroup_perfectResidual' {H : Type*} [Group H] {X : Subgroup H} {g x : H}
    (hg : g ∈ X) (hx : x ∈ inSubgroup perfectResidual X) :
    g * x * g⁻¹ ∈ inSubgroup perfectResidual X := by
  obtain ⟨y, hy, rfl⟩ := hx
  have : (perfectResidual X).Normal := inferInstance
  exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, this.conj_mem y hy _, rfl⟩

theorem radV_le_normalizer {R : Subgroup (projectiveSL 3 F)} (hRV : R ≤ radV F) :
    radV F ≤ Subgroup.normalizer (R : Set (projectiveSL 3 F)) := by
  have hcomm : ∀ u ∈ radV F, ∀ v ∈ radV F, u * v = v * u := by
    intro u hu v hv
    obtain ⟨u0, hu0, rfl⟩ := exists_radU_of_mem_radV hu
    obtain ⟨v0, hv0, rfl⟩ := exists_radU_of_mem_radV hv
    rw [← map_mul, ← map_mul, radU_commute hu0 hv0]
  intro u hu
  rw [Subgroup.mem_normalizer_iff]
  intro r
  have key : ∀ s ∈ radV F, u * s * u⁻¹ = s := fun s hs => by
    rw [hcomm u hu s hs, mul_inv_cancel_right]
  constructor
  · intro hr
    rw [key r (hRV hr)]
    exact hr
  · intro hr
    have hs : r ∈ radV F := by
      have : r = u⁻¹ * (u * r * u⁻¹) * u := by group
      rw [this]
      exact mul_mem (mul_mem (inv_mem hu) (hRV hr)) hu
    rwa [key r hs] at hr

theorem radV_le_of_le [CharP F 2] {R : Subgroup (projectiveSL 3 F)} (hRV : R ≤ radV F)
    (hK1 : inSubgroup perfectResidual (Subgroup.normalizer (R : Set (projectiveSL 3 F))) ≤
      parB F) {x : projectiveSL 3 F}
    (hx : x ∈ inSubgroup perfectResidual (Subgroup.normalizer (R : Set (projectiveSL 3 F))))
    (hx4 : x ^ 4 ≠ 1) :
    radV F ≤ inSubgroup perfectResidual (Subgroup.normalizer (R : Set (projectiveSL 3 F))) := by
  intro u hu
  have hxB : x ∈ parB F := hK1 hx
  set M := ((parKEquiv F).symm ⟨x, hxB⟩).1 with hMdef
  have hM : M ∈ parK F := ((parKEquiv F).symm ⟨x, hxB⟩).2
  have hMx : proj 3 F M = x := proj_parKEquiv_symm ⟨x, hxB⟩
  have hA := blockB_sq_ne_one (x := ⟨x, hxB⟩) hx4
  obtain ⟨u0, hu0, rfl⟩ := exists_radU_of_mem_radV hu
  obtain ⟨w', hw'⟩ := exists_sub_one_mulVec_eq hA (radCoord u0)
  have hAval : (blockB F ⟨x, hxB⟩).val = blockAMat M := rfl
  rw [hAval] at hw'
  set v := proj 3 F (uVec w') with hv
  have hvN : v ∈ Subgroup.normalizer (R : Set (projectiveSL 3 F)) :=
    radV_le_normalizer hRV ⟨_, uVec_mem_radU w', rfl⟩
  have key : proj 3 F u0 = x * (v * x⁻¹ * v⁻¹) := by
    rw [← uVec_radCoord hu0, ← hw', ← commutator_parK_uVec hM, map_mul, map_mul, map_mul,
      map_inv, map_inv, hMx, ← hv]
    group
  rw [key]
  exact mul_mem hx (conj_mem_inSubgroup_perfectResidual' hvN (inv_mem hx))

end ProofKS1624KP1

end CFSG.RankThree.PartTwo.Sec16
