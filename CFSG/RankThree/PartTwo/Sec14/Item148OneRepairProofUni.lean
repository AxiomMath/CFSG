module

public import CFSG.RankThree.PartTwo.Sec14.Item148OneRepairProofLin
import CFSG.RankThree.PartTwo.Sec14.Item148OneRepairProofSylow

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148OneRepair

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec14.Item148Rank
open Matrix

variable {p f : ℕ} {K : Type} [Field K] {ω : K}

theorem pow_succ_eq_one148 (hq : p ^ f % 3 = 2) (hω3 : ω ^ 3 = 1) : ω ^ (p ^ f + 1) = 1 := by
  obtain ⟨m, hm⟩ : 3 ∣ p ^ f + 1 := by omega
  rw [hm, pow_mul, hω3, one_pow]

theorem bar_mul_self148 (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 2) (hω3 : ω ^ 3 = 1) :
    h.bar ω * ω = 1 := by
  rw [h.bar_apply, ← pow_succ, pow_succ_eq_one148 hq hω3]

theorem diagOmega_unitary148 (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 2)
    (hω3 : ω ^ 3 = 1) : ((diagOmega148 ω).map h.bar)ᵀ * diagOmega148 ω = 1 := by
  rw [diagOmega148, diagonal_map (map_zero h.bar), diagonal_transpose, diagonal_mul_diagonal,
    ← diagonal_one]
  congr 1
  funext i
  fin_cases i
  · simp
  · simpa using bar_mul_self148 h hq hω3
  · simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    rw [map_pow, ← mul_pow, bar_mul_self148 h hq hω3, one_pow]

theorem cycle_unitary148 (h : UnitaryFieldData p f K) :
    ((cycle148 : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * cycle148 = 1 := by
  have hmap : (cycle148 : Matrix (Fin 3) (Fin 3) K).map h.bar = cycle148 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cycle148]
  rw [hmap]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cycle148, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def diagGL148 (hω3 : ω ^ 3 = 1) : GL (Fin 3) K :=
  ⟨diagOmega148 ω, diagOmega148 ω ^ 2, by rw [← pow_succ', diagOmega_pow_three148 hω3],
    by rw [← pow_succ, diagOmega_pow_three148 hω3]⟩

@[expose] def cycleGL148 : GL (Fin 3) K :=
  ⟨cycle148, cycle148 ^ 2, by rw [← pow_succ', cycle_pow_three148],
    by rw [← pow_succ, cycle_pow_three148]⟩

theorem diagGL_mem148 (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 2) (hω3 : ω ^ 3 = 1) :
    diagGL148 hω3 ∈ unitarySU p f K 3 :=
  (mem_unitarySU_iff h).mpr ⟨by
    change (diagOmega148 ω).det = 1
    rw [det_diagOmega148, hω3], diagOmega_unitary148 h hq hω3⟩

theorem cycleGL_mem148 (h : UnitaryFieldData p f K) :
    (cycleGL148 : GL (Fin 3) K) ∈ unitarySU p f K 3 :=
  (mem_unitarySU_iff h).mpr ⟨det_cycle148, cycle_unitary148 h⟩

theorem mk_eq_one_iff148 (h : UnitaryFieldData p f K) (g : unitarySU p f K 3) :
    (g : unitaryPSU h 3) = 1 ↔ ∃ c : Kˣ, h.norm (c : K) = 1 ∧ c ^ 3 = 1 ∧
      (g : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) c :=
  QuotientGroup.eq_one_iff g

theorem mk_diagSU_ne_one148 (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 2)
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    ((⟨diagGL148 hω3, diagGL_mem148 h hq hω3⟩ : unitarySU p f K 3) : unitaryPSU h 3) ≠ 1 := by
  intro h1
  obtain ⟨c, -, -, hc⟩ := (mk_eq_one_iff148 h _).mp h1
  have hc' := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K)) hc
  simp only [GeneralLinearGroup.coe_scalar] at hc'
  have h00 := congrFun (congrFun hc' 0) 0
  have h11 := congrFun (congrFun hc' 1) 1
  change diagOmega148 ω 0 0 = scalar (Fin 3) (c : K) 0 0 at h00
  change diagOmega148 ω 1 1 = scalar (Fin 3) (c : K) 1 1 at h11
  simp [diagOmega148, scalar_apply] at h00 h11
  exact hω1 (h11.trans h00.symm)

theorem mk_diagSU_pow_three148 (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 2) (hω3 : ω ^ 3 = 1) :
    ((⟨diagGL148 hω3, diagGL_mem148 h hq hω3⟩ : unitarySU p f K 3) : unitaryPSU h 3) ^ 3 = 1 := by
  rw [← QuotientGroup.mk_pow]
  have : (⟨diagGL148 hω3, diagGL_mem148 h hq hω3⟩ : unitarySU p f K 3) ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    change diagOmega148 ω ^ 3 = 1
    exact diagOmega_pow_three148 hω3
  rw [this, QuotientGroup.mk_one]

theorem mk_cycleSU_pow_three148 (h : UnitaryFieldData p f K) :
    ((⟨cycleGL148, cycleGL_mem148 h⟩ : unitarySU p f K 3) : unitaryPSU h 3) ^ 3 = 1 := by
  rw [← QuotientGroup.mk_pow]
  have : (⟨cycleGL148, cycleGL_mem148 h⟩ : unitarySU p f K 3) ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    change cycle148 ^ 3 = 1
    exact cycle_pow_three148
  rw [this, QuotientGroup.mk_one]

theorem mk_diagSU_mul_cycleSU148 (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 2)
    (hω3 : ω ^ 3 = 1) :
    ((⟨diagGL148 hω3, diagGL_mem148 h hq hω3⟩ : unitarySU p f K 3) : unitaryPSU h 3) *
        ((⟨cycleGL148, cycleGL_mem148 h⟩ : unitarySU p f K 3) : unitaryPSU h 3) =
      ((⟨cycleGL148, cycleGL_mem148 h⟩ : unitarySU p f K 3) : unitaryPSU h 3) *
        ((⟨diagGL148 hω3, diagGL_mem148 h hq hω3⟩ : unitarySU p f K 3) : unitaryPSU h 3) := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω3
  set u : Kˣ := Units.mk0 ω hω0 with hu
  have hz : GeneralLinearGroup.scalar (Fin 3) u ∈ unitarySU p f K 3 := by
    refine (mem_unitarySU_iff h).mpr ⟨?_, ?_⟩
    · rw [GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal, Fin.prod_univ_three]
      simp only [hu, Units.val_mk0]
      rw [← hω3]
      ring
    · rw [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_map (map_zero h.bar),
        diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      simp only [hu, Units.val_mk0]
      exact bar_mul_self148 h hq hω3
  have hzs : (⟨GeneralLinearGroup.scalar (Fin 3) u, hz⟩ : unitarySU p f K 3) ∈
      unitaryScalars h 3 :=
    ⟨u, by simpa [hu, UnitaryFieldData.norm, mul_comm] using bar_mul_self148 h hq hω3,
      Units.ext (by simpa [hu] using hω3), rfl⟩
  have h1 : (⟨diagGL148 hω3, diagGL_mem148 h hq hω3⟩ : unitarySU p f K 3) *
      ⟨cycleGL148, cycleGL_mem148 h⟩ = ⟨GeneralLinearGroup.scalar (Fin 3) u, hz⟩ *
        (⟨cycleGL148, cycleGL_mem148 h⟩ * ⟨diagGL148 hω3, diagGL_mem148 h hq hω3⟩) := by
    apply Subtype.ext
    apply Units.ext
    change diagOmega148 ω * cycle148 =
      (GeneralLinearGroup.scalar (Fin 3) u : Matrix (Fin 3) (Fin 3) K) *
        (cycle148 * diagOmega148 ω)
    rw [GeneralLinearGroup.coe_scalar, hu, Units.val_mk0]
    exact diagOmega_mul_cycle148 hω3
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h1, QuotientGroup.mk_mul,
    (QuotientGroup.eq_one_iff _).mpr hzs, one_mul]

theorem mk_cycleSU_ne_pow148 (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 2)
    (hω3 : ω ^ 3 = 1) (j : ℕ) :
    ((⟨cycleGL148, cycleGL_mem148 h⟩ : unitarySU p f K 3) : unitaryPSU h 3) ≠
      ((⟨diagGL148 hω3, diagGL_mem148 h hq hω3⟩ : unitarySU p f K 3) : unitaryPSU h 3) ^ j := by
  set d : unitarySU p f K 3 := ⟨diagGL148 hω3, diagGL_mem148 h hq hω3⟩ with hd
  set t : unitarySU p f K 3 := ⟨cycleGL148, cycleGL_mem148 h⟩ with ht
  intro h1
  rw [← QuotientGroup.mk_pow] at h1
  obtain ⟨c, -, -, hc⟩ := QuotientGroup.eq.mp h1.symm
  apply cycle_ne_diagOmega_pow_mul_scalar148 ω j c
  have h3 : t = d ^ j * ((d ^ j)⁻¹ * t) := by group
  have h4 : (t : GL (Fin 3) K) = ((d ^ j : unitarySU p f K 3) : GL (Fin 3) K) *
      GeneralLinearGroup.scalar (Fin 3) c := by
    conv_lhs => rw [h3]
    rw [Subgroup.coe_mul, hc]
  have h5 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K)) h4
  simp only [Units.val_mul, Subgroup.coe_pow, Units.val_pow_eq_pow_val,
    GeneralLinearGroup.coe_scalar] at h5
  exact h5

theorem psuField_mk_diagSU148 (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 2)
    (hω3 : ω ^ 3 = 1) {σ : K ≃+* K} (hσω : σ ω = ω) :
    psuField h σ ((⟨diagGL148 hω3, diagGL_mem148 h hq hω3⟩ : unitarySU p f K 3) :
      unitaryPSU h 3) = ((⟨diagGL148 hω3, diagGL_mem148 h hq hω3⟩ : unitarySU p f K 3) :
        unitaryPSU h 3) := by
  rw [psuField_mk]
  congr 1
  apply Subtype.ext
  rw [coe_suField]
  apply Units.ext
  rw [UnitaryHigher.coe_glAut]
  change (diagOmega148 ω).map σ = diagOmega148 ω
  rw [diagOmega148, diagonal_map (map_zero σ)]
  congr 1
  funext i
  fin_cases i <;> simp [hσω]

theorem psuField_mk_cycleSU148 (h : UnitaryFieldData p f K) (σ : K ≃+* K) :
    psuField h σ ((⟨cycleGL148, cycleGL_mem148 h⟩ : unitarySU p f K 3) : unitaryPSU h 3) =
      ((⟨cycleGL148, cycleGL_mem148 h⟩ : unitarySU p f K 3) : unitaryPSU h 3) := by
  rw [psuField_mk]
  congr 1
  apply Subtype.ext
  rw [coe_suField]
  apply Units.ext
  rw [UnitaryHigher.coe_glAut]
  change (cycle148 : Matrix (Fin 3) (Fin 3) K).map σ = cycle148
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cycle148]

theorem fixed_e9_unitary148 (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 2)
    (hq2 : 2 < p ^ f) (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (α : MulAut (unitaryPSU h 3))
    (hα3 : α ^ 3 = 1) (hαD : α ∉ (psuConj h).range) :
    ∃ s t : unitaryPSU h 3, α s = s ∧ α t = t ∧ s ≠ 1 ∧ s ^ 3 = 1 ∧ t ^ 3 = 1 ∧
      s * t = t * s ∧ t ∉ Subgroup.zpowers s := by
  obtain ⟨σ, hσ, H, rfl⟩ := unitary_order_three_field_descent hq2 α hα3 hαD
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hσω : σ ω = ω := ringAut_apply_eq_of_pow_three148 hσ3 hω3 hω1
  have hfix : ∀ x : unitaryPSU h 3, psuField h σ x = x →
      (psuConj h H * psuField h σ * (psuConj h H)⁻¹) (psuConj h H x) = psuConj h H x := by
    intro x hx
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hx]
  refine ⟨psuConj h H ((⟨diagGL148 hω3, diagGL_mem148 h hq hω3⟩ : unitarySU p f K 3) :
      unitaryPSU h 3), psuConj h H ((⟨cycleGL148, cycleGL_mem148 h⟩ : unitarySU p f K 3) :
      unitaryPSU h 3), hfix _ (psuField_mk_diagSU148 h hq hω3 hσω),
    hfix _ (psuField_mk_cycleSU148 h σ), ?_, ?_, ?_, ?_, ?_⟩
  · intro h1
    apply mk_diagSU_ne_one148 h hq hω3 hω1
    exact (psuConj h H).injective (h1.trans (map_one _).symm)
  · rw [← map_pow, mk_diagSU_pow_three148 h hq hω3, map_one]
  · rw [← map_pow, mk_cycleSU_pow_three148 h, map_one]
  · rw [← map_mul (psuConj h H), ← map_mul (psuConj h H), mk_diagSU_mul_cycleSU148 h hq hω3]
  · intro h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    rw [← map_zpow] at hk
    have hk' := (psuConj h H).injective hk
    rcases mem_zpowers_pow_three148 (mk_diagSU_pow_three148 h hq hω3)
        (Subgroup.mem_zpowers_iff.mpr ⟨k, hk'⟩) with h2 | h2 | h2
    · exact mk_cycleSU_ne_pow148 h hq hω3 0 (by rw [h2, pow_zero])
    · exact mk_cycleSU_ne_pow148 h hq hω3 1 (by rw [h2, pow_one])
    · exact mk_cycleSU_ne_pow148 h hq hω3 2 h2

theorem diag_mul_pow_unitary148 (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 2)
    (α : MulAut (unitaryPSU h 3)) (hαD : α ∈ (psuConj h).range) (hα : ¬ IsInnerAut α)
    (β : MulAut (unitaryPSU h 3)) (hβD : β ∈ (psuConj h).range) :
    ∃ k : ℕ, IsInnerAut (β * α ^ k) := by
  have := h.finite
  have hpow2 : p ^ (2 * f) = (p ^ f) ^ 2 := by rw [pow_mul']
  have hcardU : Nat.card Kˣ = (p ^ f) ^ 2 - 1 := by rw [Nat.card_units, h.card, hpow2]
  have hm : p ^ f + 1 ∣ Nat.card Kˣ := by
    rw [hcardU]
    refine ⟨p ^ f - 1, ?_⟩
    obtain ⟨s, hs⟩ : ∃ s, p ^ f = s + 1 := ⟨p ^ f - 1, by omega⟩
    rw [hs, Nat.add_sub_cancel]
    have : (s + 1) ^ 2 = (s + 1 + 1) * s + 1 := by ring
    omega
  have hm3 : 3 ∣ p ^ f + 1 := by omega
  obtain ⟨A, rfl⟩ := hαD
  have hnd : ¬ ∃ u : Kˣ, u ^ (p ^ f + 1) = 1 ∧ u ^ 3 = GeneralLinearGroup.det
      (A : GL (Fin 3) K) :=
    fun ⟨u, hu1, hu⟩ => hα (isInnerAut_psuConj_of_det_eq_cube148 A hu hu1)
  obtain ⟨B, rfl⟩ := hβD
  obtain ⟨k, -, u, hu1, hu⟩ := exists_mul_pow_cube148 (G := Kˣ) hm hm3
    (det_pow_succ_eq_one_of_mem_unitaryIsom3 h A.2)
    (det_pow_succ_eq_one_of_mem_unitaryIsom3 h B.2) hnd
  refine ⟨k, ?_⟩
  rw [← map_pow, ← map_mul]
  refine isInnerAut_psuConj_of_det_eq_cube148 _ (u := u) ?_ hu1
  rw [hu]
  change _ = GeneralLinearGroup.det ((B : GL (Fin 3) K) * (A : GL (Fin 3) K) ^ k)
  rw [map_mul, map_pow]

theorem autFacts148_unitary (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 2) (hq2 : 2 < p ^ f)
    (hZ : Subgroup.center (unitaryPSU h 3) = ⊥) :
    AutFacts148 (unitaryPSU h 3) (psuConj h).range := by
  have := h.finite
  have hpow2 : p ^ (2 * f) = (p ^ f) ^ 2 := by rw [pow_mul']
  have hcardU : Nat.card Kˣ = (p ^ f) ^ 2 - 1 := by rw [Nat.card_units, h.card, hpow2]
  obtain ⟨ω, hω3, hω1⟩ := exists_cube_root_one148 (K := K) (by
    rw [hcardU]
    obtain ⟨s, hs⟩ : ∃ s, p ^ f = 3 * s + 2 := ⟨p ^ f / 3, by omega⟩
    rw [hs]
    refine ⟨3 * s ^ 2 + 4 * s + 1, ?_⟩
    have : (3 * s + 2) ^ 2 = 3 * (3 * s ^ 2 + 4 * s + 1) + 1 := by ring
    omega)
  exact { center_eq_bot := hZ
          conj_mem := fun w => (stdPinnedPSU3 h).inn_le ⟨w, rfl⟩
          inner_mul_pow := fun α β h1 h2 h3 h4 =>
            exists_isInnerAut_mul_pow_unitary148 (h := h) hq hq2 h1 h2 h3 h4
          fixed_e9 := fun α h1 h2 => fixed_e9_unitary148 h hq hq2 hω3 hω1 α h1 h2
          diag_mul_pow := fun α hα h1 β hβ => diag_mul_pow_unitary148 h hq α hα h1 β hβ }

theorem nonempty_range_psuConj_mulEquiv148 (h : UnitaryFieldData p f K) :
    Nonempty (↥(psuConj h).range ≃*
      ↥(CFSG.Assembly.RankThreeEven.projImage (Sec4.glPi false 3 (p ^ f) K))) := by
  let ψ : unitaryIsom3 h →* Matrix.ProjGenLinGroup (Fin 3) K :=
    Matrix.ProjGenLinGroup.mk.comp (unitaryIsom3 h).subtype
  have hker : (psuConj h).ker = ψ.ker := by
    ext A
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hA
      obtain ⟨-, c, -, hc⟩ := eq_one_of_psuConj_mul_psuField_eq_one A 1
        (by rw [map_one, mul_one, hA])
      change Matrix.ProjGenLinGroup.mk (A : GL (Fin 3) K) = 1
      rw [hc, Matrix.ProjGenLinGroup.mk_scalar]
    · intro hA
      change Matrix.ProjGenLinGroup.mk (A : GL (Fin 3) K) = 1 at hA
      rw [Matrix.ProjGenLinGroup.mk_eq_one,
        Matrix.GeneralLinearGroup.center_eq_range_scalar] at hA
      obtain ⟨c, hc⟩ := hA
      ext x
      induction x using QuotientGroup.induction_on with
      | H g =>
        rw [psuConj_mk, MulAut.one_apply]
        congr 1
        apply Subtype.ext
        have hAc : (A : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) := by
          rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
          exact ⟨c, hc⟩
        rw [coe_suConj, Subgroup.coe_inv,
          ← Subgroup.mem_center_iff.mp hAc (g : GL (Fin 3) K), mul_inv_cancel_right]
  have hglPi : Sec4.glPi false 3 (p ^ f) K = unitaryIsom3 h := by
    ext A
    rw [Sec4.mem_glPi_false h]
    rfl
  have hrange : ψ.range = CFSG.Assembly.RankThreeEven.projImage (Sec4.glPi false 3 (p ^ f) K) := by
    rw [hglPi]
    change (Matrix.ProjGenLinGroup.mk.comp (unitaryIsom3 h).subtype).range =
      (unitaryIsom3 h).map Matrix.ProjGenLinGroup.mk
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨(QuotientGroup.quotientKerEquivRange (psuConj h)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      ((QuotientGroup.quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hrange)))⟩

end CFSG.RankThree.PartTwo.Sec14.Item148OneRepair
