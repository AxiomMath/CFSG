module

public import CFSG.RankThree.PartTwo.Sec14.Item148OneRepairProofCore
public import CFSG.RankThree.PartTwo.Sec14.Item148RankProofField
import CFSG.RankThree.PartTwo.Sec14.Item148OneRepairProofSylow

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148OneRepair

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec14.Item148Rank
open Matrix

variable {K : Type} [Field K]

theorem eq_of_pow_three148 {ω x : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hx : x ^ 3 = 1) :
    x = 1 ∨ x = ω ∨ x = ω ^ 2 := by
  have h : 1 + ω + ω ^ 2 = 0 := by
    have h1 : (ω - 1) * (1 + ω + ω ^ 2) = 0 := by linear_combination hω3
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd (sub_eq_zero.mp h2) hω1
    · exact h2
  have hprod : (x - 1) * (x - ω) * (x - ω ^ 2) = 0 := by
    linear_combination hx + (x - x ^ 2) * h + (x - 1) * hω3
  rcases mul_eq_zero.mp hprod with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact Or.inl (sub_eq_zero.mp h2)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h2))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h1))

theorem ringAut_apply_eq_of_pow_three148 {σ : K ≃+* K} (hσ : σ ^ 3 = 1) {ω : K}
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) : σ ω = ω := by
  have hσω3 : (σ ω) ^ 3 = 1 := by rw [← map_pow, hω3, map_one]
  rcases eq_of_pow_three148 hω3 hω1 hσω3 with h | h | h
  · exact absurd (σ.injective (h.trans (map_one σ).symm)) hω1
  · exact h
  · exfalso
    have h2 : σ (σ ω) = ω := by
      rw [h, map_pow, h, ← pow_mul]
      calc ω ^ (2 * 2) = ω ^ 3 * ω := by ring
        _ = ω := by rw [hω3, one_mul]
    have h3 : σ (σ (σ ω)) = ω := by
      have h4 := congrArg (fun τ : K ≃+* K => τ ω) hσ
      simp only [pow_succ, pow_zero, one_mul, RingAut.mul_apply, RingAut.one_apply] at h4
      exact h4
    rw [h2, h] at h3
    apply hω1
    have h5 : ω * (ω - 1) = 0 := by linear_combination h3
    rcases mul_eq_zero.mp h5 with h6 | h6
    · rw [h6] at hω3
      norm_num at hω3
    · exact sub_eq_zero.mp h6

theorem exists_cube_root_one148 [Finite K] (h3 : 3 ∣ Nat.card Kˣ) :
    ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 h3
  refine ⟨u, ?_, ?_⟩
  · have h1 := pow_orderOf_eq_one u
    rw [hu] at h1
    have h2 := congrArg Units.val h1
    simpa using h2
  · intro h
    have h1 : u = 1 := Units.ext h
    rw [h1, orderOf_one] at hu
    omega

@[expose] def diagOmega148 (ω : K) : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![1, ω, ω ^ 2]

@[expose] def cycle148 : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem det_diagOmega148 (ω : K) : (diagOmega148 ω).det = ω ^ 3 := by
  rw [diagOmega148, det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

theorem det_cycle148 : (cycle148 : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [cycle148, Matrix.det_fin_three]
  simp

@[expose] def diagSL148 {ω : K} (hω3 : ω ^ 3 = 1) : SpecialLinearGroup (Fin 3) K :=
  ⟨diagOmega148 ω, by rw [det_diagOmega148, hω3]⟩

@[expose] def cycleSL148 : SpecialLinearGroup (Fin 3) K :=
  ⟨cycle148, det_cycle148⟩

theorem diagOmega_mul_cycle148 {ω : K} (hω3 : ω ^ 3 = 1) :
    diagOmega148 ω * cycle148 = scalar (Fin 3) ω * (cycle148 * diagOmega148 ω) := by
  ext i j
  rw [diagOmega148, diagonal_mul, scalar_apply, diagonal_mul, mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [cycle148]
  · rw [← pow_succ', hω3]
  · ring

theorem cycle_pow_three148 : (cycle148 : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycle148, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem diagOmega_pow_three148 {ω : K} (hω3 : ω ^ 3 = 1) :
    (diagOmega148 ω) ^ 3 = 1 := by
  rw [diagOmega148, diagonal_pow, ← diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp [← pow_mul, hω3]
  calc ω ^ 6 = (ω ^ 3) ^ 2 := by ring
    _ = 1 := by rw [hω3, one_pow]

theorem diagOmega_pow_apply_zero148 (ω : K) (j : ℕ) : ((diagOmega148 ω) ^ j) 0 0 = 1 := by
  rw [diagOmega148, diagonal_pow, diagonal_apply_eq]
  simp

theorem cycle_ne_diagOmega_pow_mul_scalar148 (ω : K) (j : ℕ) (c : Kˣ) :
    cycle148 ≠ (diagOmega148 ω) ^ j * scalar (Fin 3) (c : K) := by
  intro h
  have h1 := congrFun (congrFun h 0) 0
  rw [scalar_apply, mul_diagonal, diagOmega_pow_apply_zero148, one_mul] at h1
  simp [cycle148] at h1
  exact c.ne_zero h1.symm

variable {ω : K}

theorem proj_diagSL_ne_one148 (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    proj 3 K (diagSL148 hω3) ≠ 1 := by
  intro h
  rw [proj, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_scalars] at h
  obtain ⟨c, -, hc⟩ := h
  have h00 := congrFun (congrFun hc 0) 0
  have h11 := congrFun (congrFun hc 1) 1
  change diagOmega148 ω 0 0 = scalar (Fin 3) (c : K) 0 0 at h00
  change diagOmega148 ω 1 1 = scalar (Fin 3) (c : K) 1 1 at h11
  simp [diagOmega148, scalar_apply] at h00 h11
  exact hω1 (h11.trans h00.symm)

theorem proj_diagSL_pow_three148 (hω3 : ω ^ 3 = 1) : proj 3 K (diagSL148 hω3) ^ 3 = 1 := by
  rw [← map_pow]
  have : diagSL148 hω3 ^ 3 = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_pow]
    exact diagOmega_pow_three148 hω3)
  rw [this, map_one]

theorem proj_cycleSL_pow_three148 : proj 3 K cycleSL148 ^ 3 = 1 := by
  rw [← map_pow]
  have : (cycleSL148 : SpecialLinearGroup (Fin 3) K) ^ 3 = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_pow]
    exact cycle_pow_three148)
  rw [this, map_one]

theorem proj_diagSL_mul_cycleSL148 (hω3 : ω ^ 3 = 1) :
    proj 3 K (diagSL148 hω3) * proj 3 K cycleSL148 =
      proj 3 K cycleSL148 * proj 3 K (diagSL148 hω3) := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω3
  have hu : (Units.mk0 ω hω0) ^ 3 = 1 := Units.ext (by simpa using hω3)
  have hz : proj 3 K (scalarElement (Units.mk0 ω hω0) hu) = 1 := by
    rw [proj, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact scalarElement_mem_scalars _ hu
  have h1 : diagSL148 hω3 * cycleSL148 =
      scalarElement (Units.mk0 ω hω0) hu * (cycleSL148 * diagSL148 hω3) := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, coe_scalarElement, Units.val_mk0]
    exact diagOmega_mul_cycle148 hω3)
  rw [← map_mul, ← map_mul, h1, map_mul, hz, one_mul]

theorem proj_cycleSL_ne_pow148 (hω3 : ω ^ 3 = 1) (j : ℕ) :
    proj 3 K cycleSL148 ≠ proj 3 K (diagSL148 hω3) ^ j := by
  intro h
  rw [← map_pow, proj, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at h
  have h1 := QuotientGroup.eq.mp h.symm
  obtain ⟨u, -, hu⟩ := mem_scalars.mp h1
  apply cycle_ne_diagOmega_pow_mul_scalar148 ω j u
  have h2 : (cycleSL148 : SpecialLinearGroup (Fin 3) K) =
      diagSL148 hω3 ^ j * ((diagSL148 hω3 ^ j)⁻¹ * cycleSL148) := by group
  calc (cycle148 : Matrix (Fin 3) (Fin 3) K)
      = ((cycleSL148 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := rfl
    _ = ((diagSL148 hω3 ^ j * ((diagSL148 hω3 ^ j)⁻¹ * cycleSL148) :
        SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by rw [← h2]
    _ = (diagOmega148 ω) ^ j * scalar (Fin 3) (u : K) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, hu, Matrix.SpecialLinearGroup.coe_pow]
      rfl

theorem fieldAut_proj_diagSL148 (hω3 : ω ^ 3 = 1) {σ : K ≃+* K} (hσω : σ ω = ω) :
    fieldAut 3 K σ (proj 3 K (diagSL148 hω3)) = proj 3 K (diagSL148 hω3) := by
  rw [fieldAut_proj]
  congr 1
  apply Subtype.ext
  change (diagOmega148 ω).map σ = diagOmega148 ω
  rw [diagOmega148, diagonal_map (map_zero σ)]
  congr 1
  funext i
  fin_cases i <;> simp [hσω]

theorem fieldAut_proj_cycleSL148 (σ : K ≃+* K) :
    fieldAut 3 K σ (proj 3 K cycleSL148) = proj 3 K cycleSL148 := by
  rw [fieldAut_proj]
  congr 1
  apply Subtype.ext
  change (cycle148 : Matrix (Fin 3) (Fin 3) K).map σ = cycle148
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cycle148]

theorem fixed_e9_linear148 [Finite K] (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (α : MulAut (projectiveSL 3 K)) (hα3 : α ^ 3 = 1) (hαD : α ∉ linearAutGroup 3 K) :
    ∃ s t : projectiveSL 3 K, α s = s ∧ α t = t ∧ s ≠ 1 ∧ s ^ 3 = 1 ∧ t ^ 3 = 1 ∧
      s * t = t * s ∧ t ∉ Subgroup.zpowers s := by
  obtain ⟨σ, hσ, H, rfl⟩ := linear_order_three_field_descent le_rfl α hα3 hαD
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hσω : σ ω = ω := ringAut_apply_eq_of_pow_three148 hσ3 hω3 hω1
  have hfix : ∀ x : projectiveSL 3 K, fieldAut 3 K σ x = x →
      (conjAut 3 K H * fieldAut 3 K σ * (conjAut 3 K H)⁻¹) (conjAut 3 K H x) =
        conjAut 3 K H x := by
    intro x hx
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hx]
  refine ⟨conjAut 3 K H (proj 3 K (diagSL148 hω3)), conjAut 3 K H (proj 3 K cycleSL148),
    hfix _ (fieldAut_proj_diagSL148 hω3 hσω), hfix _ (fieldAut_proj_cycleSL148 σ), ?_, ?_, ?_,
    ?_, ?_⟩
  · intro h
    apply proj_diagSL_ne_one148 hω3 hω1
    exact (conjAut 3 K H).injective (h.trans (map_one _).symm)
  · rw [← map_pow, proj_diagSL_pow_three148 hω3, map_one]
  · rw [← map_pow, proj_cycleSL_pow_three148, map_one]
  · rw [← map_mul (conjAut 3 K H), ← map_mul (conjAut 3 K H), proj_diagSL_mul_cycleSL148 hω3]
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [← map_zpow] at hk
    have hk' := (conjAut 3 K H).injective hk
    rcases mem_zpowers_pow_three148 (proj_diagSL_pow_three148 hω3)
        (Subgroup.mem_zpowers_iff.mpr ⟨k, hk'⟩) with h1 | h1 | h1
    · exact proj_cycleSL_ne_pow148 hω3 0 (by rw [h1, pow_zero])
    · exact proj_cycleSL_ne_pow148 hω3 1 (by rw [h1, pow_one])
    · exact proj_cycleSL_ne_pow148 hω3 2 h1

theorem diag_mul_pow_linear148 [Finite K] {p F : ℕ} (hp : p.Prime) (hcard : Nat.card K = p ^ F)
    (hK : p ^ F % 3 = 1) (α : MulAut (projectiveSL 3 K)) (hαD : α ∈ linearAutGroup 3 K)
    (hα : ¬ IsInnerAut α) (β : MulAut (projectiveSL 3 K)) (hβD : β ∈ linearAutGroup 3 K) :
    ∃ k : ℕ, IsInnerAut (β * α ^ k) := by
  have hcardU : Nat.card Kˣ = p ^ F - 1 := by rw [Nat.card_units, hcard]
  have hm3 : 3 ∣ p ^ F - 1 := by
    have := Nat.one_le_pow F p hp.pos
    omega
  obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hαD
  have hnd : ¬ ∃ u : Kˣ, u ^ (p ^ F - 1) = 1 ∧ u ^ 3 = GeneralLinearGroup.det A :=
    fun ⟨u, _, hu⟩ => hα (isInnerAut_conjAut_of_det_eq_cube148 A hu)
  obtain ⟨B, rfl⟩ := mem_linearAutGroup_iff.mp hβD
  obtain ⟨k, -, u, -, hu⟩ := exists_mul_pow_cube148 (G := Kˣ)
    (d := GeneralLinearGroup.det A) (b := GeneralLinearGroup.det B) (by rw [hcardU]) hm3
    (by rw [← hcardU]; exact pow_card_eq_one') (by rw [← hcardU]; exact pow_card_eq_one') hnd
  refine ⟨k, ?_⟩
  rw [← map_pow, ← map_mul]
  refine isInnerAut_conjAut_of_det_eq_cube148 _ (u := u) ?_
  rw [hu, map_mul, map_pow]

theorem autFacts148_linear [Finite K] {p F : ℕ} (hp : p.Prime) (hF : 1 ≤ F)
    (hcard : Nat.card K = p ^ F) (hK : p ^ F % 3 = 1)
    (hZ : Subgroup.center (projectiveSL 3 K) = ⊥) :
    AutFacts148 (projectiveSL 3 K) (linearAutGroup 3 K) := by
  have hcardU : Nat.card Kˣ = p ^ F - 1 := by rw [Nat.card_units, hcard]
  obtain ⟨ω, hω3, hω1⟩ := exists_cube_root_one148 (K := K) (by
    rw [hcardU]
    have := Nat.one_le_pow F p hp.pos
    omega)
  exact { center_eq_bot := hZ
          conj_mem := fun w => (stdPinnedPSL 3 K).inn_le ⟨w, rfl⟩
          inner_mul_pow := fun α β h1 h2 h3 h4 =>
            exists_isInnerAut_mul_pow_linear148 hp hF hcard hK h1 h2 h3 h4
          fixed_e9 := fun α h1 h2 => fixed_e9_linear148 hω3 hω1 α h1 h2
          diag_mul_pow := fun α hα h1 β hβ => diag_mul_pow_linear148 hp hcard hK α hα h1 β hβ }

theorem nonempty_linearAutGroup_mulEquiv148 [Finite K] (q : ℕ) :
    Nonempty (↥(linearAutGroup 3 K) ≃*
      ↥(CFSG.Assembly.RankThreeEven.projImage (Sec4.glPi true 3 q K))) := by
  let φ : Matrix.ProjGenLinGroup (Fin 3) K →* MulAut (projectiveSL 3 K) :=
    Matrix.ProjGenLinGroup.lift (conjAut 3 K) (MonoidHom.ext fun u => conjAut_scalar u)
  have hφ : ∀ A : GL (Fin 3) K, φ (Matrix.ProjGenLinGroup.mk A) = conjAut 3 K A :=
    fun A => Matrix.ProjGenLinGroup.lift_mk _ A
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective x
    rw [hφ] at hx
    obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) A 1
      (by rw [map_one, mul_one, hx])
    rw [← hc, Matrix.ProjGenLinGroup.mk_scalar]
  have hrange : φ.range = linearAutGroup 3 K := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective x
      rw [hφ]
      exact conjAut_mem_linearAutGroup A
    · rw [linearAutGroup, Subgroup.closure_le]
      rintro _ ⟨A, rfl⟩
      exact ⟨Matrix.ProjGenLinGroup.mk A, hφ A⟩
  have htop : CFSG.Assembly.RankThreeEven.projImage (Sec4.glPi true 3 q K) = ⊤ := by
    change (⊤ : Subgroup (GL (Fin 3) K)).map Matrix.ProjGenLinGroup.mk = ⊤
    rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact Matrix.ProjGenLinGroup.mk_surjective
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm.trans
    (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm))⟩

end CFSG.RankThree.PartTwo.Sec14.Item148OneRepair
