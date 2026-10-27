module

public import CFSG.Quasithin.EmptyFaithful.A38c10Nd
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4CNat4A

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.A38c10

open Matrix CFSG.Quasithin CFSG.Quasithin.FLc CFSG.QuasithinUnique
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.S15223P4.C.Nat4

theorem entry_succ_zero_of_mem_QI_one {g : SLt 4} (hg : g ∈ QI 4 {1}) (i : Fin 3) :
    (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) i.succ 0 = 0 :=
  mem_QI_one_iff.1 hg i

theorem entry_zero_zero_of_mem_QI_one {g : SLt 4} (hg : g ∈ QI 4 {1}) :
    (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 0 = 1 := by
  have h := det_eq_mul_det_blk hg
  rw [Matrix.SpecialLinearGroup.det_coe, det_blk hg, mul_one] at h
  exact h.symm

theorem exists_psi1 : ∃ ψ : ↥(QI 4 {1}) →* SLt 3, Function.Surjective ψ ∧
    ∀ x : ↥(QI 4 {1}), ψ x = 1 → (x : SLt 4) ∈ Ut 4 := by
  refine ⟨blkHom 3, blkHom_surjective 3, fun x hx => ?_⟩
  have h1 := mem_QI_one_iff.1 x.2
  have h3 : ∀ i j : Fin 3, (x.1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) i.succ j.succ =
      (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j := by
    intro i j
    have := congrArg (fun y : SLt 3 => (y : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j) hx
    simpa [blkHom_coe] using this
  have h2 := entry_zero_zero_of_mem_QI_one x.2
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · induction i using Fin.cases with
    | zero => exact absurd hij (Fin.not_lt_zero j)
    | succ i' =>
      induction j using Fin.cases with
      | zero => exact h1 i'
      | succ j' =>
        rw [h3 i' j', Matrix.one_apply_ne]
        exact (Fin.succ_lt_succ_iff.1 hij).ne'
  · induction i using Fin.cases with
    | zero => exact h2
    | succ i' => rw [h3 i' i', Matrix.one_apply_eq]

@[expose] def e1 : Multiplicative (Vt 4) := Multiplicative.ofAdd ![1, 0, 0, 0]

@[expose] def w1 : Multiplicative (Vt 4) := Multiplicative.ofAdd ![0, 0, 1, 0]

theorem actM_e1_of_mem {t : SLt 4} (ht : t ∈ QI 4 {1}) : actM t e1 = e1 := by
  have h := entry_succ_zero_of_mem_QI_one ht
  have h0 := entry_zero_zero_of_mem_QI_one ht
  apply Multiplicative.toAdd.injective
  rw [toAdd_actM]
  funext i
  fin_cases i
  · simp [e1, Matrix.mulVec, dotProduct, Fin.sum_univ_four, h0]
  · simpa [e1, Matrix.mulVec, dotProduct, Fin.sum_univ_four] using h 0
  · simpa [e1, Matrix.mulVec, dotProduct, Fin.sum_univ_four] using h 1
  · simpa [e1, Matrix.mulVec, dotProduct, Fin.sum_univ_four] using h 2

theorem actM_e1_ne_one (g : SLt 4) : actM g e1 ≠ 1 := by
  intro h
  have h1 : (mat g) *ᵥ ![1, 0, 0, 0] = 0 := congrArg Multiplicative.toAdd h
  have h2 := congrArg (fun v => mat g⁻¹ *ᵥ v) h1
  simp only [mulVec_mulVec, ← mat_mul, inv_mul_cancel, mat_one, one_mulVec, mulVec_zero] at h2
  have h3 := congrFun h2 0
  revert h3
  decide

@[expose] def t1M : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 1; 0, 0, 1, 0]

theorem t1M_det : t1M.det = 1 := by decide

@[expose] def t1 : SLt 4 := ⟨t1M, t1M_det⟩

theorem t1_pow : t1 ^ 3 = 1 := by
  apply Subtype.ext
  show t1M ^ 3 = 1
  decide

theorem t1_mem : t1 ∈ QI 4 {1} := mem_QI_single_of (by decide +revert)

theorem actM_t1_g1 : actM (t1 * g1) w1 = e1 * w1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_actM, toAdd_mul]
  show mat (t1 * g1) *ᵥ ![0, 0, 1, 0] = ![1, 0, 0, 0] + ![0, 0, 1, 0]
  rw [mat_mul]
  show (t1M * g1M) *ᵥ _ = _
  decide

private theorem conj_mul_conj_aux' {G : Type*} [Group G] (g a b : G) :
    g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by
  group

theorem exists_q_nat {V : Type} [CommGroup V] {ρ : SLt 4 →* MulAut V} {U₁ : Subgroup V}
    (D₁ : VModel 4 ρ U₁ ⊥ (Multiplicative (Vt 4)) (fun g a => actM g a)) (g : SLt 4)
    {P : Subgroup (MulAut V)} (hP₁ : ∀ a ∈ P, ∃ t ∈ QI 4 {1}, ρ (g * t * g⁻¹) = a)
    (hP₂ : ∀ t ∈ QI 4 {1}, ρ (g * t * g⁻¹) ∈ P) :
    ∃ q ∈ U₁, q ≠ 1 ∧ (∀ a ∈ P, a q = q) ∧ q ∈ commV (oTwoUpper P) := by
  obtain ⟨q₀, hq₀⟩ := D₁.surj (actM g e1)
  obtain ⟨x₀, hx₀⟩ := D₁.surj (actM g w1)
  have hq₀U : (q₀ : V) ∈ U₁ := q₀.2
  have hx₀U : (x₀ : V) ∈ U₁ := x₀.2
  have hβq : D₁.β ⟨(q₀ : V), hq₀U⟩ = actM g e1 := hq₀
  have hβx : D₁.β ⟨(x₀ : V), hx₀U⟩ = actM g w1 := hx₀
  have hmul : ∀ (g h : SLt 4) (a : Multiplicative (Vt 4)), actM (g * h) a = actM g (actM h a) :=
    fun g h a => D₁.act_mul g h a
  refine ⟨(q₀ : V), hq₀U, ?_, ?_, ?_⟩
  · intro h1
    have h2 : q₀ = 1 := Subtype.ext h1
    rw [h2, map_one] at hq₀
    exact actM_e1_ne_one g hq₀.symm
  · intro a ha
    obtain ⟨t, ht, rfl⟩ := hP₁ a ha
    refine (vmodel_rho_eq_iff D₁ hq₀U hq₀U _).2 ?_
    rw [hβq]
    show actM (g * t * g⁻¹) (actM g e1) = actM g e1
    rw [← hmul, inv_mul_cancel_right, hmul, actM_e1_of_mem ht]
  · have hodd : ∀ (t : SLt 4) (m : ℕ), Odd m → t ^ m = 1 → t ∈ QI 4 {1} →
        ρ (g * t * g⁻¹) ∈ oTwoUpper P := by
      intro t m hm htm ht
      refine mem_oTwoUpper_of_odd (hP₂ t ht) ?_
      have h1 : (ρ (g * t * g⁻¹)) ^ m = 1 := by
        rw [← map_pow, conj_pow, htm, mul_one, mul_inv_cancel, map_one]
      exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one h1)
    have ha₁ := hodd t1 3 (by decide) t1_pow t1_mem
    have ha₂ := hodd g1 7 (by decide) g1_pow g1_mem
    refine Subgroup.subset_closure ⟨_, (oTwoUpper P).mul_mem ha₁ ha₂, (x₀ : V), ?_⟩
    have hprod : ρ (g * t1 * g⁻¹) * ρ (g * g1 * g⁻¹) = ρ (g * (t1 * g1) * g⁻¹) := by
      rw [← map_mul, conj_mul_conj_aux']
    rw [hprod, mul_inv_eq_iff_eq_mul]
    have hv : (q₀ : V) * (x₀ : V) ∈ U₁ := U₁.mul_mem hq₀U hx₀U
    refine (vmodel_rho_eq_iff D₁ hx₀U hv _).2 ?_
    have hβm : D₁.β ⟨(q₀ : V) * (x₀ : V), hv⟩ = D₁.β ⟨(q₀ : V), hq₀U⟩ * D₁.β ⟨(x₀ : V), hx₀U⟩ :=
      map_mul D₁.β q₀ x₀
    rw [hβm, hβq, hβx]
    show actM (g * (t1 * g1) * g⁻¹) (actM g w1) = actM g e1 * actM g w1
    rw [← hmul, inv_mul_cancel_right, hmul, actM_t1_g1, map_mul]

end CFSG.Quasithin.A38c10
