module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Defs
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiAut
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3L3Abs
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3L3BT
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec12.ONanKS128Diag
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Open (StatedScalars)

variable {π : Bool} {f : ℕ} {K : Type} [Field K]

private theorem conj_diagTau_mem_slPi' (hK : PiField π 2 f K) (hq : ModThree π (2 ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) {H : GL (Fin 3) K} (hH : H ∈ glPi π 3 (2 ^ f) K) :
    H * diagTau hτ * H⁻¹ ∈ slPi π 3 (2 ^ f) K :=
  conj_mem_slPi (fun h => by subst h; exact hK.unitary) hH
    (diagTau_mem_slPi (fun h => by subst h; exact hK.unitary) (fun h => by subst h; exact hq) hτ)

private theorem conj_cycThree_mem_slPi' (hK : PiField π 2 f K) {H : GL (Fin 3) K}
    (hH : H ∈ glPi π 3 (2 ^ f) K) : H * cycThree * H⁻¹ ∈ slPi π 3 (2 ^ f) K :=
  conj_mem_slPi (fun h => by subst h; exact hK.unitary) hH
    (cycThree_mem_slPi (fun h => by subst h; exact hK.unitary))

private theorem frobGL_diagTau_of_fix {τ : K} (hτ : τ ^ 3 = 1) {σ : K ≃+* K} (hστ : σ τ = τ) :
    frobGL σ (diagTau hτ) = diagTau hτ := by
  apply Units.ext
  rw [coe_frobGL, coe_diagTau]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hστ]

private theorem diagTau_notMem_statedScalars' {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    diagTau hτ ∉ StatedScalars (Fin 3) K := by
  rintro ⟨t, ht⟩
  have h00 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 0 0) ht
  have h22 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 2 2) ht
  simp only [coe_diagTau, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq] at h00 h22
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one] at h00 h22
  exact hτ1 (h00.symm.trans h22)

private theorem diagE_mul_diagTau_comm (e : Kˣ) {τ : K} (hτ : τ ^ 3 = 1) :
    diagE e * diagTau hτ = diagTau hτ * diagE e := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagE, coe_diagTau_eq_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

variable {c g : MulAut (slPi π 3 (2 ^ f) K)} {V U : Subgroup (MulAut (slPi π 3 (2 ^ f) K))}

theorem false_of_field_aut_datum (hK : PiField π 2 f K) (hq : ModThree π (2 ^ f))
    (h : Res3Datum c g V U) {σ : K ≃+* K} (hσ : σ ^ 3 = 1) {H : GL (Fin 3) K}
    (hH : H ∈ glPi π 3 (2 ^ f) K)
    (hc : ∀ s : slPi π 3 (2 ^ f) K, ((c s : slPi π 3 (2 ^ f) K) : GL (Fin 3) K) =
      H * frobGL σ (H⁻¹ * s * H) * H⁻¹) : False := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have hτ2 : τ ^ 2 ≠ 1 := fun h2 => hτ1 (by
    have h' := hτ
    rw [pow_succ, h2, one_mul] at h'
    exact h')
  have hστ : σ τ = τ := by
    have hσ3 : ∀ x : K, σ (σ (σ x)) = x := fun x => by
      have h1 := congrArg (fun e : K ≃+* K => e x) hσ
      simpa [pow_succ] using h1
    have hinv : τ⁻¹ = τ ^ 2 :=
      (eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hτ)).symm
    have hsum : τ + τ⁻¹ = -1 := by
      rw [hinv]
      linear_combination one_add_tau_add_sq hτ hτ1
    exact KFacts.ringAut_fixed_of_add_inv hσ3 hτ0 hτ2 (by rw [hsum, map_neg, map_one])
  let x₁ : slPi π 3 (2 ^ f) K := ⟨H * diagTau hτ * H⁻¹, conj_diagTau_mem_slPi' hK hq hτ hH⟩
  let x₂ : slPi π 3 (2 ^ f) K := ⟨H * cycThree * H⁻¹, conj_cycThree_mem_slPi' hK hH⟩
  have hx₁ : c x₁ = x₁ := Subtype.ext (by
    rw [hc]
    show H * frobGL σ (H⁻¹ * (H * diagTau hτ * H⁻¹) * H) * H⁻¹ = H * diagTau hτ * H⁻¹
    rw [show H⁻¹ * (H * diagTau hτ * H⁻¹) * H = diagTau hτ by group,
      frobGL_diagTau_of_fix hτ hστ])
  have hx₂ : c x₂ = x₂ := Subtype.ext (by
    rw [hc]
    show H * frobGL σ (H⁻¹ * (H * cycThree * H⁻¹) * H) * H⁻¹ = H * cycThree * H⁻¹
    rw [show H⁻¹ * (H * cycThree * H⁻¹) * H = cycThree by group,
      Sec12.KS128Move.frobGL_cycThree σ])
  have hx₁3 : x₁ ^ 3 = 1 := Subtype.ext (by
    show (H * diagTau hτ * H⁻¹) ^ 3 = 1
    rw [conj_pow, diagTau_pow_three hτ, mul_one, mul_inv_cancel])
  have hx₂3 : x₂ ^ 3 = 1 := Subtype.ext (by
    show (H * cycThree * H⁻¹) ^ 3 = 1
    rw [conj_pow, cycThree_pow_three, mul_one, mul_inv_cancel])
  have hxy : x₁ * x₂ ≠ x₂ * x₁ := by
    intro hcomm
    have h1 : (H * diagTau hτ * H⁻¹) * (H * cycThree * H⁻¹) =
        (H * cycThree * H⁻¹) * (H * diagTau hτ * H⁻¹) := congrArg Subtype.val hcomm
    have h2 : diagTau hτ * cycThree = cycThree * diagTau hτ := by
      apply (MulAut.conj H).injective
      simpa only [map_mul, MulAut.conj_apply] using h1
    have h3 : cycThree * diagTau hτ * cycThree⁻¹ = diagTau hτ := by
      rw [← h2, mul_inv_cancel_right]
    have hmat := cycThree_conj_diagTau hτ
    rw [h3] at hmat
    have h22 : (1 : K) = τ ^ 2 := by
      have h4 := congrFun (congrFun hmat 2) 2
      simpa [coe_diagTau] using h4
    exact hτ2 h22.symm
  exact h.false_of_fixed_noncomm hx₁ hx₂ hx₁3 hx₂3 hxy

theorem exists_semiAct_pow_three_scalar (hK : PiField π 2 f K) (hq : ModThree π (2 ^ f))
    (h : Res3Datum c g V U) {y : GL (Fin 3) K} (hy : y ∈ glPi π 3 (2 ^ f) K)
    (hcy : KFacts.SemiAct c 1 y) :
    ∃ ℓ : Kˣ, y ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) ℓ := by
  have h1 : slPiConj hK ((⟨y, hy⟩ : glPi π 3 (2 ^ f) K) ^ 3) = 1 := by
    rw [map_pow, ← slPiConj_eq_of_semiAct hK hy hcy]
    exact h.c_pow
  obtain ⟨ℓ, hℓ⟩ := exists_scalar_of_slPiConj_eq_one hK hq h1
  exact ⟨ℓ, hℓ⟩

theorem false_of_semiAct_cube_outer (hK : PiField π 2 f K) (hq : ModThree π (2 ^ f))
    (h : Res3Datum c g V U)
    (hc : c ∉ (MulAut.conj : slPi π 3 (2 ^ f) K →* MulAut (slPi π 3 (2 ^ f) K)).range)
    {y : GL (Fin 3) K} (hy : y ∈ glPi π 3 (2 ^ f) K) (hcy : KFacts.SemiAct c 1 y)
    {μ : Kˣ} (hμ : y ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) (μ ^ 3)) : False := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hπ : π = false → UnitaryFieldData 2 f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (2 ^ f) := fun h => by subst h; exact hq
  have hcs := KFacts.semiAct_one_iff.mp hcy
  have hys : y ∉ StatedScalars (Fin 3) K := by
    intro hs
    refine h.c_ne_one (MulEquiv.ext fun s => Subtype.ext ?_)
    rw [hcs, MulAut.one_apply, mul_inv_eq_iff_eq_mul]
    exact (commute_of_mem_statedScalars hs _).symm
  obtain ⟨y', ⟨z, hz, hy'⟩, g', hg', hD⟩ := exists_diag_normal_form hK hq hτ hτ1 hy hys hμ
  have hzs : z ∈ StatedScalars (Fin 3) K := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz
  have hcs' : ∀ s : slPi π 3 (2 ^ f) K,
      ((c s : slPi π 3 (2 ^ f) K) : GL (Fin 3) K) = y' * s * y'⁻¹ := fun s => by
    rw [hcs, hy']
    have hzc := commute_of_mem_statedScalars hzs (s : GL (Fin 3) K)
    calc (y : GL (Fin 3) K) * s * y⁻¹ = y * (s * z) * z⁻¹ * y⁻¹ := by group
      _ = y * (z * s) * z⁻¹ * y⁻¹ := by rw [hzc]
      _ = y * z * s * (y * z)⁻¹ := by group
  have hy'D : ∀ D : GL (Fin 3) K, g'⁻¹ * y' * g' = D → y' = g' * D * g'⁻¹ := fun D hDe => by
    rw [← hDe]
    group
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : slPi π 3 (2 ^ f) K,
      (j₀ : GL (Fin 3) K) = g' * diagTau hτ * g'⁻¹ :=
    ⟨⟨_, conj_diagTau_mem_slPi' hK hq hτ hg'⟩, rfl⟩
  rcases hD with hD | ⟨e, -, hD⟩
  · refine hc ⟨j₀, MulEquiv.ext fun s => Subtype.ext ?_⟩
    rw [MulAut.conj_apply, hcs', hy'D _ hD]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hj₀]
  · have hfix : c j₀ = j₀ := by
      apply Subtype.ext
      rw [hcs', hj₀, hy'D _ hD]
      calc g' * diagE e * g'⁻¹ * (g' * diagTau hτ * g'⁻¹) * (g' * diagE e * g'⁻¹)⁻¹
          = g' * (diagE e * diagTau hτ * (diagE e)⁻¹) * g'⁻¹ := by group
        _ = g' * (diagTau hτ * diagE e * (diagE e)⁻¹) * g'⁻¹ := by
          rw [diagE_mul_diagTau_comm e hτ]
        _ = g' * diagTau hτ * g'⁻¹ := by group
    have hj₀3 : j₀ ^ 3 = 1 := Subtype.ext (by
      show (j₀ : GL (Fin 3) K) ^ 3 = 1
      rw [hj₀, conj_pow, diagTau_pow_three hτ, mul_one, mul_inv_cancel])
    have hjz : j₀ ∉ Subgroup.center (slPi π 3 (2 ^ f) K) := by
      intro hcen
      have hsc : (j₀ : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K :=
        mem_statedScalars_of_commute hπ hq' hτ hτ1 fun s hs =>
          (congrArg Subtype.val (Subgroup.mem_center_iff.mp hcen ⟨s, hs⟩)).symm
      rw [hj₀] at hsc
      have h1 := commute_of_mem_statedScalars hsc g'⁻¹
      have h2 : diagTau hτ = g' * diagTau hτ * g'⁻¹ :=
        calc diagTau hτ = g'⁻¹ * (g' * diagTau hτ * g'⁻¹) * g' := by group
          _ = (g' * diagTau hτ * g'⁻¹) * g'⁻¹ * g' := by rw [h1]
          _ = g' * diagTau hτ * g'⁻¹ := by group
      rw [← h2] at hsc
      exact diagTau_notMem_statedScalars' hτ hτ1 hsc
    exact h.false_of_outer_threes_noncentral hc hfix hj₀3 hjz

theorem false_of_semiAct_noncube (hK : PiField π 2 f K) (hq : ModThree π (2 ^ f))
    (hq2 : 2 < 2 ^ f) (h : Res3Datum c g V U) {y : GL (Fin 3) K}
    (hy : y ∈ glPi π 3 (2 ^ f) K) (hcy : KFacts.SemiAct c 1 y) {ℓ : K}
    (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ) (hy3 : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1) : False := by
  have hVy : slPiConj hK ⟨y, hy⟩ ∈
      Subgroup.normalizer (V : Set (MulAut (slPi π 3 (2 ^ f) K))) := by
    rw [← slPiConj_eq_of_semiAct hK hy hcy]
    exact h.c_mem
  exact h.false_of_commutator_inf_eq_bot (commutator_le_range_slPiConj hK hq2)
    (inf_range_eq_bot_of_irreducible hK hq hy hℓ hy3 h.V_isPGroup hVy)

theorem false_of_semiAct_outer (hK : PiField π 2 f K) (hq : ModThree π (2 ^ f))
    (hq2 : 2 < 2 ^ f) (h : Res3Datum c g V U)
    (hc : c ∉ (MulAut.conj : slPi π 3 (2 ^ f) K →* MulAut (slPi π 3 (2 ^ f) K)).range)
    {y : GL (Fin 3) K} (hy : y ∈ glPi π 3 (2 ^ f) K) (hcy : KFacts.SemiAct c 1 y) : False := by
  obtain ⟨ℓ, hℓ⟩ := exists_semiAct_pow_three_scalar hK hq h hy hcy
  by_cases hcube : ∃ μ : K, μ ^ 3 = (ℓ : K)
  · obtain ⟨μ, hμ⟩ := hcube
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      exact ℓ.ne_zero (by rw [← hμ]; norm_num)
    refine false_of_semiAct_cube_outer hK hq h hc hy hcy (μ := Units.mk0 μ hμ0) ?_
    rw [hℓ]
    congr 1
    exact Units.ext (by simp [hμ])
  · refine false_of_semiAct_noncube hK hq hq2 h hy hcy (ℓ := (ℓ : K))
      (fun μ hμ => hcube ⟨μ, hμ⟩) ?_
    rw [← Units.val_pow_eq_pow_val, hℓ, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
