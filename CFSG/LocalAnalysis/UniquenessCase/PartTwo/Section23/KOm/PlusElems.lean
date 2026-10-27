module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.OmegaPlusFour
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

open CFSG.Open Matrix

open scoped Pointwise commutatorElement

local notation "ιP" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

private lemma quadPlus_coord (v : ιP → K) :
    StatedQuadPlus 2 K v = v (Sum.inl 0) * v (Sum.inr 0) + v (Sum.inl 1) * v (Sum.inr 1) := by
  simp [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Fin.sum_univ_two]

private lemma quadPlus_diagonal_mulVec (f v : ιP → K)
    (h0 : f (Sum.inl 0) * f (Sum.inr 0) = 1)
    (h1 : f (Sum.inl 1) * f (Sum.inr 1) = 1) :
    StatedQuadPlus 2 K (Matrix.diagonal f *ᵥ v) = StatedQuadPlus 2 K v := by
  rw [quadPlus_coord, quadPlus_coord]
  simp only [Matrix.mulVec_diagonal]
  rw [show f (Sum.inl 0) * v (Sum.inl 0) * (f (Sum.inr 0) * v (Sum.inr 0)) =
      f (Sum.inl 0) * f (Sum.inr 0) * (v (Sum.inl 0) * v (Sum.inr 0)) by ring,
    show f (Sum.inl 1) * v (Sum.inl 1) * (f (Sum.inr 1) * v (Sum.inr 1)) =
      f (Sum.inl 1) * f (Sum.inr 1) * (v (Sum.inl 1) * v (Sum.inr 1)) by ring,
    h0, h1, one_mul, one_mul]

private lemma mem_isometryCore_of (g : GL ιP K)
    (hg : ∀ v, StatedQuadPlus 2 K ((g : Matrix ιP ιP K) *ᵥ v) = StatedQuadPlus 2 K v) :
    g ∈ CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 K) :=
  Subgroup.subset_closure hg

private lemma permutationGL_mulVec (π : Equiv.Perm ιP) (v : ιP → K) :
    (TauCeti.permutationGL (k := K) π : Matrix ιP ιP K) *ᵥ v = v ∘ ⇑π⁻¹ := by
  rw [TauCeti.permutationGL_coe, Matrix.permMatrix_mulVec]

private def s0P : Equiv.Perm ιP := Equiv.swap (Sum.inl 0) (Sum.inr 0)

private def s1P : Equiv.Perm ιP := Equiv.swap (Sum.inl 1) (Sum.inr 1)

private def sgP : Equiv.Perm ιP :=
  Equiv.swap (Sum.inl 0) (Sum.inl 1) * Equiv.swap (Sum.inr 0) (Sum.inr 1)

private lemma s0GL_mem :
    TauCeti.permutationGL (k := K) s0P ∈ CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 K) := by
  refine mem_isometryCore_of _ fun v => ?_
  rw [permutationGL_mulVec, quadPlus_coord, quadPlus_coord]
  have e0 : s0P⁻¹ (Sum.inl 0) = Sum.inr 0 := by decide
  have e1 : s0P⁻¹ (Sum.inr 0) = Sum.inl 0 := by decide
  have e2 : s0P⁻¹ (Sum.inl 1) = Sum.inl 1 := by decide
  have e3 : s0P⁻¹ (Sum.inr 1) = Sum.inr 1 := by decide
  simp only [Function.comp_apply, e0, e1, e2, e3]
  ring

private lemma s1GL_mem :
    TauCeti.permutationGL (k := K) s1P ∈ CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 K) := by
  refine mem_isometryCore_of _ fun v => ?_
  rw [permutationGL_mulVec, quadPlus_coord, quadPlus_coord]
  have e0 : s1P⁻¹ (Sum.inl 0) = Sum.inl 0 := by decide
  have e1 : s1P⁻¹ (Sum.inr 0) = Sum.inr 0 := by decide
  have e2 : s1P⁻¹ (Sum.inl 1) = Sum.inr 1 := by decide
  have e3 : s1P⁻¹ (Sum.inr 1) = Sum.inl 1 := by decide
  simp only [Function.comp_apply, e0, e1, e2, e3]
  ring

private lemma sgGL_mem :
    TauCeti.permutationGL (k := K) sgP ∈ CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 K) := by
  refine mem_isometryCore_of _ fun v => ?_
  rw [permutationGL_mulVec, quadPlus_coord, quadPlus_coord]
  have e0 : sgP⁻¹ (Sum.inl 0) = Sum.inl 1 := by decide
  have e1 : sgP⁻¹ (Sum.inr 0) = Sum.inr 1 := by decide
  have e2 : sgP⁻¹ (Sum.inl 1) = Sum.inl 0 := by decide
  have e3 : sgP⁻¹ (Sum.inr 1) = Sum.inr 0 := by decide
  simp only [Function.comp_apply, e0, e1, e2, e3]
  ring

private def dgVec (α β : Kˣ) : ιP → Kˣ :=
  Sum.elim ![α, β] ![α⁻¹, β⁻¹]

private noncomputable def dg (α β : Kˣ) : GL ιP K := TauCeti.diagGL (dgVec α β)

private noncomputable def dgHom : Kˣ × Kˣ →* GL ιP K where
  toFun p := dg p.1 p.2
  map_one' := by
    simp only [dg]
    change TauCeti.diagGL (dgVec (1 : Kˣ) (1 : Kˣ)) = 1
    have h : dgVec (1 : Kˣ) 1 = 1 := by
      funext i
      rcases i with i | i <;> fin_cases i <;> simp [dgVec]
    rw [h]
    exact map_one _
  map_mul' p q := by
    simp only [dg]
    rw [← map_mul]
    congr 1
    funext i
    rcases i with i | i <;> fin_cases i <;> simp [dgVec, mul_inv, mul_comm]

private lemma dg_mul (α β γ δ : Kˣ) : dg α β * dg γ δ = dg (α * γ) (β * δ) := by
  simpa [dgHom] using (map_mul dgHom (α, β) (γ, δ)).symm

private lemma dg_pow (α β : Kˣ) (n : ℕ) : dg α β ^ n = dg (α ^ n) (β ^ n) := by
  simpa [dgHom] using (map_pow dgHom (α, β) n).symm

private lemma dg_one : dg (1 : Kˣ) 1 = 1 := by
  simpa [dgHom] using map_one dgHom

private lemma dg_mem_isometryCore (α β : Kˣ) :
    dg α β ∈ CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 K) := by
  refine mem_isometryCore_of _ fun v => ?_
  have hmat : (dg α β : Matrix ιP ιP K) =
      Matrix.diagonal (fun i => (dgVec α β i : K)) :=
    TauCeti.diagGL_coe (dgVec α β)
  rw [hmat]
  exact quadPlus_diagonal_mulVec _ v (by simp [dgVec]) (by simp [dgVec])

private lemma dgVec_comp_s0 (α β : Kˣ) : dgVec α β ∘ ⇑s0P⁻¹ = dgVec α⁻¹ β := by
  have e0 : (Equiv.symm s0P) (Sum.inl 0) = Sum.inr 0 := by decide
  have e1 : (Equiv.symm s0P) (Sum.inr 0) = Sum.inl 0 := by decide
  have e2 : (Equiv.symm s0P) (Sum.inl 1) = Sum.inl 1 := by decide
  have e3 : (Equiv.symm s0P) (Sum.inr 1) = Sum.inr 1 := by decide
  funext i
  rcases i with i | i <;> fin_cases i <;> simp [dgVec, e0, e1, e2, e3]

private lemma dgVec_comp_s1 (α β : Kˣ) : dgVec α β ∘ ⇑s1P⁻¹ = dgVec α β⁻¹ := by
  have e0 : (Equiv.symm s1P) (Sum.inl 0) = Sum.inl 0 := by decide
  have e1 : (Equiv.symm s1P) (Sum.inr 0) = Sum.inr 0 := by decide
  have e2 : (Equiv.symm s1P) (Sum.inl 1) = Sum.inr 1 := by decide
  have e3 : (Equiv.symm s1P) (Sum.inr 1) = Sum.inl 1 := by decide
  funext i
  rcases i with i | i <;> fin_cases i <;> simp [dgVec, e0, e1, e2, e3]

private lemma dgVec_comp_w (α β : Kˣ) :
    dgVec α β ∘ ⇑(s0P * s1P)⁻¹ = dgVec α⁻¹ β⁻¹ := by
  rw [_root_.mul_inv_rev, Equiv.Perm.coe_mul, ← Function.comp_assoc, dgVec_comp_s1,
    dgVec_comp_s0]

private lemma conj_permutationGL_dg (π : Equiv.Perm ιP) (α β : Kˣ)
    (hπ : dgVec α β ∘ ⇑π⁻¹ = dgVec α⁻¹ β⁻¹) :
    TauCeti.permutationGL (k := K) π * dg α β * (TauCeti.permutationGL (k := K) π)⁻¹
      = (dg α β)⁻¹ := by
  have h := TauCeti.mul_diagGL_of_coe_eq_permMatrix (TauCeti.permutationGL (k := K) π) π⁻¹
    (TauCeti.permutationGL_coe π) (dgVec α β)
  rw [hπ] at h
  calc TauCeti.permutationGL (k := K) π * dg α β * (TauCeti.permutationGL (k := K) π)⁻¹
      = TauCeti.permutationGL (k := K) π * TauCeti.diagGL (dgVec α β) *
          (TauCeti.permutationGL (k := K) π)⁻¹ := by simp only [dg]
    _ = TauCeti.diagGL (dgVec α⁻¹ β⁻¹) * TauCeti.permutationGL (k := K) π *
          (TauCeti.permutationGL (k := K) π)⁻¹ := by rw [h]
    _ = TauCeti.diagGL (dgVec α⁻¹ β⁻¹) := by rw [mul_assoc, mul_inv_cancel, mul_one]
    _ = (dg α β)⁻¹ := by
        simp only [dg]
        exact map_inv dgHom (α, β)

private lemma commutator_dg_s0 (μ : Kˣ) :
    ⁅dg μ 1, TauCeti.permutationGL (k := K) s0P⁆ = dg (μ ^ 2) 1 := by
  have hconj : TauCeti.permutationGL (k := K) s0P * dg μ 1 *
      (TauCeti.permutationGL (k := K) s0P)⁻¹ = (dg μ 1)⁻¹ :=
    conj_permutationGL_dg s0P μ 1 (dgVec_comp_s0 μ 1)
  have h2 : TauCeti.permutationGL (k := K) s0P * (dg μ 1)⁻¹ *
      (TauCeti.permutationGL (k := K) s0P)⁻¹ = dg μ 1 := by
    have := congrArg Inv.inv hconj
    simpa [mul_assoc] using this
  rw [commutatorElement_def]
  rw [show dg μ 1 * TauCeti.permutationGL (k := K) s0P * (dg μ 1)⁻¹ *
      (TauCeti.permutationGL (k := K) s0P)⁻¹ =
      dg μ 1 * (TauCeti.permutationGL (k := K) s0P * (dg μ 1)⁻¹ *
        (TauCeti.permutationGL (k := K) s0P)⁻¹) by group,
    h2, dg_mul]
  simp [pow_two]

private lemma commutator_dg_s1 (μ : Kˣ) :
    ⁅dg 1 μ, TauCeti.permutationGL (k := K) s1P⁆ = dg 1 (μ ^ 2) := by
  have hconj : TauCeti.permutationGL (k := K) s1P * dg 1 μ *
      (TauCeti.permutationGL (k := K) s1P)⁻¹ = (dg 1 μ)⁻¹ :=
    conj_permutationGL_dg s1P 1 μ (dgVec_comp_s1 1 μ)
  have h2 : TauCeti.permutationGL (k := K) s1P * (dg 1 μ)⁻¹ *
      (TauCeti.permutationGL (k := K) s1P)⁻¹ = dg 1 μ := by
    have := congrArg Inv.inv hconj
    simpa [mul_assoc] using this
  rw [commutatorElement_def]
  rw [show dg 1 μ * TauCeti.permutationGL (k := K) s1P * (dg 1 μ)⁻¹ *
      (TauCeti.permutationGL (k := K) s1P)⁻¹ =
      dg 1 μ * (TauCeti.permutationGL (k := K) s1P * (dg 1 μ)⁻¹ *
        (TauCeti.permutationGL (k := K) s1P)⁻¹) by group,
    h2, dg_mul]
  simp [pow_two]

private lemma commutator_s0_sg :
    ⁅TauCeti.permutationGL (k := K) s0P, TauCeti.permutationGL (k := K) sgP⁆ =
      TauCeti.permutationGL (k := K) (s0P * s1P) := by
  rw [commutatorElement_def, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
  congr 1
  decide

private lemma dg_mulVec_e1 (α β : Kˣ) :
    (dg α β : Matrix ιP ιP K) *ᵥ KTabC.e1P K = (α : K) • KTabC.e1P K := by
  have hmat : (dg α β : Matrix ιP ιP K) =
      Matrix.diagonal (fun i => (dgVec α β i : K)) :=
    TauCeti.diagGL_coe (dgVec α β)
  rw [hmat]
  funext i
  rw [Matrix.mulVec_diagonal]
  rcases i with i | i <;> fin_cases i <;> simp [KTabC.e1P, dgVec, Pi.single]

private lemma permutationGL_mulVec_e1 (π : Equiv.Perm ιP) :
    (TauCeti.permutationGL (k := K) π : Matrix ιP ιP K) *ᵥ KTabC.e1P K =
      Pi.single (π (Sum.inl 0)) 1 := by
  rw [TauCeti.permutationGL_coe, Matrix.permMatrix_mulVec, KTabC.e1P]
  funext i
  by_cases hi : i = π (Sum.inl 0)
  · subst hi
    simp
  · have hne : (Equiv.symm π) i ≠ Sum.inl 0 := by
      intro h
      exact hi ((Equiv.apply_symm_apply π i).symm.trans (congrArg π h))
    simp [Function.comp_apply, Pi.single, hi, hne]

theorem exists_torus_weyl [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ Nat.card K - 1 ∧
      ∃ a ∈ StatedOmega (StatedQuadPlus 2 K), ∃ b ∈ StatedOmega (StatedQuadPlus 2 K),
      ∃ w ∈ StatedOmega (StatedQuadPlus 2 K),
        orderOf a = r ∧ orderOf b = r ∧ a * b = b * a ∧
        (a : Matrix ιP ιP K) *ᵥ KTabC.e1P K = KTabC.e1P K ∧
        (∃ ν : K, ν ≠ 1 ∧ (b : Matrix ιP ιP K) *ᵥ KTabC.e1P K = ν • KTabC.e1P K) ∧
        w * w = 1 ∧ w * a * w⁻¹ = a⁻¹ ∧ w * b * w⁻¹ = b⁻¹ ∧
        ∀ c : K, (w : Matrix ιP ιP K) *ᵥ KTabC.e1P K ≠ c • KTabC.e1P K := by
  have hqne : Nat.card K - 1 ≠ 1 := by omega
  obtain ⟨r, hrprime, hrdvd⟩ := Nat.exists_prime_and_dvd hqne
  haveI : Fact r.Prime := ⟨hrprime⟩
  have hcard_units : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
  obtain ⟨lam, hlam⟩ := exists_prime_orderOf_dvd_card' r (by rw [hcard_units]; exact hrdvd)
  have hlam_ne_one : lam ≠ 1 := by
    intro h
    rw [h] at hlam
    exact hrprime.ne_one (by simpa using hlam.symm)
  have hrne2 : r ≠ 2 := by
    intro h2
    have hord2 : orderOf lam = 2 := by rw [hlam, h2]
    have hlam2 : lam ^ 2 = 1 := by rw [← hord2]; exact pow_orderOf_eq_one lam
    have hsq : (lam : K) ^ 2 = (1 : K) ^ 2 := by
      simpa using congrArg (fun u : Kˣ => (u : K)) hlam2
    exact hlam_ne_one (Units.val_eq_one.mp (CharTwo.sq_inj.mp hsq))
  obtain ⟨μ, hμ⟩ : ∃ μ : K, μ ^ 2 = (lam : K) := by
    obtain ⟨c, hc⟩ := isSquare_of_charTwo' (R := K) (lam : K)
    exact ⟨c, by rw [pow_two, hc]⟩
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hμ
    exact lam.ne_zero hμ.symm
  let μu : Kˣ := Units.mk0 μ hμ0
  have hμu : μu ^ 2 = lam := by
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0]
    exact hμ
  have ha_mem : dg 1 lam ∈ StatedOmega (StatedQuadPlus 2 K) := by
    rw [← hμu, ← commutator_dg_s1 μu]
    exact Subgroup.commutator_mem_commutator (dg_mem_isometryCore (1 : Kˣ) μu) s1GL_mem
  have hb_mem : dg lam 1 ∈ StatedOmega (StatedQuadPlus 2 K) := by
    rw [← hμu, ← commutator_dg_s0 μu]
    exact Subgroup.commutator_mem_commutator (dg_mem_isometryCore μu 1) s0GL_mem
  have hw_mem : TauCeti.permutationGL (k := K) (s0P * s1P) ∈
      StatedOmega (StatedQuadPlus 2 K) := by
    rw [← commutator_s0_sg]
    exact Subgroup.commutator_mem_commutator s0GL_mem sgGL_mem
  have hlamr : lam ^ r = 1 := by rw [← hlam]; exact pow_orderOf_eq_one lam
  have ha_pow : dg 1 lam ^ r = 1 := by rw [dg_pow, hlamr, one_pow, dg_one]
  have ha_ne : dg 1 lam ≠ 1 := by
    intro h
    have hd : dgVec (1 : Kˣ) lam = dgVec (1 : Kˣ) 1 := by
      apply TauCeti.diagGL_injective
      change dg 1 lam = dg 1 1
      rw [h, dg_one]
    have hval : lam = 1 := by
      simpa [dgVec] using congrFun hd (Sum.inl 1)
    exact hlam_ne_one hval
  have ha_ord : orderOf (dg 1 lam) = r := orderOf_eq_prime ha_pow ha_ne
  have hb_pow : dg lam 1 ^ r = 1 := by rw [dg_pow, hlamr, one_pow, dg_one]
  have hb_ne : dg lam 1 ≠ 1 := by
    intro h
    have hd : dgVec lam 1 = dgVec (1 : Kˣ) 1 := by
      apply TauCeti.diagGL_injective
      change dg lam 1 = dg 1 1
      rw [h, dg_one]
    have hval : lam = 1 := by
      simpa [dgVec] using congrFun hd (Sum.inl 0)
    exact hlam_ne_one hval
  have hb_ord : orderOf (dg lam 1) = r := orderOf_eq_prime hb_pow hb_ne
  have hab : dg 1 lam * dg lam 1 = dg lam 1 * dg 1 lam := by
    rw [dg_mul, dg_mul]
    simp [mul_comm]
  have ha_e1 : (dg 1 lam : Matrix ιP ιP K) *ᵥ KTabC.e1P K = KTabC.e1P K := by
    rw [dg_mulVec_e1]
    simp
  have hb_e1 : ∃ ν : K, ν ≠ 1 ∧
      (dg lam 1 : Matrix ιP ιP K) *ᵥ KTabC.e1P K = ν • KTabC.e1P K :=
    ⟨(lam : K), fun h => hlam_ne_one (Units.val_eq_one.mp h), dg_mulVec_e1 lam 1⟩
  have hww : TauCeti.permutationGL (k := K) (s0P * s1P) *
      TauCeti.permutationGL (k := K) (s0P * s1P) = 1 := by
    rw [← map_mul]
    have h : (s0P * s1P) * (s0P * s1P) = 1 := by decide
    rw [h, map_one]
  have hwa : TauCeti.permutationGL (k := K) (s0P * s1P) * dg 1 lam *
      (TauCeti.permutationGL (k := K) (s0P * s1P))⁻¹ = (dg 1 lam)⁻¹ :=
    conj_permutationGL_dg (s0P * s1P) 1 lam (dgVec_comp_w 1 lam)
  have hwb : TauCeti.permutationGL (k := K) (s0P * s1P) * dg lam 1 *
      (TauCeti.permutationGL (k := K) (s0P * s1P))⁻¹ = (dg lam 1)⁻¹ :=
    conj_permutationGL_dg (s0P * s1P) lam 1 (dgVec_comp_w lam 1)
  have hw_e1 : ∀ c : K, (TauCeti.permutationGL (k := K) (s0P * s1P) :
      Matrix ιP ιP K) *ᵥ KTabC.e1P K ≠ c • KTabC.e1P K := by
    intro c
    rw [permutationGL_mulVec_e1]
    have h : (s0P * s1P) (Sum.inl 0) = Sum.inr 0 := by decide
    rw [h]
    intro hc
    have h1 := congrFun hc (Sum.inr 0)
    have h0 : c = 0 := by
      have := congrFun hc (Sum.inl 0)
      simpa [KTabC.e1P, Pi.single] using this.symm
    simp [KTabC.e1P, Pi.single, h0] at h1
  exact ⟨r, hrprime, hrne2, hrdvd, dg 1 lam, ha_mem, dg lam 1, hb_mem,
    TauCeti.permutationGL (k := K) (s0P * s1P), hw_mem, ha_ord, hb_ord, hab,
    ha_e1, hb_e1, hww, hwa, hwb, hw_e1⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

end
