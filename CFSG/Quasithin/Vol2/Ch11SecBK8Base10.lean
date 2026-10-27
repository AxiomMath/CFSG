module

public import CFSG.Quasithin.Vol2.Ch11SecBK8Base9
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base4

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K8

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Assembly.LowTwoRank Matrix
open scoped Matrix

variable {K : Type} [Field K]

noncomputable abbrev dgSub (K : Type) [Field K] : Subgroup (MulAut (W6 K)) :=
  (matHom.comp (dgHom (K := K))).range

theorem matAut_dgHom_mem_dgSub (g : GL (Fin 3) K) : matAut (dgHom g) ∈ dgSub K := ⟨g, rfl⟩

theorem dgSub_le_linSub : dgSub K ≤ linSub := by
  rintro _ ⟨g, rfl⟩
  exact isSemilinear_matAut _

theorem tensHom_natEmb (A : GL (Fin 3) K) (M : GL (Fin 2) K) (a b : K) (u : StdMod (Fin 3) K) :
    matAut (tensHom (A, M)) (natEmb a b u) =
      natEmb ((M : Matrix (Fin 2) (Fin 2) K) 0 0 * a + (M : Matrix (Fin 2) (Fin 2) K) 0 1 * b)
        ((M : Matrix (Fin 2) (Fin 2) K) 1 0 * a + (M : Matrix (Fin 2) (Fin 2) K) 1 1 * b)
        (matAut A u) := by
  apply Multiplicative.toAdd.injective
  change tensMat (A : Matrix (Fin 3) (Fin 3) K) (M : Matrix (Fin 2) (Fin 2) K) *ᵥ
    natVec a b (Multiplicative.toAdd u) = natVec _ _ ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ
      Multiplicative.toAdd u)
  rw [tensMat_mulVec, natVec_inl, natVec_inr]
  funext i
  rcases i with i | i <;> simp [natVec, Matrix.mulVec_smul, add_mul, mul_assoc]

theorem map_natSub_tensHom (A : GL (Fin 3) K) (M : GL (Fin 2) K) (a b : K) :
    (natSub a b).map (matAut (tensHom (A, M))).toMonoidHom =
      natSub ((M : Matrix (Fin 2) (Fin 2) K) 0 0 * a + (M : Matrix (Fin 2) (Fin 2) K) 0 1 * b)
        ((M : Matrix (Fin 2) (Fin 2) K) 1 0 * a + (M : Matrix (Fin 2) (Fin 2) K) 1 1 * b) := by
  apply le_antisymm
  · rintro _ ⟨y, ⟨u, rfl⟩, rfl⟩
    exact ⟨matAut A u, (tensHom_natEmb A M a b u).symm⟩
  · rintro _ ⟨w, rfl⟩
    refine ⟨natEmb a b ((matAut A).symm w), ⟨_, rfl⟩, ?_⟩
    change matAut (tensHom (A, M)) (natEmb a b ((matAut A).symm w)) = _
    rw [tensHom_natEmb, MulEquiv.apply_symm_apply]

theorem exists_tensHom [Finite K] {x : MulAut (W6 K)} (hx : x ∈ normD K) (hlin : x ∈ linSub) :
    ∃ (A : GL (Fin 3) K) (M : GL (Fin 2) K), x = matAut (tensHom (A, M)) := by
  obtain ⟨σ, Φ, M, hΦ, hxf⟩ := exists_semilinear_tens hx
  have hσ : σ = RingEquiv.refl K := (isSemilinear_of_tens hΦ hxf).unique (mem_linSub.mp hlin)
  subst hσ
  obtain ⟨A₀, rfl⟩ := exists_matAut_of_mem_linSub (show Φ ∈ linSub from hΦ)
  have hM : M.det ≠ 0 := by
    intro hdet
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have h0 : toAddMap x (natVec (v 0) (v 1) (Pi.single 0 1)) = 0 := by
      rw [hxf]
      have e0 : M 0 0 * v 0 + M 0 1 * v 1 = 0 := by
        have := congrFun hMv 0
        simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
      have e1 : M 1 0 * v 0 + M 1 1 * v 1 = 0 := by
        have := congrFun hMv 1
        simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
      funext i
      rcases i with i | i
      · simp only [natVec_inl, natVec_inr, smul_smul, ← add_smul, e0, zero_smul, Sum.elim_inl,
          toAddMap_matAut, Matrix.mulVec_zero, Pi.zero_apply]
      · simp only [natVec_inl, natVec_inr, smul_smul, ← add_smul, e1, zero_smul, Sum.elim_inr,
          toAddMap_matAut, Matrix.mulVec_zero, Pi.zero_apply]
    rw [toAddMap_eq_zero_iff] at h0
    apply hv
    funext j
    have h1 := congrFun h0 (Sum.inl 0)
    have h2 := congrFun h0 (Sum.inr 0)
    simp only [natVec, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one, Pi.zero_apply] at h1 h2
    fin_cases j
    · exact h1
    · exact h2
  have hMc : ((Matrix.GeneralLinearGroup.mkOfDetNeZero M hM : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = M := rfl
  refine ⟨A₀, Matrix.GeneralLinearGroup.mkOfDetNeZero M hM, toAddMap_injective fun v => ?_⟩
  rw [hxf v, toAddMap_matAut (tensHom _) v, coe_tensHom, tensMat_mulVec, hMc]
  funext i
  rcases i with i | i <;> simp [toAddMap_matAut, Matrix.mulVec_add, Matrix.mulVec_smul]

theorem eq_of_tensMat_eq_one {A : GL (Fin 3) K} {M : Matrix (Fin 2) (Fin 2) K}
    (h : tensMat (A : Matrix (Fin 3) (Fin 3) K) M = 1) : M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 0 0 = M 1 1 := by
  set u : Fin 3 → K := ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1 with hu
  have hAu : (A : Matrix (Fin 3) (Fin 3) K) *ᵥ u = Pi.single 0 1 := by
    rw [hu, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  have hv : ∀ v : I6 → K, tensMat (A : Matrix (Fin 3) (Fin 3) K) M *ᵥ v = v := fun v => by
    rw [h, Matrix.one_mulVec]
  have h1 := hv (Sum.elim u 0)
  have h2 := hv (Sum.elim 0 u)
  rw [tensMat_mulVec] at h1 h2
  have a1 := congrFun h1 (Sum.inl 0)
  have a2 := congrFun h1 (Sum.inr 0)
  have a3 := congrFun h2 (Sum.inl 0)
  have a4 := congrFun h2 (Sum.inr 0)
  simp only [Sum.elim_inl, Sum.elim_inr, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_zero,
    smul_zero, add_zero, zero_add, Pi.smul_apply, hAu, Pi.single_eq_same, smul_eq_mul,
    mul_one, Pi.zero_apply] at a1 a2 a3 a4
  exact ⟨a3, a2, a1.trans a4.symm⟩

theorem mem_dgSub_of_scalar (A : GL (Fin 3) K) (M : GL (Fin 2) K)
    (h01 : (M : Matrix (Fin 2) (Fin 2) K) 0 1 = 0) (h10 : (M : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h : (M : Matrix (Fin 2) (Fin 2) K) 0 0 = (M : Matrix (Fin 2) (Fin 2) K) 1 1) :
    matAut (tensHom (A, M)) ∈ dgSub K := by
  obtain ⟨g, hg⟩ := exists_dg_of_scalar (x := matAut (tensHom (A, M))) (A₀ := A)
    (β := (M : Matrix (Fin 2) (Fin 2) K) 0 0) fun v => by
      rw [toAddMap_matAut, coe_tensHom, tensMat_mulVec, h01, h10, ← h]
      funext i
      rcases i with i | i <;> simp [Matrix.mulVec_smul]
  rw [hg]
  exact matAut_dgHom_mem_dgSub g

theorem diag_eq_of_sq [CharP K 2] {A : GL (Fin 3) K} {M : GL (Fin 2) K}
    (h : matAut (tensHom (A, M)) * matAut (tensHom (A, M)) = 1) :
    (M : Matrix (Fin 2) (Fin 2) K) 0 0 = (M : Matrix (Fin 2) (Fin 2) K) 1 1 := by
  have h1 : tensHom ((A, M) * (A, M)) = 1 := by
    apply matHom_injective
    rw [map_mul, map_mul, map_one, matHom_apply, h]
  have h2 := (eq_of_tensMat_eq_one (A := A * A)
    (M := ((M * M : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) (congrArg Units.val h1)).2.2
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] at h2
  have h3 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h4 : ((M : Matrix (Fin 2) (Fin 2) K) 0 0 + (M : Matrix (Fin 2) (Fin 2) K) 1 1) *
      ((M : Matrix (Fin 2) (Fin 2) K) 0 0 + (M : Matrix (Fin 2) (Fin 2) K) 1 1) = 0 := by
    linear_combination h2 + ((M : Matrix (Fin 2) (Fin 2) K) 1 1 *
      (M : Matrix (Fin 2) (Fin 2) K) 1 1 + (M : Matrix (Fin 2) (Fin 2) K) 0 0 *
        (M : Matrix (Fin 2) (Fin 2) K) 1 1) * h3
  have h5 := mul_self_eq_zero.mp h4
  linear_combination h5 - (M : Matrix (Fin 2) (Fin 2) K) 1 1 * h3

theorem eq_zero_of_two_eigen [CharP K 2] {m β γ a b a' b' s s' : K}
    (hD : a * b' - a' * b ≠ 0) (h1 : m * a + β * b = s * a) (h2 : γ * a + m * b = s * b)
    (h3 : m * a' + β * b' = s' * a') (h4 : γ * a' + m * b' = s' * b') : β = 0 ∧ γ = 0 := by
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have key : ∀ {x y t : K}, (x ≠ 0 ∨ y ≠ 0) → m * x + β * y = t * x → γ * x + m * y = t * y →
      (t - m) * (t - m) = β * γ := by
    intro x y t hxy e1 e2
    rcases hxy with hx | hy
    · refine mul_right_cancel₀ hx ?_
      linear_combination (m - t) * e1 - β * e2
    · refine mul_right_cancel₀ hy ?_
      linear_combination (m - t) * e2 - γ * e1
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    apply hD
    rw [h.1, h.2]
    ring
  have hab' : a' ≠ 0 ∨ b' ≠ 0 := by
    by_contra h
    push Not at h
    apply hD
    rw [h.1, h.2]
    ring
  have k1 := key hab h1 h2
  have k2 := key hab' h3 h4
  have hss : (s - s') * (s - s') = 0 := by
    linear_combination k1 - k2 + (s' * s' - s * s' + s * m - s' * m) * h2K
  have hs := sub_eq_zero.mp (mul_self_eq_zero.mp hss)
  subst hs
  constructor
  · refine mul_right_cancel₀ hD ?_
    linear_combination a * h3 - a' * h1
  · refine mul_right_cancel₀ hD ?_
    linear_combination b' * h2 - b * h4

theorem ptDet_ne_zero {p p' : Option K} (h : p ≠ p') : ptA p * ptB p' - ptA p' * ptB p ≠ 0 := by
  cases p with
  | none =>
    cases p' with
    | none => exact absurd rfl h
    | some c => simp [ptA, ptB]
  | some c =>
    cases p' with
    | none => simp [ptA, ptB]
    | some c' =>
      simp only [ptA, ptB, one_mul]
      intro h0
      exact h (by rw [sub_eq_zero.mp h0])

theorem mem_dgSub_of_two_fixed [Finite K] [CharP K 2] {A : GL (Fin 3) K} {M : GL (Fin 2) K}
    (hx : matAut (tensHom (A, M)) ∈ normD K)
    (h : matAut (tensHom (A, M)) * matAut (tensHom (A, M)) = 1) {p p' : Option K} (hpp : p ≠ p')
    (hp : act ⟨_, hx⟩ p = p) (hp' : act ⟨_, hx⟩ p' = p') : matAut (tensHom (A, M)) ∈ dgSub K := by
  rw [act_eq_iff] at hp hp'
  unfold natPt at hp hp'
  rw [map_natSub_tensHom] at hp hp'
  obtain ⟨s, e1, e2⟩ := exists_smul_of_natSub_eq hp
  obtain ⟨s', e3, e4⟩ := exists_smul_of_natSub_eq hp'
  have hd := diag_eq_of_sq h
  rw [← hd] at e2 e4
  obtain ⟨h01, h10⟩ := eq_zero_of_two_eigen (ptDet_ne_zero hpp) e1 e2 e3 e4
  exact mem_dgSub_of_scalar A M h01 h10 hd

end CFSG.Quasithin.Vol2.Ch11.SecB.K8
