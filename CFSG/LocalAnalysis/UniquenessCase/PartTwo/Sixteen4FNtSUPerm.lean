module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtSUTorus
public import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

open scoped Matrix

theorem s16nt_su_perm_mem {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    {n : ℕ} (π : Equiv.Perm (Fin n)) :
    ∃ p ∈ s16ntSuMono K n, ∀ v : Fin n → K, p • v = v ∘ π := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  let P : Matrix (Fin n) (Fin n) K := π.permMatrix K
  have hPmulVec : ∀ v : Fin n → K, P *ᵥ v = v ∘ π :=
    fun v => Matrix.permMatrix_mulVec (σ := π) (v := v)
  have hPdet : P.det = 1 := by
    rw [show P = π.permMatrix K from rfl, Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h
    · rw [h]; simp
    · rw [h]; simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
        CharTwo.neg_eq]
  have hPiso : ∀ x y : Fin n → K,
      herm (s16ntSuSigma K) (P *ᵥ x) (P *ᵥ y) = herm (s16ntSuSigma K) x y := by
    intro x y
    rw [hPmulVec x, hPmulVec y, herm, herm]
    exact Equiv.sum_comp π (fun i => s16ntSuSigma K (x i) * y i)
  let p : ↥(SUid (s16ntSuSigma K) n) := mkSU (s16ntSuSigma K) P hPdet hPiso
  have hp_smul : ∀ v : Fin n → K, p • v = v ∘ π := by
    intro v
    rw [show p • v = P *ᵥ v from mkSU_smul (s16ntSuSigma K) P hPdet hPiso v]
    exact hPmulVec v
  refine ⟨p, ?_, hp_smul⟩
  change p ∈ Subgroup.normalizer (s16ntSuTorus K n : Set ↥(SUid (s16ntSuSigma K) n))
  refine Subgroup.mem_normalizer_fintype (fun t ht => ?_)
  have htH : t.1 ∈ (CFSG.ClassicalGroups.SUnThreeLocal.diagGL K n).range := by
    have h : t ∈ (CFSG.ClassicalGroups.SUnThreeLocal.diagGL K n).range.subgroupOf
        (SUid (s16ntSuSigma K) n) := ht
    exact Subgroup.mem_subgroupOf.mp h
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp htH
  have htv : ∀ v : Fin n → K, t • v = fun i => (u i : K) * v i := by
    intro v
    have htu : ((t.1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        Matrix.diagonal fun i => (u i : K) := by
      rw [← hu, CFSG.ClassicalGroups.SUnThreeLocal.coe_diagGL]
    rw [smul_def, htu]
    funext i
    exact Matrix.mulVec_diagonal _ _ _
  have hu_prod : ∏ i, u i = 1 := by
    apply Units.ext
    rw [Units.coe_prod, Units.val_one, ← CFSG.ClassicalGroups.SUnThreeLocal.det_diagGL u,
      hu]
    exact ((mem_SUid_iff (s16ntSuSigma K)).mp t.2).1
  have hp_inv_smul : ∀ v : Fin n → K, p⁻¹ • v = v ∘ π.symm := by
    intro v
    have h := hp_smul (p⁻¹ • v)
    rw [smul_inv_smul] at h
    funext i
    simpa using (congrFun h (π.symm i)).symm
  have hconj : ∀ v : Fin n → K,
      (p * t * p⁻¹) • v = fun i => (u (π i) : K) * v i := by
    intro v
    rw [mul_smul, mul_smul, htv, hp_inv_smul, hp_smul]
    funext i
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
  obtain ⟨d, hdT, hdv⟩ := s16nt_su_diag_mem hK (fun i => u (π i)) (by
    rw [Equiv.prod_comp π u]; exact hu_prod)
  have hpd : p * t * p⁻¹ = d :=
    ext_smul (s16ntSuSigma K) (fun v => by rw [hconj v, hdv v])
  rw [hpd]
  exact hdT

theorem s16nt_su_exists_s {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    {n : ℕ} (hn : 4 ≤ n) :
    ∃ s : SUid (s16ntSuSigma K) n,
      (∀ v : Fin n → K,
        s • v = v + herm (s16ntSuSigma K) (s16ntSuV0 n K) v • s16ntSuV0 n K) ∧
      ∀ (g : SUid (s16ntSuSigma K) n) (l : K),
        g • s16ntSuV0 n K = l • s16ntSuV0 n K → g * s = s * g := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hσ : ∀ c : K, s16ntSuSigma K (s16ntSuSigma K c) = c :=
    (isUnitaryInvolution_unitaryInvolution (K := K) (p := 2) (f := 1)
      (by rw [hK]; norm_num)).invol
  have hv0self : herm (s16ntSuSigma K) (s16ntSuV0 n K) (s16ntSuV0 n K) = 0 := by
    rw [herm]
    have hterm : ∀ i : Fin n,
        s16ntSuSigma K (s16ntSuV0 n K i) * s16ntSuV0 n K i =
          if i.val < 4 then (1 : K) else 0 := by
      intro i
      rw [s16ntSuV0]
      split_ifs with hi <;> simp
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_boole,
      Fin.card_filter_val_lt, min_eq_right hn, CharP.cast_eq_zero_iff K 2 4]
    norm_num
  have hc : (1 : K) + s16ntSuSigma K 1 = 0 := by
    rw [map_one]
    exact CharTwo.add_self_eq_zero 1
  refine ⟨tv hσ hv0self hc, ?_, ?_⟩
  · intro v
    rw [tv_smul, one_mul]
  · intro g l hgl
    have hl0 : l ≠ 0 := by
      intro hl
      have h0 : g • s16ntSuV0 n K = 0 := by rw [hgl, hl, zero_smul]
      have h1 : s16ntSuV0 n K = g⁻¹ • (g • s16ntSuV0 n K) :=
        (inv_smul_smul g _).symm
      rw [h0, smul_zero] at h1
      have hi := congrFun h1 (⟨0, by omega⟩ : Fin n)
      rw [s16ntSuV0] at hi
      simp at hi
    have hnorm : s16ntSuSigma K l * l = 1 := s16nt_su_norm_one hK hl0
    have hfix : g * tv hσ hv0self hc * g⁻¹ = tv hσ hv0self hc := by
      refine ext_smul (s16ntSuSigma K) (fun v => ?_)
      rw [s16nt_su_conj_smul (a := s16ntSuV0 n K) (b := s16ntSuV0 n K) g
        (tv hσ hv0self hc) hnorm (fun w => by rw [tv_smul, one_mul]) hgl v,
        tv_smul, one_mul]
    calc g * tv hσ hv0self hc = g * tv hσ hv0self hc * g⁻¹ * g := by group
      _ = tv hσ hv0self hc * g := by rw [hfix]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
