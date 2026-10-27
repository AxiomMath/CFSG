module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaPlusOpp
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUOpp

public section

namespace CFSG.StandardType

namespace GGOppRadOmega

open Module QuadraticMap CFSG.LieType.BorelTits CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.OrthogonalInvolutions GGOppRad GGOppRadSpU
open Matrix

variable {n : ℕ} {K : Type} [Field K]

@[expose] def IsUniTri (ℓ : Fin n ⊕ Fin n → ℕ) (f : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)) :
    Prop :=
  ∀ a, f (Pi.single a 1) - Pi.single a 1 ∈ stdFlag (K := K) ℓ (ℓ a)

theorem sum_single_eq (v : Fin n ⊕ Fin n → K) :
    ∑ a, v a • (Pi.single a (1 : K) : Fin n ⊕ Fin n → K) = v := by
  ext c
  simp [Finset.sum_apply, Pi.single_apply]

theorem IsUniTri.sub_mem {ℓ : Fin n ⊕ Fin n → ℕ}
    {f : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)} (hf : IsUniTri ℓ f) {k : ℕ}
    {v : Fin n ⊕ Fin n → K} (hv : v ∈ stdFlag ℓ (k + 1)) : f v - v ∈ stdFlag ℓ k := by
  have e : f v - v = ∑ a, v a • (f (Pi.single a 1) - Pi.single a 1) := by
    conv_lhs => rw [← sum_single_eq v]
    rw [map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, smul_sub]
  rw [e]
  refine Submodule.sum_mem _ fun a _ => ?_
  by_cases ha : k + 1 ≤ ℓ a
  · rw [hv a ha, zero_smul]
    exact zero_mem _
  · exact Submodule.smul_mem _ _ (stdFlag_mono ℓ (by omega) (hf a))

variable [CharP K 2]

theorem mem_plusU_iff_isUniTri [Finite K] {ℓ : Fin n ⊕ Fin n → ℕ} {h : spinGroup (quadPlus n K)} :
    h ∈ plusU ℓ ↔ IsUniTri ℓ (plusRep n K h) := by
  have : Finite (spinGroup (quadPlus n K)) := finite_spinGroup_quadPlus
  constructor
  · intro hh a
    exact hh.2 _ _ (single_mem_stdFlag.mpr (Nat.lt_succ_self _))
  · intro hh
    exact mem_flagKernel_of_sub_mem _ (stdFlag_mono ℓ) (stdFlag_zero ℓ) fun k v hv => hh.sub_mem hv

omit [CharP K 2] in
theorem isUniTri_iff_mulVec {ℓ : Fin n ⊕ Fin n → ℕ} {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} :
    IsUniTri ℓ (Matrix.mulVecLin A) ↔ ∀ c a, ¬ ℓ c < ℓ a → A c a = (1 : Matrix _ _ K) c a := by
  constructor
  · intro h c a hca
    have h1 := h a c (not_lt.mp hca)
    rw [Matrix.mulVecLin_apply, mulVec_single_one, Pi.sub_apply, col_apply, sub_eq_zero] at h1
    rw [h1, Pi.single_apply, Matrix.one_apply]
  · intro h a c hc
    rw [Matrix.mulVecLin_apply, mulVec_single_one, Pi.sub_apply, col_apply,
      h c a (not_lt.mpr hc), Pi.single_apply, Matrix.one_apply, sub_self]

omit [CharP K 2] in
theorem plusRep_eq_mulVecLin (x : spinGroup (quadPlus n K)) :
    plusRep n K x = Matrix.mulVecLin (spinMatrix (quadPlus n K) x : Matrix _ _ K) :=
  LinearMap.ext fun v => (spinMatrix_mulVec _ x v).symm

theorem exists_slElt_of_isCompl [Finite K] {M N' : ℕ}
    {ℓ : Fin n ⊕ Fin n → ℕ} (hℓ : IsSpLevel M ℓ) {F' : ℕ → Submodule K (Fin n ⊕ Fin n → K)}
    (hF' : IsSelfDual (spForm n K) F' N') (hN' : 1 ≤ N')
    (hcompl : ∀ j, ∃ k, IsCompl (stdFlag ℓ k) (F' j)) :
    ∃ (u : Matrix.SpecialLinearGroup (Fin n ⊕ Fin n) K) (i : Fin n ⊕ Fin n → ℕ),
      IsSpLevel (N' - 1) i ∧ u ∈ stdUop (K := K) i ∧ (∀ c a, i a < i c → ℓ c < ℓ a) ∧
      flagMap slRep u (stdFlag i) = F' ∧
      (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * spJ n K *
        (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = spJ n K := by
  let D : OppData ℓ F' := ⟨hF'.mono, hF'.zero, ⟨N', hF'.top N' le_rfl⟩, hcompl⟩
  have hi : IsSpLevel (N' - 1) D.idx := isSpLevel_idx hℓ hF' D
  have hE : IsSelfDual (spForm n K) (stdFlag D.idx) N' := by
    have := isSelfDual_stdFlag (K := K) hi
    rwa [Nat.sub_add_cancel hN'] at this
  have hg : D.elt ∈ stdUop (K := K) D.idx := D.elt_mem_stdUop
  have hgF : flagMap slRep D.elt (stdFlag D.idx) = F' := D.flagMap_elt
  have hα : adj D.elt = D.elt :=
    eq_of_flagMap_eq (adj_mem_stdUop hi hg) hg
      (by rw [flagMap_adj_of_isSelfDual hE hF' hgF, hgF])
  have hsp : ((D.elt : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K))ᵀ * spJ n K *
      (D.elt : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = spJ n K := by
    have := adj_transpose_mul D.elt
    rwa [hα] at this
  have hcond : ∀ c a, D.idx a < D.idx c → ℓ c < ℓ a := fun c a h => by
    have h1 : ¬ D.level (D.idx a + 1) ≤ ℓ c := fun h' => by
      have := D.idx_lt_iff.mpr h'
      omega
    have h2 : D.level (D.idx a + 1) ≤ ℓ a := D.idx_lt_iff.mp (Nat.lt_succ_self _)
    omega
  exact ⟨D.elt, D.idx, hi, hg, hcond, hgF, hsp⟩

theorem polar_quadPlus_eq_spForm (u v : Fin n ⊕ Fin n → K) :
    polar (quadPlus n K) u v = (spForm n K).β u v := by
  rw [← plusForm_β, plusForm_polar]

theorem quadPlus_mulVec_eq {D : ℕ} {i : Fin n ⊕ Fin n → ℕ} (hi : IsSpLevel (2 * D) i)
    {u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hu : ∀ c a, ¬ i a < i c → u c a = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) c a)
    (hsp : uᵀ * spJ n K * u = spJ n K)
    (hlow : ∀ a, i a < D → quadPlus n K (u *ᵥ Pi.single a 1) = 0) (v : Fin n ⊕ Fin n → K) :
    quadPlus n K (u *ᵥ v) = quadPlus n K v := by
  classical
  have hcol : ∀ a, quadPlus n K (u *ᵥ Pi.single a 1) = 0 := by
    intro a
    by_cases ha : i a < D
    · exact hlow a ha
    rw [mulVec_single_one, quadPlus_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    simp only [col_apply]
    have hs := hi t
    by_cases h1 : i a < i (Sum.inl t)
    · by_cases h2 : i a < i (Sum.inr t)
      · omega
      · rw [hu _ a h2, Matrix.one_apply_ne, mul_zero]
        rintro rfl
        omega
    · rw [hu _ a h1]
      by_cases hta : Sum.inl t = a
      · subst hta
        rw [hu (Sum.inr t) (Sum.inl t) (by omega),
          Matrix.one_apply_ne (i := Sum.inr t) (j := Sum.inl t) Sum.inr_ne_inl, mul_zero]
      · rw [Matrix.one_apply_ne hta, zero_mul]
  have hpol : ∀ x y, polar (quadPlus n K) (u *ᵥ x) (u *ᵥ y) = polar (quadPlus n K) x y := by
    intro x y
    rw [polar_quadPlus_eq_spForm, polar_quadPlus_eq_spForm, spForm_β, spForm_β, mulVec_mulVec,
      dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, ← dotProduct_mulVec,
      ← Matrix.mul_assoc, hsp]
  let L : (Fin n ⊕ Fin n → K) →+ K :=
    { toFun := fun x => quadPlus n K (u *ᵥ x) - quadPlus n K x
      map_zero' := by simp
      map_add' := fun x y => by
        rw [mulVec_add, QuadraticMap.map_add (quadPlus n K), QuadraticMap.map_add (quadPlus n K),
          hpol]
        ring }
  have hL : L v = 0 := by
    rw [← sum_single_eq v, map_sum]
    refine Finset.sum_eq_zero fun a _ => ?_
    change quadPlus n K (u *ᵥ (v a • Pi.single a 1)) - quadPlus n K (v a • Pi.single a 1) = 0
    rw [mulVec_smul, QuadraticMap.map_smul, QuadraticMap.map_smul, hcol, quadPlus_single,
      smul_zero, sub_self]
  exact sub_eq_zero.mp hL

theorem exists_mem_plusU_flagMap_eq [Finite K] (hn : 3 ≤ n) {M' D : ℕ}
    {ℓ ℓ' : Fin n ⊕ Fin n → ℕ} (hℓ' : IsSpLevel M' ℓ')
    (hvar : ∀ g : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K),
      (∀ v, quadPlus n K (g v) = quadPlus n K v) → IsUniTri ℓ' g → IsUniTri ℓ g)
    (hZ : ∃ z, (plusForm n K).IsTotallySingular (stdFlag ℓ z) ∧
      (plusForm n K).polar.perp (stdFlag ℓ z) ≤ stdFlag ℓ (z + 1))
    {F' : ℕ → Submodule K (Fin n ⊕ Fin n → K)}
    (hF' : IsSelfDual (plusForm n K).polar F' (2 * D + 1))
    (hFs : ∀ j ≤ D, (plusForm n K).IsTotallySingular (F' j))
    (hcompl : ∀ j, ∃ k, IsCompl (stdFlag ℓ' k) (F' j)) :
    ∃ (h : spinGroup (quadPlus n K)) (i : Fin n ⊕ Fin n → ℕ), IsSpLevel (2 * D) i ∧
      h ∈ plusU ℓ ∧ GGOppRad.flagMap (plusRep n K) h (stdFlag i) = F' ∧
      plusU (K := K) (i ∘ Sum.swap) ≤ plusU ℓ := by
  have hF'sp : IsSelfDual (spForm n K) F' (2 * D + 1) := by
    have := hF'
    rwa [plusForm_polar] at this
  obtain ⟨u, i, hi, hu, hcond, huF, hsp⟩ := exists_slElt_of_isCompl hℓ' hF'sp (by omega) hcompl
  rw [show 2 * D + 1 - 1 = 2 * D by omega] at hi
  have hu' := mem_stdUop_iff.mp hu
  have hlow : ∀ a, i a < D → quadPlus n K ((u : Matrix _ _ K) *ᵥ Pi.single a 1) = 0 := by
    intro a ha
    have hmem : (u : Matrix _ _ K) *ᵥ Pi.single a 1 ∈ F' (i a + 1) := by
      rw [← huF]
      exact ⟨Pi.single a 1, single_mem_stdFlag.mpr (Nat.lt_succ_self _), by rw [slRep_apply]⟩
    exact hFs (i a + 1) (by omega) _ hmem
  have hQu := quadPlus_mulVec_eq hi hu' hsp hlow
  set U := Matrix.SpecialLinearGroup.toLin' u with hU
  have hUv : ∀ v, U v = (u : Matrix _ _ K) *ᵥ v := fun v => Matrix.SpecialLinearGroup.toLin'_apply u v
  have hUO : U ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by rw [hUv, hQu]
  have hUlin : (U : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)) =
      Matrix.mulVecLin (u : Matrix _ _ K) := LinearMap.ext fun v => hUv v
  have hstdU : u ∈ stdU (K := K) ℓ' := stdUop_le_stdU hcond hu
  have hUtri' : IsUniTri ℓ' (U : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)) := by
    rw [hUlin, isUniTri_iff_mulVec]
    exact mem_stdU_iff.mp hstdU
  have hUtri := hvar _ (fun v => by rw [LinearEquiv.coe_coe, hUv, hQu]) hUtri'
  obtain ⟨z, hzs, hzperp⟩ := hZ
  have hUΩ : U ∈ omegaGroup (quadPlus n K) (nondegenerate_polarBilin_quadPlus n K) :=
    mem_omegaGroup_of_triv _ hUO (Z := stdFlag ℓ z) hzs fun v hv => hUtri.sub_mem (hzperp hv)
  obtain ⟨h, hh⟩ := exists_spinAction_eq_of_mem_omegaGroup_plus hn hUΩ
  have hρh : plusRep n K h = (U : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)) :=
    LinearMap.ext fun v => by rw [plusRep_apply, hh]; rfl
  refine ⟨h, i, hi, mem_plusU_iff_isUniTri.mpr (hρh ▸ hUtri), ?_, fun x hx => ?_⟩
  · rw [← huF]
    funext k
    change (stdFlag i k).map (plusRep n K h) = (stdFlag i k).map (slRep u)
    have e : plusRep n K h = slRep u := by
      refine LinearMap.ext fun v => ?_
      rw [hρh, slRep_apply, LinearEquiv.coe_coe, hUv]
    rw [e]
  ·
    have hx' := mem_plusU_iff_isUniTri.mp hx
    rw [plusRep_eq_mulVecLin, isUniTri_iff_mulVec] at hx'
    have hxℓ' : IsUniTri ℓ' (plusRep n K x) := by
      rw [plusRep_eq_mulVecLin, isUniTri_iff_mulVec]
      intro c a hca
      refine hx' c a fun hlt => ?_
      have h1 := hi.add_swap c
      have h2 := hi.add_swap a
      simp only [Function.comp_apply] at hlt
      exact hca (hcond c a (by omega))
    exact mem_plusU_iff_isUniTri.mpr (hvar _ (fun v => plusRep_Q x v) hxℓ')

end GGOppRadOmega

end CFSG.StandardType
