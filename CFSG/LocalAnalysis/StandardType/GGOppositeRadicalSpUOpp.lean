module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUStd
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOpp
public import CFSG.LocalAnalysis.ComponentInitial.FourGroupOddBilinear

public section

namespace CFSG.StandardType

namespace GGOppRadSpU

open Matrix CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank GGOppRad

variable {n : ℕ} {K : Type} [Field K]

theorem perp_stdFlag {M : ℕ} {ℓ : Fin n ⊕ Fin n → ℕ} (h : IsSpLevel M ℓ) (k : ℕ) :
    (spForm n K).perp (stdFlag ℓ k) = stdFlag ℓ (M + 1 - k) := by
  rcases le_total k (M + 1) with hk | hk
  · exact (isSelfDual_stdFlag h).perp k hk
  · rw [(isSelfDual_stdFlag h).top k hk, (spForm n K).perp_top, Nat.sub_eq_zero_of_le hk,
      stdFlag_zero]

theorem stdFlag_eq_of_isCompl {ι : Type*} [Fintype ι] {ℓ : ι → ℕ} {k k' : ℕ}
    {W : Submodule K (ι → K)} (h : IsCompl (stdFlag ℓ k) W) (h' : IsCompl (stdFlag ℓ k') W) :
    stdFlag (K := K) ℓ k = stdFlag ℓ k' := by
  have e := Submodule.finrank_add_eq_of_isCompl h
  have e' := Submodule.finrank_add_eq_of_isCompl h'
  rcases le_total k k' with hkk | hkk
  · exact Submodule.eq_of_le_of_finrank_eq (stdFlag_mono ℓ hkk) (by omega)
  · exact (Submodule.eq_of_le_of_finrank_eq (stdFlag_mono ℓ hkk) (by omega)).symm

theorem isSpLevel_idx {M N' : ℕ} {ℓ : Fin n ⊕ Fin n → ℕ} (hℓ : IsSpLevel M ℓ)
    {F' : ℕ → Submodule K (Fin n ⊕ Fin n → K)} (hF' : IsSelfDual (spForm n K) F' N')
    (D : OppData ℓ F') : IsSpLevel (N' - 1) D.idx := by
  have hdual : ∀ j ≤ N', stdFlag (K := K) ℓ (M + 1 - D.level j) = stdFlag ℓ (D.level (N' - j)) := by
    intro j hj
    have h1 := isCompl_perp (spForm n K) (D.isCompl_level j)
    rw [perp_stdFlag hℓ, hF'.perp j hj] at h1
    exact stdFlag_eq_of_isCompl h1 (D.isCompl_level (N' - j))
  have key : ∀ a, ∀ j ≤ N', D.idx (Sum.swap a) < N' - j ↔ ¬ D.idx a < j := by
    intro a j hj
    have h2 : ℓ (Sum.swap a) < D.level (N' - j) ↔ ℓ (Sum.swap a) < M + 1 - D.level j := by
      have e1 := single_mem_stdFlag (K := K) (ℓ := ℓ) (k := D.level (N' - j)) (a := Sum.swap a)
      have e2 := single_mem_stdFlag (K := K) (ℓ := ℓ) (k := M + 1 - D.level j) (a := Sum.swap a)
      rw [← e1, ← e2, hdual j hj]
    rw [D.idx_lt_iff, D.idx_lt_iff, ← not_lt, h2]
    have := hℓ.add_swap a
    omega
  have hlt : ∀ a, D.idx a < N' := fun a => D.idx_lt_iff.mpr (by
    rw [D.level_eq_zero (hF'.top N' le_rfl)]
    exact Nat.zero_le _)
  intro t
  have k1 := (key (Sum.inl t) (D.idx (Sum.inl t)) (hlt _).le).mpr (lt_irrefl _)
  have k2 := mt (key (Sum.inl t) (D.idx (Sum.inl t) + 1) (hlt _)).mp
    (not_not.mpr (Nat.lt_succ_self _))
  simp only [Sum.swap_inl] at k1 k2
  have := hlt (Sum.inl t)
  omega

section Adjoint

variable (n K) in
theorem det_spJ : (spJ n K).det = 1 := by
  have h : spJ n K = (Matrix.J (Fin n) K)ᵀ := by
    rw [Matrix.J, fromBlocks_transpose]
    simp [spJ]
  rw [h, Matrix.det_transpose, CFSG.LocalAnalysis.ComponentInitial.FourGroupOddBilinear.det_J]

variable (n K) in
@[expose] def spJsl : Matrix.SpecialLinearGroup (Fin n ⊕ Fin n) K :=
  ⟨spJ n K, det_spJ n K⟩

variable (n K) in
theorem spJ_transpose_eq_neg : (spJ n K)ᵀ = -spJ n K := by
  rw [spJ, fromBlocks_transpose]
  simp [fromBlocks_neg]

variable (n K) in
private theorem spJ_mul_neg_spJ : spJ n K * -spJ n K = 1 := by
  rw [Matrix.mul_neg, spJ_mul_spJ, neg_neg]

variable (n K) in
private theorem det_neg_spJ : (-spJ n K).det = 1 := by
  have hcard : Fintype.card (Fin n ⊕ Fin n) = n + n := by simp
  rw [Matrix.det_neg, det_spJ n K, mul_one, hcard]
  exact Even.neg_one_pow ⟨n, rfl⟩

variable (n K) in
private def negSpJsl : Matrix.SpecialLinearGroup (Fin n ⊕ Fin n) K :=
  ⟨-spJ n K, det_neg_spJ n K⟩

private theorem spJsl_inv_eq : (spJsl n K)⁻¹ = negSpJsl n K :=
  inv_eq_of_mul_eq_one_right (by
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    simpa only [spJsl, negSpJsl] using spJ_mul_neg_spJ n K)

variable (n K) in
theorem coe_spJsl_inv :
    (((spJsl n K)⁻¹ : Matrix.SpecialLinearGroup (Fin n ⊕ Fin n) K) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = -spJ n K := by
  rw [spJsl_inv_eq]
  rfl

@[expose] def adj : Matrix.SpecialLinearGroup (Fin n ⊕ Fin n) K ≃*
    Matrix.SpecialLinearGroup (Fin n ⊕ Fin n) K :=
  tInv.trans (MulAut.conj (spJsl n K))

theorem coe_adj (g : Matrix.SpecialLinearGroup (Fin n ⊕ Fin n) K) :
    ((adj g : Matrix.SpecialLinearGroup (Fin n ⊕ Fin n) K) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      spJ n K * ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n ⊕ Fin n) K) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * -spJ n K := by
  rw [adj, MulEquiv.trans_apply, MulAut.conj_apply, spJsl_inv_eq]
  rfl

theorem adj_transpose_mul (g : Matrix.SpecialLinearGroup (Fin n ⊕ Fin n) K) :
    ((adj g : Matrix.SpecialLinearGroup (Fin n ⊕ Fin n) K) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * spJ n K *
        (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = spJ n K := by
  have hinv : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n ⊕ Fin n) K) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
        = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  simp only [coe_adj, transpose_mul, transpose_transpose, transpose_neg, spJ_transpose_eq_neg,
    neg_neg, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (-spJ n K) (spJ n K)
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K),
    Matrix.neg_mul, spJ_mul_spJ, neg_neg, Matrix.one_mul, hinv, Matrix.mul_one]

section CharTwo

variable [CharP K 2]

theorem neg_one_matrix {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (-1 : Matrix ι ι K) = 1 := by
  ext a b
  rw [Matrix.neg_apply, CharTwo.neg_eq]

variable (n K) in
theorem spJ_transpose : (spJ n K)ᵀ = spJ n K := by
  rw [spJ_transpose_eq_neg]
  ext a b
  rw [Matrix.neg_apply, CharTwo.neg_eq]

variable (n K) in
theorem spJ_mul_spJ_two : spJ n K * spJ n K = 1 := by
  rw [spJ_mul_spJ, neg_one_matrix]

theorem spJsl_mul_self : spJsl n K * spJsl n K = 1 :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    exact spJ_mul_spJ_two n K)

theorem spJsl_inv : (spJsl n K)⁻¹ = spJsl n K :=
  inv_eq_of_mul_eq_one_right spJsl_mul_self

theorem coe_adj_charTwo (g : Matrix.SpecialLinearGroup (Fin n ⊕ Fin n) K) :
    ((adj g : Matrix.SpecialLinearGroup (Fin n ⊕ Fin n) K) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      spJ n K * ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n ⊕ Fin n) K) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * spJ n K := by
  have hneg : -spJ n K = spJ n K := by
    ext a b
    rw [Matrix.neg_apply, CharTwo.neg_eq]
  rw [coe_adj, hneg]

end CharTwo

theorem spForm_adj (g : Matrix.SpecialLinearGroup (Fin n ⊕ Fin n) K)
    (u v : Fin n ⊕ Fin n → K) :
    (spForm n K).β (slRep (adj g) u) (slRep g v) = (spForm n K).β u v := by
  rw [spForm_β, spForm_β, slRep_apply, slRep_apply, mulVec_mulVec, dotProduct_mulVec,
    ← vecMul_transpose, vecMul_vecMul, ← dotProduct_mulVec, ← Matrix.mul_assoc,
    adj_transpose_mul]

theorem slRep_injective_apply (g : Matrix.SpecialLinearGroup (Fin n ⊕ Fin n) K) :
    Function.Injective (slRep g) :=
  fun x y hxy => by simpa only [rep_inv_apply_rep] using congrArg (slRep g⁻¹) hxy

theorem perp_map_slRep (g : Matrix.SpecialLinearGroup (Fin n ⊕ Fin n) K)
    (X : Submodule K (Fin n ⊕ Fin n → K)) :
    (spForm n K).perp (X.map (slRep g)) = ((spForm n K).perp X).map (slRep (adj g)) := by
  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨x, hx, rfl⟩
    apply (spForm n K).refl
    change (spForm n K).β (slRep (adj g) a) (slRep g x) = 0
    rw [spForm_adj]
    exact (spForm n K).refl _ _ (ha x hx)
  · have h1 := (spForm n K).finrank_perp (X.map (slRep g))
    have h2 := (spForm n K).finrank_perp X
    have e1 : Module.finrank K (X.map (slRep g)) = Module.finrank K X :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (slRep_injective_apply g) _)).symm
    have e2 : Module.finrank K (((spForm n K).perp X).map (slRep (adj g))) =
        Module.finrank K ((spForm n K).perp X) :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
        (slRep_injective_apply (adj g)) _)).symm
    omega

theorem flagMap_adj_of_isSelfDual {N : ℕ} {E F' : ℕ → Submodule K (Fin n ⊕ Fin n → K)}
    (hE : IsSelfDual (spForm n K) E N) (hF : IsSelfDual (spForm n K) F' N)
    {g : Matrix.SpecialLinearGroup (Fin n ⊕ Fin n) K} (hg : flagMap slRep g E = F') :
    flagMap slRep (adj g) E = F' := by
  have key : ∀ k ≤ N, flagMap slRep (adj g) E k = F' k := by
    intro k hk
    have h1 : E k = (spForm n K).perp (E (N - k)) := by
      rw [hE.perp _ (Nat.sub_le N k), Nat.sub_sub_self hk]
    have h2 : F' k = (spForm n K).perp (F' (N - k)) := by
      rw [hF.perp _ (Nat.sub_le N k), Nat.sub_sub_self hk]
    change (E k).map (slRep (adj g)) = F' k
    rw [h1, ← perp_map_slRep, h2, ← hg]
    rfl
  funext k
  rcases le_total k N with hk | hk
  · exact key k hk
  · have := key N le_rfl
    change (E N).map (slRep (adj g)) = F' N at this
    rw [hE.top N le_rfl, hF.top N le_rfl] at this
    change (E k).map (slRep (adj g)) = F' k
    rw [hE.top k hk, hF.top k hk]
    exact this

theorem flagMap_spJsl (ℓ : Fin n ⊕ Fin n → ℕ) :
    flagMap slRep (spJsl n K) (stdFlag ℓ) = stdFlag (ℓ ∘ Sum.swap) := by
  funext k
  have hle : flagMap slRep (spJsl n K) (stdFlag ℓ) k ≤ stdFlag (ℓ ∘ Sum.swap) k := by
    rintro _ ⟨w, hw, rfl⟩ a ha
    change (slRep (spJsl n K) w) a = 0
    rw [slRep_apply]
    exact (spJ_mulVec_eq_zero_iff w a).mpr (hw _ ha)
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have e1 : Module.finrank K ((stdFlag (K := K) ℓ k).map (slRep (spJsl n K))) =
      Module.finrank K (stdFlag (K := K) ℓ k) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
      (slRep_injective_apply (spJsl n K)) _)).symm
  change Module.finrank K ((stdFlag (K := K) ℓ k).map (slRep (spJsl n K))) = _
  rw [e1, finrank_stdFlag, finrank_stdFlag]
  exact Fintype.card_congr ((Equiv.sumComm (Fin n) (Fin n)).subtypeEquiv fun a => by
    simp [Function.comp_apply])

theorem adj_mem_stdUop [Finite K] {C : ℕ} {i : Fin n ⊕ Fin n → ℕ} (hi : IsSpLevel C i)
    {g : Matrix.SpecialLinearGroup (Fin n ⊕ Fin n) K} (hg : g ∈ stdUop (K := K) i) :
    adj g ∈ stdUop (K := K) i := by
  have h1 : tInv g ∈ stdU (K := K) i := by
    obtain ⟨h, hh, rfl⟩ := hg
    have : tInv (tInv h) = h := tInv.symm_apply_apply h
    change tInv (tInv h) ∈ _
    rw [this]
    exact hh
  have h2 : adj g ∈ stdU (K := K) (i ∘ Sum.swap) := by
    rw [stdU, ← flagMap_spJsl, flagKernel_flagMap]
    exact ⟨tInv g, h1, rfl⟩
  rw [mem_stdUop_iff]
  rw [mem_stdU_iff] at h2
  intro c a hac
  refine h2 c a fun h => hac ?_
  have := hi.add_swap c
  have := hi.add_swap a
  simp only [Function.comp_apply] at h
  omega

theorem eq_of_flagMap_eq [Finite K] {ι : Type*} [Fintype ι] [DecidableEq ι] {i : ι → ℕ}
    {g h : Matrix.SpecialLinearGroup ι K} (hg : g ∈ stdUop (K := K) i)
    (hh : h ∈ stdUop (K := K) i)
    (hgh : flagMap slRep g (stdFlag i) = flagMap slRep h (stdFlag i)) : g = h := by
  have hx : g⁻¹ * h ∈ stdUop (K := K) i := mul_mem (inv_mem hg) hh
  have hE : flagMap slRep (g⁻¹ * h) (stdFlag (K := K) i) = stdFlag i := by
    rw [← flagMap_flagMap, ← hgh, flagMap_flagMap, inv_mul_cancel, flagMap_one]
  have hE' : flagMap slRep (g⁻¹ * h)⁻¹ (stdFlag (K := K) i) = stdFlag i := by
    conv_lhs => rw [← hE]
    rw [flagMap_flagMap, inv_mul_cancel, flagMap_one]
  have hP : g⁻¹ * h ∈ stdP (K := K) i := by
    intro k v hv
    refine ⟨?_, ?_⟩
    · rw [← congrFun hE k]
      exact Submodule.mem_map_of_mem hv
    · rw [← congrFun hE' k]
      exact Submodule.mem_map_of_mem hv
  have h1 : g⁻¹ * h = 1 := by
    have : g⁻¹ * h ∈ stdUop (K := K) i ⊓ stdP i := ⟨hx, hP⟩
    rwa [stdUop_inf_stdP, Subgroup.mem_bot] at this
  rw [← mul_inv_cancel_left g h, h1, mul_one]

end Adjoint

theorem exists_eq_flagMap_of_isCompl [Finite K] {M N' : ℕ}
    {ℓ : Fin n ⊕ Fin n → ℕ} (hℓ : IsSpLevel M ℓ) {F' : ℕ → Submodule K (Fin n ⊕ Fin n → K)}
    (hF' : IsSelfDual (spForm n K) F' N') (hN' : 1 ≤ N')
    (hcompl : ∀ j, ∃ k, IsCompl (stdFlag ℓ k) (F' j)) :
    ∃ (u : StatedSp n K) (i : Fin n ⊕ Fin n → ℕ), IsSpLevel (N' - 1) i ∧ u ∈ spU n K ℓ ∧
      GGOppRad.flagMap (natRep (StatedSp n K)) u (stdFlag i) = F' ∧
      spU n K (i ∘ Sum.swap) ≤ spU n K ℓ := by
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
  let u : StatedSp n K := ⟨Matrix.SpecialLinearGroup.toGL D.elt, Subgroup.subset_closure hsp⟩
  have hu : ∀ v, natRep (StatedSp n K) u v = slRep D.elt v := fun v => by
    rw [natRep_apply, slRep_apply]
    rfl
  have hcond : ∀ c a, D.idx a < D.idx c → ℓ c < ℓ a := fun c a h => by
    have h1 : ¬ D.level (D.idx a + 1) ≤ ℓ c := fun h' => by
      have := D.idx_lt_iff.mpr h'
      omega
    have h2 : D.level (D.idx a + 1) ≤ ℓ a := D.idx_lt_iff.mp (Nat.lt_succ_self _)
    omega
  refine ⟨u, D.idx, hi, ?_, ?_, ?_⟩
  · rw [mem_spU_iff]
    intro c a hca
    exact (mem_stdU_iff.mp (D.stdUop_idx_le hg)) c a hca
  · funext k
    have h1 := congrFun hgF k
    change (stdFlag D.idx k).map (slRep D.elt) = F' k at h1
    change (stdFlag D.idx k).map (natRep (StatedSp n K) u) = F' k
    rw [← h1]
    congr 1
  · intro g hgsw
    rw [mem_spU_comp_swap_iff hi] at hgsw
    rw [mem_spU_iff]
    intro c a hca
    exact hgsw c a fun h => hca (hcond c a h)

end GGOppRadSpU

end CFSG.StandardType
