module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalFlag

public section

namespace CFSG.StandardType

namespace GGOppRad

open Matrix CFSG.Open CFSG.LieType.BorelTits

theorem radicalTwo_map_mulEquiv {H : Type*} [Group H] (e : H ≃* H) {Q : Subgroup H}
    (hQ : GGRadicalTwo ⊤ Q) : GGRadicalTwo ⊤ (Q.map e.toMonoidHom) := by
  unfold GGRadicalTwo at hQ ⊢
  rw [top_inf_eq] at hQ ⊢
  rw [← Subgroup.map_equiv_normalizer_eq, pCoreOf_map_mulEquiv, hQ]

theorem mem_flagStab_of_forall {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {H : Type*} [Group H] [Finite H] (ρ : H →* Module.End K V) {F : ℕ → Submodule K V} {g : H}
    (hg : ∀ k, ∀ v ∈ F k, ρ g v ∈ F k) : g ∈ flagStab ρ F := by
  have hpow : ∀ m : ℕ, ∀ k, ∀ v ∈ F k, ρ (g ^ m) v ∈ F k := by
    intro m
    induction m with
    | zero => intro k v hv; simpa using hv
    | succ m ih =>
      intro k v hv
      rw [pow_succ, map_mul, Module.End.mul_apply]
      exact ih k _ (hg k v hv)
  have hinv : g⁻¹ = g ^ (Nat.card H - 1) := by
    refine (eq_inv_of_mul_eq_one_left (a := g ^ (Nat.card H - 1)) (b := g) ?_).symm
    rw [← pow_succ, Nat.sub_add_cancel Nat.card_pos, pow_card_eq_one']
  intro k v hv
  exact ⟨hg k v hv, hinv ▸ hpow _ k v hv⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]

@[expose] noncomputable def slRep : Matrix.SpecialLinearGroup ι K →* Module.End K (ι → K) :=
  ((Matrix.toLinAlgEquiv' : Matrix ι ι K ≃ₐ[K] Module.End K (ι → K)).toMonoidHom).comp
    ((Units.coeHom (Matrix ι ι K)).comp Matrix.SpecialLinearGroup.toGL)

@[simp] theorem slRep_apply (g : Matrix.SpecialLinearGroup ι K) (v : ι → K) :
    slRep g v = (g : Matrix ι ι K) *ᵥ v := by
  simp [slRep, Matrix.toLinAlgEquiv'_apply]

theorem slRep_injective : Function.Injective (slRep (ι := ι) (K := K)) := by
  intro a b hab
  apply Subtype.ext
  ext i j
  have h := congrArg (fun f : Module.End K (ι → K) => f (Pi.single j 1) i) hab
  simpa only [slRep_apply, mulVec_single_one, col_apply] using h

theorem containsTransvections_slRep : ContainsTransvections (slRep (ι := ι) (K := K)) := by
  intro x φ hφ
  set y : ι → K := fun i => φ (Pi.single i 1)
  have hφy : ∀ v, φ v = y ⬝ᵥ v := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ φ v, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
    congr 2
    ext j
    simp [Pi.single_apply, eq_comm]
  set A : Matrix ι ι K := 1 + vecMulVec x y with hA
  have hdet : A.det = 1 := by
    rw [hA, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, ← hφy, hφ, add_zero]
  let g : Matrix.SpecialLinearGroup ι K := ⟨A, hdet⟩
  refine ⟨g, fun v => ?_⟩
  rw [slRep_apply]
  change A *ᵥ v = v + φ v • x
  rw [hA, add_mulVec, one_mulVec, vecMulVec_mulVec, hφy, op_smul_eq_smul]

section Flags

variable {ι : Type*} {K : Type*} [Field K]

@[expose] def stdFlag (ℓ : ι → ℕ) (k : ℕ) : Submodule K (ι → K) where
  carrier := {v | ∀ a, k ≤ ℓ a → v a = 0}
  add_mem' := by
    intro v w hv hw a ha
    simp [hv a ha, hw a ha]
  zero_mem' := by
    intro a _
    rfl
  smul_mem' := by
    intro c v hv a ha
    simp [hv a ha]

theorem mem_stdFlag {ℓ : ι → ℕ} {k : ℕ} {v : ι → K} :
    v ∈ stdFlag ℓ k ↔ ∀ a, k ≤ ℓ a → v a = 0 :=
  Iff.rfl

theorem stdFlag_mono (ℓ : ι → ℕ) : Monotone (stdFlag (K := K) ℓ) :=
  fun _ _ hkk' _ hv a ha => hv a (hkk'.trans ha)

theorem stdFlag_zero (ℓ : ι → ℕ) : stdFlag (K := K) ℓ 0 = ⊥ := by
  ext v
  simp only [mem_stdFlag, zero_le, forall_const, Submodule.mem_bot]
  exact ⟨fun h => funext h, fun h a => by rw [h]; rfl⟩

theorem stdFlag_eq_top {ℓ : ι → ℕ} {k : ℕ} (hk : ∀ a, ℓ a < k) : stdFlag (K := K) ℓ k = ⊤ :=
  eq_top_iff.mpr fun _ _ a ha => absurd ha (not_le.mpr (hk a))

theorem exists_stdFlag_eq_top [Fintype ι] (ℓ : ι → ℕ) : ∃ M, stdFlag (K := K) ℓ M = ⊤ :=
  ⟨Finset.univ.sup ℓ + 1,
    stdFlag_eq_top fun a => Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ a))⟩

theorem single_mem_stdFlag [DecidableEq ι] {ℓ : ι → ℕ} {k : ℕ} {a : ι} :
    (Pi.single a (1 : K) : ι → K) ∈ stdFlag ℓ k ↔ ℓ a < k := by
  constructor
  · intro h
    by_contra hk
    have := h a (not_lt.mp hk)
    simp at this
  · intro h b hb
    have hba : b ≠ a := fun hab => absurd (hab ▸ hb) (not_le.mpr h)
    simp [hba]

theorem stdFlag_eq_span [Fintype ι] [DecidableEq ι] (ℓ : ι → ℕ) (k : ℕ) :
    stdFlag (K := K) ℓ k =
      Submodule.span K (Set.range fun a : {a // ℓ a < k} => (Pi.single a.1 (1 : K) : ι → K)) := by
  refine le_antisymm (fun v hv => ?_) (Submodule.span_le.mpr ?_)
  · have hv' : v = ∑ a : {a // ℓ a < k}, v a.1 • (Pi.single a.1 (1 : K) : ι → K) := by
      ext c
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero]
      by_cases hc : ℓ c < k
      · rw [Finset.sum_eq_single ⟨c, hc⟩]
        · simp
        · intro b _ hb
          have : ¬ c = b.1 := fun h => hb (Subtype.ext h.symm)
          simp [this]
        · simp
      · rw [hv c (not_lt.mp hc), Finset.sum_eq_zero]
        intro b _
        have : ¬ c = b.1 := fun h => hc (h ▸ b.2)
        simp [this]
    rw [hv']
    exact Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · rintro _ ⟨a, rfl⟩
    exact single_mem_stdFlag.mpr a.2

theorem finrank_stdFlag [Fintype ι] [DecidableEq ι] (ℓ : ι → ℕ) (k : ℕ) :
    Module.finrank K (stdFlag (K := K) ℓ k) = Fintype.card {a // ℓ a < k} := by
  have hli : LinearIndependent K
      (fun a : {a // ℓ a < k} => (Pi.single a.1 (1 : K) : ι → K)) := by
    have := (Pi.basisFun K ι).linearIndependent.comp (Subtype.val : {a // ℓ a < k} → ι)
      Subtype.val_injective
    convert this using 1
    funext a
    simp
  rw [stdFlag_eq_span, finrank_span_eq_card hli]

end Flags

section Groups

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]

@[expose] noncomputable def stdU (ℓ : ι → ℕ) : Subgroup (Matrix.SpecialLinearGroup ι K) :=
  flagKernel slRep (stdFlag ℓ)

@[expose] noncomputable def stdP (ℓ : ι → ℕ) : Subgroup (Matrix.SpecialLinearGroup ι K) :=
  flagStab slRep (stdFlag ℓ)

theorem mem_stdU_iff [Finite K] {ℓ : ι → ℕ} {g : Matrix.SpecialLinearGroup ι K} :
    g ∈ stdU ℓ ↔ ∀ c a, ¬ ℓ c < ℓ a → (g : Matrix ι ι K) c a = (1 : Matrix ι ι K) c a := by
  constructor
  · intro hg c a hca
    have hmem : (Pi.single a (1 : K) : ι → K) ∈ stdFlag ℓ (ℓ a + 1) :=
      single_mem_stdFlag.mpr (Nat.lt_succ_self _)
    have h1 := hg.2 (ℓ a) _ hmem c (not_lt.mp hca)
    rw [slRep_apply, mulVec_single_one, Pi.sub_apply, col_apply, sub_eq_zero] at h1
    rw [h1, Pi.single_apply, Matrix.one_apply]
  · intro h
    have key : ∀ k, ∀ v ∈ stdFlag ℓ (k + 1),
        (g : Matrix ι ι K) *ᵥ v - v ∈ stdFlag (K := K) ℓ k := by
      intro k v hv c hc
      have hsub : (g : Matrix ι ι K) *ᵥ v - v = ((g : Matrix ι ι K) - 1) *ᵥ v := by
        rw [sub_mulVec, one_mulVec]
      rw [hsub, mulVec, dotProduct]
      refine Finset.sum_eq_zero fun a _ => ?_
      by_cases hca : ℓ c < ℓ a
      · rw [hv a (by omega), mul_zero]
      · rw [Matrix.sub_apply, h c a hca, sub_self, zero_mul]
    have hstab : ∀ k, ∀ v ∈ stdFlag ℓ k, slRep g v ∈ stdFlag (K := K) ℓ k := by
      intro k v hv
      cases k with
      | zero =>
        rw [stdFlag_zero] at hv ⊢
        rw [(Submodule.mem_bot K).mp hv, map_zero]
        exact zero_mem _
      | succ k =>
        have h2 := add_mem (stdFlag_mono ℓ (Nat.le_succ k) (key k v hv)) hv
        rw [slRep_apply]
        simpa using h2
    have hS : g ∈ flagStab slRep (stdFlag (K := K) ℓ) :=
      mem_flagStab_of_forall (H := Matrix.SpecialLinearGroup ι K) slRep hstab
    have hK2 : ∀ k, ∀ v ∈ stdFlag ℓ (k + 1), slRep g v - v ∈ stdFlag (K := K) ℓ k :=
      fun k v hv => by rw [slRep_apply]; exact key k v hv
    exact (mem_flagKernel (slRep (ι := ι) (K := K))).mpr ⟨hS, hK2⟩

theorem stdP_apply_eq_zero {ℓ : ι → ℕ} {g : Matrix.SpecialLinearGroup ι K} (hg : g ∈ stdP ℓ) {c a : ι}
    (h : ℓ a < ℓ c) : (g : Matrix ι ι K) c a = 0 := by
  have hmem : (Pi.single a (1 : K) : ι → K) ∈ stdFlag ℓ (ℓ a + 1) :=
    single_mem_stdFlag.mpr (Nat.lt_succ_self _)
  have h1 := (hg (ℓ a + 1) _ hmem).1 c h
  rwa [slRep_apply, mulVec_single_one, col_apply] at h1

theorem exists_lt_of_stdU_ne_bot [Finite K] {ℓ : ι → ℕ} (h : stdU (K := K) ℓ ≠ ⊥) :
    ∃ c a, ℓ c < ℓ a := by
  by_contra hno
  refine h ((Subgroup.eq_bot_iff_forall _).mpr fun g hg =>
    Matrix.SpecialLinearGroup.ext _ _ fun c a => ?_)
  rw [Matrix.SpecialLinearGroup.coe_one]
  exact mem_stdU_iff.mp hg c a fun hca => hno ⟨c, a, hca⟩

theorem transpose_mul' (A B : Matrix.SpecialLinearGroup ι K) :
    (A * B).transpose = B.transpose * A.transpose :=
  Subtype.ext (by simp [Matrix.transpose_mul])

theorem transpose_one' : (1 : Matrix.SpecialLinearGroup ι K).transpose = 1 :=
  Subtype.ext (by simp)

theorem transpose_transpose' (A : Matrix.SpecialLinearGroup ι K) : A.transpose.transpose = A :=
  Subtype.ext (by simp)

theorem transpose_inv' (A : Matrix.SpecialLinearGroup ι K) : (A⁻¹).transpose = (A.transpose)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← transpose_mul', mul_inv_cancel, transpose_one'])

@[expose] def tInv : Matrix.SpecialLinearGroup ι K ≃* Matrix.SpecialLinearGroup ι K where
  toFun g := (g⁻¹).transpose
  invFun g := (g⁻¹).transpose
  left_inv g := by simp only [transpose_inv', inv_inv, transpose_transpose']
  right_inv g := by simp only [transpose_inv', inv_inv, transpose_transpose']
  map_mul' g h := by simp only [_root_.mul_inv_rev, transpose_mul']

theorem tInv_symm : (tInv : Matrix.SpecialLinearGroup ι K ≃* Matrix.SpecialLinearGroup ι K).symm = tInv :=
  rfl

@[expose] noncomputable def stdUop (ℓ : ι → ℕ) : Subgroup (Matrix.SpecialLinearGroup ι K) :=
  (stdU ℓ).map (tInv : Matrix.SpecialLinearGroup ι K ≃* Matrix.SpecialLinearGroup ι K).toMonoidHom

theorem mem_stdUop_iff [Finite K] {ℓ : ι → ℕ} {g : Matrix.SpecialLinearGroup ι K} :
    g ∈ stdUop ℓ ↔ ∀ c a, ¬ ℓ a < ℓ c → (g : Matrix ι ι K) c a = (1 : Matrix ι ι K) c a := by
  rw [stdUop, Subgroup.mem_map_equiv]
  have h1 : (tInv : Matrix.SpecialLinearGroup ι K ≃* Matrix.SpecialLinearGroup ι K).symm g = (g.transpose)⁻¹ :=
    transpose_inv' g
  rw [h1, Subgroup.inv_mem_iff, mem_stdU_iff]
  have h2 : ∀ c a, (1 : Matrix ι ι K) a c = (1 : Matrix ι ι K) c a := fun c a => by
    simp only [Matrix.one_apply, eq_comm]
  constructor
  · intro h c a hac
    have := h a c hac
    rwa [Matrix.SpecialLinearGroup.coe_transpose, Matrix.transpose_apply, h2] at this
  · intro h c a hca
    rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.transpose_apply, h2]
    exact h a c hca

theorem card_stdUop (ℓ : ι → ℕ) : Nat.card (stdUop (K := K) ℓ) = Nat.card (stdU (K := K) ℓ) :=
  Subgroup.card_map_of_injective (tInv : Matrix.SpecialLinearGroup ι K ≃* _).injective

theorem stdUop_inf_stdP [Finite K] (ℓ : ι → ℕ) : stdUop (K := K) ℓ ⊓ stdP ℓ = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg => Matrix.SpecialLinearGroup.ext _ _ fun c a => ?_
  by_cases h : ℓ a < ℓ c
  · rw [stdP_apply_eq_zero hg.2 h, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply_ne (fun hca => by subst hca; exact lt_irrefl _ h)]
  · rw [Matrix.SpecialLinearGroup.coe_one]
    exact mem_stdUop_iff.mp hg.1 c a h

theorem stdUop_le_stdU [Finite K] {ℓ ℓ' : ι → ℕ} (h : ∀ c a, ℓ' a < ℓ' c → ℓ c < ℓ a) :
    stdUop (K := K) ℓ' ≤ stdU ℓ := fun _ hg =>
  mem_stdU_iff.mpr fun c a hca => mem_stdUop_iff.mp hg c a fun h' => hca (h c a h')

theorem radicalTwo_stdUop {ℓ : ι → ℕ} (h : GGRadicalTwo ⊤ (stdU (K := K) ℓ)) :
    GGRadicalTwo ⊤ (stdUop (K := K) ℓ) :=
  radicalTwo_map_mulEquiv tInv h

end Groups

end GGOppRad

end CFSG.StandardType
