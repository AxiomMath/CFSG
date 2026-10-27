module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUFlag
public import CFSG.LieType.BorelTits.Symplectic

public section

namespace CFSG.StandardType

namespace GGOppRadSpU

open Matrix CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank GGOppRad

section NatRep

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]

theorem mem_flagKernel_natRep_iff [Finite K] {H : Subgroup (GL ι K)} {ℓ : ι → ℕ} {g : H} :
    g ∈ flagKernel (natRep H) (stdFlag ℓ) ↔
      ∀ c a, ¬ ℓ c < ℓ a → ((g : GL ι K) : Matrix ι ι K) c a = (1 : Matrix ι ι K) c a := by
  constructor
  · intro hg c a hca
    have hmem : (Pi.single a (1 : K) : ι → K) ∈ stdFlag ℓ (ℓ a + 1) :=
      single_mem_stdFlag.mpr (Nat.lt_succ_self _)
    have h1 := hg.2 (ℓ a) _ hmem c (not_lt.mp hca)
    rw [natRep_apply, mulVec_single_one, Pi.sub_apply, col_apply, sub_eq_zero] at h1
    rw [h1, Pi.single_apply, Matrix.one_apply]
  · intro h
    refine mem_flagKernel_of_sub_mem (natRep H) (stdFlag_mono ℓ) (stdFlag_zero ℓ)
      fun k v hv c hc => ?_
    rw [natRep_apply]
    have hsub : ((g : GL ι K) : Matrix ι ι K) *ᵥ v - v =
        (((g : GL ι K) : Matrix ι ι K) - 1) *ᵥ v := by
      rw [sub_mulVec, one_mulVec]
    rw [hsub, mulVec, dotProduct]
    refine Finset.sum_eq_zero fun a _ => ?_
    by_cases hca : ℓ c < ℓ a
    · rw [hv a (by omega), mul_zero]
    · rw [Matrix.sub_apply, h c a hca, sub_self, zero_mul]

theorem flagStab_natRep_apply_eq_zero {H : Subgroup (GL ι K)} {ℓ : ι → ℕ} {g : H}
    (hg : g ∈ flagStab (natRep H) (stdFlag ℓ)) {c a : ι} (h : ℓ a < ℓ c) :
    ((g : GL ι K) : Matrix ι ι K) c a = 0 := by
  have hmem : (Pi.single a (1 : K) : ι → K) ∈ stdFlag ℓ (ℓ a + 1) :=
    single_mem_stdFlag.mpr (Nat.lt_succ_self _)
  have h1 := (hg (ℓ a + 1) _ hmem).1 c h
  rwa [natRep_apply, mulVec_single_one, col_apply] at h1

theorem flagMap_natRep_apply {H : Subgroup (GL ι K)} (g : H) (F : ℕ → Submodule K (ι → K))
    (k : ℕ) : GGOppRad.flagMap (natRep H) g F k =
      (F k).map (Matrix.mulVecLin ((g : GL ι K) : Matrix ι ι K)) := by
  unfold GGOppRad.flagMap
  congr 1

end NatRep

section Symplectic

variable {n : ℕ} {K : Type} [Field K]

@[expose] def IsSpLevel (M : ℕ) (ℓ : Fin n ⊕ Fin n → ℕ) : Prop :=
  ∀ i, ℓ (Sum.inl i) + ℓ (Sum.inr i) = M

theorem IsSpLevel.add_swap {M : ℕ} {ℓ : Fin n ⊕ Fin n → ℕ} (h : IsSpLevel M ℓ)
    (a : Fin n ⊕ Fin n) : ℓ a + ℓ (Sum.swap a) = M := by
  rcases a with i | i
  · exact h i
  · rw [Sum.swap_inr, add_comm]
    exact h i

theorem IsSpLevel.le {M : ℕ} {ℓ : Fin n ⊕ Fin n → ℕ} (h : IsSpLevel M ℓ) (a : Fin n ⊕ Fin n) :
    ℓ a ≤ M := by
  have := h.add_swap a
  omega

theorem IsSpLevel.comp_swap {M : ℕ} {ℓ : Fin n ⊕ Fin n → ℕ} (h : IsSpLevel M ℓ) :
    IsSpLevel M (ℓ ∘ Sum.swap) := fun i => by
  simp only [Function.comp_apply, Sum.swap_inl, Sum.swap_inr]
  rw [add_comm]
  exact h i

variable (n K) in
theorem spJ_mulVec_inl (v : Fin n ⊕ Fin n → K) (i : Fin n) :
    (spJ n K *ᵥ v) (Sum.inl i) = v (Sum.inr i) := by
  simp [spJ, fromBlocks_mulVec]

variable (n K) in
theorem spJ_mulVec_inr (v : Fin n ⊕ Fin n → K) (i : Fin n) :
    (spJ n K *ᵥ v) (Sum.inr i) = -v (Sum.inl i) := by
  simp [spJ, fromBlocks_mulVec, neg_mulVec, one_mulVec]

theorem spJ_mulVec_eq_zero_iff (v : Fin n ⊕ Fin n → K) (a : Fin n ⊕ Fin n) :
    (spJ n K *ᵥ v) a = 0 ↔ v (Sum.swap a) = 0 := by
  rcases a with i | i
  · rw [spJ_mulVec_inl, Sum.swap_inl]
  · rw [spJ_mulVec_inr, Sum.swap_inr, neg_eq_zero]

theorem spForm_single (a : Fin n ⊕ Fin n) (v : Fin n ⊕ Fin n → K) :
    (spForm n K).β (Pi.single a 1) v = (spJ n K *ᵥ v) a := by
  rw [spForm_β, single_dotProduct, one_mul]

theorem isSelfDual_stdFlag {M : ℕ} {ℓ : Fin n ⊕ Fin n → ℕ} (h : IsSpLevel M ℓ) :
    IsSelfDual (spForm n K) (stdFlag ℓ) (M + 1) := by
  refine ⟨stdFlag_mono ℓ, stdFlag_zero ℓ, fun k hk => stdFlag_eq_top fun a => by
    have := h.le a
    omega, fun k hk => ?_⟩
  ext v
  constructor
  · intro hv b hb
    have h1 := hv (Pi.single (Sum.swap b) 1) (single_mem_stdFlag.mpr (by
      have := h.add_swap b
      omega))
    rw [spForm_single, spJ_mulVec_eq_zero_iff, Sum.swap_swap] at h1
    exact h1
  · intro hv w hw
    rw [spForm_β, dotProduct]
    refine Finset.sum_eq_zero fun a _ => ?_
    by_cases ha : ℓ a < k
    · rw [(spJ_mulVec_eq_zero_iff v a).mpr (hv _ (by
        have := h.add_swap a
        omega)), mul_zero]
    · rw [hw a (not_lt.mp ha), zero_mul]

end Symplectic

section SpGroup

variable (n : ℕ) (K : Type) [Field K]

theorem spForm_spJ_mulVec (u v : Fin n ⊕ Fin n → K) :
    (spForm n K).β (spJ n K *ᵥ u) (spJ n K *ᵥ v) = (spForm n K).β u v := by
  have h1 : ∀ w : Fin n ⊕ Fin n → K, (spJ n K *ᵥ w) ∘ Sum.inl = w ∘ Sum.inr :=
    fun w => funext fun i => spJ_mulVec_inl n K w i
  have h2 : ∀ w : Fin n ⊕ Fin n → K, (spJ n K *ᵥ w) ∘ Sum.inr = -(w ∘ Sum.inl) :=
    fun w => funext fun i => spJ_mulVec_inr n K w i
  rw [spForm_β, spForm_β, dotProduct_spJ_mulVec, dotProduct_spJ_mulVec, h1, h1, h2, h2,
    dotProduct_neg, neg_dotProduct]
  ring

@[expose] noncomputable def spJ' : StatedSp n K :=
  (exists_natRep_eq_of_isometry n K (Matrix.mulVecLin (spJ n K))
    fun u v => by simpa using spForm_spJ_mulVec n K u v).choose

theorem natRep_spJ' (v : Fin n ⊕ Fin n → K) :
    natRep (StatedSp n K) (spJ' n K) v = spJ n K *ᵥ v := by
  have := (exists_natRep_eq_of_isometry n K (Matrix.mulVecLin (spJ n K))
    fun u v => by simpa using spForm_spJ_mulVec n K u v).choose_spec v
  rw [spJ', this, Matrix.mulVecLin_apply]

theorem natRep_injective_apply {H : Subgroup (GL (Fin n ⊕ Fin n) K)} (g : H) :
    Function.Injective (natRep H g) :=
  fun x y hxy => by
    simpa only [GGOppRad.rep_inv_apply_rep] using congrArg (natRep H g⁻¹) hxy

theorem flagMap_spJ' (ℓ : Fin n ⊕ Fin n → ℕ) :
    GGOppRad.flagMap (natRep (StatedSp n K)) (spJ' n K) (stdFlag ℓ) =
      stdFlag (ℓ ∘ Sum.swap) := by
  funext k
  have hle : GGOppRad.flagMap (natRep (StatedSp n K)) (spJ' n K) (stdFlag ℓ) k ≤
      stdFlag (ℓ ∘ Sum.swap) k := by
    rintro _ ⟨w, hw, rfl⟩ a ha
    change (natRep (StatedSp n K) (spJ' n K) w) a = 0
    rw [natRep_spJ']
    exact (spJ_mulVec_eq_zero_iff w a).mpr (hw _ ha)
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have e1 : Module.finrank K ((stdFlag (K := K) ℓ k).map (natRep (StatedSp n K) (spJ' n K))) =
      Module.finrank K (stdFlag (K := K) ℓ k) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
      (natRep_injective_apply n K (spJ' n K)) _)).symm
  change Module.finrank K ((stdFlag (K := K) ℓ k).map (natRep (StatedSp n K) (spJ' n K))) = _
  rw [e1, finrank_stdFlag, finrank_stdFlag]
  exact Fintype.card_congr ((Equiv.sumComm (Fin n) (Fin n)).subtypeEquiv fun a => by
    simp [Function.comp_apply])

@[expose] noncomputable def spU (ℓ : Fin n ⊕ Fin n → ℕ) : Subgroup (StatedSp n K) :=
  flagKernel (natRep (StatedSp n K)) (stdFlag ℓ)

@[expose] noncomputable def spP (ℓ : Fin n ⊕ Fin n → ℕ) : Subgroup (StatedSp n K) :=
  flagStab (natRep (StatedSp n K)) (stdFlag ℓ)

theorem spU_comp_swap (ℓ : Fin n ⊕ Fin n → ℕ) :
    spU n K (ℓ ∘ Sum.swap) = (spU n K ℓ).map (MulAut.conj (spJ' n K)).toMonoidHom := by
  rw [spU, spU, ← GGOppRad.flagKernel_flagMap, flagMap_spJ']

theorem card_spU_comp_swap (ℓ : Fin n ⊕ Fin n → ℕ) :
    Nat.card (spU n K (ℓ ∘ Sum.swap)) = Nat.card (spU n K ℓ) := by
  rw [spU_comp_swap]
  exact Subgroup.card_map_of_injective (MulAut.conj _).injective

theorem mem_normalizer_top {G : Type*} [Group G] (x : G) :
    x ∈ Subgroup.normalizer ((⊤ : Subgroup G) : Set G) :=
  Subgroup.mem_normalizer_iff.mpr fun _ =>
    ⟨fun _ => Subgroup.mem_top _, fun _ => Subgroup.mem_top _⟩

theorem radicalTwo_spU_comp_swap {ℓ : Fin n ⊕ Fin n → ℕ} (h : GGRadicalTwo ⊤ (spU n K ℓ)) :
    GGRadicalTwo ⊤ (spU n K (ℓ ∘ Sum.swap)) := by
  rw [spU_comp_swap]
  exact h.map_conj (mem_normalizer_top _)

variable {n K}

theorem mem_spU_iff [Finite K] {ℓ : Fin n ⊕ Fin n → ℕ} {g : StatedSp n K} :
    g ∈ spU n K ℓ ↔ ∀ c a, ¬ ℓ c < ℓ a →
      ((g : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) c a =
        (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) c a :=
  mem_flagKernel_natRep_iff

theorem mem_spU_comp_swap_iff [Finite K] {M : ℕ} {ℓ : Fin n ⊕ Fin n → ℕ} (h : IsSpLevel M ℓ)
    {g : StatedSp n K} :
    g ∈ spU n K (ℓ ∘ Sum.swap) ↔ ∀ c a, ¬ ℓ a < ℓ c →
      ((g : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) c a =
        (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) c a := by
  have key : ∀ c a, (ℓ ∘ Sum.swap) c < (ℓ ∘ Sum.swap) a ↔ ℓ a < ℓ c := by
    intro c a
    have := h.add_swap c
    have := h.add_swap a
    simp only [Function.comp_apply]
    omega
  rw [mem_spU_iff]
  simp only [key]

theorem spU_comp_swap_inf_spP [Finite K] {M : ℕ} {ℓ : Fin n ⊕ Fin n → ℕ} (h : IsSpLevel M ℓ) :
    spU n K (ℓ ∘ Sum.swap) ⊓ spP n K ℓ = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg => Subtype.ext (Units.ext ?_)
  ext c a
  rw [Subgroup.coe_one, Units.val_one]
  by_cases hac : ℓ a < ℓ c
  · rw [flagStab_natRep_apply_eq_zero hg.2 hac,
      Matrix.one_apply_ne (fun hca => by subst hca; exact lt_irrefl _ hac)]
  · exact (mem_spU_comp_swap_iff h).mp hg.1 c a hac

theorem exists_transvection (x : Fin n ⊕ Fin n → K) :
    ∃ h : StatedSp n K, ∀ v, natRep (StatedSp n K) h v = v + (spForm n K).β x v • x :=
  exists_natRep_eq_of_isometry n K
    { toFun := fun v => v + (spForm n K).β x v • x
      map_add' := fun u v => by
        simp only [(spForm n K).add_right, add_smul]
        abel
      map_smul' := fun a v => by
        simp only [(spForm n K).smul_right, RingHom.id_apply, smul_add, smul_smul] }
    ((spForm n K).β_transvection rfl (spForm_self n K) x)

theorem exists_siegel {x y : Fin n ⊕ Fin n → K} (hxy : (spForm n K).β x y = 0) :
    ∃ h : StatedSp n K, ∀ v, natRep (StatedSp n K) h v =
      v + (spForm n K).β x v • y + (spForm n K).β y v • x :=
  exists_natRep_eq_of_isometry n K
    { toFun := fun v => v + (spForm n K).β x v • y + (spForm n K).β y v • x
      map_add' := fun u v => by
        simp only [(spForm n K).add_right, add_smul]
        abel
      map_smul' := fun a v => by
        simp only [(spForm n K).smul_right, RingHom.id_apply, smul_add, smul_smul] }
    ((spForm n K).β_siegel rfl (spForm_self n K) hxy)

end SpGroup

end GGOppRadSpU

end CFSG.StandardType
