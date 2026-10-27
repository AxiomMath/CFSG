module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUStd
public import CFSG.LieType.Universal.Unitary.Basic
public import CFSG.LieType.BorelTits.UnitaryForm

public section

namespace CFSG.StandardType

namespace GGOppRadSpU

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary GGOppRad

variable {F : Type} [Field F] (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c)

theorem antidiag_mulVec_apply {n : ℕ} (v : Fin n → F) (i : Fin n) :
    (antidiag n *ᵥ v) i = v (Fin.rev i) := by
  simp [antidiag, mulVec, dotProduct]

include hσ in
theorem sum_σ_mul_rev_symm {n : ℕ} (u v : Fin n → F) :
    ∑ i, σ (v i) * u (Fin.rev i) = σ (∑ i, σ (u i) * v (Fin.rev i)) := by
  rw [map_sum]
  simp only [map_mul, hσ]
  rw [← Equiv.sum_comp (Fin.revPerm (n := n))]
  exact Finset.sum_congr rfl fun i _ => by simp [Fin.revPerm_apply, mul_comm]

@[expose] def suForm (n : ℕ) : ReflForm F (Fin n → F) where
  σ := σ
  β u v := ∑ i, σ (u i) * v (Fin.rev i)
  add_left u u' v := by
    simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  smul_left c u v := by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc, Finset.mul_sum]
  add_right u v v' := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  smul_right c u v := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  refl u v h := by
    rw [sum_σ_mul_rev_symm σ hσ, h, map_zero]
  nondeg u h := by
    funext i
    have := h (Pi.single (Fin.rev i) 1)
    simp only [Pi.single_apply, Fin.rev_inj, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] at this
    exact (map_eq_zero_iff _ σ.injective).mp this

theorem suForm_β {n : ℕ} (u v : Fin n → F) :
    (suForm σ hσ n).β u v = ∑ i, σ (u i) * v (Fin.rev i) := rfl

theorem suForm_σ {n : ℕ} : (suForm σ hσ n).σ = σ := rfl

theorem suForm_symm {n : ℕ} (u v : Fin n → F) :
    (suForm σ hσ n).β v u = σ ((suForm σ hσ n).β u v) :=
  sum_σ_mul_rev_symm σ hσ u v

theorem suForm_β_eq {n : ℕ} (u v : Fin n → F) :
    (suForm σ hσ n).β u v = (σ ∘ u) ⬝ᵥ (antidiag n *ᵥ v) := by
  rw [suForm_β, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by rw [antidiag_mulVec_apply]; rfl

theorem suForm_single {n : ℕ} (a : Fin n) (v : Fin n → F) :
    (suForm σ hσ n).β (Pi.single a 1) v = v (Fin.rev a) := by
  rw [suForm_β]
  simp [Pi.single_apply, apply_ite σ]

theorem suForm_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (u v : Fin n → F) :
    (suForm σ hσ n).β (A *ᵥ u) (A *ᵥ v) =
      (σ ∘ u) ⬝ᵥ ((conjTr σ A * antidiag n * A) *ᵥ v) := by
  rw [suForm_β_eq]
  have h1 : (σ ∘ (A *ᵥ u)) = (A.map σ) *ᵥ (σ ∘ u) := by
    funext i
    exact RingHom.map_mulVec (σ : F →+* F) A u i
  rw [h1, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm,
    mulVec_mulVec, mulVec_mulVec, conjTr, Matrix.mul_assoc]

theorem isIsometric_natRep_SU (n : ℕ) :
    IsIsometric (suForm σ hσ n) (natRep (SU σ n)) := by
  intro g u v
  rw [natRep_apply, natRep_apply, suForm_mulVec, (mem_SU.mp g.2).2, ← suForm_β_eq]

theorem exists_SU_of_isometry {n : ℕ} (f : (Fin n → F) →ₗ[F] (Fin n → F))
    (hf : ∀ u v, (suForm σ hσ n).β (f u) (f v) = (suForm σ hσ n).β u v)
    (hdet : (LinearMap.toMatrix' f).det = 1) :
    ∃ g : SU σ n, ∀ v, natRep (SU σ n) g v = f v := by
  set M := LinearMap.toMatrix' f
  have hMv : ∀ v, M *ᵥ v = f v := LinearMap.toMatrix'_mulVec f
  have he : ∀ a : Fin n, (σ ∘ (Pi.single a (1 : F) : Fin n → F)) = Pi.single a 1 := by
    intro a
    funext i
    simp [Pi.single_apply, apply_ite σ]
  have hM : conjTr σ M * antidiag n * M = antidiag n := by
    ext a b
    have h1 := hf (Pi.single a 1) (Pi.single b 1)
    rw [← hMv, ← hMv, suForm_mulVec, suForm_single, he, single_dotProduct, one_mul,
      mulVec_single_one, col_apply] at h1
    rw [h1, antidiag, of_apply, Pi.single_apply]
    by_cases hab : b = Fin.rev a
    · subst hab
      simp
    · have : ¬ Fin.rev a = b := fun h => hab h.symm
      simp [hab, this]
  refine ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero),
    mem_SU.mpr ⟨hdet, hM⟩⟩, fun v => ?_⟩
  rw [natRep_apply]
  exact hMv v

variable {σ hσ}

theorem det_toMatrix'_id_add [CharP F 2] {n : ℕ} {N : Module.End F (Fin n → F)}
    (hN : IsNilpotent N) : (LinearMap.toMatrix' (LinearMap.id + N)).det = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN' : IsNilpotent (LinearMap.toMatrix' N) := by
    obtain ⟨k, hk⟩ := hN
    refine ⟨k, ?_⟩
    have := congrArg LinearMap.toMatrixAlgEquiv' hk
    rwa [map_pow, map_zero] at this
  rw [map_add, LinearMap.toMatrix'_id]
  exact det_one_add_of_isNilpotent 2 hN'

@[expose] def suDual {n : ℕ} (x : Fin n → F) : Module.Dual F (Fin n → F) where
  toFun v := (suForm σ hσ n).β x v
  map_add' := (suForm σ hσ n).add_right x
  map_smul' c v := (suForm σ hσ n).smul_right c x v

theorem suDual_apply {n : ℕ} (x v : Fin n → F) :
    suDual (σ := σ) (hσ := hσ) x v = (suForm σ hσ n).β x v := rfl

omit [Field F] in
theorem ReflForm.β_expand3 {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : ReflForm K V) (u v x y : V) (a b a' b' : K) :
    B.β (u + a • y + b • x) (v + a' • y + b' • x) =
      B.β u v + a' * B.β u y + b' * B.β u x + B.σ a * B.β y v + B.σ a * a' * B.β y y +
        B.σ a * b' * B.β y x + B.σ b * B.β x v + B.σ b * a' * B.β x y +
          B.σ b * b' * B.β x x := by
  simp only [B.add_left, B.add_right, B.smul_left, B.smul_right]
  ring

variable (σ hσ) in
theorem exists_SU_transvection [CharP F 2] {n : ℕ} {x : Fin n → F}
    (hx : (suForm σ hσ n).β x x = 0) :
    ∃ g : SU σ n, ∀ v, natRep (SU σ n) g v = v + (suForm σ hσ n).β x v • x := by
  set B := suForm σ hσ n
  set N : Module.End F (Fin n → F) := (suDual (σ := σ) (hσ := hσ) x).smulRight x with hN
  have hNv : ∀ v, N v = B.β x v • x := fun v => rfl
  have hnil : IsNilpotent N := ⟨2, LinearMap.ext fun v => by
    rw [pow_two, Module.End.mul_apply, hNv, hNv, B.smul_right, hx, mul_zero, zero_smul,
      LinearMap.zero_apply]⟩
  obtain ⟨g, hg⟩ := exists_SU_of_isometry σ hσ (LinearMap.id + N) (fun u v => by
    simp only [LinearMap.add_apply, LinearMap.id_apply, hNv]
    rw [ReflForm.β_add_smul_add_smul, hx, suForm_σ, suForm_symm σ hσ x u]
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination (σ (B.β x u) * B.β x v) * h2) (det_toMatrix'_id_add hnil)
  exact ⟨g, fun v => by rw [hg]; rfl⟩

variable (σ hσ) in
theorem exists_SU_eichler [CharP F 2] {n : ℕ} {x y : Fin n → F}
    (hx : (suForm σ hσ n).β x x = 0) (hxy : (suForm σ hσ n).β x y = 0) {c : F}
    (hc : c + σ c = (suForm σ hσ n).β y y) :
    ∃ g : SU σ n, ∀ v, natRep (SU σ n) g v =
      v + (suForm σ hσ n).β x v • (y + c • x) + (suForm σ hσ n).β y v • x := by
  set B := suForm σ hσ n
  have hyx : B.β y x = 0 := by rw [suForm_symm σ hσ x y, hxy, map_zero]
  set N : Module.End F (Fin n → F) := (suDual (σ := σ) (hσ := hσ) x).smulRight (y + c • x) +
    (suDual (σ := σ) (hσ := hσ) y).smulRight x with hN
  have hNv : ∀ v, N v = B.β x v • (y + c • x) + B.β y v • x := fun v => rfl
  have hNx : N x = 0 := by rw [hNv, hx, hyx, zero_smul, zero_smul, add_zero]
  have hβx : ∀ v, B.β x (N v) = 0 := by
    intro v
    rw [hNv, B.add_right, B.smul_right, B.smul_right, B.add_right, B.smul_right, hx, hxy]
    ring
  have hnil : IsNilpotent N := ⟨3, LinearMap.ext fun v => by
    have h2 : N (N v) = (B.β x v * B.β y y) • x := by
      rw [hNv (N v), hβx, zero_smul, zero_add, hNv v, B.add_right, B.smul_right, B.smul_right,
        B.add_right, B.smul_right, hyx]
      congr 1
      ring
    rw [pow_succ, pow_two, Module.End.mul_apply, Module.End.mul_apply, h2, map_smul, hNx,
      smul_zero, LinearMap.zero_apply]⟩
  have hE : ∀ w, (LinearMap.id + N : Module.End F (Fin n → F)) w =
      w + B.β x w • y + (c * B.β x w + B.β y w) • x :=
    fun w => by
      rw [LinearMap.add_apply, LinearMap.id_apply, hNv, smul_add, smul_smul, add_smul,
        mul_comm c]
      abel
  obtain ⟨g, hg⟩ := exists_SU_of_isometry σ hσ (LinearMap.id + N) (fun u v => by
    rw [hE, hE, ReflForm.β_expand3, hx, hxy, hyx, suForm_σ, suForm_symm σ hσ x u,
      suForm_symm σ hσ y u, map_add, map_mul, ← hc]
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination (B.β x v * σ (B.β y u) + B.β y v * σ (B.β x u) +
      c * B.β x v * σ (B.β x u) + σ c * σ (B.β x u) * B.β x v) * h2)
    (det_toMatrix'_id_add hnil)
  exact ⟨g, fun v => by rw [hg, LinearMap.add_apply, LinearMap.id_apply, hNv, add_assoc]⟩

@[expose] def IsSULevel {n : ℕ} (M : ℕ) (ℓ : Fin n → ℕ) : Prop :=
  ∀ a, ℓ a + ℓ (Fin.rev a) = M

theorem IsSULevel.le {n M : ℕ} {ℓ : Fin n → ℕ} (h : IsSULevel M ℓ) (a : Fin n) : ℓ a ≤ M := by
  have := h a
  omega

theorem IsSULevel.comp_rev {n M : ℕ} {ℓ : Fin n → ℕ} (h : IsSULevel M ℓ) :
    IsSULevel M (ℓ ∘ Fin.rev) := fun a => by
  simp only [Function.comp_apply, Fin.rev_rev]
  rw [add_comm]
  exact h a

variable (σ hσ) in
theorem isSelfDual_stdFlag_su {n M : ℕ} {ℓ : Fin n → ℕ} (h : IsSULevel M ℓ) :
    IsSelfDual (suForm σ hσ n) (stdFlag ℓ) (M + 1) := by
  refine ⟨stdFlag_mono ℓ, stdFlag_zero ℓ, fun k hk => stdFlag_eq_top fun a => by
    have := h.le a
    omega, fun k hk => ?_⟩
  ext v
  constructor
  · intro hv b hb
    have h1 := hv (Pi.single (Fin.rev b) 1) (single_mem_stdFlag.mpr (by
      have := h (Fin.rev b)
      rw [Fin.rev_rev] at this
      omega))
    rw [suForm_single, Fin.rev_rev] at h1
    exact h1
  · intro hv w hw
    rw [suForm_β]
    refine Finset.sum_eq_zero fun a _ => ?_
    by_cases ha : ℓ a < k
    · rw [hv _ (by
        have := h a
        omega), mul_zero]
    · rw [hw a (not_lt.mp ha), map_zero, zero_mul]

variable (σ hσ) in
theorem perp_stdFlag_su {n M : ℕ} {ℓ : Fin n → ℕ} (h : IsSULevel M ℓ) (k : ℕ) :
    (suForm σ hσ n).perp (stdFlag ℓ k) = stdFlag ℓ (M + 1 - k) := by
  rcases le_total k (M + 1) with hk | hk
  · exact (isSelfDual_stdFlag_su σ hσ h).perp k hk
  · rw [(isSelfDual_stdFlag_su σ hσ h).top k hk, (suForm σ hσ n).perp_top,
      Nat.sub_eq_zero_of_le hk, stdFlag_zero]

theorem antidiag_mulVec_antidiag_mulVec {n : ℕ} (v : Fin n → F) :
    antidiag n *ᵥ (antidiag n *ᵥ v) = v := by
  funext i
  rw [antidiag_mulVec_apply, antidiag_mulVec_apply, Fin.rev_rev]

theorem antidiag_mul_antidiag (n : ℕ) : (antidiag n : Matrix (Fin n) (Fin n) F) * antidiag n = 1 :=
  Matrix.ext_of_mulVec_single fun i => by
    rw [← mulVec_mulVec, antidiag_mulVec_antidiag_mulVec, one_mulVec]

theorem conjTr_antidiag (n : ℕ) :
    conjTr σ (antidiag n : Matrix (Fin n) (Fin n) F) = antidiag n := by
  ext a b
  simp only [conjTr, transpose_apply, map_apply, antidiag, of_apply]
  by_cases h : a = Fin.rev b
  · have h' : b = Fin.rev a := by rw [h, Fin.rev_rev]
    rw [ite_eq_left h, ite_eq_left h', map_one]
  · have h' : ¬ b = Fin.rev a := fun h' => h (by rw [h', Fin.rev_rev])
    rw [ite_eq_right h, ite_eq_right h', map_zero]

theorem det_antidiag [CharP F 2] (n : ℕ) : (antidiag n : Matrix (Fin n) (Fin n) F).det = 1 := by
  have h : (antidiag n : Matrix (Fin n) (Fin n) F).det *
      (antidiag n : Matrix (Fin n) (Fin n) F).det = 1 := by
    rw [← det_mul, antidiag_mul_antidiag, det_one]
  have h3 : ((antidiag n : Matrix (Fin n) (Fin n) F).det - 1) ^ 2 = 0 := by
    calc ((antidiag n : Matrix (Fin n) (Fin n) F).det - 1) ^ 2 =
          ((antidiag n : Matrix (Fin n) (Fin n) F).det *
            (antidiag n : Matrix (Fin n) (Fin n) F).det - 1) -
              2 * ((antidiag n : Matrix (Fin n) (Fin n) F).det - 1) := by ring
      _ = 0 := by rw [h, CharTwo.two_eq_zero]; ring
  exact sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num)).mp h3)

variable (σ) in
@[expose] noncomputable def suJ [CharP F 2] (n : ℕ) : SU σ n :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (antidiag n) (by rw [det_antidiag]; exact one_ne_zero),
    mem_SU.mpr ⟨det_antidiag n, by
      change conjTr σ (antidiag n) * antidiag n * antidiag n = antidiag n
      rw [conjTr_antidiag, antidiag_mul_antidiag, Matrix.one_mul]⟩⟩

theorem natRep_suJ [CharP F 2] {n : ℕ} (v : Fin n → F) :
    natRep (SU σ n) (suJ σ n) v = antidiag n *ᵥ v := by
  rw [natRep_apply]
  rfl

theorem natRep_injective_apply_su {n : ℕ} (g : SU σ n) :
    Function.Injective (natRep (SU σ n) g) :=
  fun x y hxy => by
    simpa only [GGOppRad.rep_inv_apply_rep] using congrArg (natRep (SU σ n) g⁻¹) hxy

theorem flagMap_suJ [CharP F 2] {n : ℕ} (ℓ : Fin n → ℕ) :
    GGOppRad.flagMap (natRep (SU σ n)) (suJ σ n) (stdFlag ℓ) = stdFlag (ℓ ∘ Fin.rev) := by
  funext k
  have hle : GGOppRad.flagMap (natRep (SU σ n)) (suJ σ n) (stdFlag ℓ) k ≤
      stdFlag (ℓ ∘ Fin.rev) k := by
    rintro _ ⟨w, hw, rfl⟩ a ha
    change (natRep (SU σ n) (suJ σ n) w) a = 0
    rw [natRep_suJ, antidiag_mulVec_apply]
    exact hw _ ha
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have e1 : Module.finrank F ((stdFlag (K := F) ℓ k).map (natRep (SU σ n) (suJ σ n))) =
      Module.finrank F (stdFlag (K := F) ℓ k) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
      (natRep_injective_apply_su (suJ σ n)) _)).symm
  change Module.finrank F ((stdFlag (K := F) ℓ k).map (natRep (SU σ n) (suJ σ n))) = _
  rw [e1, finrank_stdFlag, finrank_stdFlag]
  exact Fintype.card_congr ((Fin.revPerm (n := n)).subtypeEquiv fun a => by
    simp [Function.comp_apply, Fin.revPerm_apply])

variable (σ) in
@[expose] noncomputable def suU {n : ℕ} (ℓ : Fin n → ℕ) : Subgroup (SU σ n) :=
  flagKernel (natRep (SU σ n)) (stdFlag ℓ)

variable (σ) in
@[expose] noncomputable def suP {n : ℕ} (ℓ : Fin n → ℕ) : Subgroup (SU σ n) :=
  flagStab (natRep (SU σ n)) (stdFlag ℓ)

theorem suU_comp_rev [CharP F 2] {n : ℕ} (ℓ : Fin n → ℕ) :
    suU σ (ℓ ∘ Fin.rev) = (suU σ ℓ).map (MulAut.conj (suJ σ n)).toMonoidHom := by
  rw [suU, suU, ← GGOppRad.flagKernel_flagMap, flagMap_suJ]

theorem card_suU_comp_rev [CharP F 2] {n : ℕ} (ℓ : Fin n → ℕ) :
    Nat.card (suU σ (ℓ ∘ Fin.rev)) = Nat.card (suU σ ℓ) := by
  rw [suU_comp_rev]
  exact Subgroup.card_map_of_injective (MulAut.conj _).injective

theorem radicalTwo_suU_comp_rev [CharP F 2] {n : ℕ} {ℓ : Fin n → ℕ}
    (h : GGRadicalTwo ⊤ (suU σ ℓ)) : GGRadicalTwo ⊤ (suU σ (ℓ ∘ Fin.rev)) := by
  rw [suU_comp_rev]
  exact h.map_conj (mem_normalizer_top _)

theorem mem_suU_iff [Finite F] {n : ℕ} {ℓ : Fin n → ℕ} {g : SU σ n} :
    g ∈ suU σ ℓ ↔ ∀ c a, ¬ ℓ c < ℓ a →
      ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) c a = (1 : Matrix (Fin n) (Fin n) F) c a :=
  mem_flagKernel_natRep_iff

theorem mem_suU_comp_rev_iff [Finite F] {n M : ℕ} {ℓ : Fin n → ℕ} (h : IsSULevel M ℓ)
    {g : SU σ n} :
    g ∈ suU σ (ℓ ∘ Fin.rev) ↔ ∀ c a, ¬ ℓ a < ℓ c →
      ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) c a = (1 : Matrix (Fin n) (Fin n) F) c a := by
  have key : ∀ c a, (ℓ ∘ Fin.rev) c < (ℓ ∘ Fin.rev) a ↔ ℓ a < ℓ c := by
    intro c a
    have := h c
    have := h a
    simp only [Function.comp_apply]
    omega
  rw [mem_suU_iff]
  simp only [key]

theorem suU_comp_rev_inf_suP [Finite F] {n M : ℕ} {ℓ : Fin n → ℕ} (h : IsSULevel M ℓ) :
    suU σ (ℓ ∘ Fin.rev) ⊓ suP σ ℓ = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg => Subtype.ext (Units.ext ?_)
  ext c a
  rw [Subgroup.coe_one, Units.val_one]
  by_cases hac : ℓ a < ℓ c
  · rw [flagStab_natRep_apply_eq_zero hg.2 hac,
      Matrix.one_apply_ne (fun hca => by subst hca; exact lt_irrefl _ hac)]
  · exact (mem_suU_comp_rev_iff h).mp hg.1 c a hac

end GGOppRadSpU

end CFSG.StandardType
