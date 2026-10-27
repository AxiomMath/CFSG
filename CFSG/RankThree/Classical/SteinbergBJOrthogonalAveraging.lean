module

public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.RankThree.Classical

open Module TensorProduct

section Averaging

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {Γ : Type*} [Group Γ]

@[expose] noncomputable def avgOp (ρ : Γ →* Module.End K V) (D : Subgroup Γ) [Fintype D] :
    Module.End K V :=
  (Fintype.card D : K)⁻¹ • ∑ d : D, ρ d

variable {ρ : Γ →* Module.End K V}

theorem avgOp_def (D : Subgroup Γ) [Fintype D] :
    avgOp ρ D = (Fintype.card D : K)⁻¹ • ∑ d : D, ρ d :=
  rfl

theorem mul_avgOp {D : Subgroup Γ} [Fintype D] {g : Γ} (hg : g ∈ D) :
    ρ g * avgOp ρ D = avgOp ρ D := by
  rw [avgOp, mul_smul_comm, Finset.mul_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft (⟨g, hg⟩ : D)) _ _ fun d => by
    rw [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul]

theorem avgOp_mul {D : Subgroup Γ} [Fintype D] {g : Γ} (hg : g ∈ D) :
    avgOp ρ D * ρ g = avgOp ρ D := by
  rw [avgOp, smul_mul_assoc, Finset.sum_mul]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight (⟨g, hg⟩ : D)) _ _ fun d => by
    rw [Equiv.coe_mulRight, Subgroup.coe_mul, map_mul]

theorem avgOp_mul_avgOp_of_le {D E : Subgroup Γ} [Fintype D] [Fintype E] (h : D ≤ E)
    (hD : (Fintype.card D : K) ≠ 0) : avgOp ρ D * avgOp ρ E = avgOp ρ E := by
  rw [avgOp_def D, smul_mul_assoc, Finset.sum_mul,
    Finset.sum_congr rfl fun d _ => mul_avgOp (ρ := ρ) (h d.2), Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hD, one_smul]

theorem avgOp_mul_avgOp_of_le' {D E : Subgroup Γ} [Fintype D] [Fintype E] (h : D ≤ E)
    (hD : (Fintype.card D : K) ≠ 0) : avgOp ρ E * avgOp ρ D = avgOp ρ E := by
  rw [avgOp_def D, mul_smul_comm, Finset.mul_sum,
    Finset.sum_congr rfl fun d _ => avgOp_mul (ρ := ρ) (h d.2), Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hD, one_smul]

theorem avgOp_apply_of_fixed {D : Subgroup Γ} [Fintype D] (hD : (Fintype.card D : K) ≠ 0)
    {v : V} (hv : ∀ d ∈ D, ρ d v = v) : avgOp ρ D v = v := by
  rw [avgOp, LinearMap.smul_apply, LinearMap.sum_apply]
  simp_rw [fun d : D => hv d d.2]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul K, smul_smul,
    inv_mul_cancel₀ hD, one_smul]

theorem apply_avgOp {D : Subgroup Γ} [Fintype D] {g : Γ} (hg : g ∈ D) (v : V) :
    ρ g (avgOp ρ D v) = avgOp ρ D v := by
  rw [← Module.End.mul_apply, mul_avgOp hg]

theorem avgOp_mul_avgOp_eq_top [Fintype Γ] {D E : Subgroup Γ} [Fintype D] [Fintype E]
    [Fintype (⊤ : Subgroup Γ)] (hDE : D ⊓ E = ⊥)
    (hcard : Nat.card D * Nat.card E = Nat.card Γ) :
    avgOp ρ D * avgOp ρ E = avgOp ρ (⊤ : Subgroup Γ) := by
  let φ : D × E → (⊤ : Subgroup Γ) := fun x => ⟨(x.1 : Γ) * x.2, trivial⟩
  have hinj : Function.Injective φ := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    have h' : (a : Γ) * b = c * d := congrArg Subtype.val h
    have h1 : (c : Γ)⁻¹ * a = (d : Γ) * (b : Γ)⁻¹ := by
      calc (c : Γ)⁻¹ * a = (c : Γ)⁻¹ * ((a : Γ) * b) * (b : Γ)⁻¹ := by group
        _ = (c : Γ)⁻¹ * ((c : Γ) * d) * (b : Γ)⁻¹ := by rw [h']
        _ = (d : Γ) * (b : Γ)⁻¹ := by group
    have hmem : (c : Γ)⁻¹ * a ∈ D ⊓ E :=
      ⟨D.mul_mem (D.inv_mem c.2) a.2, h1 ▸ E.mul_mem d.2 (E.inv_mem b.2)⟩
    rw [hDE, Subgroup.mem_bot] at hmem
    have hac : (a : Γ) = c := by
      rw [← mul_inv_cancel_left (c : Γ) a, hmem, mul_one]
    have hbd : (b : Γ) = d := by
      rw [hac] at h'
      exact mul_left_cancel h'
    exact Prod.ext (Subtype.ext hac) (Subtype.ext hbd)
  have hbij : Function.Bijective φ := by
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩
    rw [Fintype.card_prod, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card, hcard, Subgroup.card_top]
  have hcardK : (Fintype.card (⊤ : Subgroup Γ) : K) =
      (Fintype.card D : K) * Fintype.card E := by
    rw [← Nat.cast_mul, ← Fintype.card_prod, Fintype.card_of_bijective hbij]
  rw [avgOp_def D, avgOp_def E, avgOp_def, smul_mul_smul_comm, Finset.sum_mul_sum, hcardK,
    mul_inv]
  congr 1
  rw [← Finset.sum_product']
  exact Fintype.sum_bijective φ hbij _ _ fun x => by rw [← map_mul]

theorem bilin_avgOp (B : LinearMap.BilinForm K V) (hB : ∀ g u w, B (ρ g u) (ρ g w) = B u w)
    (D : Subgroup Γ) [Fintype D] (u v : V) : B (avgOp ρ D u) v = B u (avgOp ρ D v) := by
  have h1 : ∀ d : D, B (ρ d u) v = B u (ρ (d⁻¹ : D) v) := fun d => by
    have hv : v = ρ d (ρ (d⁻¹ : D) v) := by
      rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, mul_inv_cancel, map_one,
        Module.End.one_apply]
    conv_lhs => rw [hv]
    exact hB d u _
  rw [avgOp, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.map_smul₂, map_sum,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  congr 1
  rw [Finset.sum_congr rfl fun d _ => h1 d]
  exact Fintype.sum_equiv (Equiv.inv D) _ _ fun d => rfl

end Averaging

section Lines

variable {Γ : Type*} [Group Γ] {p : ℕ}

theorem natCard_zpowers_of_pow (hp : p.Prime) (hexp : ∀ g : Γ, g ^ p = 1) {g : Γ} (hg : g ≠ 1) :
    Nat.card (Subgroup.zpowers g) = p := by
  have : Fact p.Prime := ⟨hp⟩
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (hexp g) hg

theorem eq_zpowers_of_natCard_eq_prime_of_mem [Finite Γ] (hp : p.Prime) (hexp : ∀ g : Γ, g ^ p = 1)
    {M : Subgroup Γ} (hM : Nat.card M = p) {g : Γ} (hg : g ≠ 1) (hgM : g ∈ M) :
    M = Subgroup.zpowers g := by
  symm
  refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hgM) ?_
  rw [hM, natCard_zpowers_of_pow hp hexp hg]

theorem inf_eq_bot_of_natCard_eq_prime [Finite Γ] (hp : p.Prime) (hexp : ∀ g : Γ, g ^ p = 1)
    {M M' : Subgroup Γ} (hM : Nat.card M = p) (hM' : Nat.card M' = p) (h : M ≠ M') :
    M ⊓ M' = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  by_contra hg1
  rw [Subgroup.mem_bot] at hg1
  exact h ((eq_zpowers_of_natCard_eq_prime_of_mem hp hexp hM hg1 hg.1).trans
    (eq_zpowers_of_natCard_eq_prime_of_mem hp hexp hM' hg1 hg.2).symm)

variable [Fintype Γ]

open _root_.Classical in
theorem card_filter_lines (hp : p.Prime) (hexp : ∀ g : Γ, g ^ p = 1) {g : Γ} (hg : g ≠ 1) :
    (Finset.univ.filter fun M : Subgroup Γ => Nat.card M = p ∧ g ∈ M).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨Subgroup.zpowers g, ?_⟩
  ext M
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨hM, hgM⟩
    exact eq_zpowers_of_natCard_eq_prime_of_mem hp hexp hM hg hgM
  · rintro rfl
    exact ⟨natCard_zpowers_of_pow hp hexp hg, Subgroup.mem_zpowers g⟩

open _root_.Classical in
theorem card_subgroups_natCard_eq_prime (hp : p.Prime) (hexp : ∀ g : Γ, g ^ p = 1)
    (hΓ : Nat.card Γ = p ^ 2) :
    (Finset.univ.filter fun M : Subgroup Γ => Nat.card M = p).card = p + 1 := by
  set Ls := Finset.univ.filter fun M : Subgroup Γ => Nat.card M = p
  have h1 : ∑ M ∈ Ls, (Finset.univ.filter fun g : Γ => g ∈ M).card =
      ∑ g : Γ, (Ls.filter fun M => g ∈ M).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have h2 : ∀ M ∈ Ls, (Finset.univ.filter fun g : Γ => g ∈ M).card = p := by
    intro M hM
    rw [← (Finset.mem_filter.mp hM).2, Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  have h3 : ∀ g : Γ, g ≠ 1 → (Ls.filter fun M => g ∈ M).card = 1 := by
    intro g hg
    rw [← card_filter_lines hp hexp hg, Finset.filter_filter]
  have h4 : (Ls.filter fun M => (1 : Γ) ∈ M).card = Ls.card := by
    rw [Finset.filter_true_of_mem fun M _ => M.one_mem]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Γ)), h4,
    Finset.sum_congr rfl fun g hg => h3 g (Finset.ne_of_mem_erase hg), Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, smul_eq_mul, mul_one,
    ← Nat.card_eq_fintype_card, hΓ] at h1
  have hp2 := hp.two_le
  have e2 : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    have := Nat.sq_sub_sq p 1
    rw [one_pow] at this
    rw [this]
  have e3 : Ls.card * p = Ls.card * (p - 1) + Ls.card := by
    conv_lhs => rw [show p = (p - 1) + 1 by omega]
    ring
  have e4 : Ls.card * (p - 1) = (p + 1) * (p - 1) := by omega
  exact Nat.eq_of_mul_eq_mul_right (by omega) e4

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {ρ : Γ →* Module.End K V}

open _root_.Classical in
theorem sum_avgOp_lines (hp : p.Prime) (hexp : ∀ g : Γ, g ^ p = 1) (hΓ : Nat.card Γ = p ^ 2)
    (hpK : (p : K) ≠ 0) :
    ∑ M ∈ Finset.univ.filter (fun M : Subgroup Γ => Nat.card M = p), avgOp ρ M =
      1 + (p : K) • avgOp ρ (⊤ : Subgroup Γ) := by
  set Ls := Finset.univ.filter fun M : Subgroup Γ => Nat.card M = p
  have hsum : ∀ M ∈ Ls, avgOp ρ M = (p : K)⁻¹ • ∑ g ∈ Finset.univ.filter (· ∈ M), ρ g := by
    intro M hM
    rw [avgOp, ← Nat.card_eq_fintype_card, (Finset.mem_filter.mp hM).2]
    congr 1
    exact (Finset.sum_subtype (Finset.univ.filter (· ∈ M)) (fun g => by simp)
      (fun g => ρ g)).symm
  rw [Finset.sum_congr rfl hsum, ← Finset.smul_sum]
  have hswap : ∑ M ∈ Ls, ∑ g ∈ Finset.univ.filter (· ∈ M), ρ g =
      ∑ g : Γ, (Ls.filter fun M => g ∈ M).card • ρ g := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const]
  have h1 : (Ls.filter fun M => (1 : Γ) ∈ M).card = p + 1 := by
    rw [Finset.filter_true_of_mem fun M _ => M.one_mem, card_subgroups_natCard_eq_prime hp hexp hΓ]
  have hrest : ∀ g ∈ Finset.univ.erase (1 : Γ),
      (Ls.filter fun M => g ∈ M).card • ρ g = ρ g := by
    intro g hg
    have hc : (Ls.filter fun M => g ∈ M).card = 1 := by
      rw [Finset.filter_filter]
      exact card_filter_lines hp hexp (Finset.ne_of_mem_erase hg)
    rw [hc, one_smul]
  have htop : avgOp ρ (⊤ : Subgroup Γ) =
      ((p : K) ^ 2)⁻¹ • (1 + ∑ g ∈ Finset.univ.erase (1 : Γ), ρ g) := by
    rw [avgOp, ← Nat.card_eq_fintype_card, Subgroup.card_top, hΓ, Nat.cast_pow]
    congr 1
    rw [← map_one ρ, Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Γ))]
    exact Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun g => Subgroup.mem_top g) _ _
      fun _ => rfl
  rw [hswap, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Γ)), h1,
    Finset.sum_congr rfl hrest, htop, map_one, smul_smul, ← Nat.cast_smul_eq_nsmul K]
  have hc : (p : K) * ((p : K) ^ 2)⁻¹ = (p : K)⁻¹ := by field_simp
  rw [hc, smul_add, smul_add, smul_smul, Nat.cast_add, Nat.cast_one, inv_mul_eq_div, add_div,
    div_self hpK, one_div, add_smul, one_smul]
  abel

end Lines

section DirectSum

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem finrank_biSup_of_iSupIndep [FiniteDimensional K V] {ι : Type*} [DecidableEq ι]
    {W : ι → Submodule K V} (hW : iSupIndep W) (S : Finset ι) :
    finrank K ↥(⨆ i ∈ S, W i) = ∑ i ∈ S, finrank K (W i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
    rw [Finset.sum_insert hj, Finset.iSup_insert, ← ih]
    have hdisj : Disjoint (W j) (⨆ i ∈ S, W i) := hW.disjoint_biSup hj
    rw [← Submodule.finrank_sup_add_finrank_inf_eq, hdisj.eq_bot, finrank_bot, add_zero]

theorem isInternal_range_of_orthogonal_idempotents {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Module.End K V) (hidem : ∀ i, f i * f i = f i)
    (horth : ∀ i j, i ≠ j → f i * f j = 0) (hsum : ∑ i, f i = 1) :
    DirectSum.IsInternal fun i => LinearMap.range (f i) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    intro v hv hv'
    obtain ⟨u, rfl⟩ := hv
    have hle : ⨆ j, ⨆ (_ : j ≠ i), LinearMap.range (f j) ≤ LinearMap.ker (f i) :=
      iSup₂_le fun j hj => by
        rintro _ ⟨w, rfl⟩
        rw [LinearMap.mem_ker, ← Module.End.mul_apply, horth i j (Ne.symm hj),
          LinearMap.zero_apply]
    have h1 := hle hv'
    rw [LinearMap.mem_ker, ← Module.End.mul_apply, hidem] at h1
    exact h1
  · rw [eq_top_iff]
    intro v _
    have hv : v = ∑ i, f i v := by rw [← LinearMap.sum_apply, hsum, Module.End.one_apply]
    rw [hv]
    exact Submodule.sum_mem_iSup fun i => ⟨v, rfl⟩

end DirectSum

section BaseChange

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (L : Type*) [Field L]
  [Algebra K L]

theorem finrank_submodule_baseChange [FiniteDimensional K V] (W : Submodule K V) :
    finrank L (W.baseChange L) = finrank K W := by
  have hinj : Function.Injective (W.subtype.baseChange L) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ W.injective_subtype
  rw [Submodule.baseChange, LinearMap.finrank_range_of_inj hinj, Module.finrank_baseChange]

theorem range_baseChange_eq (f : V →ₗ[K] V) :
    LinearMap.range (f.baseChange L) = (LinearMap.range f).baseChange L := by
  have hsurj : Function.Surjective (f.rangeRestrict.baseChange L) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective L f.surjective_rangeRestrict
  have hf : f = (LinearMap.range f).subtype ∘ₗ f.rangeRestrict := by
    ext v; rfl
  conv_lhs => rw [hf, LinearMap.baseChange_comp]
  rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hsurj)]
  rfl

theorem baseChange_one_tmul_injective : Function.Injective fun v : V => (1 : L) ⊗ₜ[K] v := by
  have h : (fun v : V => (1 : L) ⊗ₜ[K] v) =
      (Algebra.linearMap K L).rTensor V ∘ (TensorProduct.lid K V).symm := by
    funext v
    simp [LinearMap.rTensor_tmul]
  rw [h]
  exact (Module.Flat.rTensor_preserves_injective_linearMap _
    (algebraMap K L).injective).comp (TensorProduct.lid K V).symm.injective

theorem eq_of_baseChange_eq {f g : V →ₗ[K] V} (h : f.baseChange L = g.baseChange L) :
    f = g := by
  ext v
  apply baseChange_one_tmul_injective (K := K) (V := V) L
  have := LinearMap.congr_fun h ((1 : L) ⊗ₜ v)
  simpa [LinearMap.baseChange_tmul] using this

@[expose] noncomputable def ringEquivLinearEquivOfFix (σ : L ≃+* L)
    (hσ : ∀ c : K, σ (algebraMap K L c) = algebraMap K L c) : L ≃ₗ[K] L where
  toFun := σ
  invFun := σ.symm
  map_add' := map_add σ
  map_smul' c x := by rw [Algebra.smul_def, map_mul, hσ, ← Algebra.smul_def, RingHom.id_apply]
  left_inv := σ.symm_apply_apply
  right_inv := σ.apply_symm_apply

@[expose] noncomputable def fieldAutTensor (σ : L ≃+* L)
    (hσ : ∀ c : K, σ (algebraMap K L c) = algebraMap K L c) : (L ⊗[K] V) ≃+ (L ⊗[K] V) :=
  (TensorProduct.congr (ringEquivLinearEquivOfFix L σ hσ) (LinearEquiv.refl K V)).toAddEquiv

variable {L}

theorem fieldAutTensor_tmul (σ : L ≃+* L) (hσ : ∀ c : K, σ (algebraMap K L c) = algebraMap K L c)
    (a : L) (v : V) : fieldAutTensor L σ hσ (a ⊗ₜ v) = σ a ⊗ₜ v :=
  TensorProduct.congr_tmul _ _ a v

theorem fieldAutTensor_smul (σ : L ≃+* L) (hσ : ∀ c : K, σ (algebraMap K L c) = algebraMap K L c)
    (c : L) (t : L ⊗[K] V) : fieldAutTensor L σ hσ (c • t) = σ c • fieldAutTensor L σ hσ t := by
  induction t using TensorProduct.inductionOn with
  | tmul a v => rw [TensorProduct.smul_tmul', fieldAutTensor_tmul, fieldAutTensor_tmul, smul_eq_mul,
      map_mul, TensorProduct.smul_tmul', smul_eq_mul]
  | add s t hs ht => rw [smul_add, map_add, hs, ht, map_add, smul_add]

theorem fieldAutTensor_baseChange (σ : L ≃+* L)
    (hσ : ∀ c : K, σ (algebraMap K L c) = algebraMap K L c) (f : V →ₗ[K] V) (t : L ⊗[K] V) :
    fieldAutTensor L σ hσ (f.baseChange L t) = f.baseChange L (fieldAutTensor L σ hσ t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a v => rw [LinearMap.baseChange_tmul, fieldAutTensor_tmul, fieldAutTensor_tmul,
      LinearMap.baseChange_tmul]
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, map_add]

variable (L) in
theorem baseChange_apply_baseChange (B : LinearMap.BilinForm K V) (f : V →ₗ[K] V)
    (hf : ∀ v w, B (f v) (f w) = B v w) (s t : L ⊗[K] V) :
    B.baseChange L (f.baseChange L s) (f.baseChange L t) = B.baseChange L s t := by
  induction s using TensorProduct.inductionOn with
  | tmul a v =>
    induction t using TensorProduct.inductionOn with
    | tmul b w => rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
        LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, hf]
    | add t t' ht ht' => rw [map_add, map_add, map_add, ht, ht']
  | add s s' hs hs' => simp only [map_add, LinearMap.add_apply, hs, hs']

variable (L) in
theorem bilin_baseChange_separatingLeft [FiniteDimensional K V] (B : LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (s : L ⊗[K] V) (hs : ∀ t, B.baseChange L s t = 0) : s = 0 := by
  let b := Module.finBasis K V
  let bL := b.baseChange L
  have hmat : LinearMap.BilinForm.toMatrix bL (B.baseChange L) =
      (algebraMap K L).mapMatrix (LinearMap.BilinForm.toMatrix b B) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      LinearMap.BilinForm.toMatrix_apply, Module.Basis.baseChange_apply,
      Module.Basis.baseChange_apply, LinearMap.BilinForm.baseChange_tmul, mul_one,
      Algebra.smul_def, mul_one]
  have hdet : (LinearMap.BilinForm.toMatrix bL (B.baseChange L)).det ≠ 0 := by
    rw [hmat, ← RingHom.map_det]
    exact (map_ne_zero _).mpr ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hB)
  exact ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero bL).mpr hdet).1 s hs

end BaseChange

section Kernels

variable {Γ : Type*} [Group Γ] {p : ℕ}

@[expose] def charKer (χ : Additive Γ →+ ZMod p) : Subgroup Γ where
  carrier := {x | χ (Additive.ofMul x) = 0}
  mul_mem' {a b} ha hb := by
    change χ (Additive.ofMul (a * b)) = 0
    rw [ofMul_mul, map_add, ha, hb, add_zero]
  one_mem' := by
    change χ (Additive.ofMul 1) = 0
    rw [ofMul_one, map_zero]
  inv_mem' {a} ha := by
    change χ (Additive.ofMul a⁻¹) = 0
    rw [ofMul_inv, map_neg, ha, neg_zero]

theorem mem_charKer {χ : Additive Γ →+ ZMod p} {x : Γ} :
    x ∈ charKer χ ↔ χ (Additive.ofMul x) = 0 :=
  Iff.rfl

theorem natCard_charKer [Finite Γ] (hp : p.Prime) (hΓ : Nat.card Γ = p ^ 2)
    {χ : Additive Γ →+ ZMod p} (hχ : χ ≠ 0) : Nat.card (charKer χ) = p := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Finite (Additive Γ) := Finite.of_equiv Γ Additive.ofMul
  have hrange : Nat.card χ.range = p := by
    have hdvd : Nat.card χ.range ∣ p :=
      (AddSubgroup.card_addSubgroup_dvd_card _).trans (Nat.card_zmod p).dvd
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exfalso
      apply hχ
      have hbot : χ.range = ⊥ := AddSubgroup.eq_bot_of_card_eq _ h
      ext x
      have : χ x ∈ χ.range := ⟨x, rfl⟩
      rw [hbot, AddSubgroup.mem_bot] at this
      exact this
    · exact h
  have hiso := Nat.card_congr (QuotientAddGroup.quotientKerEquivRange χ).toEquiv
  have hmul := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup χ.ker
  rw [hiso, hrange, Nat.card_congr Additive.toMul, hΓ] at hmul
  have hk : Nat.card χ.ker = p := by
    have hp0 := hp.pos
    have : p * p = p * Nat.card χ.ker := by rw [← hmul]; ring
    exact (Nat.eq_of_mul_eq_mul_left hp0 this).symm
  refine (Nat.card_congr ?_).trans hk
  exact { toFun := fun x => ⟨Additive.ofMul x, x.2⟩
          invFun := fun y => ⟨Additive.toMul y, y.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }

theorem exists_eq_smul_of_le_charKer [Finite Γ] (hp : p.Prime) (hΓ : Nat.card Γ = p ^ 2)
    {χ ψ : Additive Γ →+ ZMod p} (hχ : χ ≠ 0) (hle : charKer χ ≤ charKer ψ) :
    ∃ c : ZMod p, ψ = c • χ := by
  obtain ⟨g, hg⟩ : ∃ g : Γ, χ (Additive.ofMul g) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hχ (AddMonoidHom.ext fun x => hcon (Additive.toMul x))
  set c : ZMod p := ψ (Additive.ofMul g) * (χ (Additive.ofMul g))⁻¹ with hc
  have hcg : c * χ (Additive.ofMul g) = ψ (Additive.ofMul g) := by
    have : Fact p.Prime := ⟨hp⟩
    rw [hc, mul_assoc, inv_mul_cancel₀ hg, mul_one]
  refine ⟨c, ?_⟩
  set ψ' := ψ - c • χ with hψ'
  have hker : charKer χ < charKer ψ' := by
    refine lt_of_le_of_ne (fun x hx => ?_) fun h => hg ?_
    · rw [mem_charKer] at hx ⊢
      rw [hψ', AddMonoidHom.sub_apply, AddMonoidHom.smul_apply, hx, smul_zero, sub_zero]
      exact hle hx
    · have hgψ : g ∈ charKer ψ' := by
        rw [mem_charKer, hψ', AddMonoidHom.sub_apply, AddMonoidHom.smul_apply, smul_eq_mul, hcg,
          sub_self]
      rw [← h] at hgψ
      exact hgψ
  have htop : charKer ψ' = ⊤ := by
    have hdvd : Nat.card (charKer ψ') ∣ p ^ 2 := hΓ ▸ Subgroup.card_subgroup_dvd_card _
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hlt := Subgroup.card_lt_of_lt hker
    rw [natCard_charKer hp hΓ hχ, hk'] at hlt
    have hk2 : k = 2 := by
      rcases Nat.lt_or_ge k 2 with h | h
      · interval_cases k
        · simp at hlt
          have := hp.one_lt
          omega
        · simp at hlt
      · omega
    rw [hk2, ← hΓ] at hk'
    exact Subgroup.eq_top_of_card_eq _ hk'
  have h0 : ψ' = 0 := AddMonoidHom.ext fun x => by
    have : Additive.toMul x ∈ charKer ψ' := htop ▸ Subgroup.mem_top _
    exact this
  rw [hψ', sub_eq_zero] at h0
  exact h0

end Kernels

theorem natCard_dvd_sum_of_invariant {G : Type*} [CommGroup G] [Fintype G] (H : Subgroup G)
    (φ : G → ℕ) (hφ : ∀ h ∈ H, ∀ g, φ (h * g) = φ g) : Nat.card H ∣ ∑ g, φ g := by
  classical
  rw [← Fintype.sum_fiberwise (fun g : G => (g : G ⧸ H)) φ]
  refine Finset.dvd_sum fun c _ => ?_
  have hconst : ∀ g : {g : G // (g : G ⧸ H) = c}, φ g = φ (Quotient.out c) := by
    rintro ⟨g, hg⟩
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
    rw [hg] at hh
    rw [hh, mul_comm, hφ h h.2]
  rw [Finset.sum_congr rfl fun g _ => hconst g, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  refine Dvd.dvd.mul_right ?_ _
  have := QuotientGroup.card_preimage_mk H {c}
  have h1 : Nat.card (({c} : Set (G ⧸ H))) = 1 := by simp
  rw [h1, mul_one] at this
  rw [← this, Nat.card_eq_fintype_card]
  exact dvd_of_eq (Fintype.card_congr (Equiv.refl _))

end CFSG.RankThree.Classical
