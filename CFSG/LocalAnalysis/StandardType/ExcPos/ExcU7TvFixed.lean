module

public import CFSG.LocalAnalysis.StandardType.ExcPos.ExcU7TvSwapped
public import CFSG.Mathlib.GroupTheory.SubgroupSupCommute

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos.ExcU7

open Matrix CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Classical2
open scoped MatrixGroups

variable {L : Type} [Field L] {ν : ℕ}

private lemma u7fx_finite_card_setOf_pow_eq_self_le {n : ℕ} (hn : 2 ≤ n) :
    {c : L | c ^ n = c}.Finite ∧ Nat.card {c : L | c ^ n = c} ≤ n := by
  classical
  set p : Polynomial L := Polynomial.X ^ n - Polynomial.X with hp
  have hdeg : p.natDegree = n := by
    rw [hp, Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> simp; omega
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    omega
  have hmem : ∀ c : L, c ^ n = c ↔ c ∈ p.roots.toFinset := by
    intro c
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0, Polynomial.IsRoot.def, hp,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero]
  have hsub : {c : L | c ^ n = c} ⊆ (p.roots.toFinset : Set L) :=
    fun c hc => (hmem c).mp hc
  have hfinT : ((p.roots.toFinset : Finset L) : Set L).Finite := Finset.finite_toSet _
  refine ⟨hfinT.subset hsub, ?_⟩
  rw [Nat.card_coe_set_eq]
  calc {c : L | c ^ n = c}.ncard
      ≤ ((p.roots.toFinset : Finset L) : Set L).ncard := Set.ncard_le_ncard hsub hfinT
    _ = (p.roots.toFinset).card := Set.ncard_coe_finset _
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := Polynomial.card_roots' p
    _ = n := hdeg

private lemma u7fx_vecMulVec_mul_eq_zero {σ : L ≃+* L} {v φ : Fin ν → L}
    (hv : ∑ i, σ (v i) * v i = 0) (hφ : ∑ i, σ (φ i) * φ i = 0) :
    Matrix.vecMulVec v φ * Matrix.vecMulVec (fun i => σ (φ i)) (fun i => σ (v i)) = 0 ∧
      Matrix.vecMulVec (fun i => σ (φ i)) (fun i => σ (v i)) * Matrix.vecMulVec v φ = 0 := by
  have h0 : φ ⬝ᵥ (fun i => σ (φ i)) = 0 := by
    rw [dotProduct]
    rw [show (∑ i, φ i * σ (φ i)) = ∑ i, σ (φ i) * φ i from
      Finset.sum_congr rfl fun i _ => mul_comm _ _]
    exact hφ
  have h1 : (fun i => σ (v i)) ⬝ᵥ v = 0 := by
    rw [dotProduct]
    exact hv
  constructor
  · rw [Matrix.vecMulVec_mul_vecMulVec, h0, zero_smul, Matrix.vecMulVec_zero]
  · rw [Matrix.vecMulVec_mul_vecMulVec, h1, zero_smul, Matrix.vecMulVec_zero]

private lemma u7fx_tvMat_comm {σ : L ≃+* L} {v φ : Fin ν → L}
    (hv : ∑ i, σ (v i) * v i = 0) (hφ : ∑ i, σ (φ i) * φ i = 0) (s t : L) :
    tvMat v φ s * tvMat (fun i => σ (φ i)) (fun i => σ (v i)) t =
      tvMat (fun i => σ (φ i)) (fun i => σ (v i)) t * tvMat v φ s := by
  obtain ⟨h1, h2⟩ := u7fx_vecMulVec_mul_eq_zero hv hφ
  rw [u7sw_tvMat_mul (v := v) (φ := φ) (u := fun i => σ (φ i)) (w := fun i => σ (v i)) s t,
    u7sw_tvMat_mul (v := fun i => σ (φ i)) (φ := fun i => σ (v i)) (u := v) (w := φ) t s,
    h1, h2, smul_zero, smul_zero, add_zero, add_zero]
  abel

private lemma u7fx_exists_param_of_mem_sup (σ : L ≃+* L) {v φ : Fin ν → L}
    (hv : ∀ i, σ (σ (v i)) = v i) (hφ : ∀ i, σ (σ (φ i)) = φ i) (h : φ ⬝ᵥ v = 0)
    (hcomm : ∀ x ∈ tvGroup v φ, ∀ y ∈ (tvGroup v φ).map (stdUnitary σ.toRingHom), x * y = y * x)
    {g : SL(ν, L)} (hg : g ∈ tvGroup v φ ⊔ (tvGroup v φ).map (stdUnitary σ.toRingHom)) :
    ∃ s t : L,
      (g : Matrix (Fin ν) (Fin ν) L) =
        tvMat v φ s * tvMat (fun i => σ (φ i)) (fun i => σ (v i)) t ∧
      ((stdUnitary σ.toRingHom g : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
        tvMat (fun i => σ (φ i)) (fun i => σ (v i)) (-(σ s)) * tvMat v φ (-(σ t)) := by
  obtain ⟨x, hx, y, hy, rfl⟩ :=
    (Subgroup.mem_sup_iff_of_forall_commute hcomm).mp hg
  obtain ⟨s, hs⟩ := (mem_tvGroup_iff h).mp hx
  obtain ⟨y₀, hy₀, hyy₀⟩ := (Subgroup.mem_map).mp hy
  obtain ⟨s₀, hs₀⟩ := (mem_tvGroup_iff h).mp hy₀
  have hwu : (fun i => σ (v i)) ⬝ᵥ (fun i => σ (φ i)) = 0 :=
    u7sw_dotProduct_map σ.toRingHom h
  have hy_mat : (y : Matrix (Fin ν) (Fin ν) L) =
      tvMat (fun i => σ (φ i)) (fun i => σ (v i)) (-(σ s₀)) := by
    rw [← hyy₀]
    exact u7sw_stdUnitary_tvMat_of_coe σ h hs₀
  refine ⟨s, -(σ s₀), ?_, ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_mul, hs, hy_mat]
  · have hΦx : ((stdUnitary σ.toRingHom x : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
        tvMat (fun i => σ (φ i)) (fun i => σ (v i)) (-(σ s)) :=
      u7sw_stdUnitary_tvMat_of_coe σ h hs
    have hΦy : ((stdUnitary σ.toRingHom y : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
        tvMat v φ (-(σ (-(σ s₀)))) := by
      have hy' := u7sw_stdUnitary_tvMat_of_coe σ hwu hy_mat
      simpa only [hv, hφ] using hy'
    rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, hΦx, hΦy]

private lemma u7fx_exists_fixed_param (σ : L ≃+* L) {v φ : Fin ν → L}
    (hv : ∀ i, σ (σ (v i)) = v i) (hφ : ∀ i, σ (σ (φ i)) = φ i)
    (hv0 : v ≠ 0) (hφ0 : φ ≠ 0) (h : φ ⬝ᵥ v = 0)
    (hs : IsSwappedTv (stdUnitary σ.toRingHom) (tvGroup v φ)) {g : SL(ν, L)}
    (hg : g ∈ tvGroup v φ ⊔ (tvGroup v φ).map (stdUnitary σ.toRingHom))
    (hfix : stdUnitary σ.toRingHom g = g) :
    ∃ s : L, σ (σ s) = s ∧
      (g : Matrix (Fin ν) (Fin ν) L) =
        tvMat v φ s * tvMat (fun i => σ (φ i)) (fun i => σ (v i)) (-(σ s)) := by
  obtain ⟨hviso, hφiso, hnotprop⟩ := swapped_isotropic σ hv hφ hv0 hφ0 h hs
  obtain ⟨s, t, hg1, hg2⟩ := u7fx_exists_param_of_mem_sup σ hv hφ h hs.2.1 hg
  have hfixm : ((stdUnitary σ.toRingHom g : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
      (g : Matrix (Fin ν) (Fin ν) L) := by rw [hfix]
  have hEq : tvMat (fun i => σ (φ i)) (fun i => σ (v i)) (-(σ s)) * tvMat v φ (-(σ t)) =
      tvMat v φ s * tvMat (fun i => σ (φ i)) (fun i => σ (v i)) t := by
    rw [← hg2, ← hg1]
    exact hfixm
  have hcomm := (u7fx_tvMat_comm (σ := σ) hviso hφiso (-(σ t)) (-(σ s))).symm
  rw [hcomm] at hEq
  have hNN' : Matrix.vecMulVec v φ * Matrix.vecMulVec (fun i => σ (φ i)) (fun i => σ (v i))
      = 0 := (u7fx_vecMulVec_mul_eq_zero hviso hφiso).1
  have hu0 : (fun i => σ (φ i)) ≠ 0 :=
    u7sw_map_ne_zero' σ.injective (map_zero σ) hφ0
  have hw0 : (fun i => σ (v i)) ≠ 0 :=
    u7sw_map_ne_zero' σ.injective (map_zero σ) hv0
  obtain ⟨hst, hts⟩ :=
    u7sw_tvMat_mul_eq_iff hv0 hu0 hnotprop hw0 hφ0 hNN' hEq
  refine ⟨s, ?_, ?_⟩
  · calc σ (σ s) = -(-(σ (σ s))) := by rw [neg_neg]
      _ = -(σ (-(σ s))) := by rw [map_neg]
      _ = -(σ t) := by rw [hts]
      _ = s := hst
  · rw [hg1, ← hts]

theorem card_fixed_swapped_le (σ : L ≃+* L) {Q : ℕ} (hσ : ∀ c, σ c = c ^ Q) (hQ : 2 ≤ Q)
    {v φ : Fin ν → L} (hv : ∀ i, σ (σ (v i)) = v i) (hφ : ∀ i, σ (σ (φ i)) = φ i)
    (hv0 : v ≠ 0) (hφ0 : φ ≠ 0) (h : φ ⬝ᵥ v = 0)
    (hs : IsSwappedTv (stdUnitary σ.toRingHom) (tvGroup v φ)) :
    Finite ↥((tvGroup v φ ⊔ (tvGroup v φ).map (stdUnitary σ.toRingHom)) ⊓
        (stdUnitary σ.toRingHom).eqLocus (MonoidHom.id SL(ν, L))) ∧
      Nat.card ↥((tvGroup v φ ⊔ (tvGroup v φ).map (stdUnitary σ.toRingHom)) ⊓
        (stdUnitary σ.toRingHom).eqLocus (MonoidHom.id SL(ν, L))) ≤ Q ^ 2 := by
  let A := (tvGroup v φ ⊔ (tvGroup v φ).map (stdUnitary σ.toRingHom)) ⊓
    (stdUnitary σ.toRingHom).eqLocus (MonoidHom.id SL(ν, L))
  change Finite ↥A ∧ Nat.card ↥A ≤ Q ^ 2
  have hfixed : ∀ g : ↥A, ∃ s : L, σ (σ s) = s ∧
      ((g.1 : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
        tvMat v φ s * tvMat (fun i => σ (φ i)) (fun i => σ (v i)) (-(σ s)) := by
    intro g
    obtain ⟨hgA, hgy⟩ := Subgroup.mem_inf.mp g.2
    have hgy' : stdUnitary σ.toRingHom (g.1 : SL(ν, L)) = (g.1 : SL(ν, L)) := hgy
    exact u7fx_exists_fixed_param σ hv hφ hv0 hφ0 h hs hgA hgy'
  let p : ↥A → L := fun g => Classical.choose (hfixed g)
  have hp : ∀ g : ↥A, σ (σ (p g)) = p g ∧
      ((g.1 : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
        tvMat v φ (p g) * tvMat (fun i => σ (φ i)) (fun i => σ (v i)) (-(σ (p g))) :=
    fun g => Classical.choose_spec (hfixed g)
  have hpow : ∀ c : L, c ^ (Q * Q) = c ↔ σ (σ c) = c := by
    intro c
    have h1 : σ (σ c) = c ^ (Q * Q) := by
      rw [hσ (σ c), hσ c, ← pow_mul]
    rw [h1]
  let p' : ↥A → ↥{c : L | c ^ (Q * Q) = c} := fun g =>
    ⟨p g, (hpow (p g)).mpr (hp g).1⟩
  have hp'_inj : Function.Injective p' := by
    intro g g' hgg'
    have hpgg : p g = p g' := congrArg Subtype.val hgg'
    apply Subtype.ext
    apply Subtype.ext
    rw [(hp g).2, (hp g').2, hpgg]
  have hQ2 : 2 ≤ Q * Q := by
    calc 2 ≤ 2 * 2 := by norm_num
      _ ≤ Q * Q := Nat.mul_le_mul hQ hQ
  have hSfin : {c : L | c ^ (Q * Q) = c}.Finite :=
    (u7fx_finite_card_setOf_pow_eq_self_le (L := L) hQ2).1
  haveI : Finite ↥{c : L | c ^ (Q * Q) = c} := hSfin
  refine ⟨Finite.of_injective p' hp'_inj, ?_⟩
  calc Nat.card ↥A ≤ Nat.card ↥{c : L | c ^ (Q * Q) = c} :=
        Nat.card_le_card_of_injective p' hp'_inj
    _ ≤ Q * Q := (u7fx_finite_card_setOf_pow_eq_self_le (L := L) hQ2).2
    _ = Q ^ 2 := by rw [sq]

end CFSG.StandardType.LieKnownR2.ExcPos.ExcU7
