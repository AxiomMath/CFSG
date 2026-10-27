module

public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorBridge
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarConj

public section

namespace CFSG.RankThree.PartOne.KCOrthComm

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonal

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

abbrev pairMap (g : similarityPairs Q) : (Fin d → K) ≃+ (Fin d → K) :=
  coordinateSemilinearMap g.val

theorem pairMap_smul (g : similarityPairs Q) (c : K) (v : Fin d → K) :
    pairMap Q g (c • v) = g.val.right c • pairMap Q g v :=
  coordinateSemilinearMap_smul g.val c v

theorem exists_pairMap_sim (g : similarityPairs Q) :
    ∃ μ : Kˣ, ∀ v, Q (pairMap Q g v) = (μ : K) * g.val.right (Q v) := g.2

theorem kappa_apply_conj (g : similarityPairs Q) (ω : orthDerived Q) :
    ∃ ω' : orthDerived Q, (∀ v, (ω' : (Fin d → K) ≃ₗ[K] (Fin d → K)) v =
      pairMap Q g ((ω : (Fin d → K) ≃ₗ[K] (Fin d → K)) ((pairMap Q g).symm v))) ∧
      kappa Q g (QuotientGroup.mk ω) = QuotientGroup.mk ω' := by
  obtain ⟨μ, hμ⟩ := exists_pairMap_sim Q g
  refine ⟨⟨semilinConj (pairMap Q g) g.val.right (pairMap_smul Q g) (ω : _),
    semilinConj_mem_orthDerived (pairMap Q g) g.val.right (pairMap_smul Q g) (μ : K) hμ ω.2⟩,
    fun v => rfl, ?_⟩
  exact kappa_apply Q g ω _ fun v => rfl

theorem eq_one_of_sq_eq_one_of_pow_eq_one {p : ℕ} (hp : Odd p) {z : K} (h2 : z ^ 2 = 1)
    (hz : z ^ p = 1) : z = 1 := by
  obtain ⟨k, rfl⟩ := hp
  have : z ^ (2 * k + 1) = z := by
    rw [pow_succ, pow_mul, h2, one_pow, one_mul]
  rw [← this]
  exact hz

theorem pairMap_comm_of_fixes {x : orthDerived Q} {p : ℕ} (hp : Odd p)
    (hxp : ((x : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) ^ p = 1) (hQ0 : ∃ v, Q v ≠ 0)
    (g : similarityPairs Q) (hfix : kappa Q g (QuotientGroup.mk x) = QuotientGroup.mk x)
    (v : Fin d → K) :
    pairMap Q g ((x : (Fin d → K) ≃ₗ[K] (Fin d → K)) v) =
      (x : (Fin d → K) ≃ₗ[K] (Fin d → K)) (pairMap Q g v) := by
  obtain ⟨μ, hμ⟩ := exists_pairMap_sim Q g
  set σ := g.val.right with hσ
  set F := pairMap Q g with hF
  obtain ⟨ω', hω', hk⟩ := kappa_apply_conj Q g x
  have hxe : ω' = ⟨semilinConj F σ (pairMap_smul Q g) (x : _),
      semilinConj_mem_orthDerived F σ (pairMap_smul Q g) (μ : K) hμ x.2⟩ :=
    Subtype.ext (LinearEquiv.ext hω')
  rw [hk] at hfix
  have hs : (ω'⁻¹ * x : orthDerived Q) ∈ (scalars K (Fin d → K)).subgroupOf (orthDerived Q) :=
    QuotientGroup.eq.mp hfix
  obtain ⟨z, hz⟩ := mem_scalars.mp (Subgroup.mem_subgroupOf.mp hs)
  have hxz : ∀ v, (x : (Fin d → K) ≃ₗ[K] (Fin d → K)) v =
      z • (ω' : (Fin d → K) ≃ₗ[K] (Fin d → K)) v := by
    intro v
    have h1 := hz v
    have h2 : ((ω'⁻¹ * x : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) v =
        (ω'⁻¹ : (Fin d → K) ≃ₗ[K] (Fin d → K)) ((x : (Fin d → K) ≃ₗ[K] (Fin d → K)) v) := rfl
    rw [h2] at h1
    have h3 := congrArg (ω' : (Fin d → K) ≃ₗ[K] (Fin d → K)) h1
    rw [map_smul] at h3
    have h4 : (ω' : (Fin d → K) ≃ₗ[K] (Fin d → K))
        ((ω'⁻¹ : (Fin d → K) ≃ₗ[K] (Fin d → K)) ((x : (Fin d → K) ≃ₗ[K] (Fin d → K)) v)) =
        (x : (Fin d → K) ≃ₗ[K] (Fin d → K)) v := by
      change (ω' : (Fin d → K) ≃ₗ[K] (Fin d → K))
        ((ω' : (Fin d → K) ≃ₗ[K] (Fin d → K)).symm _) = _
      exact LinearEquiv.apply_symm_apply _ _
    rw [h4] at h3
    exact h3
  obtain ⟨v₀, hv₀⟩ := hQ0
  have hz2 : z ^ 2 = 1 := by
    have hmem : ((ω'⁻¹ * x : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈
        TauCeti.QuadraticMap.orthogonalGroup Q := orthDerived_le_orthogonalGroup_of_commutator Q
        (ω'⁻¹ * x).2
    have h1 := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hmem v₀
    rw [hz v₀, QuadraticMap.map_smul] at h1
    have h2 : (z ^ 2 - 1) * Q v₀ = 0 := by
      rw [sub_mul, one_mul, pow_two]
      rw [smul_eq_mul] at h1
      linear_combination h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hv₀)
  have hω'p : (ω' : (Fin d → K) ≃ₗ[K] (Fin d → K)) ^ p = 1 := by
    have h1 : (ω' : (Fin d → K) ≃ₗ[K] (Fin d → K)) =
        semilinConj F σ (pairMap_smul Q g) (x : (Fin d → K) ≃ₗ[K] (Fin d → K)) :=
      LinearEquiv.ext hω'
    rw [h1, ← map_pow, hxp, map_one]
  have hpow : ∀ n : ℕ, ∀ v, ((x : (Fin d → K) ≃ₗ[K] (Fin d → K)) ^ n) v =
      z ^ n • ((ω' : (Fin d → K) ≃ₗ[K] (Fin d → K)) ^ n) v := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ (x : (Fin d → K) ≃ₗ[K] (Fin d → K)) n, LinearEquiv.mul_apply, ih, hxz v,
        map_smul, smul_smul, ← pow_succ z n, pow_succ (ω' : (Fin d → K) ≃ₗ[K] (Fin d → K)) n,
        LinearEquiv.mul_apply]
  have hv₀ne : v₀ ≠ 0 := by
    rintro rfl
    exact hv₀ (QuadraticMap.map_zero Q)
  have hzp : z ^ p = 1 := by
    have h1 := hpow p v₀
    rw [hxp, hω'p] at h1
    have h2 : (1 : (Fin d → K) ≃ₗ[K] (Fin d → K)) v₀ = v₀ := rfl
    rw [h2] at h1
    have h3 : (z ^ p - 1) • v₀ = 0 := by
      rw [sub_smul, one_smul, ← h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hv₀ne)
  have hz1 : z = 1 := eq_one_of_sq_eq_one_of_pow_eq_one hp hz2 hzp
  have h5 := hxz (F v)
  rw [hz1, one_smul, hω' (F v), AddEquiv.symm_apply_apply] at h5
  exact h5.symm

theorem pairMap_pow (g : similarityPairs Q) (n : ℕ) (v : Fin d → K) :
    pairMap Q (g ^ n) v = (pairMap Q g)^[n] v := by
  induction n generalizing v with
  | zero => exact coordinateSemilinearMap_one v
  | succ n ih =>
    rw [pow_succ, Function.iterate_succ_apply]
    change coordinateSemilinearMap ((g ^ n).val * g.val) v = _
    rw [coordinateSemilinearMap_mul, ih]

theorem pair_pow_right (g : similarityPairs Q) (n : ℕ) : (g ^ n).val.right = g.val.right ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ]
    change (g ^ n).val.right * g.val.right = _
    rw [ih]

theorem pair_pow_scalar {p : ℕ} (hG : GateData Q p) (g : similarityPairs Q) (n : ℕ)
    (hn : kappa Q g ^ n = 1) :
    g.val.right ^ n = 1 ∧ ∃ c : K, ∀ v, (pairMap Q g)^[n] v = c • v := by
  have h1 : kappa Q (g ^ n) = 1 := by rw [map_pow]; exact hn
  obtain ⟨hr, c, hc⟩ := hG.ker _ h1
  refine ⟨by rw [← pair_pow_right]; exact hr, (c : K), fun v => ?_⟩
  rw [← pairMap_pow, coordinateSemilinearMap_apply, hc, hr]
  ext i
  simp [Matrix.mulVec_diagonal, Matrix.scalar_apply, Matrix.GeneralLinearGroup.coe_scalar]

end CFSG.RankThree.PartOne.KCOrthComm
