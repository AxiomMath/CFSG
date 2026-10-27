module

public import CFSG.LocalAnalysis.StandardType.GGBstarLIDTwDFieldRad
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentFixed
public import CFSG.HardMathSupport.Foote.ModuleExclusions.Hilbert90
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentPair

public section

namespace CFSG.StandardType

namespace LIDTwDF

open Module QuadraticMap OrthBstarOdd

variable {K : Type} [Field K]

section Def

variable {X : Type} [AddCommGroup X] [Module K X]

structure SemiSim (Q : QuadraticForm K X) (p : ℕ) (σ : K ≃+* K) where
  G : X →+ X
  μ : K
  a : K
  smul : ∀ (c : K) (v : X), G (c • v) = σ c • G v
  quad : ∀ v, Q (G v) = μ * σ (Q v)
  pow : ∀ v, (⇑G)^[p] v = a • v
  hμ : μ ≠ 0
  ha : a ≠ 0

variable {Q : QuadraticForm K X} {p : ℕ} {σ : K ≃+* K}

@[expose] def restrictAdd (G : X →+ X) (T : Submodule K X) (hT : ∀ v ∈ T, G v ∈ T) : T →+ T where
  toFun v := ⟨G (v : X), hT v v.2⟩
  map_zero' := Subtype.ext (by simp)
  map_add' v w := Subtype.ext (by simp)

theorem restrictAdd_iterate (G : X →+ X) (T : Submodule K X) (hT : ∀ v ∈ T, G v ∈ T) (k : ℕ)
    (w : T) : (((⇑(restrictAdd G T hT))^[k] w : T) : X) = (⇑G)^[k] (w : X) := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    rfl

@[expose] def SemiSim.restrict (S : SemiSim Q p σ) (T : Submodule K X)
    (hT : ∀ v ∈ T, S.G v ∈ T) : SemiSim (Q.comp T.subtype) p σ where
  G := restrictAdd S.G T hT
  μ := S.μ
  a := S.a
  smul := fun c v => Subtype.ext (S.smul c v)
  quad := fun v => S.quad v
  pow := fun v => Subtype.ext ((restrictAdd_iterate S.G T hT p v).trans (S.pow v))
  hμ := S.hμ
  ha := S.ha

theorem SemiSim.ne_zero (S : SemiSim Q p σ) (hp : 0 < p) {v : X} (hv : v ≠ 0) : S.G v ≠ 0 := by
  intro h
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  have h1 := S.pow v
  rw [Function.iterate_succ_apply, h, Function.iterate_fixed (map_zero S.G)] at h1
  exact hv ((smul_eq_zero.mp h1.symm).resolve_left S.ha)

theorem SemiSim.sigma_a (S : SemiSim Q p σ) (hp : 0 < p) [Nontrivial X] : σ S.a = S.a := by
  obtain ⟨v, hv⟩ := exists_ne (0 : X)
  have h1 : S.G ((⇑S.G)^[p] v) = (⇑S.G)^[p] (S.G v) := by
    rw [← Function.iterate_succ_apply' (⇑S.G) p v, Function.iterate_succ_apply]
  rw [S.pow, S.pow, S.smul] at h1
  have h2 : (σ S.a - S.a) • S.G v = 0 := by rw [sub_smul, h1, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right (S.ne_zero hp hv))

end Def

section Plane

variable [CharP K 2] {X : Type} [AddCommGroup X] [Module K X] [FiniteDimensional K X]
  {Q : QuadraticForm K X} {p : ℕ} {σ : K ≃+* K}

theorem semiSim_stable_of_plane (hp : p.Prime) (hp2 : p ≠ 2) (S : SemiSim Q p σ)
    {Z : Submodule K X} (hZ : finrank K Z = 2)
    (hZnd : ∀ z ∈ Z, (∀ z' ∈ Z, polar Q z z' = 0) → z = 0) (hZG : ∀ z ∈ Z, S.G z ∈ Z) {y : X}
    (hyZ : y ∈ Z) (hy0 : y ≠ 0) (hyQ : Q y = 0) : ∃ c : K, S.G y = c • y := by
  by_contra hne
  push Not at hne
  have hp0 : 0 < p := hp.pos
  obtain ⟨y₁, hy₁⟩ : ∃ y₁, S.G y = y₁ := ⟨_, rfl⟩
  have hy₁Z : y₁ ∈ Z := hy₁ ▸ hZG y hyZ
  have hy₁Q : Q y₁ = 0 := by rw [← hy₁, S.quad, hyQ, map_zero, mul_zero]
  have hy₁0 : y₁ ≠ 0 := hy₁ ▸ S.ne_zero hp0 hy0
  have hind : ∀ a b : K, a • y + b • y₁ = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    by_cases hb : b = 0
    · subst hb
      rw [zero_smul, add_zero] at hab
      exact ⟨(smul_eq_zero.mp hab).resolve_right hy0, rfl⟩
    · exfalso
      refine hne (-(b⁻¹ * a)) ?_
      have h1 : b • y₁ = -(a • y) := eq_neg_of_add_eq_zero_right hab
      rw [hy₁]
      calc y₁ = b⁻¹ • (b • y₁) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
        _ = -(b⁻¹ * a) • y := by rw [h1, smul_neg, smul_smul, neg_smul]
  have hspan := mem_span_of_finrank_two hZ hyZ hy₁Z hind
  have hself : ∀ u : X, polar Q u u = 0 := fun u => OrthRestOdd.polar_self_eq_zero Q u
  have hβ : polar Q y y₁ ≠ 0 := by
    intro h0
    apply hy0
    refine hZnd y hyZ fun z' hz' => ?_
    obtain ⟨a, b, rfl⟩ := hspan z' hz'
    rw [polar_add_right, polar_smul_right, polar_smul_right, hself y, h0]
    simp
  have hQZ : ∀ a b : K, Q (a • y + b • y₁) = a * b * polar Q y y₁ := by
    intro a b
    rw [QuadraticMap.map_add (⇑Q), QuadraticMap.map_smul, QuadraticMap.map_smul, hyQ, hy₁Q,
      polar_smul_left, polar_smul_right, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring
  have hGy₁Z : S.G y₁ ∈ Z := hZG y₁ hy₁Z
  have hGy₁Q : Q (S.G y₁) = 0 := by rw [S.quad, hy₁Q, map_zero, mul_zero]
  obtain ⟨a₁, b₁, hGy₁⟩ := hspan _ hGy₁Z
  have hab : a₁ * b₁ * polar Q y y₁ = 0 := by rw [← hQZ, ← hGy₁]; exact hGy₁Q
  have hab' : a₁ = 0 ∨ b₁ = 0 := by
    rcases mul_eq_zero.mp hab with h | h
    · exact mul_eq_zero.mp h
    · exact absurd h hβ
  rcases hab' with ha₁ | hb₁
  ·
    have hGy₁' : S.G y₁ = b₁ • y₁ := by rw [hGy₁, ha₁, zero_smul, zero_add]
    have hv0 : σ.symm (-b₁) • y + y₁ ≠ 0 := fun h =>
      one_ne_zero (hind (σ.symm (-b₁)) 1 (by rwa [one_smul])).2
    apply S.ne_zero hp0 hv0
    rw [map_add, S.smul, hy₁, hGy₁', RingEquiv.apply_symm_apply, ← add_smul, neg_add_cancel,
      zero_smul]
  ·
    have hGy₁' : S.G y₁ = a₁ • y := by rw [hGy₁, hb₁, zero_smul, add_zero]
    have hev : ∀ k : ℕ, ∃ c : K, (⇑S.G)^[2 * k] y = c • y := by
      intro k
      induction k with
      | zero => exact ⟨1, by simp⟩
      | succ k ih =>
        obtain ⟨c, hc⟩ := ih
        refine ⟨σ (σ c) * a₁, ?_⟩
        rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Function.iterate_succ_apply',
          Function.iterate_succ_apply', hc, S.smul, hy₁, S.smul, hGy₁', smul_smul]
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    obtain ⟨c, hc⟩ := hev k
    have h1 : (⇑S.G)^[p] y = σ c • y₁ := by
      have e : (⇑S.G)^[p] y = (⇑S.G)^[2 * k + 1] y := congrArg (fun n => (⇑S.G)^[n] y) hk
      rw [e, Function.iterate_succ_apply', hc, S.smul, hy₁]
    rw [S.pow] at h1
    have h2 : S.a • y + (-(σ c)) • y₁ = 0 := by rw [neg_smul, ← h1, add_neg_cancel]
    exact S.ha (hind _ _ h2).1

end Plane

section Fixed

variable [Finite K] {X : Type} [AddCommGroup X] [Module K X] [FiniteDimensional K X]
  {Q : QuadraticForm K X} {p : ℕ} {σ : K ≃+* K}

theorem exists_fixed_singular (hp : p.Prime) {f : ℕ} (hf : Nat.card K = 2 ^ f) (hf1 : 1 ≤ f)
    (hσp : σ ^ p = 1) (hσ1 : σ ≠ 1) (hQ : (polarBilin Q).Nondegenerate) (S : SemiSim Q p σ)
    (hX : 3 ≤ finrank K X) :
    ∃ v : X, v ≠ 0 ∧ Q v = 0 ∧ ∃ c : K, c ≠ 0 ∧ S.G v = c • v := by
  have := Fact.mk hp
  have hord : orderOf σ = p := orderOf_eq_prime hσp hσ1
  have hp0 : 0 < p := hp.pos
  have : Nontrivial X := Module.nontrivial_of_finrank_pos (R := K) (M := X) (by omega)
  have hσa := S.sigma_a hp0
  obtain ⟨l, hl0, hl⟩ := CFSG.HardMathSupport.Foote.ModuleExclusions.exists_prod_pow_eq σ S.a⁻¹
    (by rw [map_inv₀, hσa]) (inv_ne_zero S.ha)
  rw [hord] at hl
  let G' : X →+ X :=
    { toFun := fun v => l • S.G v
      map_zero' := by simp
      map_add' := fun v w => by simp [smul_add] }
  have hG's : ∀ (c : K) (v : X), G' (c • v) = σ c • G' v := by
    intro c v
    show l • S.G (c • v) = σ c • (l • S.G v)
    rw [S.smul, smul_smul, smul_smul, mul_comm]
  have hG'iter : ∀ (k : ℕ) (v : X), (⇑G')^[k] v =
      (∏ i ∈ Finset.range k, (σ ^ i) l) • (⇑S.G)^[k] v := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [Function.iterate_succ_apply', ih]
      show l • S.G ((∏ i ∈ Finset.range k, (σ ^ i) l) • (⇑S.G)^[k] v) = _
      rw [S.smul, smul_smul, Finset.prod_range_succ', Function.iterate_succ_apply' (⇑S.G) k v]
      congr 1
      rw [map_prod]
      simp only [CFSG.HardMathSupport.Foote.ModuleExclusions.pow_succ_apply, pow_zero,
        RingAut.one_apply]
      ring
  have hG'p : ∀ v, (⇑G')^[p] v = v := by
    intro v
    rw [hG'iter, hl, S.pow, smul_smul, inv_mul_cancel₀ S.ha, one_smul]
  let e : X ≃+ X := AddEquiv.mk (Equiv.mk G' ((⇑G')^[p - 1])
    (fun v => by
      have h1 := hG'p v
      rw [← Nat.succ_pred_eq_of_pos hp0, Function.iterate_succ_apply] at h1
      simpa using h1)
    (fun v => by
      have h1 := hG'p v
      rw [← Nat.succ_pred_eq_of_pos hp0, Function.iterate_succ_apply'] at h1
      simpa using h1)) (map_add G')
  have hQe : ∀ v, Q (e v) = (l * l * S.μ) * σ (Q v) := by
    intro v
    show Q (l • S.G v) = _
    rw [QuadraticMap.map_smul, smul_eq_mul, S.quad]
    ring
  obtain ⟨-, -, d, Q₀, hQ₀, hnd, hfr, -⟩ :=
    CFSG.RankThree.PartOne.KCOrthogonalDescent.exists_descent Nat.prime_two hf1 hf σ hord e hG's
      hG'p Q hQ (l * l * S.μ) hQe
  have : Finite (CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ) :=
    Finite.of_injective (Subfield.subtype _) Subtype.val_injective
  have : FiniteDimensional (CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ)
      (CFSG.GroupTheory.SteinbergBK.semilinearFixedSubmodule σ e hG's) :=
    Module.finite_of_finrank_pos (by omega)
  obtain ⟨w, hw0, hwQ⟩ := exists_singular_vector Q₀ hnd (by omega)
  refine ⟨(w : X), fun h => hw0 (Subtype.ext h), ?_, l⁻¹, inv_ne_zero hl0, ?_⟩
  · have h1 := hQ₀ w
    rw [hwQ] at h1
    have h2 : (d : K) * Q (w : X) = 0 := by simpa using h1.symm
    exact (mul_eq_zero.mp h2).resolve_left d.ne_zero
  · have h1 : l • S.G (w : X) = (w : X) := w.2
    calc S.G (w : X) = l⁻¹ • (l • S.G (w : X)) := by rw [smul_smul, inv_mul_cancel₀ hl0, one_smul]
      _ = l⁻¹ • (w : X) := by rw [h1]

end Fixed

end LIDTwDF

end CFSG.StandardType
