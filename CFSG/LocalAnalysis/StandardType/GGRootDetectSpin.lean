module

public import CFSG.LocalAnalysis.StandardType.GGRootDetectCore
public import CFSG.LieType.Universal.SpinOmega.Center
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldAction

public section

namespace CFSG.StandardType

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ComponentClassification.CatalogueBHigherLinearField
open scoped Matrix

namespace RootDetect

section Hom

variable {S P G : Type*} [Group S] [Group P] [Group G] {π : S →* P} {ψ : S →* G}

theorem hom_eq_of_psi_eq (hπ : π.ker = Subgroup.center S) (hker : ψ.ker ≤ Subgroup.center S)
    {y₁ y₂ : S} (h : ψ y₁ = ψ y₂) : π y₁ = π y₂ := by
  rw [← inv_mul_eq_one, ← map_inv, ← map_mul, ← MonoidHom.mem_ker, hπ]
  apply hker
  rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]

theorem exists_homAut [Finite S] (hπs : Function.Surjective π) (hπ : π.ker = Subgroup.center S)
    (hperf : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = ⊤) (hker : ψ.ker ≤ Subgroup.center S)
    {c : G} (hc : c ∈ Subgroup.normalizer (ψ.range : Set G)) :
    ∃ α : MulAut P, ∀ y y' : S, ψ y' = c⁻¹ * ψ y * c → α (π y) = π y' := by
  obtain ⟨α', hα'⟩ := exists_quotAut (N := π.ker) hπ hperf hker hc
  let e : S ⧸ π.ker ≃* P := QuotientGroup.quotientKerEquivOfSurjective π hπs
  have he : ∀ z : S, e (z : S ⧸ π.ker) = π z := fun z => rfl
  have he' : ∀ z : S, e.symm (π z) = (z : S ⧸ π.ker) := fun z => by
    rw [MulEquiv.symm_apply_eq, he]
  refine ⟨(e.symm.trans α').trans e, fun y y' h => ?_⟩
  change e (α' (e.symm (π y))) = π y'
  rw [he', hα' y y' h, he]

theorem homAut_pow_apply (hπ : π.ker = Subgroup.center S) (hker : ψ.ker ≤ Subgroup.center S)
    {c : G} (hc : c ∈ Subgroup.normalizer (ψ.range : Set G)) {α : MulAut P}
    (hα : ∀ y y' : S, ψ y' = c⁻¹ * ψ y * c → α (π y) = π y') :
    ∀ k : ℕ, ∀ y y' : S, ψ y' = (c ^ k)⁻¹ * ψ y * c ^ k → (α ^ k) (π y) = π y'
  | 0 => fun y y' h => by
      rw [pow_zero, MulAut.one_apply]
      exact hom_eq_of_psi_eq hπ hker (by rw [h]; group)
  | k + 1 => fun y y' h => by
      obtain ⟨y'', hy''⟩ := exists_conj_preimage (Subgroup.pow_mem _ hc k) y
      rw [pow_succ', MulAut.mul_apply, homAut_pow_apply hπ hker hc hα k y y'' hy'']
      apply hα
      rw [h, hy'', pow_succ]
      group

theorem homAut_pow_eq_one (hπs : Function.Surjective π) (hπ : π.ker = Subgroup.center S)
    (hker : ψ.ker ≤ Subgroup.center S) {c : G} (hc : c ∈ Subgroup.normalizer (ψ.range : Set G))
    {α : MulAut P} (hα : ∀ y y' : S, ψ y' = c⁻¹ * ψ y * c → α (π y) = π y') {p : ℕ}
    (hcp : c ^ p ∈ Subgroup.centralizer (ψ.range : Set G)) : α ^ p = 1 := by
  ext x
  obtain ⟨y, rfl⟩ := hπs x
  rw [MulAut.one_apply]
  apply homAut_pow_apply hπ hker hc hα p y y
  have hcomm := Subgroup.mem_centralizer_iff.mp hcp (ψ y) ⟨y, rfl⟩
  rw [mul_assoc, hcomm, inv_mul_cancel_left]

theorem centralizes_of_homAut_conj (hπ : π.ker = Subgroup.center S)
    (hperf : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = ⊤) {c : G}
    (hc : c ∈ Subgroup.normalizer (ψ.range : Set G)) {α : MulAut P}
    (hα : ∀ y y' : S, ψ y' = c⁻¹ * ψ y * c → α (π y) = π y') {a : S}
    (ha : ∀ y : S, α (π y) = π (a * y * a⁻¹)) (y : S) :
    (c * ψ a)⁻¹ * ψ y * (c * ψ a) = ψ y := by
  have hratio : ∀ w, ∃ s ∈ Subgroup.center S,
      (ψ w)⁻¹ * ((c * ψ a)⁻¹ * ψ w * (c * ψ a)) = ψ s := by
    intro w
    obtain ⟨w', hw'⟩ := exists_conj_preimage hc w
    have hq : π (a * w * a⁻¹) = π w' := by
      rw [← ha w]
      exact hα w w' hw'
    have hs : (a * w * a⁻¹)⁻¹ * w' ∈ Subgroup.center S := by
      rw [← hπ, MonoidHom.mem_ker, map_mul, map_inv, hq, inv_mul_cancel]
    obtain ⟨s, hsdef⟩ : ∃ s, s = (a * w * a⁻¹)⁻¹ * w' := ⟨_, rfl⟩
    rw [← hsdef] at hs
    have hw's : w' = a * w * a⁻¹ * s := by rw [hsdef]; group
    have hs' : a⁻¹ * s * a = s := by
      rw [mul_assoc, ← Subgroup.mem_center_iff.mp hs a, inv_mul_cancel_left]
    refine ⟨s, hs, ?_⟩
    calc (ψ w)⁻¹ * ((c * ψ a)⁻¹ * ψ w * (c * ψ a)) =
        (ψ w)⁻¹ * ((ψ a)⁻¹ * (c⁻¹ * ψ w * c) * ψ a) := by group
      _ = ψ (w⁻¹ * (a⁻¹ * w' * a)) := by
        rw [← hw', map_mul, map_mul, map_mul, map_inv, map_inv]
      _ = ψ s := by
        rw [hw's]
        congr 1
        calc w⁻¹ * (a⁻¹ * (a * w * a⁻¹ * s) * a) = a⁻¹ * s * a := by group
          _ = s := hs'
  have heq := HypSixTypeA.eq_of_inv_mul_comm hperf (H := ψ.range) ψ
    ((MulAut.conj (c * ψ a)⁻¹).toMonoidHom.comp ψ) (fun w => ⟨w, rfl⟩)
    (fun w => by
      obtain ⟨w', hw'⟩ := exists_conj_preimage hc w
      refine ⟨a⁻¹ * w' * a, ?_⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [map_mul, map_mul, map_inv, hw']
      group)
    (fun w k hk => by
      obtain ⟨s, hs, hsw⟩ := hratio w
      obtain ⟨v, rfl⟩ := hk
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [hsw, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hs v])
  have h1 := congrArg (fun φ : S →* G => φ y) heq
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1
  exact h1.symm

end Hom

end RootDetect

namespace RootDetectSpin

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem coe_glFieldEquiv (φ : K ≃+* K) (A : GL ι K) :
    ((glFieldEquiv ι φ A : GL ι K) : Matrix ι ι K) = (A : Matrix ι ι K).map φ :=
  rfl

omit [Fintype ι] in
theorem map_one_add_smul {E : Matrix ι ι K} (φ : K ≃+* K) (hE : E.map φ = E) (t : K) :
    (1 + t • E).map φ = 1 + φ t • E := by
  rw [Matrix.map_add _ (map_add φ), Matrix.map_one _ (map_zero φ) (map_one φ),
    Matrix.map_smul' _ _ _ (map_mul φ), hE]

theorem detect_of_linear {Q : QuadraticForm K (ι → K)} {X : Subgroup (spinGroup Q)}
    {x : K → spinGroup Q} {E : Matrix ι ι K} (hx : ∀ t, x t ∈ X)
    (hxE : ∀ t, ((spinMatrix Q (x t) : GL ι K) : Matrix ι ι K) = 1 + t • E) (hE0 : E ≠ 0)
    (hEφ : ∀ φ : K ≃+* K, E.map φ = E) (N : GL ι K) (φ : K ≃+* K)
    (h : ∀ z ∈ X, spinMatrix Q z * N = N * glFieldEquiv ι φ (spinMatrix Q z)) : φ = 1 := by
  refine RootDetect.ringEquiv_eq_one_of_mul_conj (E := E) (M := (N : Matrix ι ι K))
    (M' := ((N⁻¹ : GL ι K) : Matrix ι ι K)) hE0
    (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) fun t => ?_
  have e'' := congrArg Units.val (h (x t) (hx t))
  rw [Units.val_mul, Units.val_mul, coe_glFieldEquiv, hxE, map_one_add_smul φ (hEφ φ)] at e''
  exact e''

theorem ggPsiInnerDiag_spin_of_aut [Finite K] [CharP K 2] {Q : QuadraticForm K (ι → K)}
    {Q₀ : (ι → K) → K} (hR : (spinMatrix Q).range = StatedOmega Q₀) [Finite (spinGroup Q)]
    (hperf : ⁅(⊤ : Subgroup (spinGroup Q)), (⊤ : Subgroup (spinGroup Q))⁆ = ⊤)
    (hsurj : Function.Surjective (spinToStatedProj Q hR))
    (hkerθ : (spinToStatedProj Q hR).ker = Subgroup.center (spinGroup Q))
    (hsq : ∀ B : GL ι K, (∀ v, Q ((B : Matrix ι ι K) *ᵥ v) = Q v) → B * B ∈ StatedOmega Q₀)
    (hscal : ∀ x : StatedOmega Q₀, (x : StatedProj (StatedOmega Q₀)) = 1 → x = 1)
    {p : ℕ} (hp : Odd p)
    (hform : ∀ β : MulAut (StatedProj (StatedOmega Q₀)), β ^ p = 1 →
      ∃ (A : GL ι K) (φ : K ≃+* K) (μ : Kˣ),
        (∀ v : ι → K, Q ((A : Matrix ι ι K) *ᵥ (fun i => φ (v i))) = μ * φ (Q v)) ∧
        ∀ x : StatedOmega Q₀, ∃ y : StatedOmega Q₀,
          (y : GL ι K) = A * glFieldEquiv ι φ (x : GL ι K) * A⁻¹ ∧
            β (QuotientGroup.mk x) = QuotientGroup.mk y)
    (Δ : UniversalRootDatum (spinGroup Q)) {γ : Fin Δ.rank → ℤ}
    (hdetect : ∀ (N : GL ι K) (φ : K ≃+* K), (∀ z ∈ Δ.rootGroup γ,
      spinMatrix Q z * N = N * glFieldEquiv ι φ (spinMatrix Q z)) → φ = 1)
    {G : Type*} [Group G] {ψ : spinGroup Q →* G}
    (hker : ψ.ker ≤ Subgroup.center (spinGroup Q)) {c : G}
    (hc : c ∈ Subgroup.normalizer (ψ.range : Set G))
    (hcp : c ^ p ∈ Subgroup.centralizer (ψ.range : Set G)) {u : spinGroup Q}
    (hT : GGTorusOnRoot Δ ψ c γ u) : GGPsiInnerDiag Δ ψ c := by
  have hθ : ∀ y, spinToStatedProj Q hR y =
      ((⟨spinMatrix Q y, spinMatrix_mem_of_range_eq Q hR y⟩ : StatedOmega Q₀) :
        StatedProj (StatedOmega Q₀)) := spinToStatedProj_apply Q hR
  obtain ⟨α, hα⟩ := RootDetect.exists_homAut hsurj hkerθ hperf hker hc
  have hαp : α ^ p = 1 := RootDetect.homAut_pow_eq_one hsurj hkerθ hker hc hα hcp
  obtain ⟨A, φ, μ, hsim, hA⟩ := hform α hαp
  have hmk : ∀ x y : StatedOmega Q₀, (x : StatedProj (StatedOmega Q₀)) = y → x = y := by
    intro x y h
    have h1 := hscal (x⁻¹ * y) (by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h, inv_mul_cancel])
    exact inv_mul_eq_one.mp h1
  obtain ⟨W, hW⟩ := RootDetect.exists_conj_of_torusOnRoot Δ hT
  have hφ : φ = 1 := by
    refine hdetect ((spinMatrix Q W)⁻¹ * A * glFieldEquiv ι φ (spinMatrix Q u)) φ fun z hz => ?_
    have h1 := hα _ _ (hW z hz)
    rw [hθ, hθ] at h1
    obtain ⟨y, hy, hβy⟩ := hA ⟨spinMatrix Q (u * z * u⁻¹), spinMatrix_mem_of_range_eq Q hR _⟩
    have h2 := hmk _ _ (hβy.symm.trans h1)
    have h3 : (y : GL ι K) = spinMatrix Q (W * z * W⁻¹) := congrArg Subtype.val h2
    rw [hy] at h3
    simp only [map_mul, map_inv] at h3
    exact HypSixTypeA.mul_conj_rel h3.symm
  subst hφ
  have hsim' : ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = μ * Q v := fun v => by
    simpa using hsim v
  have hA1 : ∀ x : StatedOmega Q₀, ∃ y : StatedOmega Q₀,
      (y : GL ι K) = A * x * A⁻¹ ∧ α (QuotientGroup.mk x) = QuotientGroup.mk y := by
    intro x
    obtain ⟨y, hy, h⟩ := hA x
    refine ⟨y, ?_, h⟩
    rw [hy]
    congr 2
  obtain ⟨s, hs⟩ := isSquare_of_charTwo' (μ : K)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hs
    exact μ.ne_zero hs
  obtain ⟨S, hS⟩ : ∃ S : GL ι K,
      S = Matrix.GeneralLinearGroup.scalar ι (Units.mk0 s hs0)⁻¹ := ⟨_, rfl⟩
  have hSm : (S : Matrix ι ι K) = s⁻¹ • (1 : Matrix ι ι K) := by
    rw [hS, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
    simp
  have hSc : S ∈ Subgroup.center (GL ι K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, hS]
    exact ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : GL ι K, B = S * A := ⟨_, rfl⟩
  have hB : ∀ v, Q ((B : Matrix ι ι K) *ᵥ v) = Q v := by
    intro v
    rw [hBdef, Units.val_mul, hSm, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mulVec,
      QuadraticMap.map_smul, hsim', hs, smul_eq_mul]
    field_simp
  have hBconj : ∀ X : GL ι K, B * X * B⁻¹ = A * X * A⁻¹ := by
    intro X
    have hcomm := Subgroup.mem_center_iff.mp hSc
    rw [hBdef]
    calc S * A * X * (S * A)⁻¹ = S * (A * X * A⁻¹) * S⁻¹ := by group
      _ = A * X * A⁻¹ := by rw [← hcomm (A * X * A⁻¹)]; group
  have hpow : ∀ k : ℕ, ∀ x : StatedOmega Q₀, ∃ y : StatedOmega Q₀,
      (y : GL ι K) = B ^ k * x * (B ^ k)⁻¹ ∧
        (α ^ k) (QuotientGroup.mk x) = QuotientGroup.mk y := by
    intro k
    induction k with
    | zero => exact fun x => ⟨x, by simp, by simp⟩
    | succ k ih =>
      intro x
      obtain ⟨y, hy, hαy⟩ := ih x
      obtain ⟨y', hy', hαy'⟩ := hA1 y
      refine ⟨y', ?_, ?_⟩
      · rw [hy', ← hBconj, hy, pow_succ']
        group
      · rw [pow_succ', MulAut.mul_apply, hαy, hαy']
  have hBp : ∀ x : StatedOmega Q₀, B ^ p * (x : GL ι K) * (B ^ p)⁻¹ = x := by
    intro x
    obtain ⟨y, hy, hαy⟩ := hpow p x
    rw [hαp, MulAut.one_apply] at hαy
    rw [← hy, ← hmk _ _ hαy]
  obtain ⟨k, hk⟩ := hp
  obtain ⟨D, hD⟩ : ∃ D : GL ι K, D = ((B * B) ^ k)⁻¹ := ⟨_, rfl⟩
  have hDΩ : D ∈ StatedOmega Q₀ := by
    rw [hD]
    exact inv_mem (pow_mem (hsq B hB) k)
  have hconjD : ∀ x : StatedOmega Q₀, A * (x : GL ι K) * A⁻¹ = D * x * D⁻¹ := by
    intro x
    have h1 := hBp x
    rw [hk] at h1
    have hBD : B = D * B ^ (2 * k + 1) := by
      rw [hD, pow_succ, pow_mul, sq, inv_mul_cancel_left]
    rw [← hBconj, hBD]
    calc D * B ^ (2 * k + 1) * (x : GL ι K) * (D * B ^ (2 * k + 1))⁻¹ =
        D * (B ^ (2 * k + 1) * (x : GL ι K) * (B ^ (2 * k + 1))⁻¹) * D⁻¹ := by group
      _ = D * x * D⁻¹ := by rw [h1]
  have hDr : D ∈ (spinMatrix Q).range := hR ▸ hDΩ
  obtain ⟨a, ha⟩ := hDr
  have ha' : ∀ y : spinGroup Q,
      α (spinToStatedProj Q hR y) = spinToStatedProj Q hR (a * y * a⁻¹) := by
    intro y
    rw [hθ, hθ]
    obtain ⟨y', hy', hαy'⟩ := hA1 ⟨spinMatrix Q y, spinMatrix_mem_of_range_eq Q hR y⟩
    rw [hαy']
    congr 1
    apply Subtype.ext
    rw [hy', hconjD]
    simp only [map_mul, map_inv, ha]
  exact RootDetect.ggPsiInnerDiag_of_centralizes Δ
    (RootDetect.centralizes_of_homAut_conj hkerθ hperf hc hα ha')

end RootDetectSpin

end CFSG.StandardType
