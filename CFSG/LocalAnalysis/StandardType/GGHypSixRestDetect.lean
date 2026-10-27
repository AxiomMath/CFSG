module

public import CFSG.LocalAnalysis.StandardType.GGRootDetectSpinPlus

public section

namespace CFSG.StandardType

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ComponentClassification.CatalogueBHigherLinearField CFSG.LieType.Steinberg.SpinFrame
open scoped Matrix

section Def

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] def GGSpinSemilinear (Q : QuadraticForm K (ι → K)) {G : Type*} [Group G]
    (ψ : spinGroup Q →* G) (c : G) : Prop :=
  ∃ (A : GL ι K) (φ : K ≃+* K) (μ : Kˣ),
    (∀ v : ι → K, Q ((A : Matrix ι ι K) *ᵥ (fun i => φ (v i))) = μ * φ (Q v)) ∧
      ∀ y y' : spinGroup Q, ψ y' = c⁻¹ * ψ y * c →
        spinMatrix Q y' = A * glFieldEquiv ι φ (spinMatrix Q y) * A⁻¹

end Def

namespace HypSixRest

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem ggPsiInnerDiag_spin_of_semilinear [Finite K] [CharP K 2] {Q : QuadraticForm K (ι → K)}
    {Q₀ : (ι → K) → K} (hR : (spinMatrix Q).range = StatedOmega Q₀) [Finite (spinGroup Q)]
    (hperf : ⁅(⊤ : Subgroup (spinGroup Q)), (⊤ : Subgroup (spinGroup Q))⁆ = ⊤)
    (hsurj : Function.Surjective (spinToStatedProj Q hR))
    (hkerθ : (spinToStatedProj Q hR).ker = Subgroup.center (spinGroup Q))
    (hsq : ∀ B : GL ι K, (∀ v, Q ((B : Matrix ι ι K) *ᵥ v) = Q v) → B * B ∈ StatedOmega Q₀)
    (hscal : ∀ x : StatedOmega Q₀, (x : StatedProj (StatedOmega Q₀)) = 1 → x = 1)
    {p : ℕ} (hp : Odd p) (Δ : UniversalRootDatum (spinGroup Q)) {γ : Fin Δ.rank → ℤ}
    (hdetect : ∀ (N : GL ι K) (φ : K ≃+* K), (∀ z ∈ Δ.rootGroup γ,
      spinMatrix Q z * N = N * glFieldEquiv ι φ (spinMatrix Q z)) → φ = 1)
    {G : Type*} [Group G] {ψ : spinGroup Q →* G}
    (hker : ψ.ker ≤ Subgroup.center (spinGroup Q)) {c : G}
    (hc : c ∈ Subgroup.normalizer (ψ.range : Set G))
    (hcp : c ^ p ∈ Subgroup.centralizer (ψ.range : Set G)) {u : spinGroup Q}
    (hT : GGTorusOnRoot Δ ψ c γ u) (hsemi : GGSpinSemilinear Q ψ c) : GGPsiInnerDiag Δ ψ c := by
  have hθ : ∀ y, spinToStatedProj Q hR y =
      ((⟨spinMatrix Q y, spinMatrix_mem_of_range_eq Q hR y⟩ : StatedOmega Q₀) :
        StatedProj (StatedOmega Q₀)) := spinToStatedProj_apply Q hR
  obtain ⟨α, hα⟩ := RootDetect.exists_homAut hsurj hkerθ hperf hker hc
  have hαp : α ^ p = 1 := RootDetect.homAut_pow_eq_one hsurj hkerθ hker hc hα hcp
  obtain ⟨A, φ, μ, hsim, hAψ⟩ := hsemi
  have hA : ∀ x : StatedOmega Q₀, ∃ y : StatedOmega Q₀,
      (y : GL ι K) = A * glFieldEquiv ι φ (x : GL ι K) * A⁻¹ ∧
        α (QuotientGroup.mk x) = QuotientGroup.mk y := by
    intro x
    obtain ⟨y₀, hy₀⟩ : (x : GL ι K) ∈ (spinMatrix Q).range := by
      rw [hR]
      exact x.2
    obtain ⟨y₀', hy₀'⟩ := RootDetect.exists_conj_preimage hc y₀
    refine ⟨⟨spinMatrix Q y₀', spinMatrix_mem_of_range_eq Q hR y₀'⟩, ?_, ?_⟩
    · change spinMatrix Q y₀' = _
      rw [hAψ y₀ y₀' hy₀', hy₀]
    · have h1 := hα y₀ y₀' hy₀'
      rw [hθ, hθ] at h1
      have hx : (⟨spinMatrix Q y₀, spinMatrix_mem_of_range_eq Q hR y₀⟩ : StatedOmega Q₀) = x :=
        Subtype.ext hy₀
      rw [← hx]
      exact h1
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

theorem ggPsiInnerDiag_spinPlus_of_semilinear {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hn3 : 3 ≤ n) {G : Type*} [Group G] {ψ : spinGroup (quadPlus n F) →* G}
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (quadPlus n F))) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {c : G} (hc : c ∈ Subgroup.normalizer (ψ.range : Set G))
    (hcp : c ^ p ∈ Subgroup.centralizer (ψ.range : Set G)) {γ : Fin n → ℤ}
    (hγ : γ ∈ (plusDatum n F hn3).roots) {u : spinGroup (quadPlus n F)}
    (hT : GGTorusOnRoot (plusDatum n F hn3) ψ c γ u)
    (hsemi : GGSpinSemilinear (quadPlus n F) ψ c) : GGPsiInnerDiag (plusDatum n F hn3) ψ c := by
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    Finite.of_injective _ ((MonoidHom.ker_eq_bot_iff _).mp
      (ker_spinMatrix_quadPlus_eq_bot (K := F) (n := n) CharTwo.two_eq_zero))
  have : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨hsurj, -, hZ⟩ := spinToStatedProj_quadPlus (K := F) hn3
  have hnd := nondegenerate_polarBilin_quadPlus n F
  have hT3 := CFSG.ComponentClassification.RankTwoClassical.exists_totallySingular_quadPlus hn3 F
  obtain ⟨i, j, hij, s, t, -, hXγ⟩ := exists_plusRootGroup_eq (K := F) hn3 hγ
  obtain ⟨hmat, hE0, hEφ⟩ := RootDetectSpin.longRoot_hroot
    (CFSG.LieType.Steinberg.SpinPlus.isCoordFrame_plusFrame (K := F) hn3) hij s t
  refine ggPsiInnerDiag_spin_of_semilinear (range_spinMatrix_quadPlus hn3)
    (isPerfect_spinGroup_quadPlus (K := F) hn3).commutator_eq_top hsurj hZ
    (RootDetectSpin.mul_self_mem_statedOmega (coe_quadPlus n F) hnd hT3)
    (RootDetectSpin.eq_one_of_mk_eq_one (coe_quadPlus n F) hnd) (hp.odd_of_ne_two hp2)
    (plusDatum n F hn3) (RootDetectSpin.detect_of_linear (x := fun c =>
      (plusFrame n F hn3).longRoot hij s t (.ofAdd c)) (fun c => ?_) hmat hE0 hEφ) hker hc hcp hT
    hsemi
  change _ ∈ plusRootGroup n F hn3 γ
  rw [hXγ]
  exact ⟨_, rfl⟩

end HypSixRest

section Family

theorem ggPsiInnerDiag_D4_of_semilinear {f : ℕ} {G : Type} [Group G]
    {ψ : (ggU .POmegaPlus 4 f).K →* G} (hker : ψ.ker ≤ Subgroup.center (ggU .POmegaPlus 4 f).K)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {c : G} (hc : c ∈ Subgroup.normalizer (ψ.range : Set G))
    (hcp : c ^ p ∈ Subgroup.centralizer (ψ.range : Set G))
    {γ : Fin (ggU .POmegaPlus 4 f).D.rank → ℤ} (hγ : γ ∈ (ggU .POmegaPlus 4 f).D.roots)
    {u : (ggU .POmegaPlus 4 f).K} (hT : GGTorusOnRoot (ggU .POmegaPlus 4 f).D ψ c γ u)
    (hsemi : GGSpinSemilinear (quadPlus 4 (GaloisField 2 f)) ψ c) :
    GGPsiInnerDiag (ggU .POmegaPlus 4 f).D ψ c :=
  HypSixRest.ggPsiInnerDiag_spinPlus_of_semilinear (F := GaloisField 2 f) (n := 4) (by norm_num)
    hker hp hp2 hc hcp hγ hT hsemi

end Family

end CFSG.StandardType
