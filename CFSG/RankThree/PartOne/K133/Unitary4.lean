module

public import CFSG.RankThree.PartOne.K133.Diag4
public import CFSG.RankThree.PartOne.K133.Indep4
public import CFSG.RankThree.PartOne.K133.FormOrth
public import CFSG.RankThree.PartOne.KF.RankGL
public import CFSG.LieType.BorelTits.UnitaryForm

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank Module Matrix

theorem statedSU_det_eq_one' {n q : ℕ} {K : Type} [Field K] {g : GL (Fin n) K} (hg : g ∈ StatedSU n q K) :
    (g : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSU hg

theorem matrix_ext_of_basis {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    (b : Basis n K (n → K)) {A B : Matrix n n K} (h : ∀ j, A *ᵥ b j = B *ᵥ b j) : A = B := by
  have : Matrix.toLin' A = Matrix.toLin' B := b.ext fun j => by simpa using h j
  exact Matrix.toLin'.injective this

theorem eigen_chars_gl_four {K : Type} [Field K] {p : ℕ} [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (E : Subgroup (GL (Fin 4) K)) [Finite E] (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g)
    (hexp : ∀ g ∈ E, g ^ p = 1) (hdet : ∀ g ∈ E, ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1) :
    ∃ (b : Basis (Fin 4) K (Fin 4 → K)) (μ : E → Fin 4 → K),
      (∀ (g : E) (j : Fin 4), ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ (b j) = μ g j • b j) ∧
      (∀ g h j, μ (g * h) j = μ g j * μ h j) ∧ (∀ g j, μ g j ^ p = 1) ∧
      (∀ g, μ g 0 * μ g 1 * μ g 2 * μ g 3 = 1) ∧ (∀ g, (∀ j, μ g j = 1) → g = 1) := by
  classical
  obtain ⟨b, μ, hb⟩ := exists_eigenbasis_gl hζ E hcomm hexp
  have hne : ∀ j, b j ≠ 0 := fun j => b.ne_zero j
  have hpowA : ∀ (g : E) (j : Fin 4) (n : ℕ),
      (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ^ n) *ᵥ b j = μ g j ^ n • b j := by
    intro g j n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hb g j, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
  refine ⟨b, μ, hb, ?_, ?_, ?_, ?_⟩
  · intro g h j
    have h1 : ((g * h : E) : GL (Fin 4) K) = (g : GL (Fin 4) K) * (h : GL (Fin 4) K) := rfl
    have h2 := hb (g * h) j
    rw [h1, Units.val_mul, ← Matrix.mulVec_mulVec, hb h j, Matrix.mulVec_smul, hb g j, smul_smul] at h2
    have : (μ h j * μ g j) • b j = μ (g * h) j • b j := h2
    rw [mul_comm] at this
    exact (smul_left_injective K (hne j) this).symm
  · intro g j
    have h1 := hpowA g j p
    have h2 : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ^ p = 1 := by
      have := congrArg (fun x : GL (Fin 4) K => (x : Matrix (Fin 4) (Fin 4) K)) (hexp g g.2)
      simpa using this
    rw [h2, Matrix.one_mulVec] at h1
    have : (1 : K) • b j = μ g j ^ p • b j := by rw [one_smul]; exact h1
    exact (smul_left_injective K (hne j) this).symm
  · intro g
    have hdg := hdet g g.2
    let A : Matrix (Fin 4) (Fin 4) K := ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
    have h1 : (LinearMap.toMatrix b b (Matrix.toLin' A)).det = (Matrix.toLin' A).det :=
      LinearMap.det_toMatrix b _
    have h2 : (LinearMap.toMatrix' (Matrix.toLin' A)).det = (Matrix.toLin' A).det :=
      LinearMap.det_toMatrix' _
    rw [LinearMap.toMatrix'_toLin'] at h2
    have h3 : LinearMap.toMatrix b b (Matrix.toLin' A) = Matrix.diagonal (μ g) := by
      ext i j
      rw [LinearMap.toMatrix_apply, Matrix.toLin'_apply, hb g j, map_smul, Basis.repr_self,
        Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]
    rw [h3, Matrix.det_diagonal, Fin.prod_univ_four] at h1
    have : A.det = μ g 0 * μ g 1 * μ g 2 * μ g 3 := by rw [h2, ← h1]
    rw [← this]
    exact hdg
  · intro g hg
    apply Subtype.ext
    apply Units.ext
    refine matrix_ext_of_basis b (fun j => ?_)
    show ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ b j = (1 : Matrix (Fin 4) (Fin 4) K) *ᵥ b j
    rw [Matrix.one_mulVec]
    have := hb g j
    rw [hg j, one_smul] at this
    exact this

theorem exists_unitary_involution_four {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hK : Nat.card K = (ℓ ^ f) ^ 2) (hp : p.Prime) (h5 : 5 ≤ p) (hpq : p ∣ ℓ ^ f + 1)
    (h2 : (2 : K) ≠ 0) (E : Subgroup (GL (Fin 4) K)) [Finite E] (hE : E ≤ StatedSU 4 (ℓ ^ f) K)
    (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) (hexp : ∀ g ∈ E, g ^ p = 1) (hcard : p ^ 3 ≤ Nat.card E) :
    ∃ τ : GL (Fin 4) K, τ ∈ StatedSU 4 (ℓ ^ f) K ∧ τ ^ 2 = 1 ∧
      (∀ μ : Kˣ, τ ≠ Matrix.GeneralLinearGroup.scalar (Fin 4) μ) ∧ ∀ g ∈ E, g * τ = τ * g := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have hdvd : p ∣ Nat.card K - 1 := by
    rw [hK]
    obtain ⟨m, hm⟩ : ∃ m, ℓ ^ f = m + 1 := ⟨ℓ ^ f - 1, by
      have := Nat.one_le_pow f ℓ (Fact.out : ℓ.Prime).pos
      omega⟩
    rw [hm] at hpq ⊢
    have : (m + 1) ^ 2 - 1 = (m + 1 + 1) * m := by
      have h : (m + 1) ^ 2 = (m + 1 + 1) * m + 1 := by ring
      omega
    rw [this]
    exact Dvd.dvd.mul_right hpq m
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd_card_sub_one hp hdvd
  obtain ⟨b, μ, hb, hmul, hpow, hprod, hinj⟩ := eigen_chars_gl_four hζ E hcomm hexp
    (fun g hg => statedSU_det_eq_one' (hE hg))
  obtain ⟨hI1, -⟩ := eigen_independence hp h5 hζ μ hmul hpow hprod hinj hcard
  let F := unitaryForm ℓ f hK 4
  have hiso : ∀ g : E, ∀ x y : Fin 4 → K,
      F.β (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ x)
        (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ y) = F.β x y :=
    fun g x y => statedSU_preserves hK (hE g.2) x y
  have hσ : ∀ a : K, a ^ p = 1 → F.σ a * a = 1 := by
    intro a ha
    have hσa : F.σ a = a ^ (ℓ ^ f) := unitaryInvolution_apply K ℓ f a
    obtain ⟨t, ht⟩ := hpq
    have : a ^ (ℓ ^ f + 1) = 1 := by rw [ht, pow_mul, ha, one_pow]
    rw [hσa, ← pow_succ]
    exact this
  have horth : ∀ j k : Fin 4, j ≠ k → F.β (b j) (b k) = 0 := by
    intro j k hjk
    obtain ⟨g, hg⟩ := hI1 j k hjk
    refine β_eq_zero_of_eigen F (g := fun v => ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v)
      (fun x y => hiso g x y) (hb g j) (hb g k) ?_
    intro h1
    apply hg
    have hjj := hσ (μ g j) (hpow g j)
    have hne : μ g j ≠ 0 := fun h0 => by rw [h0, map_zero, zero_mul] at hjj; exact zero_ne_one hjj
    have : F.σ (μ g j) * μ g k = F.σ (μ g j) * μ g j := by rw [h1, hjj]
    exact (mul_left_cancel₀ (fun h0 => by
      have := hjj
      rw [h0, zero_mul] at this
      exact zero_ne_one this) this).symm
  obtain ⟨M, hMdet, hMiso, hMb⟩ := exists_sign_matrix_four F b horth
  have hMdet0 : M.det ≠ 0 := by rw [hMdet]; exact one_ne_zero
  let τ : GL (Fin 4) K := Matrix.GeneralLinearGroup.mkOfDetNeZero M hMdet0
  have hτM : ((τ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = M := rfl
  have hMsq : M * M = 1 := by
    refine matrix_ext_of_basis b (fun j => ?_)
    rw [← Matrix.mulVec_mulVec, hMb j, Matrix.mulVec_smul, hMb j, smul_smul, Matrix.one_mulVec]
    have : (if (j : ℕ) < 2 then (-1 : K) else 1) * (if (j : ℕ) < 2 then (-1 : K) else 1) = 1 := by
      split_ifs <;> simp
    rw [this, one_smul]
  refine ⟨τ, mkOfDetNeZero_mem_statedSU hK M hMdet hMiso, ?_, ?_, ?_⟩
  · apply Units.ext
    rw [pow_two, Units.val_mul, hτM, hMsq]
    rfl
  · intro c hc
    have hscal : ∀ v, M *ᵥ v = (c : K) • v := by
      intro v
      have := congrArg (fun x : GL (Fin 4) K => (x : Matrix (Fin 4) (Fin 4) K)) hc
      simp only [hτM, Matrix.GeneralLinearGroup.coe_scalar] at this
      rw [this]
      funext i
      simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
    have h0 := hMb 0
    have h2' := hMb 2
    rw [hscal] at h0 h2'
    have e0 : (c : K) = -1 := by
      apply smul_left_injective K (b.ne_zero 0)
      simpa using h0
    have e2 : (c : K) = 1 := by
      apply smul_left_injective K (b.ne_zero 2)
      simpa using h2'
    exact h2 (by linear_combination e0 - e2)
  · intro g hg
    refine Units.ext (matrix_ext_of_basis b (fun j => ?_))
    have hbg := hb ⟨g, hg⟩ j
    have e1 : ((g * τ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = (g : Matrix (Fin 4) (Fin 4) K) * M := rfl
    have e2 : ((τ * g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = M * (g : Matrix (Fin 4) (Fin 4) K) := rfl
    rw [e1, e2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hMb j, Matrix.mulVec_smul]
    have hbg' : (g : Matrix (Fin 4) (Fin 4) K) *ᵥ b j = μ ⟨g, hg⟩ j • b j := hbg
    rw [hbg', Matrix.mulVec_smul, hMb j, smul_comm]

theorem false_of_unitary_rank_three {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hK : Nat.card K = (ℓ ^ f) ^ 2) (hp : p.Prime) (h5 : 5 ≤ p) (hpq : p ∣ ℓ ^ f - 1)
    (E : Subgroup (GL (Fin 4) K)) [Finite E] (hE : E ≤ StatedSU 4 (ℓ ^ f) K)
    (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) (hexp : ∀ g ∈ E, g ^ p = 1) (hcard : p ^ 3 ≤ Nat.card E) :
    False := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow f ℓ (Fact.out : ℓ.Prime).pos
  have hdvd : p ∣ Nat.card K - 1 := by
    rw [hK]
    obtain ⟨m, hm⟩ : ∃ m, ℓ ^ f = m + 1 := ⟨ℓ ^ f - 1, by omega⟩
    rw [hm] at hpq ⊢
    have : (m + 1) ^ 2 - 1 = (m + 1 + 1) * m := by
      have h : (m + 1) ^ 2 = (m + 1 + 1) * m + 1 := by ring
      omega
    rw [this]
    have hm' : p ∣ m := by simpa using hpq
    exact Dvd.dvd.mul_left hm' _
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd_card_sub_one hp hdvd
  obtain ⟨b, μ, hb, hmul, hpow, hprod, hinj⟩ := eigen_chars_gl_four hζ E hcomm hexp
    (fun g hg => statedSU_det_eq_one' (hE hg))
  obtain ⟨-, hI2⟩ := eigen_independence hp h5 hζ μ hmul hpow hprod hinj hcard
  let F := unitaryForm ℓ f hK 4
  have hiso : ∀ g : E, ∀ x y : Fin 4 → K,
      F.β (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ x)
        (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ y) = F.β x y :=
    fun g x y => statedSU_preserves hK (hE g.2) x y
  have hσ : ∀ a : K, a ^ p = 1 → F.σ a = a := by
    intro a ha
    have hσa : F.σ a = a ^ (ℓ ^ f) := unitaryInvolution_apply K ℓ f a
    obtain ⟨t, ht⟩ := hpq
    have : ℓ ^ f = 1 + p * t := by omega
    rw [hσa, this, pow_add, pow_mul, ha, one_pow, mul_one, pow_one]
  have horth : ∀ j k : Fin 4, F.β (b j) (b k) = 0 := by
    intro j k
    obtain ⟨g, hg⟩ := hI2 j k
    refine β_eq_zero_of_eigen F (g := fun v => ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v)
      (fun x y => hiso g x y) (hb g j) (hb g k) ?_
    rwa [hσ _ (hpow g j)]
  apply b.ne_zero 0
  apply F.nondeg
  intro v
  conv_lhs => rw [← b.sum_repr v]
  rw [ReflForm.β_sum_right]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [F.smul_right, horth 0 k, mul_zero]

theorem exists_normalized_two_subgroup {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    {p N : ℕ} (hp : p.Prime) (hN : ¬ p ∣ N) (M : Subgroup (GL ι K))
    (hZN : ∀ z : M, (z : GL ι K) ∈ StatedScalars ι K → z ^ N = 1)
    (hτ : ∀ E : Subgroup (GL ι K), E ≤ M → Finite E → (∀ g ∈ E, ∀ h ∈ E, g * h = h * g) →
      (∀ g ∈ E, g ^ p = 1) → p ^ 3 ≤ Nat.card E →
      ∃ τ : GL ι K, τ ∈ M ∧ τ ^ 2 = 1 ∧ (∀ μ : Kˣ, τ ≠ Matrix.GeneralLinearGroup.scalar ι μ) ∧
        ∀ g ∈ E, g * τ = τ * g)
    (A : Subgroup (StatedProj M)) (hA : IsElementaryAbelian p A) (hAc : Nat.card A = p ^ 3) :
    ∃ S : Subgroup (StatedProj M), S ≠ ⊥ ∧ IsPGroup 2 S ∧
      A ≤ Subgroup.normalizer (S : Set (StatedProj M)) := by
  classical
  obtain ⟨E, hEmap, hEcomm, hEexp⟩ := exists_lift_elemAb_statedProj hp hN M hZN A hA
  have hEcard : p ^ 3 ≤ Nat.card E := by
    rw [← hAc, ← hEmap]
    have hsurj : Function.Surjective
        (fun x : E => (⟨QuotientGroup.mk' ((StatedScalars ι K).subgroupOf M) x,
          Subgroup.mem_map_of_mem _ x.2⟩ :
            E.map (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf M)))) := by
      rintro ⟨_, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    exact Nat.card_le_card_of_surjective _ hsurj
  have hfinE : Finite (E.map M.subtype) := inferInstance
  obtain ⟨τ, hτM, hτ2, hτns, hτc⟩ := hτ (E.map M.subtype) (by
      rintro _ ⟨a, -, rfl⟩
      exact a.2) hfinE
    (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simpa using congrArg M.subtype (hEcomm a ha b hb))
    (by
      rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hEexp a ha, map_one])
    (by rw [Subgroup.card_map_of_injective M.subtype_injective]; exact hEcard)
  let t : StatedProj M :=
    QuotientGroup.mk (s := (StatedScalars ι K).subgroupOf M) (⟨τ, hτM⟩ : M)
  have ht2 : t ^ 2 = 1 := by
    have : (⟨τ, hτM⟩ : M) ^ 2 = 1 := Subtype.ext (by simpa using hτ2)
    show (QuotientGroup.mk (⟨τ, hτM⟩ : M) : StatedProj M) ^ 2 = 1
    rw [← QuotientGroup.mk_pow, this]
    rfl
  refine ⟨Subgroup.zpowers t, ?_, ?_, ?_⟩
  · intro hbot
    have hmem : t ∈ Subgroup.zpowers t := Subgroup.mem_zpowers t
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : (⟨τ, hτM⟩ : M) ∈ (StatedScalars ι K).subgroupOf M := (QuotientGroup.eq_one_iff _).1 hmem
    obtain ⟨μ, hμ⟩ := Subgroup.mem_subgroupOf.1 h1
    exact hτns μ hμ.symm
  · intro y
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 y.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hk]
    calc (t ^ k) ^ 2 = (t ^ 2) ^ k := by group
      _ = 1 := by rw [ht2, _root_.one_zpow]
  · intro a ha
    rw [← hEmap] at ha
    obtain ⟨g, hg, rfl⟩ := ha
    refine mem_normalizer_of_forall_commute _ _ ?_
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hgt : QuotientGroup.mk' ((StatedScalars ι K).subgroupOf M) g * t =
        t * QuotientGroup.mk' ((StatedScalars ι K).subgroupOf M) g := by
      show (QuotientGroup.mk g : StatedProj M) * QuotientGroup.mk (⟨τ, hτM⟩ : M) =
        QuotientGroup.mk (⟨τ, hτM⟩ : M) * (QuotientGroup.mk g : StatedProj M)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      exact hτc (g : GL ι K) ⟨g, hg, rfl⟩
    exact (Commute.zpow_right (show Commute _ t from hgt) k).eq

theorem statedSU_scalar_pow {n q : ℕ} {K : Type} [Field K] (z : StatedSU n q K)
    (hz : (z : GL (Fin n) K) ∈ StatedScalars (Fin n) K) : z ^ n = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow]
  have hc : (z : GL (Fin n) K) ∈ Subgroup.center (GL (Fin n) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact hz
  have := LIT.pow_card_eq_one_of_det (z : GL (Fin n) K) hc (statedSU_det_eq_one' z.2)
  simpa using this

theorem card_le_sq_of_no_cube {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (E : Subgroup G)
    (hexp : ∀ g ∈ E, g ^ p = 1)
    (hno : p ^ 3 ≤ Nat.card E → False) : Nat.card E ≤ p ^ 2 := by
  have hpg : IsPGroup p E := fun a => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hexp a a.2)⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := hpg.exists_card_eq
  by_contra hlt
  apply hno
  rw [hm] at hlt ⊢
  have hm3 : 3 ≤ m := by
    by_contra h
    have : m ≤ 2 := by omega
    exact hlt (Nat.pow_le_pow_right hp.pos this)
  exact Nat.pow_le_pow_right hp.pos hm3

theorem dead_statedProj_su_four {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hp : p.Prime) (h5 : 5 ≤ p) (hpq : p ∣ ℓ ^ f + 1) (h2 : (2 : K) ≠ 0)
    (hZ : Subgroup.center (StatedProj (StatedSU 4 (ℓ ^ f) K)) = ⊥)
    (hOut : ∀ E : Subgroup (MulAut (StatedProj (StatedSU 4 (ℓ ^ f) K))), IsElementaryAbelian p E →
      E ≤ ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSU 4 (ℓ ^ f) K))) :
    Dead p (StatedProj (StatedSU 4 (ℓ ^ f) K)) := by
  have hp4 : ¬ p ∣ 4 := fun h => by
    have := Nat.le_of_dvd (by norm_num) h
    omega
  refine dead_of_inner_el hp hZ hOut ?_
  intro A hA hAc
  exact exists_normalized_two_subgroup (N := 4) hp hp4 (StatedSU 4 (ℓ ^ f) K)
    (fun z hz => statedSU_scalar_pow z hz)
    (fun E hEM hfin hcomm hexp hcard => by
      obtain ⟨τ, hτM, hτ2, hτns, hτc⟩ :=
        exists_unitary_involution_four hK hp h5 hpq h2 E hEM hcomm hexp hcard
      exact ⟨τ, hτM, hτ2, hτns, hτc⟩) A hA hAc

theorem noRankThree_statedProj_su_four {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hK : Nat.card K = (ℓ ^ f) ^ 2) (hp : p.Prime) (h5 : 5 ≤ p) (hpK : (p : K) ≠ 0)
    (hpq : ¬ p ∣ ℓ ^ f + 1)
    (hZ : Subgroup.center (StatedProj (StatedSU 4 (ℓ ^ f) K)) = ⊥)
    (hOut : ∀ E : Subgroup (MulAut (StatedProj (StatedSU 4 (ℓ ^ f) K))), IsElementaryAbelian p E →
      E ≤ ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSU 4 (ℓ ^ f) K))) :
    NoRankThree p (StatedProj (StatedSU 4 (ℓ ^ f) K)) := by
  have hp4 : ¬ p ∣ 4 := fun h => by
    have := Nat.le_of_dvd (by norm_num) h
    omega
  refine noRankThree_of_inner_rank_el hp hZ hOut ?_
  intro A hA hAc
  have hle : Nat.card A ≤ p ^ 2 := by
    by_cases hm : p ∣ ℓ ^ f - 1
    · refine statedProj_card_le_of_bound (N := 4) (k := 2) hp hp4 (StatedSU 4 (ℓ ^ f) K)
        (fun z hz => statedSU_scalar_pow z hz) (fun E hEM hcomm hexp => ?_) A hA
      exact card_le_sq_of_no_cube hp E hexp fun hcard =>
        false_of_unitary_rank_three hK hp h5 hm E hEM hcomm hexp hcard
    · refine statedProj_card_le_of_bound (N := 4) (k := 2) hp hp4 (StatedSU 4 (ℓ ^ f) K)
        (fun z hz => statedSU_scalar_pow z hz) (fun E hEM hcomm hexp => ?_) A hA
      have hdiv : ¬ p ∣ Nat.card K - 1 := by
        intro hd
        rw [hK] at hd
        have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow f ℓ (Fact.out : ℓ.Prime).pos
        obtain ⟨m, hmq⟩ : ∃ m, ℓ ^ f = m + 1 := ⟨ℓ ^ f - 1, by omega⟩
        rw [hmq] at hd hpq hm
        have e : (m + 1) ^ 2 - 1 = (m + 1 + 1) * m := by
          have h : (m + 1) ^ 2 = (m + 1 + 1) * m + 1 := by ring
          omega
        rw [e] at hd
        rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
        · exact hpq h
        · exact hm (by simpa using h)
      have := LIT.card_le_pow_div_gl hp hpK (d := 2) (by norm_num)
        (fun i hi0 hi2 => by
          have : i = 1 := by omega
          subst this
          simpa using hdiv) E hcomm hexp
      simpa using this
  rw [hAc] at hle
  have h2 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

end CFSG.RankThree.PartOne.K133
