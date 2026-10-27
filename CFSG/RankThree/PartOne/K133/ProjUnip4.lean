module

public import CFSG.RankThree.PartOne.K133.PerfectUnip4
public import CFSG.RankThree.PartOne.K133.ProjUnip3

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG.Assembly.LowTwoRank Matrix Module
open scoped commutatorElement

theorem one_add_pow_of_sq_eq_zero {R : Type*} [Ring R] {N : R} (h : N * N = 0) (k : ℕ) :
    (1 + N) ^ k = 1 + (k : R) * N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    have : (1 + (k : R) * N) * (1 + N) = 1 + ((k : R) + 1) * N + (k : R) * (N * N) := by
      noncomm_ring
    rw [this, h]
    push_cast
    simp

theorem exists_unip_normalization {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] (a : GL n K) (c : Kˣ)
    (hac : a ^ p = Matrix.GeneralLinearGroup.scalar n c) :
    ∃ μ : Kˣ, (μ : K) ^ p = (c : K) ∧
      (((μ⁻¹ : Kˣ) : K) • ((a : GL n K) : Matrix n n K) - 1) ^ p = 0 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨μ, hμ⟩ : ∃ μ : K, μ ^ p = (c : K) := by
    have hsurj : Function.Surjective (frobenius K p) :=
      Finite.surjective_of_injective (frobenius_inj K p)
    obtain ⟨μ, hμ⟩ := hsurj (c : K)
    exact ⟨μ, by simpa [frobenius_def] using hμ⟩
  have hμ0 : μ ≠ 0 := by
    intro h0
    have : (c : K) = 0 := by rw [← hμ, h0, zero_pow (Fact.out : p.Prime).ne_zero]
    exact c.ne_zero this
  refine ⟨Units.mk0 μ hμ0, hμ, ?_⟩
  set A : Matrix n n K := ((a : GL n K) : Matrix n n K) with hA
  have hAp : A ^ p = (c : K) • (1 : Matrix n n K) := by
    have := congrArg (fun g : GL n K => (g : Matrix n n K)) hac
    simp only [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar] at this
    rw [scalar_eq_smul_one'] at this
    exact this
  have hc : Commute ((((Units.mk0 μ hμ0)⁻¹ : Kˣ) : K) • A : Matrix n n K) 1 := Commute.one_right _
  have := sub_pow_char_of_commute p hc
  rw [this, smul_pow, hAp, one_pow, smul_smul]
  have : (((Units.mk0 μ hμ0)⁻¹ : Kˣ) : K) ^ p * (c : K) = 1 := by
    rw [Units.val_inv_eq_inv_val, inv_pow, Units.val_mk0, hμ]
    simp [c.ne_zero]
  simp only [this]
  simp

@[expose] def unipPart {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] (μ : Kˣ) (a : GL ι K) :
    Matrix ι ι K :=
  ((μ⁻¹ : Kˣ) : K) • ((a : GL ι K) : Matrix ι ι K) - 1

theorem hom_perfect_pow_eq_one_four' {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp5 : 5 ≤ p) {ι : Type} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = 4) {G : Type*} [Group G] [Group.IsPerfect G]
    (σ : G →* GL ι K) (a₁ a₂ : GL ι K) (hcomm₁ : ∀ y, σ y * a₁ = a₁ * σ y)
    (hcomm₂ : ∀ y, σ y * a₂ = a₂ * σ y) (h12 : a₁ * a₂ = a₂ * a₁) (c₁ c₂ : Kˣ)
    (hac₁ : a₁ ^ p = Matrix.GeneralLinearGroup.scalar ι c₁)
    (hac₂ : a₂ ^ p = Matrix.GeneralLinearGroup.scalar ι c₂)
    (hna₁ : ∀ μ : Kˣ, a₁ ≠ Matrix.GeneralLinearGroup.scalar ι μ)
    (hind : ∀ (k : ℕ) (μ : Kˣ), a₂ ≠ Matrix.GeneralLinearGroup.scalar ι μ * a₁ ^ k)
    (hK : ∀ μ₁ μ₂ : Kˣ, (μ₁ : K) ^ p = (c₁ : K) → (μ₂ : K) ^ p = (c₂ : K) →
      unipPart μ₁ a₁ * unipPart μ₁ a₁ = 0 → unipPart μ₁ a₁ ≠ 0 →
      ∀ c : K, unipPart μ₂ a₂ = c • unipPart μ₁ a₁ → ∃ k : ℕ, (k : K) = c) :
    ∀ y, σ y ^ p = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hne : Nonempty ι := Fintype.card_pos_iff.1 (by rw [hι]; norm_num)
  obtain ⟨μ₁, hμ₁p, hN₁p⟩ := exists_unip_normalization a₁ c₁ hac₁
  obtain ⟨μ₂, hμ₂p, hN₂p⟩ := exists_unip_normalization a₂ c₂ hac₂
  set A₁ : Matrix ι ι K := ((a₁ : GL ι K) : Matrix ι ι K) with hA₁
  set A₂ : Matrix ι ι K := ((a₂ : GL ι K) : Matrix ι ι K) with hA₂
  set N₁ : Matrix ι ι K := ((μ₁⁻¹ : Kˣ) : K) • A₁ - 1 with hN₁
  set N₂ : Matrix ι ι K := ((μ₂⁻¹ : Kˣ) : K) • A₂ - 1 with hN₂
  have hA₁₂ : A₁ * A₂ = A₂ * A₁ := by
    have := congrArg (fun g : GL ι K => (g : Matrix ι ι K)) h12
    simpa [hA₁, hA₂] using this
  have hN₁₂ : N₁ * N₂ = N₂ * N₁ := by
    have hC : Commute A₁ A₂ := hA₁₂
    have h1 : Commute (((μ₁⁻¹ : Kˣ) : K) • A₁) (((μ₂⁻¹ : Kˣ) : K) • A₂) :=
      (hC.smul_left _).smul_right _
    have h2 : Commute (((μ₁⁻¹ : Kˣ) : K) • A₁ - 1) (((μ₂⁻¹ : Kˣ) : K) • A₂) :=
      h1.sub_left (Commute.one_left _)
    exact (h2.sub_right (Commute.one_right _)).eq
  have hN₁0 : N₁ ≠ 0 := by
    intro h0
    apply hna₁ μ₁
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar, scalar_eq_smul_one']
    have h1 : ((μ₁⁻¹ : Kˣ) : K) • A₁ = 1 := sub_eq_zero.1 h0
    have h2 : A₁ = (μ₁ : K) • (1 : Matrix ι ι K) := by
      calc A₁ = (μ₁ : K) • (((μ₁⁻¹ : Kˣ) : K) • A₁) := by
            rw [smul_smul, Units.val_inv_eq_inv_val, mul_inv_cancel₀ μ₁.ne_zero, one_smul]
        _ = (μ₁ : K) • (1 : Matrix ι ι K) := by rw [h1]
    simpa [hA₁] using h2
  let e : Matrix ι ι K ≃ₐ[K] Module.End K (ι → K) := Matrix.toLinAlgEquiv'
  let ρ : G →* Module.End K (ι → K) :=
    (e.toRingEquiv.toMonoidHom).comp ((Units.coeHom (Matrix ι ι K)).comp σ)
  have hρ : ∀ y, ρ y = e ((σ y : GL ι K) : Matrix ι ι K) := fun y => rfl
  have hcommA : ∀ (a : GL ι K), (∀ y, σ y * a = a * σ y) → ∀ y,
      ((σ y : GL ι K) : Matrix ι ι K) * ((a : GL ι K) : Matrix ι ι K) =
        ((a : GL ι K) : Matrix ι ι K) * ((σ y : GL ι K) : Matrix ι ι K) := by
    intro a ha y
    have := congrArg (fun g : GL ι K => (g : Matrix ι ι K)) (ha y)
    simpa using this
  have hcommN : ∀ (A : Matrix ι ι K) (r : K), (∀ y, ((σ y : GL ι K) : Matrix ι ι K) * A =
      A * ((σ y : GL ι K) : Matrix ι ι K)) → ∀ y,
      ((σ y : GL ι K) : Matrix ι ι K) * (r • A - 1) =
        (r • A - 1) * ((σ y : GL ι K) : Matrix ι ι K) := by
    intro A r hA y
    rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, hA y]
    simp
  have hcN₁ := hcommN A₁ ((μ₁⁻¹ : Kˣ) : K) (hcommA a₁ hcomm₁)
  have hcN₂ := hcommN A₂ ((μ₂⁻¹ : Kˣ) : K) (hcommA a₂ hcomm₂)
  have hnil₁ : IsNilpotent (e N₁) := ⟨p, by rw [← map_pow, hN₁p, map_zero]⟩
  have hnil₂ : IsNilpotent (e N₂) := ⟨p, by rw [← map_pow, hN₂p, map_zero]⟩
  have hn0 : e N₁ ≠ 0 := fun h => hN₁0 (e.injective (by rw [h, map_zero]))
  have hrcomm₁ : ∀ y, ρ y * e N₁ = e N₁ * ρ y := fun y => by
    rw [hρ, ← map_mul, ← map_mul]
    exact congrArg e (hcN₁ y)
  have hrcomm₂ : ∀ y, ρ y * e N₂ = e N₂ * ρ y := fun y => by
    rw [hρ, ← map_mul, ← map_mul]
    exact congrArg e (hcN₂ y)
  have hfin : Module.finrank K (ι → K) = 4 := by rw [Module.finrank_fintype_fun_eq_card, hι]
  have h2K : (2 : K) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff K p] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hindN : ¬ ((e N₁) ^ 2 = 0 ∧ ∃ c : K, e N₂ = c • e N₁) := by
    rintro ⟨hsq, c, hc⟩
    have hsqm : N₁ * N₁ = 0 := by
      have : e (N₁ ^ 2) = 0 := by rw [map_pow]; exact hsq
      have h0 : N₁ ^ 2 = 0 := e.injective (by rw [this, map_zero])
      rwa [pow_two] at h0
    have hN₂c : N₂ = c • N₁ := by
      apply e.injective
      rw [hc, map_smul]
    obtain ⟨k, rfl⟩ := hK μ₁ μ₂ hμ₁p hμ₂p hsqm hN₁0 c hN₂c
    have hN₂eq : N₂ = (k : K) • N₁ := hN₂c
    have hpow : (1 + N₁) ^ k = 1 + (k : K) • N₁ := by
      have := one_add_pow_of_sq_eq_zero hsqm k
      rw [this]
      congr 1
      rw [← nsmul_eq_mul, Nat.cast_smul_eq_nsmul]
    have hN₁' : ((μ₁⁻¹ : Kˣ) : K) • A₁ = 1 + N₁ := by rw [hN₁]; abel
    have hN₂' : ((μ₂⁻¹ : Kˣ) : K) • A₂ = 1 + N₂ := by rw [hN₂]; abel
    have hA₂eq : A₂ = ((μ₂ * μ₁⁻¹ ^ k : Kˣ) : K) • A₁ ^ k := by
      have h1 : (((μ₂⁻¹ : Kˣ) : K) • A₂) = (((μ₁⁻¹ : Kˣ) : K) • A₁) ^ k := by
        rw [hN₂', hN₁', hpow, hN₂eq]
      have h2 : A₂ = ((μ₂ : Kˣ) : K) • (((μ₂⁻¹ : Kˣ) : K) • A₂) := by
        rw [smul_smul, Units.val_inv_eq_inv_val, mul_inv_cancel₀ μ₂.ne_zero, one_smul]
      rw [h2, h1, smul_pow, smul_smul, Units.val_mul, Units.val_pow_eq_pow_val]
    apply hind k (μ₂ * μ₁⁻¹ ^ k)
    apply Units.ext
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, scalar_eq_smul_one',
      Units.val_pow_eq_pow_val, smul_mul_assoc, one_mul]
    exact hA₂eq
  have hkey := perfect_unipotent_of_two_nilpotents_four h2K hfin ρ inferInstance
    (by rw [← map_mul, ← map_mul, hN₁₂]) hnil₁ hnil₂ hrcomm₁ hrcomm₂ hn0 hindN
  intro y
  have h3 : ((((σ y : GL ι K) : Matrix ι ι K) - 1) ^ 4 = 0) := by
    have := hkey y
    rw [hρ] at this
    have h4 : e (((σ y : GL ι K) : Matrix ι ι K) - 1) ^ 4 = 0 := by
      simpa [map_sub, map_one] using this
    rw [← map_pow] at h4
    exact e.injective (by rw [h4, map_zero])
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  set E : Matrix ι ι K := ((σ y : GL ι K) : Matrix ι ι K) - 1 with hE
  have hEy : ((σ y : GL ι K) : Matrix ι ι K) = 1 + E := by rw [hE]; abel
  rw [hEy]
  have hEp : E ^ p = 0 := by
    obtain ⟨k, hk⟩ : ∃ k, p = 4 + k := ⟨p - 4, by omega⟩
    rw [hk, pow_add, h3, zero_mul]
  have := add_pow_char_of_commute (x := (1 : Matrix ι ι K)) (y := E) p
    (Commute.one_left E)
  rw [this, hEp, one_pow]
  simp

theorem statedProj_four_no_config' {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp5 : 5 ≤ p) {ι : Type} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = 4) (M : Subgroup (GL ι K))
    (hK : ∀ (a₁ a₂ : M) (c₁ c₂ : Kˣ) (μ₁ μ₂ : Kˣ),
      (a₁ : GL ι K) ^ p = Matrix.GeneralLinearGroup.scalar ι c₁ →
      (a₂ : GL ι K) ^ p = Matrix.GeneralLinearGroup.scalar ι c₂ →
      (μ₁ : K) ^ p = (c₁ : K) → (μ₂ : K) ^ p = (c₂ : K) →
      unipPart μ₁ (a₁ : GL ι K) * unipPart μ₁ (a₁ : GL ι K) = 0 → unipPart μ₁ (a₁ : GL ι K) ≠ 0 →
      ∀ c : K, unipPart μ₂ (a₂ : GL ι K) = c • unipPart μ₁ (a₁ : GL ι K) → ∃ k : ℕ, (k : K) = c)
    (C : Subgroup (StatedProj M)) (hC : IsElementaryAbelian p C) (hCc : Nat.card C = p ^ 2)
    (Kb : Subgroup (StatedProj M)) [IsSimpleGroup Kb] (hKn : ∃ a b : Kb, a * b ≠ b * a)
    (hcomm : ∀ c ∈ C, ∀ k ∈ Kb, c * k = k * c) : False := by
  classical
  have hp : p.Prime := Fact.out
  set Z : Subgroup M := (StatedScalars ι K).subgroupOf M with hZ
  have hZc : Z ≤ Subgroup.center M := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro m
    have hz' : (z : GL ι K) ∈ StatedScalars ι K := hz
    rw [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz'
    exact Subtype.ext (Subgroup.mem_center_iff.1 hz' (m : GL ι K))
  let mk : M →* StatedProj M := QuotientGroup.mk' Z
  have hKperf : Group.IsPerfect Kb := isPerfect_of_simple_nonabelian hKn
  set P₀ : Subgroup M := ⁅Kb.comap mk, Kb.comap mk⁆ with hP₀
  have hP₀perf : Group.IsPerfect P₀ := CFSG.RankThree.SubgroupLists.isPerfect_commutator_comap hZc Kb
  have hP₀map : P₀.map mk = Kb := CFSG.RankThree.SubgroupLists.map_commutator_comap Kb
  have hP₀K : ∀ y ∈ P₀, mk y ∈ Kb := fun y hy => hP₀map ▸ Subgroup.mem_map_of_mem mk hy
  have : Nontrivial C := by
    have : Finite C := inferInstance
    apply Finite.one_lt_card_iff_nontrivial.1
    rw [hCc]
    exact Nat.one_lt_pow (by norm_num) hp.one_lt
  obtain ⟨x₁, hx₁1⟩ := exists_ne (1 : C)
  have hxp : ∀ x : C, (x : StatedProj M) ^ p = 1 := fun x =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := C) (x : StatedProj M) x.2
  obtain ⟨x₂, hx₂⟩ : ∃ x₂ : C, (x₂ : StatedProj M) ∉ Subgroup.zpowers (x₁ : StatedProj M) := by
    by_contra hall
    push Not at hall
    have hle : (⊤ : Subgroup C) ≤ Subgroup.zpowers x₁ := by
      intro y _
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hall y)
      exact Subgroup.mem_zpowers_iff.2 ⟨n, Subtype.ext (by simpa using hn)⟩
    have hord : orderOf x₁ = p := by
      apply orderOf_eq_prime
      · exact Subtype.ext (hxp x₁)
      · exact hx₁1
    have h1 : Nat.card C ≤ p := by
      have := Subgroup.card_le_of_le hle
      rw [Nat.card_zpowers, hord] at this
      simpa using this
    rw [hCc] at h1
    have hp2 : 2 ≤ p := hp.two_le
    nlinarith
  obtain ⟨a₁, ha₁⟩ := QuotientGroup.mk_surjective (x₁ : StatedProj M)
  obtain ⟨a₂, ha₂⟩ := QuotientGroup.mk_surjective (x₂ : StatedProj M)
  have hmk₁ : mk a₁ = (x₁ : StatedProj M) := ha₁
  have hmk₂ : mk a₂ = (x₂ : StatedProj M) := ha₂
  have hap : ∀ (a : M) (x : StatedProj M), mk a = x → x ^ p = 1 → a ^ p ∈ Z := by
    intro a x hax hxp'
    rw [← QuotientGroup.eq_one_iff]
    change mk (a ^ p) = 1
    rw [map_pow, hax, hxp']
  have hap₁ := hap a₁ _ hmk₁ (hxp x₁)
  have hap₂ := hap a₂ _ hmk₂ (hxp x₂)
  obtain ⟨c₁, hc₁⟩ : ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c = ((a₁ ^ p : M) : GL ι K) := by
    exact hap₁
  obtain ⟨c₂, hc₂⟩ : ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c = ((a₂ ^ p : M) : GL ι K) := by
    exact hap₂
  have hna₁ : ∀ μ : Kˣ, (a₁ : GL ι K) ≠ Matrix.GeneralLinearGroup.scalar ι μ := by
    intro μ hμ
    apply hx₁1
    apply Subtype.ext
    show (x₁ : StatedProj M) = 1
    rw [← hmk₁]
    change ((a₁ : M) : StatedProj M) = 1
    rw [QuotientGroup.eq_one_iff]
    change (a₁ : GL ι K) ∈ StatedScalars ι K
    exact ⟨μ, hμ.symm⟩
  have hx₁₂ : (x₁ : StatedProj M) * x₂ = x₂ * x₁ := by
    have := hC.is_comm.comm x₁ x₂
    exact congrArg Subtype.val this
  have hcomm₁₂ : a₁ * a₂ = a₂ * a₁ := by
    have hz : ⁅a₁, a₂⁆ ∈ Z := by
      rw [← QuotientGroup.eq_one_iff]
      change mk ⁅a₁, a₂⁆ = 1
      rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, hmk₁, hmk₂, hx₁₂]
      group
    set z : M := ⁅a₁, a₂⁆ with hzdef
    have hzc : z ∈ Subgroup.center M := hZc hz
    have hcz : Commute z a₂ := (Subgroup.mem_center_iff.1 hzc a₂).symm
    have hconj : a₁ * a₂ * a₁⁻¹ = z * a₂ := by
      rw [hzdef, commutatorElement_def]; group
    have ha₂p : a₁ * a₂ ^ p * a₁⁻¹ = a₂ ^ p := by
      have := Subgroup.mem_center_iff.1 (hZc hap₂) a₁
      calc a₁ * a₂ ^ p * a₁⁻¹ = a₂ ^ p * a₁ * a₁⁻¹ := by rw [this]
        _ = a₂ ^ p := by group
    have hzp : z ^ p = 1 := by
      have h1 : a₁ * a₂ ^ p * a₁⁻¹ = z ^ p * a₂ ^ p := by
        rw [← conj_pow, hconj, hcz.mul_pow]
      rw [h1] at ha₂p
      exact mul_eq_right.1 ha₂p
    obtain ⟨s, hs⟩ : ∃ s : Kˣ, Matrix.GeneralLinearGroup.scalar ι s = (z : GL ι K) := hz
    have hdet : s ^ 4 = 1 := by
      have h1 : Matrix.GeneralLinearGroup.det (z : GL ι K) = 1 := by
        have h0 : (z : GL ι K) = ⁅(a₁ : GL ι K), (a₂ : GL ι K)⁆ := by
          simp [hzdef, commutatorElement_def]
        rw [h0, map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
      rw [← hs, Matrix.GeneralLinearGroup.det_scalar, hι] at h1
      simpa using h1
    have hsp : s ^ p = 1 := by
      have h1 : ((z : M) : GL ι K) ^ p = 1 := by
        rw [← Subgroup.coe_pow, hzp]; rfl
      have h2 : (Matrix.GeneralLinearGroup.scalar ι (s ^ p) : GL ι K) = 1 := by
        rw [map_pow, hs]; exact h1
      have h3 := congrArg (fun g : GL ι K => (g : Matrix ι ι K)) h2
      rw [Matrix.GeneralLinearGroup.coe_scalar] at h3
      obtain ⟨i₀⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by rw [hι]; norm_num)
      have h4 := congrFun (congrFun h3 i₀) i₀
      apply Units.ext
      rw [Units.val_one]
      simpa [Matrix.scalar_apply, Matrix.diagonal_apply_eq] using h4
    have hcop : Nat.Coprime p 4 := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    have hs1 : s = 1 := (pow_eq_one_iff_of_coprime hcop).1 ⟨hsp, hdet⟩
    have hz1 : z = 1 := by
      apply Subtype.ext
      rw [← hs, hs1, map_one]
      rfl
    exact commutatorElement_eq_one_iff_mul_comm.1 hz1
  have : Group.IsPerfect P₀ := hP₀perf
  have hcommA : ∀ (a : M) (x : C), mk a = (x : StatedProj M) → ∀ y : P₀, (y : M) * a = a * (y : M) := by
    intro a x hax y
    have h := KFU.commute_of_central_commute (S := ↥P₀) (S' := ↥(Subgroup.zpowers a)) mk
      (by rw [QuotientGroup.ker_mk']; exact hZc) P₀.subtype (Subgroup.zpowers a).subtype
      (fun A B => by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 B.2
        have hB : mk (B : M) = (x : StatedProj M) ^ k := by
          rw [← hk, map_zpow, hax]
        change mk (A : M) * mk (B : M) = mk (B : M) * mk (A : M)
        rw [hB]
        exact (Commute.zpow_right
          (show Commute (mk (A : M)) (x : StatedProj M) from (hcomm _ x.2 _ (hP₀K _ A.2)).symm) k).eq)
      y ⟨a, Subgroup.mem_zpowers a⟩
    exact h
  let σ : ↥P₀ →* GL ι K := M.subtype.comp P₀.subtype
  have hind : ∀ (k : ℕ) (μ : Kˣ), (a₂ : GL ι K) ≠
      Matrix.GeneralLinearGroup.scalar ι μ * (a₁ : GL ι K) ^ k := by
    intro k μ hμ
    apply hx₂
    have hu : (a₂ * (a₁ ^ k)⁻¹ : M) ∈ Z := by
      change ((a₂ * (a₁ ^ k)⁻¹ : M) : GL ι K) ∈ StatedScalars ι K
      refine ⟨μ, ?_⟩
      have : ((a₂ * (a₁ ^ k)⁻¹ : M) : GL ι K) =
          (a₂ : GL ι K) * ((a₁ : GL ι K) ^ k)⁻¹ := by simp
      rw [this, hμ]
      group
    have hmku : mk (a₂ * (a₁ ^ k)⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 hu
    have : mk a₂ = mk a₁ ^ k := by
      have h1 : mk a₂ = mk (a₂ * (a₁ ^ k)⁻¹) * mk (a₁ ^ k) := by
        rw [← map_mul]; group
      rw [h1, hmku, one_mul, map_pow]
    rw [hmk₂, hmk₁] at this
    rw [this]
    exact ⟨k, by simp⟩
  have hpow := hom_perfect_pow_eq_one_four' hp5 hι σ (a₁ : GL ι K) (a₂ : GL ι K)
    (fun y => by
      have := congrArg (fun m : M => (m : GL ι K)) (hcommA a₁ x₁ hmk₁ y)
      simpa [σ] using this)
    (fun y => by
      have := congrArg (fun m : M => (m : GL ι K)) (hcommA a₂ x₂ hmk₂ y)
      simpa [σ] using this)
    (by
      have := congrArg (fun m : M => (m : GL ι K)) hcomm₁₂
      simpa using this)
    c₁ c₂ (by rw [← Subgroup.coe_pow]; exact hc₁.symm)
    (by rw [← Subgroup.coe_pow]; exact hc₂.symm) hna₁ hind
    (fun μ₁ μ₂ h1 h2 h3 h4 c h5 => hK a₁ a₂ c₁ c₂ μ₁ μ₂ (by rw [← Subgroup.coe_pow]; exact hc₁.symm)
      (by rw [← Subgroup.coe_pow]; exact hc₂.symm) h1 h2 h3 h4 c h5)
  have hKp : IsPGroup p Kb := by
    intro k
    have hk : (k : StatedProj M) ∈ P₀.map mk := by rw [hP₀map]; exact k.2
    obtain ⟨y, hy, hyk⟩ := hk
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [pow_one]
    have : (y ^ p : M) = 1 := by
      apply Subtype.ext
      have := hpow ⟨y, hy⟩
      simpa [σ] using this
    show (k : StatedProj M) ^ p = 1
    rw [← hyk, ← map_pow, this, map_one]
  have : Finite Kb := inferInstance
  have hnil : Group.IsNilpotent Kb := hKp.isNilpotent
  have hsol : Group.IsSolvable Kb := inferInstance
  obtain ⟨u, v, huv⟩ := hKn
  exact huv ((IsSimpleGroup.comm_iff_isSolvable).2 hsol u v)

theorem statedProj_four_no_config {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp5 : 5 ≤ p) (hK : ∀ c : K, ∃ k : ℕ, (k : K) = c) {ι : Type} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = 4) (M : Subgroup (GL ι K))
    (C : Subgroup (StatedProj M)) (hC : IsElementaryAbelian p C) (hCc : Nat.card C = p ^ 2)
    (Kb : Subgroup (StatedProj M)) [IsSimpleGroup Kb] (hKn : ∃ a b : Kb, a * b ≠ b * a)
    (hcomm : ∀ c ∈ C, ∀ k ∈ Kb, c * k = k * c) : False :=
  statedProj_four_no_config' hp5 hι M (fun _ _ _ _ _ _ _ _ _ _ _ _ c _ => hK c) C hC hCc Kb hKn hcomm

end CFSG.RankThree.PartOne.K133
