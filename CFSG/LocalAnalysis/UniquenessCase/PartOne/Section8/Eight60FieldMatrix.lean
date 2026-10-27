module

public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Matrix
open CFSG.Open (StatedProj StatedScalars)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

private lemma glMap_injective {ι K L : Type*} [Fintype ι] [DecidableEq ι] [CommRing K]
    [CommRing L] (f : K →+* L) (hf : Function.Injective f) :
    Function.Injective (Matrix.GeneralLinearGroup.map (n := ι) f) := by
  intro g h hgh
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  exact hf (by
    have := congrArg (fun x : GL ι L => (x : Matrix ι ι L) i j) hgh
    simpa [Matrix.GeneralLinearGroup.map_apply] using this)

@[expose] def IsFieldMapQuot {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (H : Subgroup (GL ι K)) (φ : RingAut K) (τ : MulAut (StatedProj H)) : Prop :=
  ∀ g : H, ∃ h : H,
    (h : GL ι K) = Matrix.GeneralLinearGroup.map (φ : K →+* K) (g : GL ι K) ∧
      τ (QuotientGroup.mk g) = QuotientGroup.mk h

private lemma map_eq_conj_of_isFieldMapQuot
    {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (H : Subgroup (GL ι K)) (hperf : Group.IsPerfect H) (ψ : RingAut K)
    (τ : MulAut (StatedProj H)) (hτ : IsFieldMapQuot H ψ τ)
    (g₀ : H) (hg₀ : τ = MulAut.conj (QuotientGroup.mk g₀)) :
    ∀ g : H, Matrix.GeneralLinearGroup.map (ψ : K →+* K) (g : GL ι K)
      = ((g₀ * g * g₀⁻¹ : H) : GL ι K) := by
  let hmap : H → H := fun g => Classical.choose (hτ g)
  have hmap_val : ∀ g, ((hmap g : H) : GL ι K)
      = Matrix.GeneralLinearGroup.map (ψ : K →+* K) (g : GL ι K) :=
    fun g => (Classical.choose_spec (hτ g)).1
  have hmap_mk : ∀ g, τ (QuotientGroup.mk g) = QuotientGroup.mk (hmap g) :=
    fun g => (Classical.choose_spec (hτ g)).2
  have hmap_one : hmap 1 = 1 := by
    apply Subtype.ext
    rw [hmap_val 1, Subgroup.coe_one]
    simp
  have hmap_mul : ∀ g g' : H, hmap (g * g') = hmap g * hmap g' := by
    intro g g'
    apply Subtype.ext
    rw [hmap_val (g * g')]
    change Matrix.GeneralLinearGroup.map (ψ : K →+* K) ((g : GL ι K) * (g' : GL ι K))
      = ((hmap g * hmap g' : H) : GL ι K)
    rw [map_mul]
    simp only [Subgroup.coe_mul, hmap_val]
  let p : H → H := fun g => g₀ * g * g₀⁻¹
  have p_one : p 1 = 1 := by dsimp [p]; group
  have p_mul : ∀ g g' : H, p (g * g') = p g * p g' := by
    intro g g'; dsimp [p]; group
  have hmkeq : ∀ g : H,
      (QuotientGroup.mk (hmap g) : StatedProj H) = QuotientGroup.mk (p g) := by
    intro g
    rw [← hmap_mk g, hg₀, MulAut.conj_apply]
    dsimp [p]
  have hcN : ∀ g : H, (p g)⁻¹ * hmap g ∈ (StatedScalars ι K).subgroupOf H := by
    intro g
    exact (QuotientGroup.eq_one_iff ((p g)⁻¹ * hmap g)).mp (by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hmkeq g, inv_mul_cancel])
  have hNcenter : (StatedScalars ι K).subgroupOf H ≤ Subgroup.center H := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hxgl : (x : GL ι K) ∈ Subgroup.center (GL ι K) := by
      rw [Subgroup.mem_subgroupOf] at hx
      simpa [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] using hx
    exact Subgroup.mem_center_iff.mp hxgl (y : GL ι K)
  let c : H →* Subgroup.center H :=
    { toFun := fun g => ⟨(p g)⁻¹ * hmap g, hNcenter (hcN g)⟩
      map_one' := by
        apply Subtype.ext
        dsimp
        rw [p_one, hmap_one]
        simp
      map_mul' := by
        intro g g'
        apply Subtype.ext
        dsimp
        rw [p_mul, hmap_mul, _root_.mul_inv_rev]
        have hcomm : (p g')⁻¹ * ((p g)⁻¹ * hmap g)
            = ((p g)⁻¹ * hmap g) * (p g')⁻¹ :=
          Subgroup.mem_center_iff.mp (hNcenter (hcN g)) (p g')⁻¹
        rw [show (p g')⁻¹ * (p g)⁻¹ * (hmap g * hmap g')
              = (p g')⁻¹ * ((p g)⁻¹ * hmap g) * hmap g' by group]
        rw [show (p g)⁻¹ * hmap g * ((p g')⁻¹ * hmap g')
              = ((p g)⁻¹ * hmap g) * (p g')⁻¹ * hmap g' by group]
        rw [← hcomm] }
  have hc1 : c = 1 := by
    have hrange : Group.IsPerfect (c.range) :=
      @Group.IsPerfect.range H (Subgroup.center H) _ _ c hperf
    have hcomm : IsMulCommutative (c.range) := inferInstance
    have hsub : Subsingleton (c.range) :=
      @Group.IsPerfect.subsingleton_of_isMulCommutative (c.range) _ hrange hcomm
    exact MonoidHom.range_eq_bot_iff.mp
      (@Subgroup.eq_bot_of_subsingleton (Subgroup.center H) _ (c.range) hsub)
  intro g
  have htell : c g = 1 := by rw [hc1]; rfl
  have hval : (p g)⁻¹ * hmap g = 1 := congrArg Subtype.val htell
  have : hmap g = p g := by
    have h2 : p g * ((p g)⁻¹ * hmap g) = p g * 1 := by rw [hval]
    simpa using h2
  rw [← hmap_val g]
  exact congrArg Subtype.val this

theorem exists_isFieldMapQuot {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] (H : Subgroup (GL ι K)) (φ : RingAut K)
    (hH : ∀ g ∈ H, Matrix.GeneralLinearGroup.map (φ : K →+* K) g ∈ H) :
    ∃ τ : MulAut (StatedProj H), IsFieldMapQuot H φ τ := by
  let N : Subgroup H := (StatedScalars ι K).subgroupOf H
  let eHom : H →* H :=
    { toFun := fun g => ⟨Matrix.GeneralLinearGroup.map (φ : K →+* K) (g : GL ι K), hH g g.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hinj : Function.Injective eHom := by
    intro g h hgh
    apply Subtype.ext
    exact glMap_injective (φ : K →+* K) φ.injective (congrArg Subtype.val hgh)
  have hbij : Function.Bijective eHom :=
    ⟨hinj, Finite.surjective_of_injective hinj⟩
  let e : H ≃* H := MulEquiv.ofBijective eHom hbij
  have he_apply : ∀ g : H, e g = eHom g := fun g => MulEquiv.ofBijective_apply eHom hbij g
  have hle : N.map (e : H →* H) ≤ N := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := hx
    change (n : GL ι K) ∈ StatedScalars ι K at hn
    change (↑(e n) : GL ι K) ∈ StatedScalars ι K
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hn
    refine MonoidHom.mem_range.mpr ⟨Units.map (φ : K →+* K) u, ?_⟩
    have hev : (↑(e n) : GL ι K) = Matrix.GeneralLinearGroup.map (φ : K →+* K) (↑n : GL ι K) := by
      rw [he_apply]; rfl
    rw [← Matrix.GeneralLinearGroup.map_scalar, hu]
    exact hev.symm
  have hcard : Nat.card N ≤ Nat.card (N.map (e : H →* H)) := by
    rw [Subgroup.card_map_of_injective e.injective]
  have he_map : N.map (e : H →* H) = N := Subgroup.eq_of_le_of_card_ge hle hcard
  let τ : MulAut (StatedProj H) :=
    QuotientGroup.congr ((StatedScalars ι K).subgroupOf H) ((StatedScalars ι K).subgroupOf H) e he_map
  refine ⟨τ, ?_⟩
  intro g
  refine ⟨e g, ?_, ?_⟩
  · rw [he_apply]; rfl
  · exact QuotientGroup.congr_mk ((StatedScalars ι K).subgroupOf H)
      ((StatedScalars ι K).subgroupOf H) e he_map g

theorem isFieldMapQuot_pow {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {H : Subgroup (GL ι K)} {φ : RingAut K} {τ : MulAut (StatedProj H)}
    (hτ : IsFieldMapQuot H φ τ) (m : ℕ) : IsFieldMapQuot H (φ ^ m) (τ ^ m) := by
  induction m with
  | zero =>
    intro g
    refine ⟨g, ?_, ?_⟩
    · rw [pow_zero, show ((1 : RingAut K) : K →+* K) = RingHom.id K from rfl,
        Matrix.GeneralLinearGroup.map_id]
      rfl
    · rw [pow_zero]
      rfl
  | succ m ih =>
    intro g
    obtain ⟨h1, hh1, hτ1⟩ := hτ g
    obtain ⟨h2, hh2, hτ2⟩ := ih h1
    refine ⟨h2, ?_, ?_⟩
    · rw [hh2, hh1]
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      simp only [Matrix.GeneralLinearGroup.map_apply]
      rw [pow_succ]
      rfl
    · rw [pow_succ, MulAut.mul_apply, hτ1, hτ2]

theorem eq_one_of_isFieldMapQuot_one {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {H : Subgroup (GL ι K)} {τ : MulAut (StatedProj H)} (hτ : IsFieldMapQuot H 1 τ) :
    τ = 1 := by
  apply MulEquiv.ext
  intro x
  refine QuotientGroup.induction_on x ?_
  intro g
  obtain ⟨h, hh, hτh⟩ := hτ g
  have hhg : h = g := by
    apply Subtype.ext
    rw [hh, show ((1 : RingAut K) : K →+* K) = RingHom.id K from rfl,
      Matrix.GeneralLinearGroup.map_id]
    rfl
  rw [hτh, hhg]
  rfl

theorem exists_ringAut_pow_of_charP {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime]
    [CharP K p] (k : ℕ) : ∃ φ : RingAut K, ∀ x : K, φ x = x ^ (p ^ k) := by
  refine ⟨iterateFrobeniusEquiv K p k, ?_⟩
  intro x
  rw [iterateFrobeniusEquiv_def]

theorem fixes_of_fixes_add_inv_of_odd_orderOf {K : Type} [Field K] (σ : RingAut K)
    (hσ : Odd (orderOf σ)) (a : K) (ha : σ (a + a⁻¹) = a + a⁻¹) : σ a = a := by
  by_cases ha0 : a = 0
  · rw [ha0]
    simp
  · have hba : σ a ≠ 0 := by
      intro h
      apply ha0
      have := congrArg σ.symm h
      simpa using this
    have hb : σ a + (σ a)⁻¹ = a + a⁻¹ := by
      rw [← map_inv₀, ← map_add]
      exact ha
    have hpoly : σ a * (a + a⁻¹) = (σ a) ^ 2 + 1 := by
      have := congrArg (fun x => σ a * x) hb
      simpa [mul_add, mul_inv_cancel₀ hba, pow_two, mul_assoc] using this.symm
    have hroot : (σ a - a) * (σ a - a⁻¹) = 0 := by
      calc (σ a - a) * (σ a - a⁻¹)
          = (σ a) ^ 2 - σ a * (a + a⁻¹) + a * a⁻¹ := by ring
        _ = (σ a) ^ 2 - σ a * (a + a⁻¹) + 1 := by rw [mul_inv_cancel₀ ha0]
        _ = 0 := by rw [hpoly]; ring
    rcases mul_eq_zero.mp hroot with h | h
    · exact sub_eq_zero.mp h
    · have hba' : σ a = a⁻¹ := sub_eq_zero.mp h
      have hfix2 : σ (σ a) = a := by
        rw [hba']
        simp [map_inv₀, hba']
      obtain ⟨k, hk⟩ := hσ
      have hpow : σ ^ (2 * k + 1) = 1 := by
        rw [← hk]
        exact pow_orderOf_eq_one σ
      have hfixpow : ∀ n, ((σ ^ 2) ^ n) a = a := by
        intro n
        induction n with
        | zero => rw [pow_zero, RingAut.one_apply]
        | succ n ih =>
          have h2 : (σ ^ 2 : RingAut K) a = a := by rw [pow_two, RingAut.mul_apply, hfix2]
          rw [pow_succ, RingAut.mul_apply, h2, ih]
      have hsplit : σ = (σ ^ 2) ^ (k + 1) := by
        calc σ = σ ^ (2 * k + 1) * σ := by rw [hpow, one_mul]
          _ = σ ^ ((2 * k + 1) + 1) := (pow_succ σ (2 * k + 1)).symm
          _ = σ ^ (2 * (k + 1)) := by
                rw [show (2 * k + 1) + 1 = 2 * (k + 1) from by omega]
          _ = (σ ^ 2) ^ (k + 1) := by rw [pow_mul]
      rw [hsplit]
      exact hfixpow (k + 1)

theorem dvd_of_pow_sub_one_dvd_pow_sub_one {q₀ m j : ℕ} (hq : 2 ≤ q₀) (hm : 0 < m)
    (h : q₀ ^ m - 1 ∣ q₀ ^ j - 1) : m ∣ j := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
  have hgcd : Nat.gcd (q₀ ^ (m' + 1) - 1) (q₀ ^ j - 1) = q₀ ^ (m' + 1) - 1 := Nat.gcd_eq_left h
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at hgcd
  have h1 : 1 ≤ q₀ ^ Nat.gcd (m' + 1) j := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ q₀ ^ (m' + 1) := Nat.one_le_pow _ _ (by omega)
  have heq : q₀ ^ Nat.gcd (m' + 1) j = q₀ ^ (m' + 1) := by omega
  have hg : Nat.gcd (m' + 1) j = m' + 1 := Nat.pow_right_injective hq heq
  have hd := Nat.gcd_dvd_right (m' + 1) j
  rwa [hg] at hd

theorem pow_eq_one_of_pow_mem_inner {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (H : Subgroup (GL ι K)) (hperf : Group.IsPerfect H) (φ : RingAut K)
    (hφ : Odd (orderOf φ)) (a : K) (ha : ∀ σ : RingAut K, σ a = a → σ = 1) (m : ℕ)
    (A₀ : H) (hA₀ : Matrix.trace (((A₀ : GL ι K)) : Matrix ι ι K) = a + a⁻¹ + (m : K))
    (τ : MulAut (StatedProj H)) (hτ : IsFieldMapQuot H φ τ)
    (j : ℕ) (hj : τ ^ j ∈ inner (StatedProj H)) : φ ^ j = 1 := by
  let ψ : RingAut K := φ ^ j
  have hψ : ψ = φ ^ j := rfl
  have hτj : IsFieldMapQuot H ψ (τ ^ j) := by
    rw [hψ]
    exact isFieldMapQuot_pow hτ j
  change τ ^ j ∈ (MulAut.conj : StatedProj H →* MulAut (StatedProj H)).range at hj
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hj
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective u
  have hconj : τ ^ j = MulAut.conj (QuotientGroup.mk g₀) := hu.symm
  have hmap_eq := map_eq_conj_of_isFieldMapQuot H hperf ψ (τ ^ j) hτj g₀ hconj
  have htrace_map : Matrix.trace
        ((↑(Matrix.GeneralLinearGroup.map (ψ : K →+* K) (A₀ : GL ι K)) : Matrix ι ι K))
      = ψ (Matrix.trace ((A₀ : GL ι K) : Matrix ι ι K)) := by
    have hcoe : (↑(Matrix.GeneralLinearGroup.map (ψ : K →+* K) (A₀ : GL ι K)) : Matrix ι ι K)
        = ((A₀ : GL ι K) : Matrix ι ι K).map (ψ : K →+* K) := by
      ext i j
      simp [Matrix.GeneralLinearGroup.map_apply]
    rw [hcoe, ← AddMonoidHom.map_trace]
    rfl
  have htrace_conj : Matrix.trace (((g₀ * A₀ * g₀⁻¹ : H) : GL ι K) : Matrix ι ι K)
      = Matrix.trace ((A₀ : GL ι K) : Matrix ι ι K) := by
    have hcoe2 : (((g₀ * A₀ * g₀⁻¹ : H) : GL ι K) : Matrix ι ι K)
        = ((g₀ : GL ι K) : Matrix ι ι K) * ((A₀ : GL ι K) : Matrix ι ι K)
          * (((g₀ : GL ι K)⁻¹) : Matrix ι ι K) := by
      simp [Subgroup.coe_mul]
    rw [hcoe2, ← Matrix.GeneralLinearGroup.coe_inv]
    exact Matrix.trace_units_conj (g₀ : GL ι K) ((A₀ : GL ι K) : Matrix ι ι K)
  have hψtrace : ψ (Matrix.trace ((A₀ : GL ι K) : Matrix ι ι K))
      = Matrix.trace ((A₀ : GL ι K) : Matrix ι ι K) := by
    rw [← htrace_map, hmap_eq A₀]
    exact htrace_conj
  have hψadd : ψ (a + a⁻¹) = a + a⁻¹ := by
    have h := hψtrace
    rw [hA₀, map_add] at h
    simp only [map_natCast] at h
    exact add_right_cancel h
  have hodd : Odd (orderOf ψ) := by
    refine hφ.of_dvd_nat ?_
    rw [hψ]
    exact orderOf_pow_dvd (x := φ) j
  have hψa : ψ a = a := fixes_of_fixes_add_inv_of_odd_orderOf ψ hodd a hψadd
  have hψ1 : ψ = 1 := ha ψ hψa
  rw [hψ] at hψ1
  exact hψ1

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
