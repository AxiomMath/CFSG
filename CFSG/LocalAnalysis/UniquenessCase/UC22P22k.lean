module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22c
import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
import CFSG.LocalAnalysis.UniquenessCase.UC6Syl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped commutatorElement

universe u

theorem uc22p22k_odd_aut_cyclic_two {C : Type*} [Group C] [Finite C] [IsCyclic C]
    (hC : IsPGroup 2 C) (φ : MulAut C) (hφ : Odd (orderOf φ)) : φ = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hC
  have hcard : Nat.card (MulAut C) = Nat.totient (2 ^ k) := by
    rw [IsCyclic.card_mulAut C, hk]
  have h2 : ∃ j : ℕ, Nat.card (MulAut C) = 2 ^ j := by
    rw [hcard]
    rcases k with _ | k
    · exact ⟨0, by simp⟩
    · exact ⟨k, by rw [Nat.totient_prime_pow_succ Nat.prime_two]; simp⟩
  obtain ⟨j, hj⟩ := h2
  have hdvd : orderOf φ ∣ 2 ^ j := hj ▸ orderOf_dvd_natCard φ
  have hcop : Nat.Coprime (orderOf φ) (2 ^ j) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hφ)
  have h1 : orderOf φ = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd
  exact orderOf_eq_one_iff.1 h1


theorem uc22p22k_ML {Q : Type*} [Group Q] [Finite Q] (hc : IsCyclic (commutator Q))
    {S : Subgroup Q} (hS : IsPGroup 2 S) {a : Q} (ha : a ∈ normalizer (S : Set Q))
    (hodd : Odd (orderOf a)) : ∀ s ∈ S, a * s * a⁻¹ = s := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hc
  have hnorm : (commutator Q).Normal := inferInstance
  set S₀ : Subgroup Q := S ⊓ commutator Q with hS₀
  haveI : IsCyclic ↥S₀ := Subgroup.isCyclic_of_le (inf_le_right : S₀ ≤ commutator Q)
  have hS₀2 : IsPGroup 2 ↥S₀ := hS.to_inf_left
  have haS₀ : a ∈ normalizer (S₀ : Set Q) := by
    rw [mem_normalizer_iff] at ha ⊢
    intro x
    constructor
    · intro hx
      exact ⟨(ha x).1 hx.1, hnorm.conj_mem x hx.2 a⟩
    · intro hx
      refine ⟨(ha x).2 hx.1, ?_⟩
      have := hnorm.conj_mem _ hx.2 a⁻¹
      simpa [mul_assoc] using this
  have hcent : ∀ x ∈ S₀, a * x * a⁻¹ = x := by
    intro x hx
    let φ : MulAut ↥S₀ := S₀.normalizerMonoidHom ⟨a, haS₀⟩
    have hφ : Odd (orderOf φ) := by
      have h1 : orderOf φ ∣ orderOf (⟨a, haS₀⟩ : ↥(normalizer (S₀ : Set Q))) := orderOf_map_dvd _ _
      rw [Subgroup.orderOf_mk] at h1
      exact Odd.of_dvd_nat hodd h1
    have hφ1 : φ = 1 := uc22p22k_odd_aut_cyclic_two hS₀2 φ hφ
    have h2 := congrArg (fun f : MulAut ↥S₀ => ((f ⟨x, hx⟩ : ↥S₀) : Q)) hφ1
    simpa [φ] using h2
  intro s hs
  set c : Q := a * s * a⁻¹ * s⁻¹ with hcdef
  have hcS : c ∈ S := S.mul_mem ((ha s).1 hs) (S.inv_mem hs)
  have hcC : c ∈ commutator Q := commutator_mem_commutator (mem_top a) (mem_top s)
  have hcS₀ : c ∈ S₀ := ⟨hcS, hcC⟩
  have hac : a * c * a⁻¹ = c := hcent c hcS₀
  have hpow : ∀ k : ℕ, a ^ k * s * (a ^ k)⁻¹ = c ^ k * s := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e1 : a ^ (k + 1) * s * (a ^ (k + 1))⁻¹ = a * (a ^ k * s * (a ^ k)⁻¹) * a⁻¹ := by
        rw [pow_succ', mul_inv_rev]; group
      rw [e1, ih]
      have e2 : a * (c ^ k * s) * a⁻¹ = (a * c * a⁻¹) ^ k * (a * s * a⁻¹) := by
        rw [conj_pow]; group
      rw [e2, hac, pow_succ]
      have e3 : a * s * a⁻¹ = c * s := by rw [hcdef]; group
      rw [e3]; group
  have h1 := hpow (orderOf a)
  rw [pow_orderOf_eq_one] at h1
  simp only [inv_one, mul_one, one_mul] at h1
  have hck : c ^ orderOf a = 1 := by
    have : c ^ orderOf a * s = 1 * s := by rw [← h1]; simp
    exact mul_right_cancel this
  obtain ⟨j, hj⟩ := hS ⟨c, hcS⟩
  have hcj : c ^ (2 ^ j) = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  have hcop : Nat.Coprime (orderOf a) (2 ^ j) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hodd)
  have hd : orderOf c ∣ Nat.gcd (orderOf a) (2 ^ j) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hck) (orderOf_dvd_of_pow_eq_one hcj)
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hd
  rw [hd] at hcdef
  exact mul_inv_eq_one.1 hcdef.symm

theorem uc22p22k_cyclic_descent {A B₁ B₂ : Type*} [Group A] [Group B₁] [Group B₂] (H : Subgroup A)
    (f₁ : A →* B₁) (f₂ : A →* B₂) (hker : ∀ x, f₁ x = 1 → f₂ x = 1)
    (h : IsCyclic ↥(H.map f₁)) : IsCyclic ↥(H.map f₂) := by
  obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top (H.map f₁)).1 h
  have hgmem : g ∈ H.map f₁ := hg ▸ Subgroup.mem_zpowers g
  obtain ⟨h₀, hh₀, rfl⟩ := hgmem
  have hle : H.map f₂ ≤ Subgroup.zpowers (f₂ h₀) := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : f₁ x ∈ Subgroup.zpowers (f₁ h₀) := hg ▸ mem_map_of_mem f₁ hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
    have h2 : f₁ (x * (h₀ ^ k)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_zpow, hk]; simp
    have h3 := hker _ h2
    rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h3
    exact Subgroup.mem_zpowers_iff.2 ⟨k, h3.symm⟩
  exact Subgroup.isCyclic_of_le hle


section CoordinateModel

variable {K : Type u} [Field K]

theorem uc22p22k_translation_zero : translation K 0 = 1 := by
  apply Equiv.ext
  intro y
  cases y with
  | none => rfl
  | some x => simp

theorem uc22p22k_translation_injective {a b : K} (h : translation K a = translation K b) :
    a = b := by
  have := congrArg (fun f : Equiv.Perm (Omega K) => f (some 0)) h
  simpa using this

theorem uc22p22k_D_affine {d : Equiv.Perm (Omega K)} (hd : d ∈ coordinateD K)
    (hnone : d none = none) :
    ∃ (l : Kˣ) (μ : K), ∀ x : K, d (some x) = some (l * x + μ) := by
  rw [← coordinateGLAction_range_eq_D] at hd
  obtain ⟨A, rfl⟩ := hd
  have hc : A.val 1 0 = 0 := by
    by_contra hc
    have h1 := coordinateGLAction_infinity K A hc
    change coordinateGLAction K A none = none at hnone
    rw [h1] at hnone
    exact absurd hnone (by simp)
  have hdet : A.val 0 0 * A.val 1 1 ≠ 0 := by
    have h1 := (Matrix.GeneralLinearGroup.det A).ne_zero
    have h2 : (Matrix.GeneralLinearGroup.det A : K) = A.val.det :=
      Matrix.GeneralLinearGroup.val_det_apply A
    rw [h2, Matrix.det_fin_two, hc] at h1
    simpa using h1
  have ha : A.val 0 0 ≠ 0 := left_ne_zero_of_mul hdet
  have hd' : A.val 1 1 ≠ 0 := right_ne_zero_of_mul hdet
  refine ⟨Units.mk0 (A.val 0 0 / A.val 1 1) (div_ne_zero ha hd'), A.val 0 1 / A.val 1 1, ?_⟩
  intro x
  have hden : A.val 1 0 * x + A.val 1 1 ≠ 0 := by rw [hc]; simpa using hd'
  have h1 := coordinateGLAction_finite K A x hden
  change coordinateGLAction K A (some x) = _
  rw [h1, hc]
  congr 1
  simp only [zero_mul, zero_add, Units.val_mk0]
  field_simp


theorem uc22p22k_E_affine [Finite K] {ε : Equiv.Perm (Omega K)} (hε : ε ∈ coordinateE K)
    (hnone : ε none = none) :
    ∃ (l : Kˣ) (σ : K ≃+* K) (μ : K), ∀ x : K, ε (some x) = some (l * σ x + μ) := by
  rw [← coordinateNormalizer_eq_E] at hε
  obtain ⟨d, σ, hd⟩ := coordinateNormalizer_decomposition K ε hε
  have hdnone : (d : Equiv.Perm (Omega K)) none = none := by
    rw [hd] at hnone
    simpa using hnone
  obtain ⟨l, μ, hlμ⟩ := uc22p22k_D_affine d.2 hdnone
  refine ⟨l, σ, μ, fun x => ?_⟩
  rw [hd]
  simpa using hlμ (σ x)

theorem uc22p22k_conj_translation {ε : Equiv.Perm (Omega K)} (hnone : ε none = none) (l : Kˣ)
    (σ : K ≃+* K) (μ : K) (hε : ∀ x : K, ε (some x) = some (l * σ x + μ)) (t : K) :
    ε * translation K t * ε⁻¹ = translation K (l * σ t) := by
  have h : ε * translation K t = translation K (l * σ t) * ε := by
    apply Equiv.ext
    intro y
    cases y with
    | none => simp [hnone]
    | some x =>
      simp only [Equiv.Perm.mul_apply, translation_some, hε, map_add]
      congr 1
      ring
  rw [mul_inv_eq_iff_eq_mul, h]

theorem uc22p22k_pelt_translation [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    {g : Equiv.Perm (Omega K)} (hg : g ∈ coordinateG K) (hnone : g none = none) {k : ℕ}
    (hk : g ^ (p ^ k) = 1) : ∃ t : K, g = translation K t := by
  obtain ⟨l, μ, hlμ⟩ := uc22p22k_D_affine (coordinateG_le_D K hg) hnone
  have hpow : ∀ m : ℕ, ∃ μ' : K, ∀ x : K, (g ^ m) (some x) = some ((l : K) ^ m * x + μ') := by
    intro m
    induction m with
    | zero => exact ⟨0, fun x => by simp⟩
    | succ m ih =>
      obtain ⟨μ', hμ'⟩ := ih
      refine ⟨l * μ' + μ, fun x => ?_⟩
      rw [pow_succ', Equiv.Perm.mul_apply, hμ', hlμ]
      congr 1
      ring
  obtain ⟨μ', hμ'⟩ := hpow (p ^ k)
  have h0 := hμ' 0
  have h1 := hμ' 1
  rw [hk] at h0 h1
  simp only [Equiv.Perm.coe_one, id_eq, Option.some.injEq] at h0 h1
  have hμ0 : μ' = 0 := by simpa using h0.symm
  have hl : (l : K) ^ (p ^ k) = 1 := by simpa [hμ0] using h1.symm
  have hl1 : (l : K) = 1 := by
    have : ((l : K) - 1) ^ (p ^ k) = 0 := by
      rw [sub_pow_char_pow, hl, one_pow, sub_self]
    have := pow_eq_zero_iff (n := p ^ k) (pow_ne_zero k (Fact.out : p.Prime).ne_zero) |>.1 this
    exact sub_eq_zero.1 this
  refine ⟨μ, Equiv.ext fun y => ?_⟩
  cases y with
  | none => simpa using hnone
  | some x => rw [hlμ, translation_some, hl1]; simp [add_comm]


theorem uc22p22k_exists_fixed_point [Finite K] {p n : ℕ} [Fact p.Prime] (hn : 0 < n)
    (hK : Nat.card K = p ^ n) (W : Subgroup (coordinateG K)) (hW : IsPGroup p W) :
    ∃ ω : Omega K, ∀ w ∈ W, ((w : coordinateG K) : Equiv.Perm (Omega K)) ω = ω := by
  let f : ↥W →* Equiv.Perm (Omega K) := (coordinateG K).subtype.comp W.subtype
  letI : MulAction ↥W (Omega K) := MulAction.compHom (Omega K) f
  have hmod := hW.card_modEq_card_fixedPoints (Omega K)
  have hcard : Nat.card (Omega K) = p ^ n + 1 := by
    rw [Finite.card_option, hK]
  have hp1 : p ^ n + 1 ≡ 1 [MOD p] := by
    have h0 : p ^ n ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.2 (dvd_pow_self p hn.ne')
    simpa using h0.add_right 1
  have hne : Nat.card (MulAction.fixedPoints ↥W (Omega K)) ≠ 0 := by
    intro h0
    rw [h0, hcard] at hmod
    have h2 : 1 ≡ 0 [MOD p] := hp1.symm.trans hmod
    have : p ∣ 1 := (Nat.modEq_zero_iff_dvd).1 h2
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 this)
  obtain ⟨⟨ω, hω⟩⟩ := (Nat.card_pos_iff.1 (Nat.pos_of_ne_zero hne)).1
  refine ⟨ω, fun w hw => ?_⟩
  exact hω ⟨w, hw⟩

theorem uc22p22k_normalize [Finite K] {p n : ℕ} [Fact p.Prime] [CharP K p] (hn : 0 < n)
    (hK : Nat.card K = p ^ n) (W : Subgroup (coordinateG K)) (hW : IsPGroup p W) :
    ∃ g : coordinateG K, ∀ w ∈ W, ∃ t : K,
      ((g⁻¹ * w * g : coordinateG K) : Equiv.Perm (Omega K)) = translation K t := by
  obtain ⟨ω, hω⟩ := uc22p22k_exists_fixed_point hn hK W hW
  obtain ⟨g, hg⟩ := coordinateG_transitive K none ω
  refine ⟨g, fun w hw => ?_⟩
  have hnone : ((g⁻¹ * w * g : coordinateG K) : Equiv.Perm (Omega K)) none = none := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply]
    rw [hg, hω w hw]
    rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
    exact hg.symm
  obtain ⟨k, hk⟩ := hW ⟨w, hw⟩
  have hpow : ((g⁻¹ * w * g : coordinateG K) : Equiv.Perm (Omega K)) ^ (p ^ k) = 1 := by
    have h1 : (g⁻¹ * w * g) ^ (p ^ k) = g⁻¹ * w ^ (p ^ k) * g := by
      have := conj_pow (a := g⁻¹) (b := w) (i := p ^ k)
      simpa using this
    have h2 : (w : coordinateG K) ^ (p ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have h3 : (g⁻¹ * w * g : coordinateG K) ^ (p ^ k) = 1 := by
      rw [h1, h2]; group
    have := congrArg Subtype.val h3
    simpa using this
  exact uc22p22k_pelt_translation (g⁻¹ * w * g).2 hnone hpow


@[expose] def uc22p22k_sl (l : Kˣ) (σ : K ≃+* K) : Equiv.Perm K :=
  σ.toEquiv.trans (Equiv.mulLeft₀ (l : K) l.ne_zero)

@[simp] theorem uc22p22k_sl_apply (l : Kˣ) (σ : K ≃+* K) (t : K) :
    uc22p22k_sl l σ t = l * σ t := rfl

@[expose] def uc22p22k_linHom (K : Type u) [Field K] : Kˣ →* Equiv.Perm K where
  toFun l := uc22p22k_sl l (RingEquiv.refl K)
  map_one' := by ext t; simp
  map_mul' l l' := by ext t; simp [mul_assoc]

theorem uc22p22k_linHom_cyclic [Finite K] : IsCyclic ↥(uc22p22k_linHom K).range := by
  haveI : IsCyclic Kˣ := inferInstance
  exact isCyclic_of_surjective (uc22p22k_linHom K).rangeRestrict
    (uc22p22k_linHom K).rangeRestrict_surjective

theorem uc22p22k_symm_form {g : Equiv.Perm K} {l : Kˣ} {σ : K ≃+* K} (h : ∀ t, g t = l * σ t)
    (u : K) : g⁻¹ u = σ.symm ((l⁻¹ : Kˣ) * u) := by
  have : g (σ.symm ((l⁻¹ : Kˣ) * u)) = u := by
    rw [h]; simp
  rw [Equiv.Perm.inv_def]
  exact (Equiv.symm_apply_eq g).2 this.symm

theorem uc22p22k_comm_linear [Finite K] {g₁ g₂ : Equiv.Perm K} {l₁ l₂ : Kˣ} {σ₁ σ₂ : K ≃+* K}
    (h₁ : ∀ t, g₁ t = l₁ * σ₁ t) (h₂ : ∀ t, g₂ t = l₂ * σ₂ t) :
    ⁅g₁, g₂⁆ ∈ (uc22p22k_linHom K).range := by
  haveI := fieldAut_isCyclic K
  have hc : σ₁ * σ₂ = σ₂ * σ₁ := IsCyclic.commGroup.mul_comm σ₁ σ₂
  have hc' : ∀ x, σ₁ (σ₂ x) = σ₂ (σ₁ x) := fun x => by
    have := congrArg (fun f : K ≃+* K => f x) hc
    simpa using this
  have hl1 : (l₁ : K) ≠ 0 := l₁.ne_zero
  have hl2 : (l₂ : K) ≠ 0 := l₂.ne_zero
  have hs1 : σ₁ (l₂ : K) ≠ 0 := by simpa using hl2
  have hs2 : σ₂ (l₁ : K) ≠ 0 := by simpa using hl1
  let L : Kˣ := Units.mk0 ((l₁ : K) * σ₁ l₂ / (σ₂ l₁ * l₂))
    (div_ne_zero (mul_ne_zero hl1 hs1) (mul_ne_zero hs2 hl2))
  refine ⟨L, ?_⟩
  ext t
  have e1 : g₂⁻¹ t = σ₂.symm ((l₂⁻¹ : Kˣ) * t) := uc22p22k_symm_form h₂ t
  have e2 := uc22p22k_symm_form h₁ (g₂⁻¹ t)
  simp only [commutatorElement_def, Equiv.Perm.mul_apply]
  rw [e2, e1, h₁, h₂]
  simp only [uc22p22k_linHom, MonoidHom.coe_mk, OneHom.coe_mk, uc22p22k_sl_apply,
    RingEquiv.coe_refl, id_eq, L, Units.val_mk0]
  have h3 : σ₁ (σ₂ (σ₁.symm (((l₁⁻¹ : Kˣ) : K) * σ₂.symm (((l₂⁻¹ : Kˣ) : K) * t)))) =
      (σ₂ (l₁ : K))⁻¹ * (((l₂ : K))⁻¹ * t) := by
    rw [hc', RingEquiv.apply_symm_apply, map_mul, RingEquiv.apply_symm_apply,
      Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀]
  rw [map_mul, h3]
  field_simp


theorem uc22p22k_cyc_of_semilinear [Finite K] {Y : Type*} [Group Y] (ψ : Y →* Equiv.Perm K)
    (hψ : ∀ y, ∃ (l : Kˣ) (σ : K ≃+* K), ∀ t, ψ y t = l * σ t) :
    IsCyclic ↥((commutator Y).map ψ) := by
  haveI := uc22p22k_linHom_cyclic (K := K)
  have hle : (commutator Y).map ψ ≤ (uc22p22k_linHom K).range := by
    have h1 : (commutator Y).map ψ = ⁅(⊤ : Subgroup Y).map ψ, (⊤ : Subgroup Y).map ψ⁆ :=
      Subgroup.map_commutator ⊤ ⊤ ψ
    rw [h1, Subgroup.commutator_le]
    rintro _ ⟨y₁, -, rfl⟩ _ ⟨y₂, -, rfl⟩
    obtain ⟨l₁, σ₁, h₁⟩ := hψ y₁
    obtain ⟨l₂, σ₂, h₂⟩ := hψ y₂
    exact uc22p22k_comm_linear h₁ h₂
  exact Subgroup.isCyclic_of_le hle


theorem uc22p22k_act [Finite K] {Y : Type*} [Group Y] (α : Y →* MulAut (coordinateG K))
    (W : Subgroup (coordinateG K)) (hW : W ≠ ⊥)
    (hWt : ∀ w ∈ W, ∃ t : K, ((w : coordinateG K) : Equiv.Perm (Omega K)) = translation K t)
    (hWn : ∀ y, ∀ w ∈ W, α y w ∈ W) :
    ∃ ψ : Y →* Equiv.Perm K, (∀ y, ∃ (l : Kˣ) (σ : K ≃+* K), ∀ t, ψ y t = l * σ t) ∧
      ∀ y t, ((α y ⟨translation K t, translation_mem_coordinateG K t⟩ : coordinateG K) :
        Equiv.Perm (Omega K)) = translation K (ψ y t) := by
  have hε : ∀ y : Y, ∃ ε : Equiv.Perm (Omega K), ε ∈ coordinateE K ∧ ∀ g : coordinateG K,
      ((α y g : coordinateG K) : Equiv.Perm (Omega K)) = ε * (g : Equiv.Perm (Omega K)) * ε⁻¹ := by
    intro y
    refine ⟨(((coordinateConjugationEquiv K).symm (α y) : coordinateE K) : Equiv.Perm (Omega K)),
      ((coordinateConjugationEquiv K).symm (α y)).2, fun g => ?_⟩
    have h := coordinateConjugation_apply_coe K ((coordinateConjugationEquiv K).symm (α y)) g
    have h2 : coordinateConjugation K ((coordinateConjugationEquiv K).symm (α y)) = α y :=
      (coordinateConjugationEquiv K).apply_symm_apply (α y)
    rw [h2] at h
    exact h
  obtain ⟨⟨w₀, hw₀⟩, hw₀1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hW
  have hw₀1 : w₀ ≠ 1 := fun h => hw₀1' (Subtype.ext h)
  obtain ⟨t₀, ht₀⟩ := hWt w₀ hw₀
  have ht₀0 : t₀ ≠ 0 := by
    rintro rfl
    apply hw₀1
    apply Subtype.ext
    rw [ht₀, uc22p22k_translation_zero]
    rfl
  have hex : ∀ y : Y, ∃ (l : Kˣ) (σ : K ≃+* K), ∀ t : K,
      ((α y ⟨translation K t, translation_mem_coordinateG K t⟩ : coordinateG K) :
        Equiv.Perm (Omega K)) = translation K (l * σ t) := by
    intro y
    obtain ⟨ε, hεE, hεα⟩ := hε y
    have hnone : ε none = none := by
      obtain ⟨s, hs⟩ := hWt _ (hWn y w₀ hw₀)
      have hs0 : s ≠ 0 := by
        rintro rfl
        have h1 : α y w₀ = 1 := by
          apply Subtype.ext
          rw [hs, uc22p22k_translation_zero]
          rfl
        exact hw₀1 ((MulEquiv.map_eq_one_iff (α y)).1 h1)
      have h2 : translation K s = ε * translation K t₀ * ε⁻¹ := by
        rw [← hs, hεα, ht₀]
      have h3 := congrArg (fun f : Equiv.Perm (Omega K) => f (ε none)) h2
      have hinvε : ε⁻¹ (ε none) = none := by
        rw [Equiv.Perm.inv_def]; exact ε.symm_apply_apply none
      simp only [Equiv.Perm.mul_apply, hinvε, translation_none] at h3
      cases h : ε none with
      | none => rfl
      | some x =>
        rw [h] at h3
        simp only [translation_some, Option.some.injEq] at h3
        exact absurd (by simpa using h3) hs0
    obtain ⟨l, σ, μ, hlσμ⟩ := uc22p22k_E_affine hεE hnone
    refine ⟨l, σ, fun t => ?_⟩
    rw [hεα]
    exact uc22p22k_conj_translation hnone l σ μ hlσμ t
  choose l σ hlσ using hex
  have hinj : ∀ {a b : K}, translation K a = translation K b → a = b :=
    fun h => uc22p22k_translation_injective h
  have hmul : ∀ y y' : Y, ∀ t : K, l (y * y') * σ (y * y') t = l y * σ y (l y' * σ y' t) := by
    intro y y' t
    apply hinj
    rw [← hlσ (y * y') t]
    have h1 : α (y * y') ⟨translation K t, translation_mem_coordinateG K t⟩ =
        α y (α y' ⟨translation K t, translation_mem_coordinateG K t⟩) := by
      rw [map_mul]; rfl
    rw [h1]
    have h2 : α y' ⟨translation K t, translation_mem_coordinateG K t⟩ =
        ⟨translation K (l y' * σ y' t), translation_mem_coordinateG K _⟩ :=
      Subtype.ext (hlσ y' t)
    rw [h2]
    exact hlσ y _
  refine ⟨MonoidHom.mk' (fun y => uc22p22k_sl (l y) (σ y)) (fun y y' => ?_), fun y => ⟨l y, σ y, fun t => rfl⟩,
    fun y t => hlσ y t⟩
  ext t
  exact hmul y y' t


end CoordinateModel

theorem uc22p22k_quot_cyc {G : Type*} [Group G] [Finite G] {M K N : Subgroup G}
    [hK : (K.subgroupOf M).Normal] (hNM : N ≤ M) (hKM : K ≤ M)
    (hfrat : ∀ m ∈ M, ∃ k ∈ K, ∃ n ∈ N, m = k * n)
    {Γ : Type*} [Group Γ] (ψ : ↥N →* Γ) (hψ : IsCyclic ↥((commutator ↥N).map ψ))
    (hker : ∀ n : ↥N, ψ n = 1 → (n : G) ∈ K) :
    IsCyclic ↥(commutator (↥M ⧸ K.subgroupOf M)) := by
  let ρ : ↥N →* ↥M ⧸ K.subgroupOf M :=
    (QuotientGroup.mk' (K.subgroupOf M)).comp (Subgroup.inclusion hNM)
  have hρ : Function.Surjective ρ := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H m =>
      obtain ⟨k, hk, n, hn, hmkn⟩ := hfrat m m.2
      refine ⟨⟨n, hn⟩, ?_⟩
      have h1 : (QuotientGroup.mk m : ↥M ⧸ K.subgroupOf M) =
          QuotientGroup.mk (⟨k, hKM hk⟩ : ↥M) * QuotientGroup.mk (⟨n, hNM hn⟩ : ↥M) := by
        rw [← QuotientGroup.mk_mul]
        congr 1
        exact Subtype.ext hmkn
      have h2 : (QuotientGroup.mk (⟨k, hKM hk⟩ : ↥M) : ↥M ⧸ K.subgroupOf M) = 1 :=
        (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hk)
      rw [h1, h2, one_mul]
      rfl
  have hcomm : commutator (↥M ⧸ K.subgroupOf M) = (commutator ↥N).map ρ := by
    have h1 := Subgroup.map_commutator (⊤ : Subgroup ↥N) ⊤ ρ
    have h2 : (⊤ : Subgroup ↥N).map ρ = ⊤ := by
      rw [Subgroup.map_top, MonoidHom.range_eq_top]; exact hρ
    rw [h2] at h1
    exact h1.symm
  rw [hcomm]
  refine uc22p22k_cyclic_descent (commutator ↥N) ψ ρ (fun n hn => ?_) hψ
  have := hker n hn
  show (QuotientGroup.mk (Subgroup.inclusion hNM n) : ↥M ⧸ K.subgroupOf M) = 1
  rw [QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf.2 this


theorem uc22p22k_ml_apply {X : Type*} [Group X] [Finite X] {K : Subgroup X} [K.Normal]
    (hc : IsCyclic ↥(commutator (X ⧸ K))) {R : Subgroup X} (hR : IsPGroup 2 ↥R) {a : X}
    (ha : a ∈ normalizer (R : Set X)) {m : ℕ} (hm : Odd m) (ham : a ^ m ∈ K) :
    ∀ r ∈ R, ⁅a, r⁆ ∈ K := by
  let ρ : X →* X ⧸ K := QuotientGroup.mk' K
  have hS : IsPGroup 2 ↥(R.map ρ) := hR.map ρ
  have hnorm : ρ a ∈ normalizer ((R.map ρ : Subgroup (X ⧸ K)) : Set (X ⧸ K)) := by
    rw [mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨r, hr, rfl⟩
      refine ⟨a * r * a⁻¹, (mem_normalizer_iff.1 ha r).1 hr, ?_⟩
      simp [ρ]
    · rintro ⟨r, hr, hrz⟩
      refine ⟨a⁻¹ * r * a, ?_, ?_⟩
      · have := (mem_normalizer_iff.1 (inv_mem ha) r).1 hr
        simpa using this
      · rw [map_mul, map_mul, map_inv, hrz]; group
  have hodd : Odd (orderOf (ρ a)) := by
    have : (ρ a) ^ m = 1 := by rw [← map_pow]; exact (QuotientGroup.eq_one_iff _).2 ham
    exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one this)
  intro r hr
  have h := uc22p22k_ML hc hS hnorm hodd (ρ r) ⟨r, hr, rfl⟩
  have : ρ ⁅a, r⁆ = 1 := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, h]; group
  exact (QuotientGroup.eq_one_iff _).1 this

theorem uc22p22k_final {X B : Type*} [Group X] [Finite X] [Group B] (π : X →* B)
    (hπ : Function.Surjective π) (K : Subgroup X) [K.Normal] (hker2 : IsPGroup 2 ↥π.ker)
    (hkerK : π.ker ≤ K) (hc : IsCyclic ↥(commutator (X ⧸ K)))
    (hT1 : ∀ c ∈ K, (∃ j : ℕ, (π c) ^ (2 ^ j) = 1) → π c = 1)
    {R : Subgroup B} (hR : IsPGroup 2 ↥R) {a : B} (ha : a ∈ normalizer (R : Set B))
    (hodd : Odd (orderOf a)) : ∀ x ∈ R, a * x * a⁻¹ = x := by
  obtain ⟨ã, rfl⟩ := hπ a
  have hR' : IsPGroup 2 ↥(R.comap π) := hR.comap_of_ker_isPGroup π hker2
  have hnorm : ã ∈ normalizer ((R.comap π : Subgroup X) : Set X) := by
    rw [mem_normalizer_iff] at ha ⊢
    intro z
    have := ha (π z)
    simpa [Subgroup.mem_comap] using this
  have hm : ã ^ (orderOf (π ã)) ∈ K := by
    apply hkerK
    rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
  have key := uc22p22k_ml_apply hc hR' hnorm hodd hm
  intro x hx
  obtain ⟨r, rfl⟩ := hπ x
  have hr : r ∈ R.comap π := hx
  have hcK := key r hr
  have hc2 : π ⁅ã, r⁆ = π ã * π r * (π ã)⁻¹ * (π r)⁻¹ := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
  have hcR : π ⁅ã, r⁆ ∈ R := by
    rw [hc2]
    exact R.mul_mem ((mem_normalizer_iff.1 ha _).1 hx) (R.inv_mem hx)
  obtain ⟨j, hj⟩ := hR ⟨π ⁅ã, r⁆, hcR⟩
  have hj' : (π ⁅ã, r⁆) ^ (2 ^ j) = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  have h1 : π ⁅ã, r⁆ = 1 := hT1 _ hcK ⟨j, hj'⟩
  rw [hc2] at h1
  exact mul_inv_eq_one.1 (by simpa using h1)


section Configuration

variable {G : Type} [Group G] [Finite G]

theorem uc22p22k_mem_sup {A B : Subgroup G} (hAB : A ≤ normalizer (B : Set G)) {z : G}
    (hz : z ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, z = a * b := by
  let T : Subgroup G :=
    { carrier := {z | ∃ a ∈ A, ∃ b ∈ B, z = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', (a'⁻¹ * b * a') * b', ?_, by group⟩
        refine B.mul_mem ?_ hb'
        have := (mem_normalizer_iff.1 (hAB (A.inv_mem ha')) b).1 hb
        simpa using this
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, a * b⁻¹ * a⁻¹, ?_, by group⟩
        have := (mem_normalizer_iff.1 (hAB ha) b⁻¹).1 (B.inv_mem hb)
        exact this }
  have : A ⊔ B ≤ T := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact this hz

theorem uc22p22k_frob_norm {R' O V : Subgroup G} (hF : uniqueFourIsFrobenius R' O V) :
    V ≤ normalizer (O : Set G) := by
  obtain ⟨_, _, hOR, hnorm, hVR, _, _, _⟩ := hF
  intro v hv
  rw [mem_normalizer_iff]
  have key : ∀ w ∈ V, ∀ k ∈ O, w * k * w⁻¹ ∈ O := by
    intro w hw k hk
    have := hnorm.conj_mem ⟨k, hOR hk⟩ (mem_subgroupOf.2 hk) ⟨w, hVR hw⟩
    exact mem_subgroupOf.1 this
  intro k
  constructor
  · exact key v hv k
  · intro hk
    have := key v⁻¹ (V.inv_mem hv) _ hk
    simpa [mul_assoc] using this

theorem uc22p22k_frob_odd {R' O V : Subgroup G} (hF : uniqueFourIsFrobenius R' O V)
    (hO : IsPGroup 2 ↥O) : ∀ d ∈ V, Odd (orderOf d) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm := uc22p22k_frob_norm hF
  obtain ⟨hOne, _, _, _, _, _, _, hfix⟩ := hF
  intro d hd
  by_contra hev
  have hev' : Even (orderOf d) := Nat.not_odd_iff_even.1 hev
  have h2 : 2 ∣ orderOf d := even_iff_two_dvd.1 hev'
  have hpos : 0 < orderOf d := orderOf_pos d
  set v : G := d ^ (orderOf d / 2) with hv
  have hvo : orderOf v = 2 := orderOf_pow_orderOf_div hpos.ne' h2
  have hvV : v ∈ V := V.pow_mem hd _
  have hv1 : v ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hvo
    omega
  have hT : IsPGroup 2 ↥(zpowers v) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hvo]; simp
  have hTV : zpowers v ≤ normalizer (O : Set G) := by
    intro x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    exact hnorm (V.zpow_mem hvV k)
  obtain ⟨k, hkO, hk1, hkfix⟩ := uc22p22c_exists_fixed hO hOne hT hTV
  have hcomm : k * v = v * k := by
    have := hkfix v (mem_zpowers v)
    calc k * v = (v * k * v⁻¹) * v := by rw [this]
      _ = v * k := by group
  exact hk1 (hfix v hvV hv1 k hkO hcomm)

theorem uc22p22k_O_inf_L {O L P₀ V : Subgroup G}
    (hfix : ∀ v ∈ V, v ≠ 1 → ∀ k ∈ O, k * v = v * k → k = 1) (hP₀V : P₀ ≤ V) (hP₀ : P₀ ≠ ⊥)
    (hV : V ≤ centralizer (L : Set G)) : O ⊓ L = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨⟨v, hv⟩, hv1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hP₀
  have hv1 : v ≠ 1 := fun h => hv1' (Subtype.ext h)
  have hcomm : y * v = v * y := mem_centralizer_iff.1 (hV (hP₀V hv)) y hy.2
  exact mem_bot.2 (hfix v (hP₀V hv) hv1 y hy.1 hcomm)


theorem uc22p22k_normalizer_centralizer {P₀ : Subgroup G} {n : G}
    (hn : n ∈ normalizer (P₀ : Set G)) : n ∈ normalizer ((centralizer (P₀ : Set G) : Subgroup G) : Set G) := by
  have key : ∀ n' ∈ normalizer (P₀ : Set G), ∀ c ∈ centralizer (P₀ : Set G),
      n' * c * n'⁻¹ ∈ centralizer (P₀ : Set G) := by
    intro n' hn' c hc
    rw [mem_centralizer_iff] at hc ⊢
    intro x hx
    have hx' : n'⁻¹ * x * n' ∈ P₀ := by
      have := (mem_normalizer_iff.1 (inv_mem hn') x).1 hx
      simpa using this
    have h := hc _ hx'
    calc x * (n' * c * n'⁻¹) = n' * ((n'⁻¹ * x * n') * c) * n'⁻¹ := by group
      _ = n' * (c * (n'⁻¹ * x * n')) * n'⁻¹ := by rw [h]
      _ = n' * c * n'⁻¹ * x := by group
  rw [mem_normalizer_iff]
  intro c
  constructor
  · exact key n hn c
  · intro hc
    have := key n⁻¹ (inv_mem hn) _ hc
    simpa [mul_assoc] using this

theorem uc22p22k_normalizer_inftyOf {H : Subgroup G} {n : G} (hn : n ∈ normalizer (H : Set G)) :
    n ∈ normalizer ((UC6.inftyOf H : Subgroup G) : Set G) := by
  have key : ∀ n' ∈ normalizer (H : Set G), ∀ z ∈ UC6.inftyOf H, n' * z * n'⁻¹ ∈ UC6.inftyOf H := by
    intro n' hn' z hz
    obtain ⟨x, hx, rfl⟩ := hz
    refine ⟨Subgroup.normalizerMonoidHom H ⟨n', hn'⟩ x, ?_, by simp⟩
    have hfix : (derivedSeries ↥H (Nat.card H)).map
        (Subgroup.normalizerMonoidHom H ⟨n', hn'⟩).toMonoidHom = derivedSeries ↥H (Nat.card H) :=
      Subgroup.characteristic_iff_map_eq.1 inferInstance _
    rw [← hfix]
    exact Subgroup.mem_map_of_mem _ hx
  rw [mem_normalizer_iff]
  intro z
  constructor
  · exact key n hn z
  · intro hz
    have := key n⁻¹ (inv_mem hn) _ hz
    simpa [mul_assoc] using this

theorem uc22p22k_normalizes_P1 {O P₁ L : Subgroup G} (hOL : O ⊓ L = ⊥) (hP₁L : P₁ ≤ L)
    (hP₁n : P₁ ≤ normalizer (O : Set G)) {n : G}
    (hnQ : n ∈ normalizer ((P₁ ⊔ O : Subgroup G) : Set G)) (hnL : n ∈ normalizer (L : Set G)) :
    n ∈ normalizer (P₁ : Set G) := by
  have key : ∀ n' ∈ normalizer ((P₁ ⊔ O : Subgroup G) : Set G), n' ∈ normalizer (L : Set G) →
      ∀ y ∈ P₁, n' * y * n'⁻¹ ∈ P₁ := by
    intro n' hn'Q hn'L y hy
    have h1 : n' * y * n'⁻¹ ∈ P₁ ⊔ O :=
      (mem_normalizer_iff.1 hn'Q y).1 (mem_sup_left hy)
    have h2 : n' * y * n'⁻¹ ∈ L := (mem_normalizer_iff.1 hn'L y).1 (hP₁L hy)
    obtain ⟨y', hy', o, ho, hyo⟩ := uc22p22k_mem_sup hP₁n h1
    have hoL : o ∈ L := by
      have : o = y'⁻¹ * (n' * y * n'⁻¹) := by rw [hyo]; group
      rw [this]
      exact L.mul_mem (L.inv_mem (hP₁L hy')) h2
    have ho1 : o = 1 := mem_bot.1 (hOL ▸ (mem_inf.2 ⟨ho, hoL⟩))
    rw [hyo, ho1, mul_one]
    exact hy'
  rw [mem_normalizer_iff]
  intro y
  constructor
  · exact key n hnQ hnL y
  · intro hy
    have hnQ' : n⁻¹ ∈ normalizer ((P₁ ⊔ O : Subgroup G) : Set G) := inv_mem hnQ
    have hnL' : n⁻¹ ∈ normalizer (L : Set G) := inv_mem hnL
    have := key n⁻¹ hnQ' hnL' _ hy
    simpa [mul_assoc] using this


@[expose] def uc22p22k_Ktil (M O Q : Subgroup G) (hOn : M ≤ normalizer (O : Set G)) : Subgroup G where
  carrier := {m | m ∈ M ∧ ∀ z ∈ Q, m * z * m⁻¹ * z⁻¹ ∈ O}
  one_mem' := ⟨M.one_mem, fun z _ => by simp [O.one_mem]⟩
  mul_mem' := by
    rintro a b ⟨haM, ha⟩ ⟨hbM, hb⟩
    refine ⟨M.mul_mem haM hbM, fun z hz => ?_⟩
    have e : a * b * z * (a * b)⁻¹ * z⁻¹ =
        (a * (b * z * b⁻¹ * z⁻¹) * a⁻¹) * (a * z * a⁻¹ * z⁻¹) := by group
    rw [e]
    exact O.mul_mem ((mem_normalizer_iff.1 (hOn haM) _).1 (hb z hz)) (ha z hz)
  inv_mem' := by
    rintro a ⟨haM, ha⟩
    refine ⟨M.inv_mem haM, fun z hz => ?_⟩
    have e : a⁻¹ * z * a⁻¹⁻¹ * z⁻¹ = a⁻¹ * (a * z * a⁻¹ * z⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 (hOn (M.inv_mem haM)) _).1 (O.inv_mem (ha z hz))

theorem uc22p22k_Ktil_le {M O Q : Subgroup G} (hOn : M ≤ normalizer (O : Set G)) :
    uc22p22k_Ktil M O Q hOn ≤ M := fun _ h => h.1

theorem uc22p22k_Ktil_normal {M O Q : Subgroup G} (hOn : M ≤ normalizer (O : Set G))
    (hQ : M ≤ normalizer (Q : Set G)) :
    M ≤ normalizer ((uc22p22k_Ktil M O Q hOn : Subgroup G) : Set G) := by
  have key : ∀ g ∈ M, ∀ k ∈ uc22p22k_Ktil M O Q hOn, g * k * g⁻¹ ∈ uc22p22k_Ktil M O Q hOn := by
    rintro g hg k ⟨hkM, hk⟩
    refine ⟨M.mul_mem (M.mul_mem hg hkM) (M.inv_mem hg), fun z hz => ?_⟩
    have hz' : g⁻¹ * z * g ∈ Q := by
      have := (mem_normalizer_iff.1 (hQ (M.inv_mem hg)) z).1 hz
      simpa using this
    have e : (g * k * g⁻¹) * z * (g * k * g⁻¹)⁻¹ * z⁻¹ =
        g * (k * (g⁻¹ * z * g) * k⁻¹ * (g⁻¹ * z * g)⁻¹) * g⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 (hOn hg) _).1 (hk _ hz')
  intro g hg
  rw [mem_normalizer_iff]
  intro k
  constructor
  · exact key g hg k
  · intro hk
    have := key g⁻¹ (M.inv_mem hg) _ hk
    simpa [mul_assoc] using this

theorem uc22p22k_mem_Ktil {M O P₁ : Subgroup G} (hOn : M ≤ normalizer (O : Set G))
    (hP₁M : P₁ ≤ M) {m : G} (hm : m ∈ M) (hcomm : ∀ y ∈ P₁, m * y * m⁻¹ = y) :
    m ∈ uc22p22k_Ktil M O (P₁ ⊔ O) hOn := by
  refine ⟨hm, fun z hz => ?_⟩
  obtain ⟨y, hy, o, ho, rfl⟩ := uc22p22k_mem_sup (hP₁M.trans hOn) hz
  have e : m * (y * o) * m⁻¹ * (y * o)⁻¹ = y * (m * o * m⁻¹ * o⁻¹) * y⁻¹ := by
    have h := hcomm y hy
    calc m * (y * o) * m⁻¹ * (y * o)⁻¹ = (m * y * m⁻¹) * (m * o * m⁻¹) * o⁻¹ * y⁻¹ := by group
      _ = y * (m * o * m⁻¹) * o⁻¹ * y⁻¹ := by rw [h]
      _ = y * (m * o * m⁻¹ * o⁻¹) * y⁻¹ := by group
  rw [e]
  have h1 : m * o * m⁻¹ * o⁻¹ ∈ O :=
    O.mul_mem ((mem_normalizer_iff.1 (hOn hm) o).1 ho) (O.inv_mem ho)
  exact (mem_normalizer_iff.1 (hOn (hP₁M hy)) _).1 h1

theorem uc22p22k_O_le_Ktil {M O Q : Subgroup G} (hOn : M ≤ normalizer (O : Set G)) (hOM : O ≤ M)
    (hQM : Q ≤ M) : O ≤ uc22p22k_Ktil M O Q hOn := by
  intro o ho
  refine ⟨hOM ho, fun z hz => ?_⟩
  have h1 : z * o⁻¹ * z⁻¹ ∈ O := by
    have := (mem_normalizer_iff.1 (hOn (hQM hz)) o⁻¹).1 (O.inv_mem ho)
    exact this
  have e : o * z * o⁻¹ * z⁻¹ = o * (z * o⁻¹ * z⁻¹) := by group
  rw [e]
  exact O.mul_mem ho h1

theorem uc22p22k_frattini {p : ℕ} [Fact p.Prime] {M P P₀ K : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P M) (hP₀P : P₀ ≤ P)
    (hwc : CFSG.ASVolI.ChIJK.IsWeaklyClosedIn P₀ P) (hKM : K ≤ M)
    (hKn : M ≤ normalizer (K : Set G)) (hP₀K : P₀ ≤ K) :
    ∀ m ∈ M, ∃ k ∈ K, ∃ n ∈ M ⊓ normalizer (P₀ : Set G), m = k * n := by
  intro m hm
  have hKsyl : CFSG.ABGLocalTools.IsSylowOf p (P ⊓ K) K := hP.inf_of_le_normalizer hKM hKn
  set S : Subgroup G := CFSG.conjugate P₀ m⁻¹ with hS
  have hSK : S ≤ K := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : m * x * m⁻¹ ∈ K := (mem_normalizer_iff.1 (hKn hm) x).1 (hP₀K hx)
    simpa [MulAut.conj_apply] using h1
  have hSp : IsPGroup p ↥S := by
    have hP₀p : IsPGroup p ↥P₀ := hP.isPGroup.to_le hP₀P
    have := hP₀p.map (MulAut.conj m⁻¹⁻¹).toMonoidHom
    exact this
  obtain ⟨k, hkK, hk⟩ := UC6.exists_conj_le_of_isSylowOf hKsyl hSK hSp
  have hconj : CFSG.conjugate P₀ (m⁻¹ * k) ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : m * x * m⁻¹ ∈ S := ⟨x, hx, by simp [MulAut.conj_apply]⟩
    have h2 := (hk _ h1).1
    simpa [MulAut.conj_apply, mul_assoc] using h2
  have heq := hwc (m⁻¹ * k) hconj
  have hcj : ∀ x : G, (MulAut.conj (m⁻¹ * k)⁻¹) x = (k⁻¹ * m) * x * (k⁻¹ * m)⁻¹ := by
    intro x; simp [MulAut.conj_apply, mul_assoc]
  refine ⟨k, hkK, k⁻¹ * m, mem_inf.2 ⟨M.mul_mem (M.inv_mem (hKM hkK)) hm, ?_⟩, by group⟩
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← heq]
    exact ⟨x, hx, hcj x⟩
  · intro hx
    rw [← heq] at hx
    obtain ⟨x', hx', hx'e⟩ := hx
    rw [MulEquiv.coe_toMonoidHom, hcj] at hx'e
    have : x' = x := by simpa using hx'e
    exact this ▸ hx'


theorem uc22p22k_T1 {M O Dd P₁ : Subgroup G} {B : Type*} [Group B] (π : ↥M →* B)
    (hπ : ∀ m : ↥M, π m = 1 ↔ (m : G) ∈ O) (hOM : O ≤ M) (hP₁M : P₁ ≤ M)
    (hDn : Dd ≤ normalizer (O : Set G)) (hP₁n : P₁ ≤ normalizer (O : Set G))
    (hDodd : ∀ d ∈ Dd, Odd (orderOf d)) (hP₁odd : ∀ y ∈ P₁, Odd (orderOf y))
    (hcomm : ∀ d ∈ Dd, ∀ y ∈ P₁, d * y = y * d) (c : ↥M) (hc : (c : G) ∈ Dd ⊔ P₁ ⊔ O) :
    Odd (orderOf (π c)) := by
  have key : ∀ d ∈ Dd, ∀ y ∈ P₁, d * y * d⁻¹ = y := fun d hd y hy => by
    rw [hcomm d hd y hy]; group
  have hDP : Dd ≤ normalizer (P₁ : Set G) := by
    intro d hd
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy; rw [key d hd y hy]; exact hy
    · intro hw
      have h1 := key d⁻¹ (Dd.inv_mem hd) _ hw
      have e : d⁻¹ * (d * y * d⁻¹) * d⁻¹⁻¹ = y := by group
      rw [e] at h1
      rw [h1]; exact hw
  obtain ⟨a, ha, o, ho, hao⟩ := uc22p22k_mem_sup (sup_le hDn hP₁n) hc
  obtain ⟨d, hd, y, hy, rfl⟩ := uc22p22k_mem_sup hDP ha
  have hdM : d ∈ M := by
    have : d = (c : G) * o⁻¹ * y⁻¹ := by rw [hao]; group
    rw [this]
    exact M.mul_mem (M.mul_mem c.2 (M.inv_mem (hOM ho))) (M.inv_mem (hP₁M hy))
  let dm : ↥M := ⟨d, hdM⟩
  let ym : ↥M := ⟨y, hP₁M hy⟩
  let om : ↥M := ⟨o, hOM ho⟩
  have hc' : c = dm * ym * om := Subtype.ext hao
  have hom : π om = 1 := (hπ om).2 ho
  have hπc : π c = π dm * π ym := by rw [hc', map_mul, map_mul, hom, mul_one]
  have hcommute : Commute (π dm) (π ym) := by
    have : dm * ym = ym * dm := Subtype.ext (hcomm d hd y hy)
    show π dm * π ym = π ym * π dm
    rw [← map_mul, ← map_mul, this]
  have h1 : Odd (orderOf (π dm)) := by
    have := orderOf_map_dvd π dm
    rw [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat (hDodd d hd) this
  have h2 : Odd (orderOf (π ym)) := by
    have := orderOf_map_dvd π ym
    rw [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat (hP₁odd y hy) this
  rw [hπc]
  exact Odd.of_dvd_nat (h1.mul h2) (hcommute.orderOf_mul_dvd_mul_orderOf)


theorem uc22p22k_psi_exists {p n : ℕ} [Fact p.Prime] (hn : 0 < n)
    {K : Type} [Field K] [Finite K] [CharP K p] (hK : Nat.card K = p ^ n)
    {L P₁ N : Subgroup G} (e₀ : ↥L ≃* coordinateG K) (hP₁L : P₁ ≤ L) (hP₁p : IsPGroup p ↥P₁)
    (hNL : N ≤ normalizer (L : Set G)) (hNP : N ≤ normalizer (P₁ : Set G)) :
    ∃ ψ : ↥N →* Equiv.Perm K, (∀ x : ↥N, ∃ (l : Kˣ) (σ : K ≃+* K), ∀ t, ψ x t = l * σ t) ∧
      ∀ x : ↥N, ψ x = 1 → ∀ y ∈ P₁, (x : G) * y * (x : G)⁻¹ = y := by
  by_cases hP₁ : P₁ = ⊥
  · refine ⟨1, fun x => ⟨1, RingEquiv.refl K, fun t => by simp⟩, fun x _ y hy => ?_⟩
    rw [hP₁] at hy
    have : y = 1 := mem_bot.1 hy
    subst this
    simp
  · let W₀ : Subgroup (coordinateG K) := (P₁.subgroupOf L).map e₀.toMonoidHom
    have hW₀p : IsPGroup p ↥W₀ := (hP₁p.comap_subtype).map e₀.toMonoidHom
    obtain ⟨g, hg⟩ := uc22p22k_normalize hn hK W₀ hW₀p
    let e : ↥L ≃* coordinateG K := e₀.trans (MulAut.conj g⁻¹)
    let W : Subgroup (coordinateG K) := (P₁.subgroupOf L).map e.toMonoidHom
    have hWt : ∀ w ∈ W, ∃ t : K,
        ((w : coordinateG K) : Equiv.Perm (Omega K)) = translation K t := by
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨t, ht⟩ := hg (e₀ z) ⟨z, hz, rfl⟩
      refine ⟨t, ?_⟩
      rw [← ht]
      simp [e, MulAut.conj_apply]
    let α : ↥N →* MulAut (coordinateG K) :=
      (MulAut.congr e).toMonoidHom.comp (L.normalizerMonoidHom.comp (Subgroup.inclusion hNL))
    have hα : ∀ (x : ↥N) (z : ↥L), α x (e z) =
        e (L.normalizerMonoidHom (Subgroup.inclusion hNL x) z) := by
      intro x z
      simp [α, MulAut.congr_apply]
    have hαcoe : ∀ (x : ↥N) (z : ↥L), ((L.normalizerMonoidHom (Subgroup.inclusion hNL x) z : ↥L) : G) =
        (x : G) * (z : G) * (x : G)⁻¹ := by
      intro x z
      exact Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
    have hWbot : W ≠ ⊥ := by
      obtain ⟨⟨y, hy⟩, hy1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hP₁
      intro hW
      have hz : e ⟨y, hP₁L hy⟩ ∈ W := ⟨_, mem_subgroupOf.2 hy, rfl⟩
      rw [hW, mem_bot, MulEquiv.map_eq_one_iff] at hz
      have hy1 : y = 1 := by simpa using congrArg Subtype.val hz
      exact hy1' (Subtype.ext hy1)
    have hWn : ∀ x : ↥N, ∀ w ∈ W, α x w ∈ W := by
      rintro x _ ⟨z, hz, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, hα]
      refine ⟨_, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_subgroupOf, hαcoe]
      have := (mem_normalizer_iff.1 (hNP x.2) (z : G)).1 (mem_subgroupOf.1 hz)
      exact this
    obtain ⟨ψ, hψ, hψact⟩ := uc22p22k_act α W hWbot hWt hWn
    refine ⟨ψ, hψ, fun x hx y hy => ?_⟩
    have hz : e ⟨y, hP₁L hy⟩ ∈ W := ⟨_, mem_subgroupOf.2 hy, rfl⟩
    obtain ⟨t, ht⟩ := hWt _ hz
    have hez : e ⟨y, hP₁L hy⟩ = ⟨translation K t, translation_mem_coordinateG K t⟩ := Subtype.ext ht
    have h1 := hψact x t
    rw [hx] at h1
    have h2 : α x (e ⟨y, hP₁L hy⟩) = e ⟨y, hP₁L hy⟩ := by
      rw [hez]
      apply Subtype.ext
      rw [h1]
      simp [hez, ht]
    rw [hα] at h2
    have h3 := e.injective h2
    have h4 := congrArg Subtype.val h3
    rw [hαcoe] at h4
    exact h4


end Configuration

section Main

variable {G : Type} [Group G] [Finite G]

theorem uc22p22k_r613rank_of (D : Data G) (h613 : UC6.R6_13 D) : R613Rank D := by
  intro V hVM hker p P P₀ hyp R hR a haR hodd _h3 x hx
  obtain ⟨⟨hp3, _hsolv, hweak, _hΓ, hLieEx, hFrob⟩, _hstr, _hU, ⟨h4a, h4b, h4c⟩, _h5⟩ :=
    h613 p P P₀ hyp
  obtain ⟨hpP, _⟩ := D.sig_prime p (by rw [D.sig_sub]; exact Or.inl (Or.inr hyp.mem_sig2))
  have hp2 : p ≠ 2 := by omega
  haveI : Fact p.Prime := ⟨hpP⟩
  obtain ⟨L, hL⟩ : ∃ L : Subgroup G, L = UC6.inftyOf (centralizer (P₀ : Set G)) := ⟨_, rfl⟩
  rw [← hL] at hLieEx hFrob h4a h4b h4c
  have hLC : L ≤ centralizer (P₀ : Set G) := by rw [hL]; exact Subgroup.map_subtype_le _
  have hOM : pCoreOf 2 D.M ≤ D.M := Subgroup.map_subtype_le _
  have hOn : D.M ≤ normalizer (pCoreOf 2 D.M : Set G) :=
    Subgroup.le_normalizer.trans (UC6S846.normalizer_le_normalizer_pCoreOf D.M)
  have hO2 : IsPGroup 2 ↥(pCoreOf 2 D.M) := by
    unfold pCoreOf; exact CFSG.pCore_isPGroup.map _
  have hP₁p : IsPGroup p ↥(P ⊓ L) := hyp.sylow.isPGroup.to_le inf_le_left
  have hP₁M : P ⊓ L ≤ D.M := inf_le_left.trans hyp.sylow.le
  have hP₁L : P ⊓ L ≤ L := inf_le_right
  have hP₁On : P ⊓ L ≤ normalizer (pCoreOf 2 D.M : Set G) := hP₁M.trans hOn
  have hDn := uc22p22k_frob_norm hFrob
  have hDodd := uc22p22k_frob_odd hFrob hO2
  have hfix := hFrob.2.2.2.2.2.2.2
  have hP₀M : P₀ ≤ D.M := hyp.le.trans hyp.sylow.le
  have hP₀V : P₀ ≤ centralizer (L : Set G) := by
    intro v hv
    rw [mem_centralizer_iff]
    intro l hl
    exact (mem_centralizer_iff.1 (hLC hl) v hv).symm
  have hP₀ne : P₀ ≠ ⊥ := by
    intro h
    have := hyp.card
    rw [h, Subgroup.card_bot] at this
    exact hpP.one_lt.ne this
  have hOL : pCoreOf 2 D.M ⊓ L = ⊥ := uc22p22k_O_inf_L hfix hP₀V hP₀ne le_rfl
  have hN'L : ∀ n ∈ D.M ⊓ normalizer (P₀ : Set G), n ∈ normalizer (L : Set G) := by
    intro n hn
    rw [hL]
    exact uc22p22k_normalizer_inftyOf (uc22p22k_normalizer_centralizer hn.2)
  have hN'P : D.M ⊓ normalizer (P₀ : Set G) ≤ normalizer ((P ⊓ L : Subgroup G) : Set G) := fun n hn =>
    uc22p22k_normalizes_P1 hOL hP₁L hP₁On (h4b hn.1) (hN'L n hn)
  let Kt : Subgroup G := uc22p22k_Ktil D.M (pCoreOf 2 D.M) (P ⊓ L ⊔ pCoreOf 2 D.M) hOn
  have hKM : Kt ≤ D.M := uc22p22k_Ktil_le hOn
  have hKn : D.M ≤ normalizer (Kt : Set G) := uc22p22k_Ktil_normal hOn h4b
  have hP₀K : P₀ ≤ Kt := by
    intro v hv
    refine uc22p22k_mem_Ktil hOn hP₁M (hP₀M hv) (fun y hy => ?_)
    have := mem_centralizer_iff.1 (hP₀V hv) y (hP₁L hy)
    calc v * y * v⁻¹ = (v * y) * v⁻¹ := rfl
      _ = (y * v) * v⁻¹ := by rw [← this]
      _ = y := by group
  have hOK : pCoreOf 2 D.M ≤ Kt := uc22p22k_O_le_Ktil hOn hOM (sup_le hP₁M hOM)
  have hfrat := uc22p22k_frattini hyp.sylow hyp.le hweak hKM hKn hP₀K
  obtain ⟨f, hf1, hLie⟩ := hLieEx
  have hst := CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hLie
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hst
  have : Fintype F := Fintype.ofFinite F
  haveI : CharP F p :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hcard])
  let e₀ : ↥L ≃* coordinateG F := e.trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm.trans
      (pslEquivCoordinateG F))
  obtain ⟨ψ, hψsl, hψker⟩ := uc22p22k_psi_exists (G := G) (by omega : 0 < f) hcard e₀ hP₁L hP₁p
    (L := L) (N := D.M ⊓ normalizer (P₀ : Set G)) (fun n hn => hN'L n hn)
    (fun n hn => hN'P hn)
  have hψcyc := uc22p22k_cyc_of_semilinear ψ hψsl
  have hker' : ∀ n : ↥(D.M ⊓ normalizer (P₀ : Set G)), ψ n = 1 → (n : G) ∈ Kt :=
    fun n h => uc22p22k_mem_Ktil hOn hP₁M n.2.1 (hψker n h)
  haveI hKnorm : (Kt.subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).2 hKn
  have hcyc := uc22p22k_quot_cyc (M := D.M) (K := Kt) (N := D.M ⊓ normalizer (P₀ : Set G))
    inf_le_left hKM hfrat ψ hψcyc hker'
  let π : ↥D.M →* MBar D.M V := QuotientGroup.mk' (kerAct D.M V).normalCore
  have hkerπ : ∀ m : ↥D.M, π m = 1 ↔ (m : G) ∈ pCoreOf 2 D.M := by
    intro m
    show (QuotientGroup.mk m : MBar D.M V) = 1 ↔ _
    rw [uc22br_gt_mk_eq_one_iff hVM m]
    constructor
    · intro h
      rw [← hker]
      exact ⟨m.2, h⟩
    · intro h
      rw [← hker] at h
      exact h.2
  have hker2 : IsPGroup 2 ↥π.ker := by
    have h1 : π.ker = (pCoreOf 2 D.M).subgroupOf D.M := by
      ext m
      rw [MonoidHom.mem_ker, hkerπ, mem_subgroupOf]
    rw [h1]
    exact hO2.comap_subtype
  have hkerK : π.ker ≤ Kt.subgroupOf D.M := by
    intro m hm
    rw [MonoidHom.mem_ker, hkerπ] at hm
    exact mem_subgroupOf.2 (hOK hm)
  have hP₁odd : ∀ y ∈ P ⊓ L, Odd (orderOf y) := by
    intro y hy
    obtain ⟨j, hj⟩ := hP₁p ⟨y, hy⟩
    have hj' : y ^ (p ^ j) = 1 := by
      have := congrArg Subtype.val hj
      simpa using this
    have hodd' : Odd p := hpP.odd_of_ne_two hp2
    exact Odd.of_dvd_nat (hodd'.pow) (orderOf_dvd_of_pow_eq_one hj')
  have hcommDP : ∀ d ∈ centralizer (L : Set G), ∀ y ∈ P ⊓ L, d * y = y * d := fun d hd y hy =>
    (mem_centralizer_iff.1 hd y (hP₁L hy)).symm
  have hT1 : ∀ c ∈ Kt.subgroupOf D.M, (∃ j : ℕ, (π c) ^ (2 ^ j) = 1) → π c = 1 := by
    rintro c hc ⟨j, hj⟩
    have hcK : (c : G) ∈ Kt := mem_subgroupOf.1 hc
    have hmem : (c : G) ∈ centralizer (L : Set G) ⊔ (P ⊓ L) ⊔ pCoreOf 2 D.M :=
      h4a (c : G) c.2 (fun y hy => hcK.2 y (mem_sup_left hy))
    have hod := uc22p22k_T1 π hkerπ hOM hP₁M hDn hP₁On hDodd hP₁odd hcommDP c hmem
    have hd : orderOf (π c) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj
    have hcop : Nat.Coprime (orderOf (π c)) (2 ^ j) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hod)
    have h1 : orderOf (π c) = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hd
    exact orderOf_eq_one_iff.1 h1
  exact uc22p22k_final π (QuotientGroup.mk'_surjective _) (Kt.subgroupOf D.M) hker2 hkerK hcyc hT1
    hR haR hodd x hx

theorem uc22p22k_s22_8_of (D : Data G) (Ch : Choice2011 G) (h111 : F11.R111 D) (hV : S22_V D Ch)
    (h112 : F11.R112 D) (hhyp612 : ∀ p ∈ D.sig2, ∃ P P₀ : Subgroup G, UC6.Hyp612 D p P P₀)
    (h613 : UC6.R6_13 D) (hn3 : ∀ c : Ctx22b D Ch, 3 ≤ c.n) : S22_8 D Ch :=
  s22_8_of D Ch h111 hV h112 hhyp612 h613 hn3 (uc22p22k_r613rank_of D h613)

end Main

end CFSG.LocalAnalysis.UniquenessCase.UC22
