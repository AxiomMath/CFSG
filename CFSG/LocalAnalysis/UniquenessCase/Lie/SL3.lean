module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.GraphInput
public import CFSG.LocalAnalysis.UniquenessCase.Lie.SL3Cover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Subgroup Matrix

section PowerForm

variable {K : Type} [Field K] {X : Type} [Group X]

@[expose] def uc22pwI3PF (xd : Kˣ →* X) (U : Subgroup X) (β : MulAut X) (i : ℕ) : Prop :=
  ∀ a : Kˣ, β (xd a) * (xd (a ^ 2 ^ i))⁻¹ ∈ U

theorem uc22pwI3PF_one (xd : Kˣ →* X) (U : Subgroup X) : uc22pwI3PF xd U 1 0 := fun a => by
  simp [uc22pwI3PF]

theorem uc22pwI3PF_mul {xd : Kˣ →* X} {U : Subgroup X} {β₁ β₂ : MulAut X} (hβ₁ : ∀ u ∈ U, β₁ u ∈ U)
    {i₁ i₂ : ℕ} (h₁ : uc22pwI3PF xd U β₁ i₁) (h₂ : uc22pwI3PF xd U β₂ i₂) :
    uc22pwI3PF xd U (β₁ * β₂) (i₁ + i₂) := by
  intro a
  have hu₂ := h₂ a
  have hu₁ := h₁ (a ^ 2 ^ i₂)
  have e : (β₁ * β₂) (xd a) * (xd (a ^ 2 ^ (i₁ + i₂)))⁻¹ =
      β₁ (β₂ (xd a) * (xd (a ^ 2 ^ i₂))⁻¹) *
        (β₁ (xd (a ^ 2 ^ i₂)) * (xd ((a ^ 2 ^ i₂) ^ 2 ^ i₁))⁻¹) := by
    rw [← pow_mul, ← pow_add, add_comm i₁ i₂] at *
    simp only [MulAut.mul_apply, map_mul, map_inv]
    group
  rw [e]
  exact Subgroup.mul_mem _ (hβ₁ _ hu₂) hu₁

theorem uc22pwI3PF_pow {xd : Kˣ →* X} {U : Subgroup X} {β : MulAut X} (hβ : ∀ u ∈ U, β u ∈ U) {i : ℕ}
    (h : uc22pwI3PF xd U β i) (j : ℕ) : uc22pwI3PF xd U (β ^ j) (j * i) := by
  induction j with
  | zero =>
    rw [pow_zero, zero_mul]
    exact uc22pwI3PF_one xd U
  | succ j ih =>
    have := uc22pwI3PF_mul hβ h ih
    rw [pow_succ', Nat.succ_mul, add_comm]
    exact this

theorem uc22pwI3PF_eq_of_one {xd : Kˣ →* X} {U : Subgroup X} (hxd : ∀ c : Kˣ, xd c ∈ U → c = 1) {i : ℕ}
    (h : uc22pwI3PF xd U 1 i) (a : Kˣ) : a ^ 2 ^ i = a := by
  have h1 := h a
  rw [MulAut.one_apply, ← map_inv, ← map_mul] at h1
  exact (mul_inv_eq_one.1 (hxd _ h1)).symm

end PowerForm

theorem uc22pwI3_pow_fixed {G : Type} [Monoid G] {u : G} {m : ℕ} (hu : u ^ 2 ^ m = u) (r : ℕ) :
    u ^ 2 ^ (m * r) = u := by
  induction r with
  | zero => simp
  | succ r ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hu]

theorem uc22pwI3_orderOf_dvd {G : Type} [Group G] {a : G} {N M : ℕ} (hN : orderOf a ∣ N)
    (hNsq : Squarefree N) (hM : ∀ p : ℕ, p.Prime → p ∣ orderOf a → p ∣ M) : orderOf a ∣ M := by
  have hsq : Squarefree (orderOf a) := hNsq.squarefree_of_dvd hN
  rw [← Nat.prod_primeFactors_of_squarefree hsq]
  exact Finset.prod_primes_dvd M (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime)
    (fun p hp => hM p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))

variable {K : Type} [Field K]

theorem uc22pwI3_Ep_units [Finite K] {d : ℕ} (hd : Squarefree d) (R : Subgroup Kˣ)
    (hR : ∀ x ∈ R, x ^ d = 1) (hodd : Odd (Nat.card R)) : uc22pwI2Ep Kˣ R := by
  refine ⟨inferInstance, hodd, fun p hp => ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  let Q : Sylow p R := default
  have hexp : ∀ x ∈ (Q : Subgroup R), x ^ p = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp Q.isPGroup') ⟨x, hx⟩
    have hk' : orderOf x = p ^ k := by rwa [Subgroup.orderOf_mk] at hk
    have hxd : x ^ d = 1 := Subtype.ext (hR x x.2)
    have hdvd : p ^ k ∣ d := hk' ▸ orderOf_dvd_of_pow_eq_one hxd
    have hk1 : k ≤ 1 := by
      by_contra hk2
      have hk2' : 2 ≤ k := by omega
      have h2 : p * p ∣ d := by
        rw [← pow_two]
        exact (pow_dvd_pow p hk2').trans hdvd
      exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hd p h2))
    rw [← orderOf_dvd_iff_pow_eq_one, hk']
    exact (pow_dvd_pow p hk1).trans (by simp)
  refine ⟨Q, ⟨inferInstance, hexp⟩, ?_⟩
  let f : ↥(Q : Subgroup R) → {u : Kˣ // u ^ p = 1} := fun x => ⟨((x : R) : Kˣ), by
    have h1 := hexp x x.2
    exact congrArg Subtype.val h1⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : (f x).1 = (f y).1 := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h1)
  calc Nat.card Q ≤ Nat.card {u : Kˣ // u ^ p = 1} := Nat.card_le_card_of_injective f hf
    _ ≤ p := uc22pwI2_card_rootsOfUnity_le hp.pos
    _ ≤ p ^ 2 := Nat.le_self_pow (by norm_num) p

theorem uc22pwI3_concl_of_isSL3G {X : Type} [Group X] [Finite X] (hq : CFSG.Open.IsQuasisimple X) {n : ℕ}
    (hn : 2 < n) (hsl3 : IsSL3 X n) (U : Sylow 2 X) {P : Type} [Group P] (hP : IsPGroup 2 P)
    (ψ : P →* MulAut X) (hψ : ∀ (g : P) (x : X), x ∈ (U : Subgroup X) ↔ ψ g x ∈ (U : Subgroup X))
    {e m' : ℕ} (hm' : Odd m') (hnem : n = 2 ^ e * m') :
    ∃ E : Subgroup X, uc22pwlie_ConclAt uc22pwI2Ep X (U : Subgroup X) P ψ n m' E ∧
      uc22pwlie_Gal (U : Subgroup X) E ψ := by
  obtain ⟨K, _, _, _, α, hK, hα, hαc, hαU⟩ := uc22pwI3_exists_cover_sylow hq hn hsl3.2 U
  have hK5 : 5 ≤ Nat.card K := by
    rw [hK]
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  let xd : Kˣ →* X := α.comp (uc22pwI3dSL K)
  have hker : ∀ c : Kˣ, xd c ∈ (U : Subgroup X) → c = 1 := by
    intro c hc
    rw [← hαU] at hc
    obtain ⟨u, hu, hue⟩ := hc
    have hz : u⁻¹ * uc22pwI3dSL K c ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      change (α u)⁻¹ * xd c = 1
      rw [hue, inv_mul_cancel]
    exact uc22pwI3_dSL_eq_one_of_mul_center (u := u) (z := u⁻¹ * uc22pwI3dSL K c) hu (hαc hz) (by group)
  have hinj : Function.Injective xd := by
    rw [injective_iff_map_eq_one]
    intro c hc
    exact hker c (by rw [hc]; exact one_mem _)
  have hcardK : Nat.card Kˣ = 2 ^ n - 1 := by rw [Nat.card_units, hK]
  have hQodd : Odd (Nat.card Kˣ) := by
    rw [hcardK]
    obtain ⟨j, hj⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [hj, pow_succ]
    have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    exact ⟨2 ^ j - 1, by omega⟩
  obtain ⟨R, -, hRsq, hRodd, hRprimes, -⟩ := uc22pw_radical_subgroup (C := Kˣ) hQodd
  have hRexp : ∀ x ∈ R, x ^ Nat.card R = 1 := by
    intro x hx
    have h1 := pow_card_eq_one' (G := R) (x := (⟨x, hx⟩ : R))
    exact congrArg Subtype.val h1
  have hEp : uc22pwI2Ep X (R.map xd) :=
    (uc22pwI3_Ep_units hRsq R hRexp hRodd).map xd hinj
  have hpi : piSet (R.map xd) = etaSet n := by
    show {p | p.Prime ∧ p ∣ Nat.card ↥(R.map xd)} = {p | p.Prime ∧ p ∣ 2 ^ n - 1}
    rw [Subgroup.card_map_of_injective hinj]
    ext p
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hp, hd⟩
      exact ⟨hp, hcardK ▸ (hRprimes p hp).1 hd⟩
    · rintro ⟨hp, hd⟩
      exact ⟨hp, (hRprimes p hp).2 (hcardK ▸ hd)⟩
  have hEnorm : R.map xd ≤ normalizer ((U : Subgroup X) : Set X) := by
    rintro _ ⟨a, -, rfl⟩
    have hd : uc22pwI3dSL K a ∈ normalizer (unitriangular 3 K : Set (SpecialLinearGroup (Fin 3) K)) := by
      rw [normalizer_unitriangular]
      exact uc22pwI3dSL_mem_upper a
    rw [← hαU]
    exact Subgroup.le_normalizer_map α ⟨_, hd, rfl⟩
  have hpf : ∀ g : P, ∃ i : ℕ, m' ∣ i ∧ uc22pwI3PF xd (U : Subgroup X) (ψ g) i := by
    intro g
    have hφ : ∀ x, x ∈ (unitriangular 3 K).map α ↔ ψ g x ∈ (unitriangular 3 K).map α := by
      intro x
      rw [hαU]
      exact hψ g x
    obtain ⟨i, hi⟩ := uc22pwI3_pf hq hK5 α hα hαc (ψ g) hφ
    have hi' : uc22pwI3PF xd (U : Subgroup X) (ψ g) i := fun a => by
      rw [← hαU]
      exact hi a
    refine ⟨i, ?_, hi'⟩
    obtain ⟨k, hk⟩ := hP g
    have hU : ∀ u ∈ (U : Subgroup X), ψ g u ∈ (U : Subgroup X) := fun u hu => (hψ g u).1 hu
    have hpow := uc22pwI3PF_pow hU hi' (2 ^ k)
    have h1 : (ψ g) ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
    rw [h1] at hpow
    have hfix : ∀ a : Kˣ, a ^ 2 ^ (2 ^ k * i) = a := uc22pwI3PF_eq_of_one hker hpow
    have hfixK : ∀ x : K, x ^ 2 ^ (2 ^ k * i) = x := by
      intro x
      by_cases hx : x = 0
      · subst hx
        simp
      · have h2 := congrArg (fun u : Kˣ => (u : K)) (hfix (Units.mk0 x hx))
        simpa using h2
    have hndvd : n ∣ 2 ^ k * i := uc22pwI2_dvd_of_forall_pow hK hfixK
    have hm'n : m' ∣ n := ⟨2 ^ e, by rw [hnem, mul_comm]⟩
    exact (Nat.Coprime.pow_right k hm'.coprime_two_right).dvd_of_dvd_mul_left (hm'n.trans hndvd)
  have hinv : ∀ g : P, ∀ x ∈ R.map xd, ψ g x ∈ R.map xd ⊔ (U : Subgroup X) := by
    intro g x hx
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨i, -, hi⟩ := hpf g
    have h1 : ψ g (xd a) = (ψ g (xd a) * (xd (a ^ 2 ^ i))⁻¹) * xd (a ^ 2 ^ i) := by group
    rw [h1, sup_comm]
    exact Subgroup.mul_mem_sup (hi a) ⟨a ^ 2 ^ i, pow_mem ha _, rfl⟩
  have hαcl : ∀ g : P, ∀ x ∈ oPi {p | p.Prime ∧ p ∣ 2 ^ m' - 1} (R.map xd),
      ψ g x * x⁻¹ ∈ (U : Subgroup X) := by
    intro g x hx
    obtain ⟨hxE, hxα⟩ := uc22pwlie_mem_of_mem_oPi hEp.1 hx
    obtain ⟨a, ha, rfl⟩ := hxE
    obtain ⟨i, hmi, hi⟩ := hpf g
    have hord : orderOf (xd a) = orderOf a := orderOf_injective xd hinj a
    have hdvdR : orderOf a ∣ Nat.card R := Subgroup.orderOf_dvd_natCard R ha
    have hdvdM : orderOf a ∣ 2 ^ m' - 1 :=
      uc22pwI3_orderOf_dvd hdvdR hRsq (fun p hp hpd => (hxα p hp (hord ▸ hpd)).2)
    have hafix : a ^ 2 ^ m' = a := by
      have h3 : a ^ (2 ^ m' - 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 hdvdM
      have h4 : 2 ^ m' = (2 ^ m' - 1) + 1 := by
        have : 1 ≤ 2 ^ m' := Nat.one_le_two_pow
        omega
      rw [h4, pow_succ, h3, one_mul]
    obtain ⟨r, rfl⟩ := hmi
    have hfix : a ^ 2 ^ (m' * r) = a := uc22pwI3_pow_fixed hafix r
    have h5 := hi a
    rw [hfix] at h5
    exact h5
  have hw2 : (α (uc22pwI3Jsl K)) ^ 2 = 1 := by rw [← map_pow, uc22pwI3Jsl_sq, map_one]
  have hwinv : ∀ x ∈ R.map xd, α (uc22pwI3Jsl K) * x * (α (uc22pwI3Jsl K))⁻¹ = x⁻¹ := by
    rintro _ ⟨a, -, rfl⟩
    show α (uc22pwI3Jsl K) * α (uc22pwI3dSL K a) * (α (uc22pwI3Jsl K))⁻¹ = (α (uc22pwI3dSL K a))⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, uc22pwI3Jsl_conj_dSL, map_inv]
  have hgen : normalizer ((U : Subgroup X) : Set X) ⊔ Subgroup.zpowers (α (uc22pwI3Jsl K)) = ⊤ := by
    have hT : (upperTriangular 3 K ⊔ Subgroup.zpowers (uc22pwI3Jsl K)).map α = ⊤ := by
      rw [uc22pwI3_upper_sup_Jsl, Subgroup.map_top_of_surjective α hα]
    rw [Subgroup.map_sup, MonoidHom.map_zpowers] at hT
    have hle : (upperTriangular 3 K).map α ≤ normalizer ((U : Subgroup X) : Set X) := by
      rintro _ ⟨b, hb, rfl⟩
      have hb' : b ∈ normalizer (unitriangular 3 K : Set (SpecialLinearGroup (Fin 3) K)) := by
        rw [normalizer_unitriangular]
        exact hb
      rw [← hαU]
      exact Subgroup.le_normalizer_map α ⟨_, hb', rfl⟩
    rw [eq_top_iff, ← hT]
    exact sup_le_sup hle le_rfl
  refine ⟨R.map xd, ⟨hEnorm, hEp, hpi, hinv, hαcl, α (uc22pwI3Jsl K), hw2, hwinv, hgen⟩, fun g => ?_⟩
  obtain ⟨i, -, hi⟩ := hpf g
  refine ⟨i, ?_⟩
  rintro _ ⟨a, -, rfl⟩
  rw [← map_pow]
  exact hi a

theorem uc22pwCartanSL3_holds : uc22pwCartanSL3 := by
  intro X _ _ hq n hn hsl3 U P _ hP ψ hψ e m' hm' hnem
  obtain ⟨E, ⟨hEnorm, ⟨hab, hodd, hsyl⟩, hpi, hinv, hαcl, w, hw2, hwinv, hgen⟩, -⟩ :=
    uc22pwI3_concl_of_isSL3G hq hn hsl3 U hP ψ hψ hm' hnem
  exact ⟨E, hEnorm, hab, hodd, hsyl, hpi, hinv, hαcl, w, hw2, hwinv, hgen⟩

theorem uc22pwCartanGraph_holds : uc22pwCartanGraph :=
  uc22pwCartanGraph_of_sl3 uc22pwCartanSL3_holds

end CFSG.LocalAnalysis.UniquenessCase.UC22
