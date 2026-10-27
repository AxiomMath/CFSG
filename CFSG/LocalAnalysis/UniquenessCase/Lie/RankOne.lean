module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.ConclAt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

@[expose] def uc22pwr1_shape (Y : Type) [Group Y] (E : Subgroup Y) : Prop :=
  IsCyclic E ∧ Squarefree (Nat.card E) ∧ Odd (Nat.card E)

theorem uc22pwr1_shape_map {Y Z : Type} [Group Y] [Group Z] (e : Y ≃* Z) (E : Subgroup Y)
    (h : uc22pwr1_shape Y E) : uc22pwr1_shape Z (E.map e.toMonoidHom) := by
  obtain ⟨hc, hsq, hodd⟩ := h
  have hcard : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective e.injective
  refine ⟨?_, hcard ▸ hsq, hcard ▸ hodd⟩
  exact isCyclic_of_surjective (e.subgroupMap E).toMonoidHom (e.subgroupMap E).surjective

@[expose] def UC22pwR1Datum (X : Type) [Group X] (U : Subgroup X) (n : ℕ) : Prop :=
  ∃ (T : Subgroup X) (w : X), IsCyclic T ∧ Odd (Nat.card T) ∧ T ≤ normalizer (U : Set X) ∧
    (∀ p : ℕ, p.Prime → p ∣ 2 ^ n - 1 → p ∣ Nat.card T) ∧
    w ^ 2 = 1 ∧ (∀ t ∈ T, t ^ (2 ^ n - 1) = 1 → w * t * w⁻¹ = t⁻¹) ∧
    normalizer (U : Set X) ⊔ Subgroup.zpowers w = ⊤ ∧
    ∀ ψ : MulAut X, (∀ x, x ∈ U ↔ ψ x ∈ U) →
      ∃ i : ℕ, ∀ t ∈ T, t ^ (2 ^ n - 1) = 1 → ∃ u ∈ U, ψ t = u * t ^ (2 ^ i)

theorem uc22pwr1_pow_card {X : Type} [Group X] [Finite X] {H : Subgroup X} {x : X} (hx : x ∈ H) :
    x ^ Nat.card H = 1 :=
  congrArg Subtype.val (pow_card_eq_one' (x := (⟨x, hx⟩ : H)))

theorem uc22pwr1_iter {X : Type} [Group X] {U E : Subgroup X} {φ : MulAut X} {i : ℕ}
    (hφU : ∀ x, x ∈ U ↔ φ x ∈ U) (hφE : ∀ x ∈ E, ∃ u ∈ U, φ x = u * x ^ 2 ^ i) (j : ℕ) :
    ∀ x ∈ E, ∃ u ∈ U, (φ ^ j) x = u * x ^ 2 ^ (i * j) := by
  induction j with
  | zero => intro x _; exact ⟨1, U.one_mem, by simp⟩
  | succ j ih =>
    intro x hx
    obtain ⟨u, hu, hj⟩ := ih x hx
    obtain ⟨u', hu', h'⟩ := hφE (x ^ 2 ^ (i * j)) (Subgroup.pow_mem _ hx _)
    refine ⟨φ u * u', U.mul_mem ((hφU u).1 hu) hu', ?_⟩
    rw [pow_succ', MulAut.mul_apply, hj, map_mul, h', ← pow_mul, ← pow_add, Nat.mul_succ, mul_assoc]

theorem uc22pwr1_eq_one_of_mem_inf {X : Type} [Group X] {U T : Subgroup X} (hU : IsPGroup 2 U)
    (hT : Odd (Nat.card T)) {u : X} (huU : u ∈ U) (huT : u ∈ T) : u = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_orderOf.1 hU ⟨u, huU⟩
  have h1 : orderOf u = 2 ^ a := (Subgroup.orderOf_coe (⟨u, huU⟩ : U)).trans ha
  have h2 : orderOf u ∣ Nat.card T := Subgroup.orderOf_dvd_natCard T huT
  have h3 : 2 ^ a ∣ Nat.card T := h1 ▸ h2
  have h4 : a = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.2 hT) (even_iff_two_dvd.2 ((dvd_pow_self 2 hne).trans h3))
  rw [h4, pow_zero] at h1
  exact orderOf_eq_one_iff.1 h1

theorem uc22pwr1_of_datumG {X : Type} [Group X] [Finite X] {U : Subgroup X} (hU : IsPGroup 2 U) {n : ℕ}
    (D : UC22pwR1Datum X U n) {P : Type} [Group P] (hP : IsPGroup 2 P) (ψ : P →* MulAut X)
    (hψ : ∀ (g : P) (x : X), x ∈ U ↔ ψ g x ∈ U) {m' : ℕ} (hm' : Odd m') {e : ℕ} (hnem : n = 2 ^ e * m') :
    ∃ E : Subgroup X, uc22pwlie_ConclAt uc22pwr1_shape X U P ψ n m' E ∧ uc22pwlie_Gal U E ψ := by
  obtain ⟨T, w, hTc, hTodd, hTN, hη, hw2, hwinv, hwgen, hfrob⟩ := D
  have hn1 : 1 ≤ n := by
    rw [hnem]
    exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero (pow_ne_zero _ two_ne_zero) hm'.pos.ne')
  have hN0 : 2 ^ n - 1 ≠ 0 := by
    have : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
    omega
  have hSp : ∀ p ∈ (2 ^ n - 1).primeFactors, p.Prime ∧ p ∣ Nat.card T := fun p hp =>
    ⟨Nat.prime_of_mem_primeFactors hp,
      hη p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)⟩
  obtain ⟨R, hRT, hRcard, hRx⟩ := uc22pwlie_exists_subgroup_of_primes T (2 ^ n - 1).primeFactors hSp
  have hrN : Nat.card R ∣ 2 ^ n - 1 := by
    rw [hRcard]
    exact Finset.prod_primes_dvd _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime)
      (fun p hp => Nat.dvd_of_mem_primeFactors hp)
  have hRN : ∀ x ∈ R, x ^ (2 ^ n - 1) = 1 := by
    intro x hx
    obtain ⟨c, hc⟩ := hrN
    rw [hc, pow_mul, uc22pwr1_pow_card hx, one_pow]
  have hRodd : Odd (Nat.card R) := hTodd.of_dvd_nat (Subgroup.card_dvd_of_le hRT)
  have hRsq : Squarefree (Nat.card R) := by
    rw [hRcard]
    exact uc22pwlie_squarefree_prod_primes _ fun p hp => Nat.prime_of_mem_primeFactors hp
  have hRcyc : IsCyclic R :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hRT).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hRT).surjective
  have hRab : IsMulCommutative R := inferInstance
  have hRpi : piSet R = etaSet n := by
    ext p
    constructor
    · rintro ⟨hp, hpd⟩
      exact ⟨hp, hpd.trans hrN⟩
    · rintro ⟨hp, hpd⟩
      refine ⟨hp, ?_⟩
      rw [hRcard]
      exact Finset.dvd_prod_of_mem _ (Nat.mem_primeFactors.2 ⟨hp, hpd, hN0⟩)
  refine ⟨R, ⟨hRT.trans hTN, ⟨hRcyc, hRsq, hRodd⟩, hRpi, ?_, ?_, w, hw2,
    fun x hx => hwinv x (hRT hx) (hRN x hx), hwgen⟩, fun g => ?_⟩
  · intro g x hx
    obtain ⟨i, hi⟩ := hfrob (ψ g) (hψ g)
    obtain ⟨u, hu, hux⟩ := hi x (hRT hx) (hRN x hx)
    rw [hux, sup_comm]
    exact Subgroup.mul_mem_sup hu (Subgroup.pow_mem R hx _)
  · intro g x hx
    obtain ⟨hxR, hxα⟩ := uc22pwlie_mem_of_mem_oPi hRab hx
    obtain ⟨i, hi⟩ := hfrob (ψ g) (hψ g)
    obtain ⟨u₀, hu₀, hux⟩ := hi x (hRT hxR) (hRN x hxR)
    obtain ⟨k, hk⟩ := hP g
    have hiter := uc22pwr1_iter (E := R) (φ := ψ g) (i := i) (hψ g)
      (fun y hy => hi y (hRT hy) (hRN y hy)) (2 ^ k) x hxR
    obtain ⟨u, hu, hxu⟩ := hiter
    have hφk : (ψ g) ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
    rw [hφk] at hxu
    have hM : 1 ≤ 2 ^ (i * 2 ^ k) := Nat.one_le_two_pow
    have hxM : x ^ 2 ^ (i * 2 ^ k) = x := by
      have hu1 : u = 1 := by
        have h1 : u = x * (x ^ 2 ^ (i * 2 ^ k))⁻¹ := by
          rw [eq_mul_inv_iff_mul_eq]
          exact (by simpa using hxu.symm)
        refine uc22pwr1_eq_one_of_mem_inf hU hTodd hu ?_
        rw [h1]
        exact T.mul_mem (hRT hxR) (T.inv_mem (Subgroup.pow_mem T (hRT hxR) _))
      rw [hu1, one_mul] at hxu
      exact hxu.symm
    have hxord : orderOf x ∣ 2 ^ (i * 2 ^ k) - 1 := by
      refine orderOf_dvd_of_pow_eq_one ?_
      have : x ^ (2 ^ (i * 2 ^ k) - 1) * x = x := by
        rw [← pow_succ, Nat.sub_add_cancel hM]
        exact hxM
      exact (mul_left_inj x).1 (by rw [one_mul]; exact this)
    have hxord2 : orderOf x ∣ 2 ^ i - 1 := by
      have hsq : Squarefree (orderOf x) :=
        hRsq.squarefree_of_dvd (hRcard ▸ (Subgroup.orderOf_dvd_natCard R hxR))
      rw [← Nat.prod_primeFactors_of_squarefree hsq]
      refine Finset.prod_primes_dvd _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime) fun p hp => ?_
      have hp' := Nat.prime_of_mem_primeFactors hp
      have hpd := Nat.dvd_of_mem_primeFactors hp
      exact uc22pwlie_dvd_two_pow_sub_one hm' (hxα p hp' hpd).2 (hpd.trans hxord)
    have hxi : x ^ 2 ^ i = x := by
      have hM' : 1 ≤ 2 ^ i := Nat.one_le_two_pow
      have : x ^ (2 ^ i - 1) * x = x := by
        rw [orderOf_dvd_iff_pow_eq_one.1 hxord2, one_mul]
      calc x ^ 2 ^ i = x ^ (2 ^ i - 1) * x := by rw [← pow_succ, Nat.sub_add_cancel hM']
        _ = x := this
    rw [hux, hxi, mul_inv_cancel_right]
    exact hu₀
  · obtain ⟨i, hi⟩ := hfrob (ψ g) (hψ g)
    refine ⟨i, fun x hx => ?_⟩
    obtain ⟨u, hu, hux⟩ := hi x (hRT hx) (hRN x hx)
    rw [hux, mul_inv_cancel_right]
    exact hu

theorem uc22pwr1_exists_equiv_sylow {X C : Type} [Group X] [Finite X] [Group C] (e₀ : X ≃* C) (U : Sylow 2 X)
    (U₀ : Sylow 2 C) : ∃ e : X ≃* C, (U : Subgroup X).map e.toMonoidHom = (U₀ : Subgroup C) := by
  haveI : Finite C := Finite.of_equiv X e₀.toEquiv
  let S' : Sylow 2 C := U.mapSurjective (f := e₀.toMonoidHom) e₀.surjective
  have hS' : (S' : Subgroup C) = (U : Subgroup X).map e₀.toMonoidHom := rfl
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C S' U₀
  refine ⟨e₀.trans (MulAut.conj g), ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, hS']
  ext y
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨e₀ x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem uc22pwr1_concl_of_datum_sylowG {X C : Type} [Group X] [Finite X] [Group C] (e₀ : X ≃* C) (U : Sylow 2 X)
    (U₀ : Sylow 2 C) {n : ℕ} (D : UC22pwR1Datum C (U₀ : Subgroup C) n) {P : Type} [Group P] (hP : IsPGroup 2 P)
    (ψ : P →* MulAut X) (hψ : ∀ (g : P) (x : X), x ∈ (U : Subgroup X) ↔ ψ g x ∈ (U : Subgroup X)) {m' : ℕ}
    (hm' : Odd m') {e : ℕ} (hnem : n = 2 ^ e * m') :
    ∃ E : Subgroup X, uc22pwlie_ConclAt uc22pwr1_shape X (U : Subgroup X) P ψ n m' E ∧
      uc22pwlie_Gal (U : Subgroup X) E ψ := by
  haveI : Finite C := Finite.of_equiv X e₀.toEquiv
  obtain ⟨e', he'⟩ := uc22pwr1_exists_equiv_sylow e₀ U U₀
  have hψ' : ∀ (g : P) (x : C), x ∈ (U₀ : Subgroup C) ↔
      ((MulAut.congr e').toMonoidHom.comp ψ) g x ∈ (U₀ : Subgroup C) := by
    intro g x
    rw [← he', uc22pwlie_mem_map_iff, uc22pwlie_mem_map_iff]
    have h1 := hψ g (e'.symm x)
    simpa [MulAut.congr_apply] using h1
  obtain ⟨E', hE', hG⟩ := uc22pwr1_of_datumG U₀.isPGroup' D hP _ hψ' hm' hnem
  rw [← he'] at hE' hG
  exact ⟨_, uc22pwlie_ConclAt.of_mulEquiv (fun e E h => uc22pwr1_shape_map e E h) e' ψ hE',
    uc22pwlie_Gal.of_mulEquiv e' ψ hG⟩

theorem uc22pwr1_concl_of_datum_sylow {X C : Type} [Group X] [Finite X] [Group C] (e₀ : X ≃* C) (U : Sylow 2 X)
    (U₀ : Sylow 2 C) {n : ℕ} (D : UC22pwR1Datum C (U₀ : Subgroup C) n) {P : Type} [Group P] (hP : IsPGroup 2 P)
    (ψ : P →* MulAut X) (hψ : ∀ (g : P) (x : X), x ∈ (U : Subgroup X) ↔ ψ g x ∈ (U : Subgroup X)) {m' : ℕ}
    (hm' : Odd m') {e : ℕ} (hnem : n = 2 ^ e * m') :
    uc22pwlie_Concl uc22pwr1_shape X (U : Subgroup X) P ψ n m' := by
  obtain ⟨E, hE, -⟩ := uc22pwr1_concl_of_datum_sylowG e₀ U U₀ D hP ψ hψ hm' hnem
  exact ⟨E, hE⟩

theorem uc22pwr1_literal_of_concl {X : Type} [Group X] [Finite X] {U : Subgroup X} {P : Type} [Group P]
    {ψ : P →* MulAut X} {n m' : ℕ} (h : uc22pwlie_Concl uc22pwr1_shape X U P ψ n m') :
    ∃ E : Subgroup X, E ≤ normalizer (U : Set X) ∧ IsCyclic E ∧ Squarefree (Nat.card E) ∧
      Odd (Nat.card E) ∧ piSet E = etaSet n ∧ (∀ (g : P), ∀ x ∈ E, ψ g x ∈ E ⊔ U) ∧
      (∀ (g : P), ∀ x ∈ oPi {p | p.Prime ∧ p ∣ 2 ^ m' - 1} E, ψ g x * x⁻¹ ∈ U) ∧
      ∃ w : X, w ^ 2 = 1 ∧ (∀ x ∈ E, w * x * w⁻¹ = x⁻¹) ∧
        normalizer (U : Set X) ⊔ Subgroup.zpowers w = ⊤ := by
  obtain ⟨E, hEN, ⟨hc, hsq, hodd⟩, hrest⟩ := h
  exact ⟨E, hEN, hc, hsq, hodd, hrest⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
