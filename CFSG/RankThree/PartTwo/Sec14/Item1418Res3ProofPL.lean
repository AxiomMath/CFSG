module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Commutator.Basic
import CFSG.GroupTheory.ThompsonAxB
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.RankThree.Coprime.ThompsonElementaryComplement
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer

public section

namespace CFSG.RankThree.PartTwo.Sec14.Proof1418Res3

open Subgroup
open scoped commutatorElement

variable {K : Type*} [Group K]

theorem isPGroup_zpowers_three {c : K} (hc3 : c ^ 3 = 1) : IsPGroup 3 (zpowers c) := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp g.2
  simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
  rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3, one_zpow]

theorem isPGroup_three_of_exp {P : Subgroup K} (hexp : ∀ x ∈ P, x ^ 3 = 1) : IsPGroup 3 P := by
  intro g
  exact ⟨1, Subtype.ext (by simpa using hexp g g.2)⟩

theorem not_three_dvd_of_two [Finite K] {R : Subgroup K} (hR : IsPGroup 2 R) :
    ¬ 3 ∣ Nat.card R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  rw [hk]
  intro h
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow h)
  omega

theorem not_two_dvd_of_three [Finite K] {P : Subgroup K} (hP : IsPGroup 3 P) :
    ¬ 2 ∣ Nat.card P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  rw [hk]
  intro h
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two Nat.prime_three).mp
    (Nat.prime_two.dvd_of_dvd_pow h)
  omega

theorem mem_normalizer_of_conj_mem [Finite K] {H : Subgroup K} {g : K}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ normalizer (H : Set K) := by
  have hpow : ∀ n : ℕ, ∀ x ∈ H, g ^ n * x * (g ^ n)⁻¹ ∈ H := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      have := h _ (ih x hx)
      rw [pow_succ', mul_inv_rev]
      convert this using 1
      group
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have hn := hpow (orderOf g - 1) _ hx
  have hg : g ^ (orderOf g - 1) * g = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos g), pow_orderOf_eq_one]
  have hginv : g ^ (orderOf g - 1) = g⁻¹ := eq_inv_of_mul_eq_one_left hg
  rw [hginv] at hn
  simpa [mul_assoc] using hn

omit [Group K] in
theorem eq_one_of_pow_three_of_sq {M : Type*} [Group M] {x : M} (h3 : x ^ 3 = 1)
    (h2 : x ^ 2 = 1) : x = 1 := by
  have : x = x ^ 3 * (x ^ 2)⁻¹ := by group
  rw [this, h3, h2]
  simp

theorem centralizer_le_of_thompson [Finite K] {P Q : Subgroup K} {c : K} (hP : IsPGroup 3 P)
    (hQ : ¬ 3 ∣ Nat.card Q) (hc3 : c ^ 3 = 1) (hQP : Q ≤ normalizer (P : Set K))
    (hcP : c ∈ normalizer (P : Set K)) (hQc : ∀ q ∈ Q, q * c = c * q)
    (hfix : ∀ x ∈ P, x * c = c * x → ∀ q ∈ Q, q * x = x * q) :
    ∀ q ∈ Q, ∀ x ∈ P, q * x = x * q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set B := zpowers c with hBdef
  have hBP : B ≤ normalizer (P : Set K) := zpowers_le.mpr hcP
  have hB3 : IsPGroup 3 B := isPGroup_zpowers_three hc3
  let α : Q →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hQP)
  let β : B →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hBP)
  have hα : ∀ (a : Q) (x : P), ((α a x : P) : K) = (a : K) * x * (a : K)⁻¹ := fun _ _ => rfl
  have hβ : ∀ (b : B) (x : P), ((β b x : P) : K) = (b : K) * x * (b : K)⁻¹ := fun _ _ => rfl
  have hab : ∀ (a : Q) (b : B), (a : K) * b = b * a := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (hQc a ha) k).eq
  have hcomm : ∀ a b, α a * β b = β b * α a := by
    intro a b
    ext x
    simp only [MulAut.mul_apply]
    rw [hα, hβ, hβ, hα]
    calc (a : K) * ((b : K) * x * (b : K)⁻¹) * (a : K)⁻¹
        = ((a : K) * b) * x * ((a : K) * b)⁻¹ := by group
      _ = ((b : K) * a) * x * ((b : K) * a)⁻¹ := by rw [hab a b]
      _ = (b : K) * ((a : K) * x * (a : K)⁻¹) * (b : K)⁻¹ := by group
  have hfix' : ∀ a r, (∀ b, β b r = r) → α a r = r := by
    rintro ⟨a, ha⟩ r hr
    have hrc : (r : K) * c = c * r := by
      have h := congrArg Subtype.val (hr ⟨c, mem_zpowers c⟩)
      rw [hβ] at h
      calc (r : K) * c = c * r * c⁻¹ * c := by rw [h]
        _ = c * r := by group
    have hq := hfix r r.2 hrc a ha
    apply Subtype.ext
    rw [hα]
    change a * r * a⁻¹ = r
    rw [hq]
    group
  have h := CFSG.GroupTheory.thompson_A_times_B hP hQ hB3 α β hcomm hfix'
  intro q hq x hx
  have hx' := congrArg (fun φ : MulAut P => ((φ ⟨x, hx⟩ : P) : K)) (h ⟨q, hq⟩)
  rw [hα] at hx'
  change q * x * q⁻¹ = ((1 : MulAut P) ⟨x, hx⟩ : K) at hx'
  rw [MulAut.one_apply] at hx'
  calc q * x = q * x * q⁻¹ * q := by group
    _ = x * q := by rw [hx']

theorem commutator_zpowers_le_of_conj [Finite K] {M K₁ : Subgroup K} {c : K}
    (hcM : c ∈ normalizer (M : Set K)) (hK₁ : M ≤ normalizer (K₁ : Set K))
    (hcK₁ : c ∈ normalizer (K₁ : Set K)) (h : ∀ m ∈ M, c * m * c⁻¹ * m⁻¹ ∈ K₁) :
    ⁅M, zpowers c⁆ ≤ K₁ := by
  have hpow : ∀ n : ℕ, ∀ m ∈ M, c ^ n * m * (c ^ n)⁻¹ * m⁻¹ ∈ K₁ := by
    intro n
    induction n with
    | zero => intro m _; simp
    | succ n ih =>
      intro m hm
      have h1 := ih m hm
      have hcm : c ^ n * m * (c ^ n)⁻¹ ∈ M := by
        have hcn : c ^ n ∈ normalizer (M : Set K) := pow_mem hcM n
        exact (mem_normalizer_iff.mp hcn m).mp hm
      have h2 := h _ hcm
      have h3 : c * (c ^ n * m * (c ^ n)⁻¹ * m⁻¹) * c⁻¹ ∈ K₁ :=
        (mem_normalizer_iff.mp hcK₁ _).mp h1
      have h4 : c * (c ^ n * m * (c ^ n)⁻¹ * m⁻¹) * c⁻¹ *
          (c * m * c⁻¹ * m⁻¹) ∈ K₁ := mul_mem h3 (h m hm)
      have e : c ^ (n + 1) * m * (c ^ (n + 1))⁻¹ * m⁻¹ =
          c * (c ^ n * m * (c ^ n)⁻¹ * m⁻¹) * c⁻¹ * (c * m * c⁻¹ * m⁻¹) := by
        rw [pow_succ']; group
      rw [e]
      exact h4
  rw [commutator_le]
  intro m hm g hg
  obtain ⟨n, -, rfl⟩ : ∃ n : ℕ, n < orderOf c ∧ c ^ n = g := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    refine ⟨(k % (orderOf c : ℤ)).toNat, ?_, ?_⟩
    · have hpos : (0 : ℤ) < orderOf c := by exact_mod_cast orderOf_pos c
      have := Int.emod_lt_of_pos k hpos
      have h0 := Int.emod_nonneg k hpos.ne'
      omega
    · rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k
        (by exact_mod_cast (orderOf_pos c).ne')), zpow_mod_orderOf]
  have h1 := hpow n m⁻¹ (inv_mem hm)
  have h2 : m * (c ^ n * m⁻¹ * (c ^ n)⁻¹ * m⁻¹⁻¹) * m⁻¹ ∈ K₁ :=
    (mem_normalizer_iff.mp (hK₁ hm) _).mp h1
  rw [commutatorElement_def]
  convert h2 using 1
  group

theorem map_conj_eq_of_mem_normalizer {H : Subgroup K} {g : K} (hg : g ∈ normalizer (H : Set K)) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have := (mem_normalizer_iff.mp (inv_mem hg) x).mp hx
    simpa [mul_assoc] using this

theorem mem_normalizer_commutator [Finite K] {H₁ H₂ : Subgroup K} {g : K}
    (h₁ : g ∈ normalizer (H₁ : Set K)) (h₂ : g ∈ normalizer (H₂ : Set K)) :
    g ∈ normalizer ((⁅H₁, H₂⁆ : Subgroup K) : Set K) := by
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  have hmap : (⁅H₁, H₂⁆ : Subgroup K).map (MulAut.conj g).toMonoidHom = ⁅H₁, H₂⁆ := by
    rw [map_commutator, map_conj_eq_of_mem_normalizer h₁, map_conj_eq_of_mem_normalizer h₂]
  rw [← hmap]
  exact ⟨x, hx, by simp [MulAut.conj_apply]⟩

theorem le_normalizer_commutator [Finite K] {H₁ H₂ M : Subgroup K}
    (h₁ : M ≤ normalizer (H₁ : Set K)) (h₂ : M ≤ normalizer (H₂ : Set K)) :
    M ≤ normalizer ((⁅H₁, H₂⁆ : Subgroup K) : Set K) :=
  fun _ hg => mem_normalizer_commutator (h₁ hg) (h₂ hg)

theorem mem_normalizer_sup [Finite K] {H₁ H₂ : Subgroup K} {g : K}
    (h₁ : g ∈ normalizer (H₁ : Set K)) (h₂ : g ∈ normalizer (H₂ : Set K)) :
    g ∈ normalizer ((H₁ ⊔ H₂ : Subgroup K) : Set K) := by
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  have hmap : (H₁ ⊔ H₂).map (MulAut.conj g).toMonoidHom = H₁ ⊔ H₂ := by
    rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer h₁, map_conj_eq_of_mem_normalizer h₂]
  rw [← hmap]
  exact ⟨x, hx, by simp [MulAut.conj_apply]⟩

theorem dichotomy [Finite K] {R K₁ : Subgroup K} {c : K} (hc3 : c ^ 3 = 1) (hR : IsPGroup 2 R)
    (hmin : ∀ R' : Subgroup K, R' ≤ R → R' ≠ R → c ∈ normalizer (R' : Set K) →
      ⁅R', zpowers c⁆ = R' → R' ≤ K₁)
    (hCc : R ⊓ centralizer ({c} : Set K) ≤ K₁) {M : Subgroup K} (hK₁M : K₁ ≤ M) (hMR : M ≤ R)
    (hcM : c ∈ normalizer (M : Set K)) : M = K₁ ∨ M = R := by
  have hZ3 : IsPGroup 3 (zpowers c) := isPGroup_zpowers_three hc3
  have hZM : zpowers c ≤ normalizer (M : Set K) := zpowers_le.mpr hcM
  have hM3 : ¬ 3 ∣ Nat.card M :=
    fun h => not_three_dvd_of_two hR (h.trans (Subgroup.card_dvd_of_le hMR))
  have hM'M : ⁅M, zpowers c⁆ ≤ M := le_normalizer_iff_commutator_le_left.mp hZM
  have hcM' : c ∈ normalizer ((⁅M, zpowers c⁆ : Subgroup K) : Set K) :=
    mem_normalizer_commutator hcM (le_normalizer (mem_zpowers c))
  have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3
    Nat.prime_three (zpowers c) M hZ3 hM3 hZM
  by_cases hM'R : ⁅M, zpowers c⁆ = R
  · right
    exact le_antisymm hMR (hM'R ▸ hM'M)
  · left
    have hle := hmin _ (hM'M.trans hMR) hM'R hcM' hidem
    refine le_antisymm ?_ hK₁M
    rw [CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization 3
      Nat.prime_three (zpowers c) M hZ3 hM3 hZM]
    refine sup_le hle ((le_inf (inf_le_left.trans hMR) ?_).trans hCc)
    exact inf_le_right.trans (centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers c)))

theorem exists_central_mod [Finite K] {R K₁ : Subgroup K} (hR : IsPGroup 2 R) (hK₁R : K₁ ≤ R)
    (hne : K₁ ≠ R) : ∃ t ∈ R, t ∉ K₁ ∧ t ^ 2 ∈ K₁ ∧ ∀ r ∈ R, ⁅t, r⁆ ∈ K₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₁ := K₁.subgroupOf R with hL₁
  have hnil : Group.IsNilpotent R := hR.isNilpotent
  obtain ⟨n, hn⟩ := hnil.nilpotent
  have hex : ∃ n, ¬ Subgroup.upperCentralSeries R n ≤ L₁ := by
    refine ⟨n, fun h => hne ?_⟩
    rw [hn] at h
    refine le_antisymm hK₁R fun x hx => ?_
    have : (⟨x, hx⟩ : R) ∈ L₁ := h (mem_top _)
    exact mem_subgroupOf.mp this
  have hn₀spec : ¬ Subgroup.upperCentralSeries R (Nat.find hex) ≤ L₁ := Nat.find_spec hex
  have hn₀pos : Nat.find hex ≠ 0 := by
    intro h0
    apply hn₀spec
    rw [h0, Subgroup.upperCentralSeries_zero]
    exact bot_le
  obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := Nat.exists_eq_succ_of_ne_zero hn₀pos
  have hmle : Subgroup.upperCentralSeries R m ≤ L₁ := by
    by_contra h
    exact Nat.find_min hex (show m < Nat.find hex by omega) h
  obtain ⟨t', ht'U, ht'L⟩ := Set.not_subset.mp hn₀spec
  rw [hm] at ht'U
  obtain ⟨k, hk⟩ := hR t'
  have hexj : ∃ j, t' ^ 2 ^ (j + 1) ∈ L₁ :=
    ⟨k, by rw [pow_succ, pow_mul, hk, one_pow]; exact one_mem _⟩
  have ht₀U : t' ^ 2 ^ Nat.find hexj ∈ Subgroup.upperCentralSeries R (m + 1) :=
    pow_mem ht'U _
  have ht₀L : t' ^ 2 ^ Nat.find hexj ∉ L₁ := by
    rcases Nat.eq_zero_or_pos (Nat.find hexj) with h | h
    · rw [h, pow_zero, pow_one]
      exact ht'L
    · obtain ⟨i, hi⟩ : ∃ i, Nat.find hexj = i + 1 := ⟨Nat.find hexj - 1, by omega⟩
      have := Nat.find_min hexj (show i < Nat.find hexj by omega)
      rw [hi]
      exact this
  have ht₀2 : (t' ^ 2 ^ Nat.find hexj) ^ 2 ∈ L₁ := by
    rw [← pow_mul, ← pow_succ]
    exact Nat.find_spec hexj
  refine ⟨((t' ^ 2 ^ Nat.find hexj : R) : K), (t' ^ 2 ^ Nat.find hexj).2,
    fun h => ht₀L (mem_subgroupOf.mpr h), ?_, ?_⟩
  · have := mem_subgroupOf.mp ht₀2
    simpa using this
  · intro r hr
    have := mem_subgroupOf.mp (hmle ((Subgroup.mem_upperCentralSeries_succ_iff.mp ht₀U) ⟨r, hr⟩))
    simpa [commutatorElement_def] using this

theorem exists_four_group [Finite K] {R K₁ : Subgroup K} {c : K} (hc3 : c ^ 3 = 1)
    (hR : IsPGroup 2 R) (hK₁R : K₁ ≤ R) (hRK₁ : R ≤ normalizer (K₁ : Set K)) (hne : K₁ ≠ R)
    (hcR : c ∈ normalizer (R : Set K)) (hcK₁ : c ∈ normalizer (K₁ : Set K))
    (hdich : ∀ M : Subgroup K, K₁ ≤ M → M ≤ R → c ∈ normalizer (M : Set K) → M = K₁ ∨ M = R)
    (hgen : ¬ ⁅R, zpowers c⁆ ≤ K₁) :
    ∃ t ∈ R, t ^ 2 ∈ K₁ ∧ (∀ r ∈ R, ⁅t, r⁆ ∈ K₁) ∧
      t * (c * t * c⁻¹) * (c * (c * t * c⁻¹) * c⁻¹) ∈ K₁ ∧
      R = closure ({t, c * t * c⁻¹, c * (c * t * c⁻¹) * c⁻¹} : Set K) ⊔ K₁ := by
  obtain ⟨t, htR, htK, ht2, htc⟩ := exists_central_mod hR hK₁R hne
  have hconjR : ∀ x ∈ R, c * x * c⁻¹ ∈ R := fun x hx => (mem_normalizer_iff.mp hcR x).mp hx
  have ht₂R : c * t * c⁻¹ ∈ R := hconjR t htR
  have ht₃R : c * (c * t * c⁻¹) * c⁻¹ ∈ R := hconjR _ ht₂R
  have hccc : c * c * c = 1 := by rw [← hc3, pow_three, mul_assoc]
  have hct₃ : c * (c * (c * t * c⁻¹) * c⁻¹) * c⁻¹ = t := by
    have : c * (c * (c * t * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * t * (c * c * c)⁻¹ := by group
    rw [this, hccc]
    group
  let S : Subgroup K :=
    { carrier := {m | m ∈ R ∧ c * m * c⁻¹ * m⁻¹ ∈ K₁}
      mul_mem' := by
        rintro a b ⟨haR, ha⟩ ⟨hbR, hb⟩
        refine ⟨mul_mem haR hbR, ?_⟩
        have h1 : a * (c * b * c⁻¹ * b⁻¹) * a⁻¹ ∈ K₁ :=
          (mem_normalizer_iff.mp (hRK₁ haR) _).mp hb
        have e : c * (a * b) * c⁻¹ * (a * b)⁻¹ =
            (c * a * c⁻¹ * a⁻¹) * (a * (c * b * c⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e]
        exact mul_mem ha h1
      one_mem' := ⟨one_mem _, by simp⟩
      inv_mem' := by
        rintro a ⟨haR, ha⟩
        refine ⟨inv_mem haR, ?_⟩
        have h1 : a⁻¹ * (c * a * c⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ ∈ K₁ :=
          (mem_normalizer_iff.mp (hRK₁ (inv_mem haR)) _).mp (inv_mem ha)
        have e : c * a⁻¹ * c⁻¹ * a⁻¹⁻¹ = a⁻¹ * (c * a * c⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e]
        exact h1 }
  have hSR : S ≤ R := fun m hm => hm.1
  have hK₁S : K₁ ≤ S := fun k hk =>
    ⟨hK₁R hk, mul_mem ((mem_normalizer_iff.mp hcK₁ k).mp hk) (inv_mem hk)⟩
  have hcS : c ∈ normalizer (S : Set K) := by
    refine mem_normalizer_of_conj_mem fun m hm => ⟨hconjR m hm.1, ?_⟩
    have h1 : c * (c * m * c⁻¹ * m⁻¹) * c⁻¹ ∈ K₁ := (mem_normalizer_iff.mp hcK₁ _).mp hm.2
    have e : c * (c * m * c⁻¹) * c⁻¹ * (c * m * c⁻¹)⁻¹ = c * (c * m * c⁻¹ * m⁻¹) * c⁻¹ := by
      group
    rw [e]
    exact h1
  have hSK : S = K₁ := by
    rcases hdich S hK₁S hSR hcS with h | h
    · exact h
    · exfalso
      apply hgen
      refine commutator_zpowers_le_of_conj hcR hRK₁ hcK₁ fun m hm => ?_
      have hmS : m ∈ S := h ▸ hm
      exact hmS.2
  have hN : t * (c * t * c⁻¹) * (c * (c * t * c⁻¹) * c⁻¹) ∈ K₁ := by
    rw [← hSK]
    refine ⟨mul_mem (mul_mem htR ht₂R) ht₃R, ?_⟩
    have hcN : c * (t * (c * t * c⁻¹) * (c * (c * t * c⁻¹) * c⁻¹)) * c⁻¹ =
        (c * t * c⁻¹) * (c * (c * t * c⁻¹) * c⁻¹) * t := by
      calc c * (t * (c * t * c⁻¹) * (c * (c * t * c⁻¹) * c⁻¹)) * c⁻¹
          = (c * t * c⁻¹) * (c * (c * t * c⁻¹) * c⁻¹) *
              (c * (c * (c * t * c⁻¹) * c⁻¹) * c⁻¹) := by group
        _ = (c * t * c⁻¹) * (c * (c * t * c⁻¹) * c⁻¹) * t := by rw [hct₃]
    have e : c * (t * (c * t * c⁻¹) * (c * (c * t * c⁻¹) * c⁻¹)) * c⁻¹ *
        (t * (c * t * c⁻¹) * (c * (c * t * c⁻¹) * c⁻¹))⁻¹ =
        ⁅t, (c * t * c⁻¹) * (c * (c * t * c⁻¹) * c⁻¹)⁆⁻¹ := by
      rw [hcN, commutatorElement_def]
      group
    rw [e]
    exact inv_mem (htc _ (mul_mem ht₂R ht₃R))
  have hM₀R : closure ({t, c * t * c⁻¹, c * (c * t * c⁻¹) * c⁻¹} : Set K) ⊔ K₁ ≤ R := by
    refine sup_le ((closure_le _).mpr ?_) hK₁R
    rintro x (rfl | rfl | rfl)
    · exact htR
    · exact ht₂R
    · exact ht₃R
  have hcM₀ : c ∈ normalizer
      ((closure ({t, c * t * c⁻¹, c * (c * t * c⁻¹) * c⁻¹} : Set K) ⊔ K₁ : Subgroup K) :
        Set K) := by
    refine mem_normalizer_sup ?_ hcK₁
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    have hmap : (closure ({t, c * t * c⁻¹, c * (c * t * c⁻¹) * c⁻¹} : Set K)).map
        (MulAut.conj c).toMonoidHom ≤ closure {t, c * t * c⁻¹, c * (c * t * c⁻¹) * c⁻¹} := by
      rw [MonoidHom.map_closure]
      refine (closure_le _).mpr ?_
      rintro _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rcases hy with rfl | rfl | rfl
      · exact subset_closure (by simp)
      · exact subset_closure (by simp)
      · rw [hct₃]
        exact subset_closure (by simp)
    exact hmap ⟨x, hx, by simp [MulAut.conj_apply]⟩
  rcases hdich _ le_sup_right hM₀R hcM₀ with h | h
  · exfalso
    apply htK
    rw [← h]
    exact mem_sup_left (subset_closure (by simp))
  · exact ⟨t, htR, ht2, htc, hN, h.symm⟩

def Ev (Z : Subgroup K) (t y : K) : Bool → Prop
  | true => t * y * t⁻¹ * y⁻¹ ∈ Z
  | false => t * y * t⁻¹ * y ∈ Z

theorem ev_conj {Z : Subgroup K} {c t y : K} (hcZ : c ∈ normalizer (Z : Set K)) {s : Bool}
    (h : Ev Z t y s) : Ev Z (c * t * c⁻¹) (c * y * c⁻¹) s := by
  cases s
  · have h1 := (mem_normalizer_iff.mp hcZ _).mp (show t * y * t⁻¹ * y ∈ Z from h)
    show c * t * c⁻¹ * (c * y * c⁻¹) * (c * t * c⁻¹)⁻¹ * (c * y * c⁻¹) ∈ Z
    convert h1 using 1
    group
  · have h1 := (mem_normalizer_iff.mp hcZ _).mp (show t * y * t⁻¹ * y⁻¹ ∈ Z from h)
    show c * t * c⁻¹ * (c * y * c⁻¹) * (c * t * c⁻¹)⁻¹ * (c * y * c⁻¹)⁻¹ ∈ Z
    convert h1 using 1
    group

theorem ev_mem {Z M : Subgroup K} {t y : K} {s : Bool} (h : Ev Z t y s) (hy : y ∈ M)
    (hZM : Z ≤ M) : t * y * t⁻¹ ∈ M := by
  cases s
  · have h1 : t * y * t⁻¹ * y ∈ M := hZM h
    have e : t * y * t⁻¹ = (t * y * t⁻¹ * y) * y⁻¹ := by group
    rw [e]
    exact mul_mem h1 (inv_mem hy)
  · have h1 : t * y * t⁻¹ * y⁻¹ ∈ M := hZM h
    have e : t * y * t⁻¹ = (t * y * t⁻¹ * y⁻¹) * y := by group
    rw [e]
    exact mul_mem h1 hy

theorem ev_comp {P Z : Subgroup K} {t₀ t₂ t₃ y : K} (hZ : Z ≤ centralizer (P : Set K))
    (hyP : y ∈ P) (ht₂Z : t₂ ∈ normalizer (Z : Set K))
    (hcomp : t₃ * y * t₃⁻¹ = t₂ * (t₀ * y * t₀⁻¹) * t₂⁻¹) {s₀ s₂ : Bool}
    (h₀ : Ev Z t₀ y s₀) (h₂ : Ev Z t₂ y s₂) : Ev Z t₃ y (s₀ == s₂) := by
  have hzy : ∀ z ∈ Z, z * y = y * z := fun z hz => (mem_centralizer_iff.mp (hZ hz) y hyP).symm
  cases s₀ <;> cases s₂
  ·
    have h₀' : t₀ * y * t₀⁻¹ * y ∈ Z := h₀
    have h₂' : t₂ * y * t₂⁻¹ * y ∈ Z := h₂
    have h₀c := (mem_normalizer_iff.mp ht₂Z _).mp h₀'
    have hc := hzy _ (inv_mem h₂')
    show t₃ * y * t₃⁻¹ * y⁻¹ ∈ Z
    have e : t₃ * y * t₃⁻¹ * y⁻¹ =
        (t₂ * (t₀ * y * t₀⁻¹ * y) * t₂⁻¹) * (y * (t₂ * y * t₂⁻¹ * y)⁻¹ * y⁻¹) := by
      rw [hcomp]; group
    rw [e, show y * (t₂ * y * t₂⁻¹ * y)⁻¹ * y⁻¹ = (t₂ * y * t₂⁻¹ * y)⁻¹ by
      rw [← hc]; group]
    exact mul_mem h₀c (inv_mem h₂')
  ·
    have h₀' : t₀ * y * t₀⁻¹ * y ∈ Z := h₀
    have h₂' : t₂ * y * t₂⁻¹ * y⁻¹ ∈ Z := h₂
    have h₀c := (mem_normalizer_iff.mp ht₂Z _).mp h₀'
    have hc := hzy _ (inv_mem h₂')
    show t₃ * y * t₃⁻¹ * y ∈ Z
    have e : t₃ * y * t₃⁻¹ * y =
        (t₂ * (t₀ * y * t₀⁻¹ * y) * t₂⁻¹) * (y⁻¹ * (t₂ * y * t₂⁻¹ * y⁻¹)⁻¹ * y) := by
      rw [hcomp]; group
    rw [e, show y⁻¹ * (t₂ * y * t₂⁻¹ * y⁻¹)⁻¹ * y = (t₂ * y * t₂⁻¹ * y⁻¹)⁻¹ by
      rw [mul_assoc, hc]; group]
    exact mul_mem h₀c (inv_mem h₂')
  ·
    have h₀' : t₀ * y * t₀⁻¹ * y⁻¹ ∈ Z := h₀
    have h₂' : t₂ * y * t₂⁻¹ * y ∈ Z := h₂
    have h₀c := (mem_normalizer_iff.mp ht₂Z _).mp h₀'
    show t₃ * y * t₃⁻¹ * y ∈ Z
    have e : t₃ * y * t₃⁻¹ * y =
        (t₂ * (t₀ * y * t₀⁻¹ * y⁻¹) * t₂⁻¹) * (t₂ * y * t₂⁻¹ * y) := by
      rw [hcomp]; group
    rw [e]
    exact mul_mem h₀c h₂'
  ·
    have h₀' : t₀ * y * t₀⁻¹ * y⁻¹ ∈ Z := h₀
    have h₂' : t₂ * y * t₂⁻¹ * y⁻¹ ∈ Z := h₂
    have h₀c := (mem_normalizer_iff.mp ht₂Z _).mp h₀'
    show t₃ * y * t₃⁻¹ * y⁻¹ ∈ Z
    have e : t₃ * y * t₃⁻¹ * y⁻¹ =
        (t₂ * (t₀ * y * t₀⁻¹ * y⁻¹) * t₂⁻¹) * (t₂ * y * t₂⁻¹ * y⁻¹) := by
      rw [hcomp]; group
    rw [e]
    exact mul_mem h₀c h₂'

theorem commutatorElement_mul_left_of_comm {x y z : K} (h : z * (x * y * x⁻¹) = x * y * x⁻¹ * z) :
    ⁅z * x, y⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc z * x * y * (z * x)⁻¹ * y⁻¹ = z * (x * y * x⁻¹) * z⁻¹ * y⁻¹ := by group
    _ = x * y * x⁻¹ * z * z⁻¹ * y⁻¹ := by rw [h]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem commutatorElement_mul_right_of_comm {x y z : K} (hx : z * x = x * z)
    (h : z * ⁅x, y⁆ = ⁅x, y⁆ * z) : ⁅x, z * y⁆ = ⁅x, y⁆ := by
  have hx' : x * z⁻¹ = z⁻¹ * x := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hx, inv_mul_cancel_left]
  calc ⁅x, z * y⁆ = z * ⁅x, y⁆ * z⁻¹ := by
        rw [commutatorElement_def, commutatorElement_def]
        calc x * (z * y) * x⁻¹ * (z * y)⁻¹ = x * z * y * x⁻¹ * y⁻¹ * z⁻¹ := by group
          _ = z * x * y * x⁻¹ * y⁻¹ * z⁻¹ := by rw [hx]
          _ = z * (x * y * x⁻¹ * y⁻¹) * z⁻¹ := by group
    _ = ⁅x, y⁆ := by rw [h]; group

theorem commutatorElement_inv_right_of_comm {x y : K} (h : ⁅x, y⁆ * y = y * ⁅x, y⁆) :
    ⁅x, y⁻¹⁆ = ⁅x, y⁆⁻¹ := by
  have h' : ⁅x, y⁆⁻¹ * y = y * ⁅x, y⁆⁻¹ := (show Commute ⁅x, y⁆ y from h).inv_left.eq
  calc ⁅x, y⁻¹⁆ = y⁻¹ * (⁅x, y⁆⁻¹ * y) := by
        rw [commutatorElement_def, commutatorElement_def]; group
    _ = ⁅x, y⁆⁻¹ := by rw [h']; group

theorem commute_of_ev {P Z : Subgroup K} {t a b : K} (hexp : ∀ x ∈ P, x ^ 3 = 1)
    (hZ : Z ≤ centralizer (P : Set K)) (hZP : Z ≤ P) (haP : a ∈ P) (hbP : b ∈ P)
    (hcen : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ centralizer (P : Set K))
    (htc : ∀ x ∈ P, ∀ y ∈ P, t * ⁅x, y⁆ * t⁻¹ = ⁅x, y⁆) {s : Bool} (ha : Ev Z t a s)
    (hb : Ev Z t b (!s)) : a * b = b * a := by
  have key : ∀ a b : K, a ∈ P → b ∈ P → Ev Z t a true → Ev Z t b false → ⁅a, b⁆ = 1 := by
    intro a b haP hbP ha hb
    have ha' : t * a * t⁻¹ * a⁻¹ ∈ Z := ha
    have hb' : t * b * t⁻¹ * b ∈ Z := hb
    set z₁ := t * a * t⁻¹ * a⁻¹ with hz₁
    set z₂ := t * b * t⁻¹ * b with hz₂
    have hta : t * a * t⁻¹ = z₁ * a := by rw [hz₁]; group
    have htb : t * b * t⁻¹ = z₂ * b⁻¹ := by rw [hz₂]; group
    have hcomm : ∀ z ∈ Z, ∀ x ∈ P, z * x = x * z :=
      fun z hz x hx => (mem_centralizer_iff.mp (hZ hz) x hx).symm
    have hwP : ⁅a, b⁆ ∈ P := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem haP hbP) (inv_mem haP)) (inv_mem hbP)
    have hbinvP : z₂ * b⁻¹ ∈ P := mul_mem (hZP hb') (inv_mem hbP)
    have h1 : ⁅z₁ * a, z₂ * b⁻¹⁆ = ⁅a, z₂ * b⁻¹⁆ := by
      refine commutatorElement_mul_left_of_comm (hcomm _ ha' _ ?_)
      exact mul_mem (mul_mem haP hbinvP) (inv_mem haP)
    have hwinvP : ⁅a, b⁻¹⁆ ∈ P := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem haP (inv_mem hbP)) (inv_mem haP)) (inv_mem (inv_mem hbP))
    have h2 : ⁅a, z₂ * b⁻¹⁆ = ⁅a, b⁻¹⁆ :=
      commutatorElement_mul_right_of_comm (hcomm _ hb' _ haP) (hcomm _ hb' _ hwinvP)
    have h3 : ⁅a, b⁻¹⁆ = ⁅a, b⁆⁻¹ :=
      commutatorElement_inv_right_of_comm (mem_centralizer_iff.mp (hcen a haP b hbP) b hbP).symm
    have h4 : t * ⁅a, b⁆ * t⁻¹ = ⁅t * a * t⁻¹, t * b * t⁻¹⁆ := by
      rw [commutatorElement_def, commutatorElement_def]; group
    have h5 : ⁅a, b⁆ = ⁅a, b⁆⁻¹ :=
      calc ⁅a, b⁆ = t * ⁅a, b⁆ * t⁻¹ := (htc a haP b hbP).symm
        _ = ⁅t * a * t⁻¹, t * b * t⁻¹⁆ := h4
        _ = ⁅z₁ * a, z₂ * b⁻¹⁆ := by rw [hta, htb]
        _ = ⁅a, z₂ * b⁻¹⁆ := h1
        _ = ⁅a, b⁻¹⁆ := h2
        _ = ⁅a, b⁆⁻¹ := h3
    have hsq : ⁅a, b⁆ ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [h5]
      exact mul_inv_cancel _
    exact eq_one_of_pow_three_of_sq (hexp _ hwP) hsq
  cases s
  ·
    have h := key b a hbP haP hb ha
    rw [commutatorElement_eq_one_iff_mul_comm] at h
    exact h.symm
  · have h := key a b haP hbP ha hb
    rwa [commutatorElement_eq_one_iff_mul_comm] at h

theorem sup_le_centralizer_self {P Z : Subgroup K} {S : Set K} (hSP : S ⊆ P)
    (hZ : Z ≤ centralizer (P : Set K)) (hZP : Z ≤ P) (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) :
    closure S ⊔ Z ≤ centralizer ((closure S ⊔ Z : Subgroup K) : Set K) := by
  have hMP : closure S ⊔ Z ≤ P := sup_le ((closure_le _).mpr hSP) hZP
  refine sup_le ((closure_le _).mpr fun a ha => ?_) (hZ.trans (centralizer_le hMP))
  rw [SetLike.mem_coe, mem_centralizer_iff]
  intro m hm
  have hle : closure S ⊔ Z ≤ centralizer ({a} : Set K) := by
    refine sup_le ((closure_le _).mpr fun b hb => ?_) fun z hz => ?_
    · rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      exact hS b hb a ha
    · rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.mp (hZ hz) a (hSP ha)).symm
  exact (mem_centralizer_singleton_iff.mp (hle hm))

theorem mem_normalizer_center [Finite K] {P : Subgroup K} {g : K}
    (hg : g ∈ normalizer (P : Set K)) :
    g ∈ normalizer ((P ⊓ centralizer (P : Set K) : Subgroup K) : Set K) := by
  refine mem_normalizer_of_conj_mem fun z hz =>
    Subgroup.mem_inf.mpr ⟨(mem_normalizer_iff.mp hg z).mp hz.1, ?_⟩
  rw [mem_centralizer_iff]
  intro p hp
  have hp' : g⁻¹ * p * g ∈ P := by
    have := (mem_normalizer_iff.mp (inv_mem hg) p).mp hp
    simpa using this
  have h := mem_centralizer_iff.mp hz.2 _ hp'
  calc p * (g * z * g⁻¹) = g * ((g⁻¹ * p * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * p * g)) * g⁻¹ := by rw [h]
    _ = g * z * g⁻¹ * p := by group

theorem mem_normalizer_closure_sup [Finite K] {S : Set K} {Z : Subgroup K} {g : K}
    (hS : ∀ s ∈ S, g * s * g⁻¹ ∈ closure S ⊔ Z) (hgZ : g ∈ normalizer (Z : Set K)) :
    g ∈ normalizer ((closure S ⊔ Z : Subgroup K) : Set K) := by
  refine mem_normalizer_of_conj_mem fun m hm => ?_
  have hmap : (closure S ⊔ Z).map (MulAut.conj g).toMonoidHom ≤ closure S ⊔ Z := by
    rw [Subgroup.map_sup, MonoidHom.map_closure, map_conj_eq_of_mem_normalizer hgZ]
    refine sup_le ((closure_le _).mpr ?_) le_sup_right
    rintro _ ⟨y, hy, rfl⟩
    exact hS y hy
  exact hmap ⟨m, hm, by simp [MulAut.conj_apply]⟩

theorem mem_of_mul_self_mem {Z : Subgroup K} {x : K} (h3 : x ^ 3 = 1) (h : x * x ∈ Z) :
    x ∈ Z := by
  have e : x = (x * x) * (x * x) := by
    calc x = x ^ 3 * x := by rw [h3, one_mul]
      _ = x * x * x * x := by rw [pow_three']
      _ = (x * x) * (x * x) := by simp only [mul_assoc]
  rw [e]
  exact mul_mem h h

theorem false_of_nonabelian [Finite K] {P R K₁ : Subgroup K} {c t : K} (hc3 : c ^ 3 = 1)
    (hexp : ∀ x ∈ P, x ^ 3 = 1) (hRP : R ≤ normalizer (P : Set K))
    (hcP : c ∈ normalizer (P : Set K)) (hK₁P : K₁ ≤ centralizer (P : Set K))
    (hcK₁ : c ∈ normalizer (K₁ : Set K)) (htR : t ∈ R) (hcR : c ∈ normalizer (R : Set K))
    (ht2 : t ^ 2 ∈ K₁) (htc : ∀ r ∈ R, ⁅t, r⁆ ∈ K₁)
    (hN : t * (c * t * c⁻¹) * (c * (c * t * c⁻¹) * c⁻¹) ∈ K₁)
    (hRgen : R = closure ({t, c * t * c⁻¹, c * (c * t * c⁻¹) * c⁻¹} : Set K) ⊔ K₁)
    (hPR : ⁅P, R⁆ = P) (hP'R : ⁅P, P⁆ ≤ centralizer (R : Set K))
    (hP'Z : ⁅P, P⁆ ≤ centralizer (P : Set K))
    (hmin : ∀ M : Subgroup K, M ≤ P → M ≠ P → R ≤ normalizer (M : Set K) →
      c ∈ normalizer (M : Set K) → ⁅M, R⁆ = ⊥)
    (hnab : ¬ P ≤ centralizer (P : Set K)) : False := by
  set Z := P ⊓ centralizer (P : Set K) with hZdef
  set t₂ := c * t * c⁻¹ with ht₂def
  set t₃ := c * t₂ * c⁻¹ with ht₃def
  have hZP : Z ≤ P := inf_le_left
  have hZC : Z ≤ centralizer (P : Set K) := inf_le_right
  have hconjR : ∀ x ∈ R, c * x * c⁻¹ ∈ R := fun x hx => (mem_normalizer_iff.mp hcR x).mp hx
  have hconjP : ∀ g ∈ normalizer (P : Set K), ∀ x ∈ P, g * x * g⁻¹ ∈ P :=
    fun g hg x hx => (mem_normalizer_iff.mp hg x).mp hx
  have ht₂R : t₂ ∈ R := hconjR t htR
  have ht₃R : t₃ ∈ R := hconjR t₂ ht₂R
  have hccc : c * c * c = 1 := by rw [← hc3, pow_three, mul_assoc]
  have hct₃ : c * t₃ * c⁻¹ = t := by
    have : c * t₃ * c⁻¹ = (c * c * c) * t * (c * c * c)⁻¹ := by
      simp only [ht₃def, ht₂def]; group
    rw [this, hccc]; group
  have hRZ : ∀ r ∈ R, r ∈ normalizer (Z : Set K) := fun r hr => mem_normalizer_center (hRP hr)
  have hcZ : c ∈ normalizer (Z : Set K) := mem_normalizer_center hcP
  have hK₁act : ∀ k ∈ K₁, ∀ x ∈ P, k * x * k⁻¹ = x := fun k hk x hx => by
    have h := mem_centralizer_iff.mp (hK₁P hk) x hx
    rw [← h]; group
  have hsq : ∀ s ∈ R, s ^ 2 ∈ K₁ → ∀ x ∈ P, s * (s * x * s⁻¹) * s⁻¹ = x := by
    intro s _ hs x hx
    calc s * (s * x * s⁻¹) * s⁻¹ = s ^ 2 * x * (s ^ 2)⁻¹ := by rw [sq]; group
      _ = x := hK₁act _ hs x hx
  have hinv : ∀ s ∈ R, s ^ 2 ∈ K₁ → ∀ x ∈ P, s⁻¹ * x * s = s * x * s⁻¹ := by
    intro s hsR hs x hx
    have hx' : s⁻¹ * x * s ∈ P := by
      have := hconjP s⁻¹ (inv_mem (hRP hsR)) x hx
      simpa using this
    calc s⁻¹ * x * s = s * (s * (s⁻¹ * x * s) * s⁻¹) * s⁻¹ := (hsq s hsR hs _ hx').symm
      _ = s * x * s⁻¹ := by group
  have ht₂sq : t₂ ^ 2 ∈ K₁ := by
    have e : t₂ ^ 2 = c * t ^ 2 * c⁻¹ := by simp only [ht₂def]; rw [sq, sq]; group
    rw [e]
    exact (mem_normalizer_iff.mp hcK₁ _).mp ht2
  have h02 : ∀ x ∈ P, t * (t₂ * x * t₂⁻¹) * t⁻¹ = t₂ * (t * x * t⁻¹) * t₂⁻¹ := by
    intro x hx
    have hy : t₂ * (t * x * t⁻¹) * t₂⁻¹ ∈ P :=
      hconjP _ (hRP ht₂R) _ (hconjP _ (hRP htR) x hx)
    have h := hK₁act _ (htc t₂ ht₂R) _ hy
    calc t * (t₂ * x * t₂⁻¹) * t⁻¹
        = ⁅t, t₂⁆ * (t₂ * (t * x * t⁻¹) * t₂⁻¹) * ⁅t, t₂⁆⁻¹ := by
          rw [commutatorElement_def]; group
      _ = t₂ * (t * x * t⁻¹) * t₂⁻¹ := h
  have h3 : ∀ x ∈ P, t₃ * x * t₃⁻¹ = t₂ * (t * x * t⁻¹) * t₂⁻¹ := by
    intro x hx
    have hNx := hK₁act _ hN x hx
    have hy : t * x * t⁻¹ ∈ P := hconjP _ (hRP htR) x hx
    calc t₃ * x * t₃⁻¹
        = t₂⁻¹ * (t⁻¹ * ((t * t₂ * t₃) * x * (t * t₂ * t₃)⁻¹) * t) * t₂ := by group
      _ = t₂⁻¹ * (t⁻¹ * x * t) * t₂ := by rw [hNx]
      _ = t₂⁻¹ * (t * x * t⁻¹) * t₂ := by rw [hinv t htR ht2 x hx]
      _ = t₂ * (t * x * t⁻¹) * t₂⁻¹ := hinv t₂ ht₂R ht₂sq _ hy
  have hT : ∀ (y : K) (s : Bool), Ev Z t₃ y s → Ev Z t (c * y * c⁻¹) s := by
    intro y s h
    have := ev_conj hcZ h
    rwa [hct₃] at this
  have hT₂ : ∀ (y : K) (s : Bool), Ev Z t y s → Ev Z t₂ (c * y * c⁻¹) s :=
    fun y s h => ev_conj hcZ h
  have hT₃ : ∀ (y : K) (s : Bool), Ev Z t₂ y s → Ev Z t₃ (c * y * c⁻¹) s :=
    fun y s h => ev_conj hcZ h
  have hcommP : ∀ p ∈ P, ∀ q ∈ P, ⁅p, q⁆ ∈ P := fun p hp q hq => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hp hq) (inv_mem hp)) (inv_mem hq)
  have hcommZ : ∀ p ∈ P, ∀ q ∈ P, ⁅p, q⁆ ∈ Z := fun p hp q hq =>
    ⟨hcommP p hp q hq, hP'Z (commutator_mem_commutator hp hq)⟩
  have hcen : ∀ p ∈ P, ∀ q ∈ P, ⁅p, q⁆ ∈ centralizer (P : Set K) :=
    fun p hp q hq => hP'Z (commutator_mem_commutator hp hq)
  have htcR : ∀ r ∈ R, ∀ p ∈ P, ∀ q ∈ P, r * ⁅p, q⁆ * r⁻¹ = ⁅p, q⁆ := by
    intro r hr p hp q hq
    have h := mem_centralizer_iff.mp (hP'R (commutator_mem_commutator hp hq)) r hr
    rw [h]; group
  have hy : ∃ y ∈ P, ⁅y, t⁆ ∉ Z := by
    by_contra hcon
    push Not at hcon
    have hcon₂ : ∀ y ∈ P, ⁅y, t₂⁆ ∈ Z := by
      intro y hy
      have hy' : c⁻¹ * y * c ∈ P := by
        have := hconjP c⁻¹ (inv_mem hcP) y hy
        simpa using this
      have h := (mem_normalizer_iff.mp hcZ _).mp (hcon _ hy')
      convert h using 1
      rw [ht₂def, commutatorElement_def, commutatorElement_def]
      group
    have hcon₃ : ∀ y ∈ P, ⁅y, t₃⁆ ∈ Z := by
      intro y hy
      have hy' : c⁻¹ * y * c ∈ P := by
        have := hconjP c⁻¹ (inv_mem hcP) y hy
        simpa using this
      have h := (mem_normalizer_iff.mp hcZ _).mp (hcon₂ _ hy')
      convert h using 1
      rw [ht₃def, commutatorElement_def, commutatorElement_def]
      group
    let T : Subgroup K :=
      { carrier := {r | r ∈ R ∧ ∀ y ∈ P, ⁅y, r⁆ ∈ Z}
        mul_mem' := by
          rintro a b ⟨haR, ha⟩ ⟨hbR, hb⟩
          refine ⟨mul_mem haR hbR, fun y hy => ?_⟩
          have h1 := (mem_normalizer_iff.mp (hRZ a haR) _).mp (hb y hy)
          have e : ⁅y, a * b⁆ = ⁅y, a⁆ * (a * ⁅y, b⁆ * a⁻¹) := by
            rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]; group
          rw [e]
          exact mul_mem (ha y hy) h1
        one_mem' := ⟨one_mem _, fun y _ => by simp⟩
        inv_mem' := by
          rintro a ⟨haR, ha⟩
          refine ⟨inv_mem haR, fun y hy => ?_⟩
          have h1 := (mem_normalizer_iff.mp (hRZ _ (inv_mem haR)) _).mp (inv_mem (ha y hy))
          have e : ⁅y, a⁻¹⁆ = a⁻¹ * ⁅y, a⁆⁻¹ * a⁻¹⁻¹ := by
            rw [commutatorElement_def, commutatorElement_def]; group
          rw [e]
          exact h1 }
    have hRT : R ≤ T := by
      have hle : closure ({t, t₂, t₃} : Set K) ⊔ K₁ ≤ T := by
        refine sup_le ((closure_le _).mpr ?_) fun k hk => ⟨?_, fun y hy => ?_⟩
        · intro r hr
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
          rcases hr with rfl | rfl | rfl
          · exact ⟨htR, hcon⟩
          · exact ⟨ht₂R, hcon₂⟩
          · exact ⟨ht₃R, hcon₃⟩
        · rw [hRgen]; exact mem_sup_right hk
        · have h := hK₁act k hk y⁻¹ (inv_mem hy)
          have e : ⁅y, k⁆ = y * (k * y⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
          rw [e, h, mul_inv_cancel]
          exact one_mem _
      rw [hRgen]
      exact hle
    apply hnab
    have hle : ⁅P, R⁆ ≤ Z := commutator_le.mpr fun y hy r hr => (hRT hr).2 y hy
    rw [hPR] at hle
    exact hle.trans hZC
  obtain ⟨y, hyP, hyZ⟩ := hy
  obtain ⟨w, hwdef⟩ : ∃ w, w = ⁅y, t⁆ := ⟨_, rfl⟩
  rw [← hwdef] at hyZ
  have hwP : w ∈ P := by
    have e : w = y * (t * y⁻¹ * t⁻¹) := by rw [hwdef, commutatorElement_def]; group
    rw [e]
    exact mul_mem hyP (hconjP _ (hRP htR) _ (inv_mem hyP))
  have htw : t * w * t⁻¹ = w⁻¹ := by
    have h := hsq t htR ht2 y⁻¹ (inv_mem hyP)
    rw [hwdef, commutatorElement_def]
    calc t * (y * t * y⁻¹ * t⁻¹) * t⁻¹ = (t * y * t⁻¹) * (t * (t * y⁻¹ * t⁻¹) * t⁻¹) := by group
      _ = (t * y * t⁻¹) * y⁻¹ := by rw [h]
      _ = (y * t * y⁻¹ * t⁻¹)⁻¹ := by group
  obtain ⟨a, hadef⟩ : ∃ a, a = t₂ * w * t₂⁻¹ := ⟨_, rfl⟩
  have haP : a ∈ P := by rw [hadef]; exact hconjP _ (hRP ht₂R) w hwP
  have ht₂a : t₂ * a * t₂⁻¹ = w := by rw [hadef]; exact hsq t₂ ht₂R ht₂sq w hwP
  have hta : t * a * t⁻¹ = a⁻¹ := by
    rw [hadef, h02 w hwP, htw]; group
  have hu₂ : Ev Z t₂ (w * a) true := by
    show t₂ * (w * a) * t₂⁻¹ * (w * a)⁻¹ ∈ Z
    have e : t₂ * (w * a) * t₂⁻¹ * (w * a)⁻¹ = ⁅a, w⁆ := by
      calc t₂ * (w * a) * t₂⁻¹ * (w * a)⁻¹
          = (t₂ * w * t₂⁻¹) * (t₂ * a * t₂⁻¹) * (w * a)⁻¹ := by group
        _ = a * w * (w * a)⁻¹ := by rw [ht₂a, ← hadef]
        _ = ⁅a, w⁆ := by rw [commutatorElement_def]; group
    rw [e]
    exact hcommZ a haP w hwP
  have hu₀ : Ev Z t (w * a) false := by
    show t * (w * a) * t⁻¹ * (w * a) ∈ Z
    have e : t * (w * a) * t⁻¹ * (w * a) = ⁅w⁻¹, a⁻¹⁆ := by
      calc t * (w * a) * t⁻¹ * (w * a) = (t * w * t⁻¹) * (t * a * t⁻¹) * (w * a) := by group
        _ = w⁻¹ * a⁻¹ * (w * a) := by rw [htw, hta]
        _ = ⁅w⁻¹, a⁻¹⁆ := by rw [commutatorElement_def]; group
    rw [e]
    exact hcommZ _ (inv_mem hwP) _ (inv_mem haP)
  have hv₂ : Ev Z t₂ (w * a⁻¹) false := by
    show t₂ * (w * a⁻¹) * t₂⁻¹ * (w * a⁻¹) ∈ Z
    have e : t₂ * (w * a⁻¹) * t₂⁻¹ * (w * a⁻¹) = 1 := by
      calc t₂ * (w * a⁻¹) * t₂⁻¹ * (w * a⁻¹)
          = (t₂ * w * t₂⁻¹) * (t₂ * a * t₂⁻¹)⁻¹ * (w * a⁻¹) := by group
        _ = a * w⁻¹ * (w * a⁻¹) := by rw [ht₂a, ← hadef]
        _ = 1 := by group
    rw [e]
    exact one_mem _
  have hv₀ : Ev Z t (w * a⁻¹) false := by
    show t * (w * a⁻¹) * t⁻¹ * (w * a⁻¹) ∈ Z
    have e : t * (w * a⁻¹) * t⁻¹ * (w * a⁻¹) = ⁅w⁻¹, a⁆ := by
      calc t * (w * a⁻¹) * t⁻¹ * (w * a⁻¹)
          = (t * w * t⁻¹) * (t * a * t⁻¹)⁻¹ * (w * a⁻¹) := by group
        _ = w⁻¹ * a * (w * a⁻¹) := by rw [htw, hta, inv_inv]
        _ = ⁅w⁻¹, a⁆ := by rw [commutatorElement_def]; group
    rw [e]
    exact hcommZ _ (inv_mem hwP) _ haP
  have hnotboth : w * a ∉ Z ∨ w * a⁻¹ ∉ Z := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hu, hv⟩ := hcon
    have haa : a * a ∈ Z := by
      have e : a * a = (w * a⁻¹)⁻¹ * (w * a) := by group
      rw [e]
      exact mul_mem (inv_mem hv) hu
    have haZ : a ∈ Z := mem_of_mul_self_mem (hexp a haP) haa
    apply hyZ
    have h := (mem_normalizer_iff.mp (hRZ _ (inv_mem ht₂R)) a).mp haZ
    have e : t₂⁻¹ * a * t₂⁻¹⁻¹ = w := by
      rw [hadef]; group
    rwa [e] at h
  obtain ⟨x, s, hxP, hxZ, hxt, hxt₂⟩ : ∃ (x : K) (s : Bool), x ∈ P ∧ x ∉ Z ∧ Ev Z t x false ∧
      Ev Z t₂ x s := by
    rcases hnotboth with h | h
    · exact ⟨w * a, true, mul_mem hwP haP, h, hu₀, hu₂⟩
    · exact ⟨w * a⁻¹, false, mul_mem hwP (inv_mem haP), h, hv₀, hv₂⟩
  have hxt₃ : Ev Z t₃ x (false == s) := ev_comp hZC hxP (hRZ t₂ ht₂R) (h3 x hxP) hxt hxt₂
  obtain ⟨x₂, hx₂def⟩ : ∃ x₂, x₂ = c * x * c⁻¹ := ⟨_, rfl⟩
  obtain ⟨x₃, hx₃def⟩ : ∃ x₃, x₃ = c * x₂ * c⁻¹ := ⟨_, rfl⟩
  have hx₂P : x₂ ∈ P := by rw [hx₂def]; exact hconjP c hcP x hxP
  have hx₃P : x₃ ∈ P := by rw [hx₃def]; exact hconjP c hcP x₂ hx₂P
  have hcx₃ : c * x₃ * c⁻¹ = x := by
    rw [hx₃def, hx₂def]
    calc c * (c * (c * x * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * x * (c * c * c)⁻¹ := by group
      _ = x := by rw [hccc]; group
  have hx₂t : Ev Z t x₂ (false == s) := hx₂def ▸ hT x _ hxt₃
  have hx₂t₂ : Ev Z t₂ x₂ false := hx₂def ▸ hT₂ x _ hxt
  have hx₂t₃ : Ev Z t₃ x₂ s := hx₂def ▸ hT₃ x _ hxt₂
  have hx₃t : Ev Z t x₃ s := hx₃def ▸ hT x₂ _ hx₂t₃
  have hx₃t₂ : Ev Z t₂ x₃ (false == s) := hx₃def ▸ hT₂ x₂ _ hx₂t
  have hx₃t₃ : Ev Z t₃ x₃ false := hx₃def ▸ hT₃ x₂ _ hx₂t₂
  have hfb : (false == s) = !s := by cases s <;> rfl
  rw [hfb] at hxt₃ hx₂t hx₃t₂
  have c23 : x₂ * x₃ = x₃ * x₂ :=
    (commute_of_ev hexp hZC hZP hx₃P hx₂P hcen (htcR t htR) hx₃t hx₂t).symm
  have c13 : x * x₃ = x₃ * x :=
    commute_of_ev hexp hZC hZP hxP hx₃P hcen (htcR t₂ ht₂R) hxt₂ hx₃t₂
  have c12 : x * x₂ = x₂ * x := by
    cases s
    · exact commute_of_ev (s := false) hexp hZC hZP hxP hx₂P hcen (htcR t htR) hxt hx₂t
    · exact commute_of_ev (s := true) hexp hZC hZP hxP hx₂P hcen (htcR t₂ ht₂R) hxt₂ hx₂t₂
  set M := closure ({x, x₂, x₃} : Set K) ⊔ Z with hMdef
  have hSP : ({x, x₂, x₃} : Set K) ⊆ P := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact hxP
    · exact hx₂P
    · exact hx₃P
  have hMP : M ≤ P := sup_le ((closure_le _).mpr hSP) hZP
  have hgen : ∀ y ∈ ({x, x₂, x₃} : Set K), y ∈ M := fun y hy => mem_sup_left (subset_closure hy)
  have hnormT : ∀ g ∈ R, ∀ sx s₂ s₃ : Bool, Ev Z g x sx → Ev Z g x₂ s₂ → Ev Z g x₃ s₃ →
      g ∈ normalizer (M : Set K) := by
    intro g hg sx s₂ s₃ h1 h2 h3'
    refine mem_normalizer_closure_sup ?_ (hRZ g hg)
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact ev_mem h1 (hgen _ (by simp)) le_sup_right
    · exact ev_mem h2 (hgen _ (by simp)) le_sup_right
    · exact ev_mem h3' (hgen _ (by simp)) le_sup_right
  have hRM : R ≤ normalizer (M : Set K) := by
    have hle : closure ({t, t₂, t₃} : Set K) ⊔ K₁ ≤ normalizer (M : Set K) := by
      refine sup_le ((closure_le _).mpr ?_) fun k hk => ?_
      · intro r hr
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
        rcases hr with rfl | rfl | rfl
        · exact hnormT _ htR _ _ _ hxt hx₂t hx₃t
        · exact hnormT _ ht₂R _ _ _ hxt₂ hx₂t₂ hx₃t₂
        · exact hnormT _ ht₃R _ _ _ hxt₃ hx₂t₃ hx₃t₃
      · refine mem_normalizer_of_conj_mem fun m hm => ?_
        rw [hK₁act k hk m (hMP hm)]
        exact hm
    rw [hRgen]
    exact hle
  have hcM : c ∈ normalizer (M : Set K) := by
    refine mem_normalizer_closure_sup ?_ hcZ
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · rw [← hx₂def]; exact hgen _ (by simp)
    · rw [← hx₃def]; exact hgen _ (by simp)
    · rw [hcx₃]; exact hgen _ (by simp)
  have hMR : ⁅M, R⁆ ≠ ⊥ := by
    intro h
    have hxR : x ∈ centralizer (R : Set K) :=
      commutator_eq_bot_iff_le_centralizer.mp h (hgen x (by simp))
    have htx : t * x = x * t := mem_centralizer_iff.mp hxR t htR
    apply hxZ
    refine mem_of_mul_self_mem (hexp x hxP) ?_
    have h' : t * x * t⁻¹ * x ∈ Z := hxt
    rwa [htx, mul_inv_cancel_right] at h'
  have hMeq : M = P := by
    by_contra hne
    exact hMR (hmin M hMP hne hRM hcM)
  have hab : M ≤ centralizer (M : Set K) := by
    refine sup_le_centralizer_self hSP hZC hZP ?_
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · rfl
    · exact c12
    · exact c13
    · exact c12.symm
    · rfl
    · exact c23
    · exact c13.symm
    · exact c23.symm
    · rfl
  apply hnab
  rw [hMeq] at hab
  exact hab

theorem mem_normalizer_centralizer [Finite K] {P : Subgroup K} {g : K}
    (hg : g ∈ normalizer (P : Set K)) :
    g ∈ normalizer ((centralizer (P : Set K) : Subgroup K) : Set K) := by
  refine mem_normalizer_of_conj_mem fun z hz => ?_
  rw [mem_centralizer_iff]
  intro p hp
  have hp' : g⁻¹ * p * g ∈ P := by
    have := (mem_normalizer_iff.mp (inv_mem hg) p).mp hp
    simpa using this
  have h := mem_centralizer_iff.mp hz _ hp'
  calc p * (g * z * g⁻¹) = g * ((g⁻¹ * p * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * p * g)) * g⁻¹ := by rw [h]
    _ = g * z * g⁻¹ * p := by group

theorem mem_normalizer_inf [Finite K] {H₁ H₂ : Subgroup K} {g : K}
    (h₁ : g ∈ normalizer (H₁ : Set K)) (h₂ : g ∈ normalizer (H₂ : Set K)) :
    g ∈ normalizer ((H₁ ⊓ H₂ : Subgroup K) : Set K) :=
  mem_normalizer_of_conj_mem fun x hx => Subgroup.mem_inf.mpr
    ⟨(mem_normalizer_iff.mp h₁ x).mp hx.1, (mem_normalizer_iff.mp h₂ x).mp hx.2⟩

theorem commutator_ne_self [Finite K] {P : Subgroup K} (hP : IsPGroup 3 P) (hP1 : P ≠ ⊥) :
    ⁅P, P⁆ ≠ P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hnil
  have htop : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = ⊤ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, h]
  have hall : ∀ k, (⊤ : Subgroup P).lowerCentralSeries k = ⊤ := by
    intro k
    induction k with
    | zero => exact Subgroup.lowerCentralSeries_zero _
    | succ k ih => rw [Subgroup.lowerCentralSeries_succ, ih, htop]
  rw [hall n] at hn
  apply hP1
  rw [← Subgroup.range_subtype P, MonoidHom.range_eq_map, hn, Subgroup.map_bot]

theorem false_of_abelian [Finite K] {P R : Subgroup K} {c : K} (hc3 : c ^ 3 = 1)
    (hexp : ∀ x ∈ P, x ^ 3 = 1) (hR : IsPGroup 2 R) (hRP : R ≤ normalizer (P : Set K))
    (hcP : c ∈ normalizer (P : Set K))
    (hfix : ∀ x ∈ P, x * c = c * x → ∀ r ∈ R, x * r = r * x)
    (hPR : ⁅P, R⁆ = P) (hP1 : P ≠ ⊥) (hab : P ≤ centralizer (P : Set K)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP3 : IsPGroup 3 P := isPGroup_three_of_exp hexp
  have hcop : (Nat.card R).Coprime (Nat.card P) := by
    obtain ⟨a, ha⟩ := hR.exists_card_eq
    obtain ⟨b, hb⟩ := hP3.exists_card_eq
    rw [ha, hb]
    exact Nat.Coprime.pow a b (by norm_num)
  have hbot := CFSG.RankThree.Coprime.commutator_inf_centralizer_eq_bot (B := R) (K := P)
    (fun x hx y hy => mem_centralizer_iff.mp (hab hy) x hx) hRP hcop
  rw [commutator_comm, hPR] at hbot
  set B := zpowers c with hBdef
  have hBP : B ≤ normalizer (P : Set K) := zpowers_le.mpr hcP
  let φ : B →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hBP)
  have hφ : ∀ (g : B) (x : P), ((φ g x : P) : K) = (g : K) * x * (g : K)⁻¹ := fun _ _ => rfl
  let _ : MulAction B P := MulAction.compHom P φ
  have hdvd : 3 ∣ Nat.card P := by
    obtain ⟨k, hk⟩ := hP3.exists_card_eq
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · exfalso
      apply hP1
      rw [← Subgroup.card_eq_one, hk, h0, pow_zero]
    · rw [hk]
      exact dvd_pow_self 3 hpos.ne'
  have h1 : (1 : P) ∈ MulAction.fixedPoints B P := fun g => by
    show φ g 1 = 1
    exact map_one _
  obtain ⟨b, hb, hb1⟩ :=
    (isPGroup_zpowers_three hc3).exists_fixed_point_of_prime_dvd_card_of_fixed_point P hdvd h1
  have hcb : c * (b : K) * c⁻¹ = b := by
    have h := congrArg Subtype.val (hb ⟨c, mem_zpowers c⟩)
    change ((φ ⟨c, mem_zpowers c⟩ b : P) : K) = b at h
    rwa [hφ] at h
  have hbc : (b : K) * c = c * b := by
    calc (b : K) * c = c * b * c⁻¹ * c := by rw [hcb]
      _ = c * b := by group
  have hbR : (b : K) ∈ P ⊓ centralizer (R : Set K) := by
    refine Subgroup.mem_inf.mpr ⟨b.2, mem_centralizer_iff.mpr fun r hr => ?_⟩
    exact (hfix b b.2 hbc r hr).symm
  rw [hbot, Subgroup.mem_bot] at hbR
  exact hb1 (Subtype.ext hbR).symm

theorem commutator_eq_bot_of_fix [Finite K] {c : K} (hc3 : c ^ 3 = 1) (R P : Subgroup K)
    (hexp : ∀ x ∈ P, x ^ 3 = 1) (hR : IsPGroup 2 R) (hRP : R ≤ normalizer (P : Set K))
    (hcP : c ∈ normalizer (P : Set K)) (hcR : c ∈ normalizer (R : Set K))
    (hgen : ⁅R, zpowers c⁆ = R) (hfix : ∀ x ∈ P, x * c = c * x → ∀ r ∈ R, x * r = r * x) :
    ⁅P, R⁆ = ⊥ := by
  suffices h : ∀ n : ℕ, ∀ R : Subgroup K, Nat.card R = n → ∀ m : ℕ, ∀ P : Subgroup K,
      Nat.card P = m → (∀ x ∈ P, x ^ 3 = 1) → IsPGroup 2 R → R ≤ normalizer (P : Set K) →
      c ∈ normalizer (P : Set K) → c ∈ normalizer (R : Set K) → ⁅R, zpowers c⁆ = R →
      (∀ x ∈ P, x * c = c * x → ∀ r ∈ R, x * r = r * x) → ⁅P, R⁆ = ⊥ from
    h _ R rfl _ P rfl hexp hR hRP hcP hcR hgen hfix
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihR =>
  intro R hRn m
  induction m using Nat.strong_induction_on with
  | _ m ihP =>
  intro P hPm hexp hR hRP hcP hcR hgen hfix
  by_contra hne
  have hP3 : IsPGroup 3 P := isPGroup_three_of_exp hexp
  have hP2 : ¬ 2 ∣ Nat.card P := not_two_dvd_of_three hP3
  have hminR : ∀ R' : Subgroup K, R' ≤ R → R' ≠ R → c ∈ normalizer (R' : Set K) →
      ⁅R', zpowers c⁆ = R' → R' ≤ R ⊓ centralizer (P : Set K) := by
    intro R' hR'R hne' hcR' hgen'
    have hlt : Nat.card R' < n := hRn ▸ card_lt_of_lt (lt_of_le_of_ne hR'R hne')
    have h := ihR _ hlt R' rfl _ P rfl hexp (hR.to_le hR'R) (hR'R.trans hRP) hcP hcR' hgen'
      (fun x hx hxc r hr => hfix x hx hxc r (hR'R hr))
    rw [commutator_comm, commutator_eq_bot_iff_le_centralizer] at h
    exact le_inf hR'R h
  have hminP : ∀ M : Subgroup K, M ≤ P → M ≠ P → R ≤ normalizer (M : Set K) →
      c ∈ normalizer (M : Set K) → ⁅M, R⁆ = ⊥ := by
    intro M hMP hneM hRM hcM
    have hlt : Nat.card M < m := hPm ▸ card_lt_of_lt (lt_of_le_of_ne hMP hneM)
    exact ihP _ hlt M rfl (fun x hx => hexp x (hMP hx)) hR hRM hcM hcR hgen
      (fun x hx hxc r hr => hfix x (hMP hx) hxc r hr)
  have hPRle : ⁅P, R⁆ ≤ P := le_normalizer_iff_commutator_le_left.mp hRP
  have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 2
    Nat.prime_two R P hR hP2 hRP
  have hPR : ⁅P, R⁆ = P := by
    by_contra hneP
    apply hne
    rw [← hidem]
    exact hminP _ hPRle hneP (le_normalizer_commutator hRP le_normalizer)
      (mem_normalizer_commutator hcP hcR)
  have hP1 : P ≠ ⊥ := by
    intro h
    apply hne
    rw [h, Subgroup.commutator_bot_left]
  have hK₁R : R ⊓ centralizer (P : Set K) ≤ R := inf_le_left
  have hRK₁ : R ≤ normalizer ((R ⊓ centralizer (P : Set K) : Subgroup K) : Set K) :=
    fun r hr => mem_normalizer_inf (le_normalizer hr) (mem_normalizer_centralizer (hRP hr))
  have hcK₁ : c ∈ normalizer ((R ⊓ centralizer (P : Set K) : Subgroup K) : Set K) :=
    mem_normalizer_inf hcR (mem_normalizer_centralizer hcP)
  have hne₁ : R ⊓ centralizer (P : Set K) ≠ R := by
    intro h
    apply hne
    rw [commutator_comm, commutator_eq_bot_iff_le_centralizer]
    exact h ▸ inf_le_right
  have hCc : R ⊓ centralizer ({c} : Set K) ≤ R ⊓ centralizer (P : Set K) := by
    have h := centralizer_le_of_thompson (Q := R ⊓ centralizer ({c} : Set K)) hP3
      (fun h3 => not_three_dvd_of_two hR (h3.trans (Subgroup.card_dvd_of_le inf_le_left)))
      hc3 (inf_le_left.trans hRP) hcP
      (fun q hq => mem_centralizer_singleton_iff.mp hq.2)
      (fun x hx hxc q hq => (hfix x hx hxc q hq.1).symm)
    intro q hq
    exact Subgroup.mem_inf.mpr ⟨hq.1, mem_centralizer_iff.mpr fun x hx => (h q hq x hx).symm⟩
  have hdich : ∀ M : Subgroup K, R ⊓ centralizer (P : Set K) ≤ M → M ≤ R →
      c ∈ normalizer (M : Set K) → M = R ⊓ centralizer (P : Set K) ∨ M = R :=
    fun M h1 h2 h3 => dichotomy hc3 hR hminR hCc h1 h2 h3
  have hgen' : ¬ ⁅R, zpowers c⁆ ≤ R ⊓ centralizer (P : Set K) := by
    rw [hgen]
    intro h
    exact hne₁ (le_antisymm hK₁R h)
  obtain ⟨t, htR, ht2, htc, hN, hRgen⟩ :=
    exists_four_group hc3 hR hK₁R hRK₁ hne₁ hcR hcK₁ hdich hgen'
  by_cases hab : P ≤ centralizer (P : Set K)
  · exact false_of_abelian hc3 hexp hR hRP hcP hfix hPR hP1 hab
  ·
    have hP'P : ⁅P, P⁆ ≤ P := le_normalizer_iff_commutator_le_left.mp le_normalizer
    have hP'R : ⁅P, P⁆ ≤ centralizer (R : Set K) := by
      have h := hminP _ hP'P (commutator_ne_self hP3 hP1) (le_normalizer_commutator hRP hRP)
        (mem_normalizer_commutator hcP hcP)
      exact commutator_eq_bot_iff_le_centralizer.mp h
    have hP'Z : ⁅P, P⁆ ≤ centralizer (P : Set K) := by
      have h3 : ⁅⁅P, R⁆, ⁅P, P⁆⁆ = ⊥ := by
        refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
        · have h0 : ⁅R, ⁅P, P⁆⁆ = ⊥ := by
            rw [commutator_comm, commutator_eq_bot_iff_le_centralizer]
            exact hP'R
          rw [h0, Subgroup.commutator_bot_left]
        · refine le_bot_iff.mp ((Subgroup.commutator_mono
            (le_normalizer_iff_commutator_le_left.mp (le_normalizer_commutator le_normalizer
              le_normalizer)) le_rfl).trans ?_)
          rw [commutator_eq_bot_iff_le_centralizer.mpr hP'R]
      rw [hPR, commutator_comm, commutator_eq_bot_iff_le_centralizer] at h3
      exact h3
    exact false_of_nonabelian hc3 hexp hRP hcP inf_le_right hcK₁ htR hcR ht2 htc hN hRgen hPR
      hP'R hP'Z hminP hab

end CFSG.RankThree.PartTwo.Sec14.Proof1418Res3
