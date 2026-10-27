module

public import CFSG.RankThree.PartTwo.KFacts.K71SU3Normal

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut)
open Matrix

section Group

theorem eq_one_of_pow_three_pow_eq_one {M : Type*} [Group M] {N : Subgroup M}
    (hN : ¬ 3 ∣ Nat.card N) {ν : M} (hν : ν ∈ N) {k : ℕ} (hk : ν ^ 3 ^ k = 1) : ν = 1 := by
  have h1 : orderOf ν ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf ν ∣ Nat.card N := by
    rw [show orderOf ν = orderOf (⟨ν, hν⟩ : N) from Subgroup.orderOf_coe ⟨ν, hν⟩]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (3 ^ k) (Nat.card N) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN)
  have h3 : orderOf ν ∣ 1 := by
    rw [← Nat.Coprime.gcd_eq_one hcop]
    exact Nat.dvd_gcd h1 h2
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

variable {S : Type*} [Group S]

theorem mul_conj_mul_inv (φ : MulAut S) (x : S) :
    φ * MulAut.conj x * φ⁻¹ = MulAut.conj (φ x) := by
  ext g
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  rw [show φ (φ⁻¹ g) = g from MulEquiv.apply_symm_apply φ g]

theorem conj_mul_inv_apply_mem {N : Subgroup (MulAut S)} {ν : MulAut S} (hν : ν ∈ N) {ℓ : S}
    (hℓ : ∀ μ ∈ N, MulAut.conj ℓ * μ * (MulAut.conj ℓ)⁻¹ ∈ N) :
    MulAut.conj (ℓ * (ν ℓ)⁻¹) ∈ N := by
  have h1 := mul_mem (hℓ ν hν) (inv_mem hν)
  have h2 : MulAut.conj ℓ * ν * (MulAut.conj ℓ)⁻¹ * ν⁻¹ = MulAut.conj (ℓ * (ν ℓ)⁻¹) := by
    rw [map_mul, map_inv, ← mul_conj_mul_inv ν ℓ]
    group
  rwa [h2] at h1

theorem apply_apply_eq_of_commute {ν ε : MulAut S} (hνε : ν * ε = ε * ν) {ℓ : S}
    (hℓ : ε ℓ = ℓ) : ε (ν ℓ) = ν ℓ := by
  rw [← MulAut.mul_apply, ← hνε, MulAut.mul_apply, hℓ]

theorem eq_bot_of_conj {ε ε₀ φ : MulAut S} (hε : ε = φ * ε₀ * φ⁻¹)
    (H : ∀ N₀ : Subgroup (MulAut S), (∀ ν ∈ N₀, ν * ε₀ = ε₀ * ν) → ¬ 3 ∣ Nat.card N₀ →
      (∀ ℓ, ε₀ ℓ = ℓ → ∀ ν ∈ N₀, MulAut.conj ℓ * ν * (MulAut.conj ℓ)⁻¹ ∈ N₀) → N₀ = ⊥)
    {N : Subgroup (MulAut S)} (hNc : ∀ ν ∈ N, ν * ε = ε * ν) (hN3 : ¬ 3 ∣ Nat.card N)
    (hNn : ∀ ℓ, ε ℓ = ℓ → ∀ ν ∈ N, MulAut.conj ℓ * ν * (MulAut.conj ℓ)⁻¹ ∈ N) : N = ⊥ := by
  set ψ : MulAut S →* MulAut S := (MulAut.conj φ⁻¹).toMonoidHom with hψ
  have hψa : ∀ ν, ψ ν = φ⁻¹ * ν * φ := fun ν => by
    rw [hψ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hψinj : Function.Injective ψ := (MulAut.conj φ⁻¹).injective
  have h0 : N.map ψ = ⊥ := by
    refine H _ ?_ ?_ ?_
    · rintro _ ⟨ν, hν, rfl⟩
      have h1 := hNc ν hν
      rw [hε] at h1
      rw [hψa]
      calc φ⁻¹ * ν * φ * ε₀ = φ⁻¹ * (ν * (φ * ε₀ * φ⁻¹)) * φ := by group
        _ = φ⁻¹ * ((φ * ε₀ * φ⁻¹) * ν) * φ := by rw [h1]
        _ = ε₀ * (φ⁻¹ * ν * φ) := by group
    · rwa [Subgroup.card_map_of_injective hψinj]
    · rintro ℓ hℓ _ ⟨ν, hν, rfl⟩
      have hφℓ : ε (φ ℓ) = φ ℓ := by
        rw [hε, MulAut.mul_apply, MulAut.mul_apply,
          show φ⁻¹ (φ ℓ) = ℓ from MulEquiv.symm_apply_apply φ ℓ, hℓ]
      refine ⟨MulAut.conj (φ ℓ) * ν * (MulAut.conj (φ ℓ))⁻¹, hNn _ hφℓ ν hν, ?_⟩
      rw [hψa, hψa, ← mul_conj_mul_inv φ ℓ]
      group
  rw [eq_bot_iff]
  intro ν hν
  have h1 : ψ ν ∈ N.map ψ := ⟨ν, hν, rfl⟩
  rw [h0, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact hψinj (h1.trans (map_one ψ).symm)

theorem eq_bot_of_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {ε : MulAut X}
    (H : ∀ N₀ : Subgroup (MulAut Y),
      (∀ ν ∈ N₀, ν * MulAut.congr e ε = MulAut.congr e ε * ν) → ¬ 3 ∣ Nat.card N₀ →
      (∀ ℓ, MulAut.congr e ε ℓ = ℓ → ∀ ν ∈ N₀, MulAut.conj ℓ * ν * (MulAut.conj ℓ)⁻¹ ∈ N₀) →
      N₀ = ⊥)
    {N : Subgroup (MulAut X)} (hNc : ∀ ν ∈ N, ν * ε = ε * ν) (hN3 : ¬ 3 ∣ Nat.card N)
    (hNn : ∀ ℓ, ε ℓ = ℓ → ∀ ν ∈ N, MulAut.conj ℓ * ν * (MulAut.conj ℓ)⁻¹ ∈ N) : N = ⊥ := by
  set ψ : MulAut X →* MulAut Y := (MulAut.congr e).toMonoidHom with hψ
  have hψa : ∀ ν, ψ ν = MulAut.congr e ν := fun ν => rfl
  have hψinj : Function.Injective ψ := (MulAut.congr e).injective
  have hcj : ∀ ℓ : X, ψ (MulAut.conj ℓ) = MulAut.conj (e ℓ) := fun ℓ => by
    ext y
    rw [hψa]
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
  have h0 : N.map ψ = ⊥ := by
    refine H _ ?_ ?_ ?_
    · rintro _ ⟨ν, hν, rfl⟩
      rw [← hψa, ← map_mul, ← map_mul, hNc ν hν]
    · rwa [Subgroup.card_map_of_injective hψinj]
    · rintro ℓ hℓ _ ⟨ν, hν, rfl⟩
      have hℓ' : ε (e.symm ℓ) = e.symm ℓ := by
        have h1 := congrArg e.symm hℓ
        rwa [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
          MulEquiv.symm_apply_apply] at h1
      refine ⟨MulAut.conj (e.symm ℓ) * ν * (MulAut.conj (e.symm ℓ))⁻¹, hNn _ hℓ' ν hν, ?_⟩
      rw [map_mul, map_mul, map_inv, hcj, MulEquiv.apply_symm_apply]
  rw [eq_bot_iff]
  intro ν hν
  have h1 : ψ ν ∈ N.map ψ := ⟨ν, hν, rfl⟩
  rw [h0, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact hψinj (h1.trans (map_one ψ).symm)

end Group

section SU

variable {p f : ℕ} {K : Type} [Field K]

theorem exists_suConj_mul_suField (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    (β : MulAut (unitarySU p f K 3)) :
    ∃ (B : unitaryIsom3 h) (δ : K ≃+* K), β = suConj h B * suField h δ := by
  obtain ⟨B, δ, hBδ⟩ := exists_psuConj_mul_psuField hq (suDescend h hq β)
  refine ⟨B, δ, eq_of_suDescend_eq h hq ?_⟩
  rw [hBδ, map_mul, suDescend_suConj, suDescend_suField]

theorem exists_psuConj_mul_psuField_pow (h : UnitaryFieldData p f K) (B : unitaryIsom3 h)
    (δ : K ≃+* K) (n : ℕ) : ∃ B' : unitaryIsom3 h,
      (psuConj h B * psuField h δ) ^ n = psuConj h B' * psuField h (δ ^ n) := by
  induction n with
  | zero => exact ⟨1, by rw [pow_zero, pow_zero, map_one, map_one, mul_one]⟩
  | succ n ih =>
    obtain ⟨B', hB'⟩ := ih
    refine ⟨B' * ⟨glAut (δ ^ n) B, glAut_mem_unitaryIsom3 (δ ^ n) B.2⟩, ?_⟩
    rw [pow_succ, hB', psuConj_mul_psuField_mul, ← pow_succ]

theorem pow_eq_one_of_suConj_mul_suField_pow_eq_one (h : UnitaryFieldData p f K)
    (hq : 2 < p ^ f) {B : unitaryIsom3 h} {δ : K ≃+* K} {n : ℕ}
    (hn : (suConj h B * suField h δ) ^ n = 1) : δ ^ n = 1 := by
  have h1 := congrArg (suDescend h hq) hn
  rw [map_pow, map_mul, suDescend_suConj, suDescend_suField, map_one] at h1
  obtain ⟨B', hB'⟩ := exists_psuConj_mul_psuField_pow h B δ n
  rw [hB'] at h1
  exact (eq_one_of_psuConj_mul_psuField_eq_one B' (δ ^ n) h1).1

theorem exists_scalar_of_conj_eq_one (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    {z : unitarySU p f K 3} (hz : MulAut.conj z = 1) :
    ∃ c : Kˣ, c ^ 3 = 1 ∧ (z : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) c := by
  have hzc : z ∈ Subgroup.center (unitarySU p f K 3) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := DFunLike.congr_fun hz g
    rw [MulAut.conj_apply, MulAut.one_apply] at h1
    calc g * z = z * g * z⁻¹ * z := by rw [h1]
      _ = z * g := by group
  rw [center_unitarySU_three (h := h) hq] at hzc
  obtain ⟨c, -, hc3, hzc'⟩ := mem_unitaryScalars.mp hzc
  exact ⟨c, hc3, hzc'⟩

end SU

section F64

variable {K : Type} [Field K]

theorem sq_eq_one_of_pow_eq_one (h : UnitaryFieldData 2 3 K) {δ : K ≃+* K} {n : ℕ}
    (hn : ¬ 3 ∣ n) (hδ : δ ^ n = 1) : δ ^ 2 = 1 := by
  have := h.finite
  have h6 : Nat.card (K ≃+* K) = 6 := (card_ringAut_and_isCyclic h.prime K h.card).1
  have hδ6 : δ ^ 6 = 1 := by rw [← h6]; exact pow_card_eq_one'
  have hg : δ ^ Nat.gcd n 6 = 1 := pow_gcd_eq_one.mpr ⟨hδ, hδ6⟩
  obtain ⟨g, hgdef⟩ : ∃ g, g = Nat.gcd n 6 := ⟨_, rfl⟩
  have hd6 : g ∣ 6 := hgdef ▸ Nat.gcd_dvd_right n 6
  have hdn : g ∣ n := hgdef ▸ Nat.gcd_dvd_left n 6
  rw [← hgdef] at hg
  have h2 : g ∣ 2 := by
    have hle : g ≤ 6 := Nat.le_of_dvd (by norm_num) hd6
    interval_cases g
    · norm_num at hd6
    · norm_num
    · norm_num
    · exact absurd hdn hn
    · norm_num at hd6
    · norm_num at hd6
    · exact absurd (dvd_trans (by norm_num : 3 ∣ 6) hdn) hn
  obtain ⟨k, hk⟩ := h2
  rw [hk, pow_mul, hg, one_pow]

theorem eq_one_or_apply_eq_pow_of_sq_eq_one (h : UnitaryFieldData 2 3 K) {δ : K ≃+* K}
    (hδ : δ ^ 2 = 1) : δ = 1 ∨ ∀ x, δ x = x ^ 2 ^ 3 := by
  classical
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := h.charP
  have := Fintype.ofFinite (K ≃+* K)
  have hcyc : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic h.prime K h.card).2
  set β : K ≃+* K := iterateFrobeniusEquiv K 2 3 with hβ
  have hβa : ∀ x, β x = x ^ 2 ^ 3 := fun x => by
    rw [hβ, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  have hβ1 : β ≠ 1 := by
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    intro h1
    apply hc
    rw [h.bar_apply, ← hβa, h1]
    rfl
  have hβ2 : β ^ 2 = 1 := RingEquiv.ext fun x => by
    rw [pow_two]
    change β (β x) = x
    have := Fintype.ofFinite K
    have hc : Fintype.card K = 2 ^ 3 * 2 ^ 3 := by
      rw [← Nat.card_eq_fintype_card, h.card]
      norm_num
    rw [hβa, hβa, ← pow_mul, ← hc]
    exact FiniteField.pow_card x
  have hle : (Finset.univ.filter (fun x : K ≃+* K => x ^ 2 = 1)).card ≤ 2 :=
    IsCyclic.card_pow_eq_one_le (by norm_num)
  have hT : ({1, β} : Finset (K ≃+* K)) ⊆ Finset.univ.filter (fun x : K ≃+* K => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl
    · exact one_pow 2
    · exact hβ2
  have hTc : ({1, β} : Finset (K ≃+* K)).card = 2 := Finset.card_pair (Ne.symm hβ1)
  have heq := Finset.eq_of_subset_of_card_le hT (by rw [hTc]; exact hle)
  have hδS : δ ∈ Finset.univ.filter (fun x : K ≃+* K => x ^ 2 = 1) := by simp [hδ]
  rw [← heq] at hδS
  simp only [Finset.mem_insert, Finset.mem_singleton] at hδS
  rcases hδS with h1 | h1
  · exact Or.inl h1
  · exact Or.inr fun x => by rw [h1, hβa]

end F64

end CFSG.RankThree.PartTwo.KFacts
