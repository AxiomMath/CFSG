module

public import CFSG.LocalAnalysis.StandardType.GGTableBCoverMarked

public section

namespace CFSG.StandardType

theorem exists_pPart_generator_of_isCyclic {G : Type*} [Group G] [Finite G] [IsCyclic G] {p : ℕ}
    (hp : p.Prime) :
    ∃ σ₀ : G, (∃ c : ℕ, orderOf σ₀ = p ^ c) ∧
      ∀ σ : G, (∃ k : ℕ, σ ^ p ^ k = 1) → ∃ j : ℤ, σ = σ₀ ^ j := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have : Nonempty G := ⟨1⟩
  have horder_ne : orderOf g ≠ 0 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg]
    exact (Nat.card_pos (α := G)).ne'
  obtain ⟨c, m, hpm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd horder_ne p hp.ne_one
  have hm_ne : m ≠ 0 := by
    rintro rfl
    exact hpm (dvd_zero p)
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_ne
  have hm_dvd : m ∣ orderOf g := ⟨p ^ c, by rw [hn, mul_comm]⟩
  have horder_sigma0 : orderOf (g ^ m) = p ^ c := by
    rw [orderOf_pow_of_dvd hm_ne hm_dvd, hn]
    exact Nat.mul_div_left (p ^ c) hm_pos
  refine ⟨g ^ m, ⟨c, horder_sigma0⟩, ?_⟩
  intro σ hσ
  obtain ⟨k, hk⟩ := hσ
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hg σ)
  have hpow : g ^ (i * (p : ℤ) ^ k) = 1 := by
    rw [zpow_mul, hi, ← Nat.cast_pow, zpow_natCast]
    exact hk
  have hdiv : (orderOf g : ℤ) ∣ i * (p : ℤ) ^ k :=
    (orderOf_dvd_iff_zpow_eq_one (x := g) (i := i * (p : ℤ) ^ k)).2 hpow
  have hm_dvd_int : (m : ℤ) ∣ (orderOf g : ℤ) := by
    rw [hn, Nat.cast_mul, Nat.cast_pow]
    exact dvd_mul_left (m : ℤ) ((p : ℤ) ^ c)
  have hm_dvd_prod : (m : ℤ) ∣ i * (p : ℤ) ^ k := dvd_trans hm_dvd_int hdiv
  have hcopmp : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm).symm
  have hcop : Nat.Coprime m (p ^ k) := Nat.Coprime.pow_right k hcopmp
  have hiscop : IsCoprime (m : ℤ) ((p : ℤ) ^ k) := by
    simpa using hcop.isCoprime
  obtain ⟨j, hj⟩ := hiscop.dvd_of_dvd_mul_right hm_dvd_prod
  refine ⟨j, ?_⟩
  rw [← hi, hj, zpow_mul, zpow_natCast]

theorem exists_marked_of_quotient {R : Type} [Group R] {p : ℕ} {G : Type*} [Group G]
    (Θ : MulAut R →* G) {I F : Set (MulAut R)} (σ₀ : G) (hσ₀ : ∃ c : ℕ, orderOf σ₀ = p ^ c)
    (hgen : ∀ σ : G, (∃ k : ℕ, σ ^ p ^ k = 1) → ∃ j : ℤ, σ = σ₀ ^ j)
    (hlift : ∃ φ ∈ Subgroup.closure F, Θ φ = σ₀)
    (hinj : ∀ φ ∈ Subgroup.closure F, Θ φ = 1 → φ = 1)
    (hker : ∀ φ : MulAut R, Θ φ = 1 → φ ∈ I) :
    ∃ f : MulAut R, GGTableBFieldSylowMark p F f ∧ GGTableBMarkedFactorization p I f := by
  obtain ⟨φ₀, hφ₀mem, hφ₀⟩ := hlift
  obtain ⟨c, hc⟩ := hσ₀
  have horder : orderOf φ₀ = orderOf σ₀ := by
    rw [orderOf_eq_orderOf_iff]
    intro n
    constructor
    · intro hn
      have h : Θ (φ₀ ^ n) = 1 := by rw [hn, map_one]
      rwa [map_pow, hφ₀] at h
    · intro hn
      refine hinj (φ₀ ^ n) (Subgroup.pow_mem (Subgroup.closure F) hφ₀mem n) ?_
      rw [map_pow, hφ₀, hn]
  refine ⟨φ₀, ?_, ?_⟩
  · refine ⟨hφ₀mem, ⟨c, horder.trans hc⟩, ?_⟩
    intro g hgmem hg
    obtain ⟨k, hk⟩ := hg
    have hΘg : (Θ g) ^ p ^ k = 1 := by
      rw [← map_pow, hk, map_one]
    obtain ⟨j, hj⟩ := hgen (Θ g) ⟨k, hΘg⟩
    refine ⟨j, ?_⟩
    have hker_elem : Θ (g * (φ₀ ^ j)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_zpow, hφ₀, hj, mul_inv_cancel]
    have hmem : g * (φ₀ ^ j)⁻¹ ∈ Subgroup.closure F :=
      Subgroup.mul_mem (Subgroup.closure F) hgmem
        (Subgroup.inv_mem (Subgroup.closure F)
          (Subgroup.zpow_mem (Subgroup.closure F) hφ₀mem j))
    exact mul_inv_eq_one.1 (hinj _ hmem hker_elem)
  · intro a ha
    obtain ⟨k, hk⟩ := ha
    have hΘa : (Θ a) ^ p ^ k = 1 := by
      rw [← map_pow, hk, map_one]
    obtain ⟨j, hj⟩ := hgen (Θ a) ⟨k, hΘa⟩
    refine ⟨a * (φ₀ ^ j)⁻¹, ?_, j, ?_⟩
    · apply hker
      rw [map_mul, map_inv, map_zpow, hφ₀, hj, mul_inv_cancel]
    · rw [mul_assoc, inv_mul_cancel, mul_one]

end CFSG.StandardType
