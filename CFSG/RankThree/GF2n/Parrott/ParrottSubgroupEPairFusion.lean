module

public import CFSG.RankThree.GF2n.Parrott.CaseII
public import TauCeti.Algebra.Group.Subgroup.ZPowers

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K] {w : K}

omit [Finite K] in
private theorem H_commute_w {y : K} (hy : y ∈ H w) : y * w = w * y :=
  Subgroup.mem_centralizer_singleton_iff.mp hy

omit [Finite K] in
theorem relIndex_normalizer_inf_H_eq_21 {E K' : Subgroup K} (hEH : E ≤ H w)
    (hcard : Nat.card E = 2 ^ 9)
    (hrel : E.relIndex (Subgroup.normalizer (E : Set K) ⊓ H w) = 1920)
    (hEK' : E ≤ K') (hKi : K'.relIndex (Subgroup.normalizer (E : Set K)) = 2)
    (hKq : (E.subgroupOf K').Normal ∧ Nat.card (↥K' ⧸ E.subgroupOf K') = 20160 ∧
             ∀ L : Subgroup K, E ≤ L → L ≤ K' → L.relIndex K' ≠ 2) :
    (Subgroup.normalizer (E : Set K) ⊓ H w).relIndex (Subgroup.normalizer (E : Set K)) = 21 := by
  obtain ⟨hKN, hQcard, -⟩ := hKq
  have hK'N : K' ≤ Subgroup.normalizer (E : Set K) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have := hKN.conj_mem ⟨x, hEK' hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨k, hk⟩
      exact Subgroup.mem_subgroupOf.mp this
    · intro hx
      have h1 := hKN.conj_mem ⟨k * x * k⁻¹, hEK' hx⟩ (Subgroup.mem_subgroupOf.mpr hx)
        (⟨k, hk⟩⁻¹)
      have h2 := Subgroup.mem_subgroupOf.mp h1
      simpa [mul_assoc] using h2
  have hEM : E ≤ Subgroup.normalizer (E : Set K) ⊓ H w := le_inf Subgroup.le_normalizer hEH
  have hK'card : Nat.card K' = 20160 * 2 ^ 9 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (E.subgroupOf K')
    rw [hQcard, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK').toEquiv, hcard] at h1
    exact h1
  have hNcard : Nat.card (Subgroup.normalizer (E : Set K)) = 2 * (20160 * 2 ^ 9) := by
    have h1 := Subgroup.relIndex_mul_card K' (Subgroup.normalizer (E : Set K))
    rw [inf_eq_left.mpr hK'N, hKi, hK'card] at h1
    exact h1.symm
  have hMcard : Nat.card ↥(Subgroup.normalizer (E : Set K) ⊓ H w) = 1920 * 2 ^ 9 := by
    have h1 := Subgroup.relIndex_mul_card E (Subgroup.normalizer (E : Set K) ⊓ H w)
    rw [inf_eq_left.mpr hEM, hrel, hcard] at h1
    exact h1.symm
  have h2 := Subgroup.relIndex_mul_card (Subgroup.normalizer (E : Set K) ⊓ H w)
    (Subgroup.normalizer (E : Set K))
  rw [inf_eq_left.mpr (inf_le_left : Subgroup.normalizer (E : Set K) ⊓ H w ≤ _), hMcard,
    hNcard] at h2
  omega


theorem ncard_conj_orbit_le {E : Subgroup K}
    (h21 : (Subgroup.normalizer (E : Set K) ⊓ H w).relIndex
      (Subgroup.normalizer (E : Set K)) = 21) :
    Set.ncard {y : K | ∃ n ∈ Subgroup.normalizer (E : Set K), y = n * w * n⁻¹} ≤ 21 := by
  classical
  set N : Subgroup K := Subgroup.normalizer (E : Set K) with hN
  set M : Subgroup K := N ⊓ H w with hM
  let f : ↥N ⧸ M.subgroupOf N → K := Quotient.lift (fun n : ↥N => (n : K) * w * (n : K)⁻¹) (by
    intro a b hab
    have hab' : (a⁻¹ * b : ↥N) ∈ M.subgroupOf N := QuotientGroup.leftRel_apply.mp hab
    have hH : ((a : K)⁻¹ * (b : K)) ∈ H w := (Subgroup.mem_inf.mp hab').2
    have hc := H_commute_w hH
    show (a : K) * w * (a : K)⁻¹ = (b : K) * w * (b : K)⁻¹
    calc (a : K) * w * (a : K)⁻¹ = (a : K) * (w * ((a : K)⁻¹ * (b : K))) * (b : K)⁻¹ := by group
      _ = (a : K) * (((a : K)⁻¹ * (b : K)) * w) * (b : K)⁻¹ := by rw [← hc]
      _ = (b : K) * w * (b : K)⁻¹ := by group)
  have hsub : {y : K | ∃ n ∈ N, y = n * w * n⁻¹} ⊆ Set.range f := by
    rintro _ ⟨n, hn, rfl⟩
    exact ⟨(⟨n, hn⟩ : ↥N), rfl⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : (Set.range f).ncard ≤ Nat.card (↥N ⧸ M.subgroupOf N) := by
    rw [← Nat.card_coe_set_eq]
    exact Finite.card_range_le f
  have h3 : Nat.card (↥N ⧸ M.subgroupOf N) = 21 := by
    rw [← h21]
    rfl
  omega

theorem exists_t_j0_of_orbit (hw : orderOf w = 2) {E K' : Subgroup K} (hEH : E ≤ H w)
    (hJ : ∀ j ∈ J w, j ∉ Subgroup.zpowers w → ¬ IsConj w j)
    (hJN : J w ≤ Subgroup.normalizer (E : Set K))
    (hcard : Nat.card E = 2 ^ 9)
    (hrel : E.relIndex (Subgroup.normalizer (E : Set K) ⊓ H w) = 1920)
    (hJE : ∀ e ∈ E, e ∉ J w → ∃ j ∈ J w, j * e * j⁻¹ ≠ e ∧ j * e * j⁻¹ ≠ e * w)
    (horb : ∀ e ∈ E, e ∉ J w → 20 ≤ Set.ncard {y : K |
      ∃ m ∈ Subgroup.normalizer (E : Set K) ⊓ H w, y = m * e * m⁻¹})
    (hEK' : E ≤ K') (hKi : K'.relIndex (Subgroup.normalizer (E : Set K)) = 2)
    (hKq : (E.subgroupOf K').Normal ∧ Nat.card (↥K' ⧸ E.subgroupOf K') = 20160 ∧
             ∀ L : Subgroup K, E ≤ L → L ≤ K' → L.relIndex K' ≠ 2)
    (hfus : ∃ e ∈ E, e ≠ w ∧ ∃ n ∈ Subgroup.normalizer (E : Set K), n * w * n⁻¹ = e) :
    ∃ t j₀ : K, t ∈ E ∧ t ∉ J w ∧ orderOf t = 2 ∧ IsConj w t ∧
      j₀ ∈ J w ∧ j₀ ∉ Subgroup.zpowers w ∧ IsConj (t * w) j₀ := by
  classical
  have hw1 : w ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hw
    exact absurd hw (by decide)
  have hw2 : w * w = 1 := by
    have h1 := pow_orderOf_eq_one w
    rwa [hw, pow_two] at h1
  have h21 := relIndex_normalizer_inf_H_eq_21 hEH hcard hrel hEK' hKi hKq
  have hΩ := ncard_conj_orbit_le h21
  set N : Subgroup K := Subgroup.normalizer (E : Set K) with hN
  set M : Subgroup K := N ⊓ H w with hM
  obtain ⟨e, heE, hew, n₀, hn₀, hne⟩ := hfus
  have hc : IsConj w e := isConj_iff.mpr ⟨n₀, hne⟩
  have heJ : e ∉ J w := by
    intro heJ
    refine hJ e heJ (fun hmem => ?_) hc
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hw).mp hmem with h1 | h1
    · apply hw1
      have h2 : n₀ * w * n₀⁻¹ = 1 := hne.trans h1
      calc w = n₀⁻¹ * (n₀ * w * n₀⁻¹) * n₀ := by group
        _ = 1 := by rw [h2]; group
    · exact hew h1
  have he2 : orderOf e = 2 := hc.orderOf_eq.symm.trans hw
  have hee : e * e = 1 := by
    have h1 := pow_orderOf_eq_one e
    rwa [he2, pow_two] at h1
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
  have heH : e ∈ H w := hEH heE
  obtain ⟨j, hj, hj1, hj2⟩ := hJE e heE heJ
  set Ω : Set K := {y | ∃ n ∈ N, y = n * w * n⁻¹} with hΩdef
  set O : Set K := {y | ∃ m ∈ M, y = m * e * m⁻¹} with hOdef
  have hwΩ : w ∈ Ω := ⟨1, one_mem _, by group⟩
  have hOsub : O ⊆ Ω \ {w} := by
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨hmN, hmH⟩ := Subgroup.mem_inf.mp hm
    refine ⟨⟨m * n₀, mul_mem hmN hn₀, ?_⟩, ?_⟩
    · rw [← hne]
      group
    · intro hmw
      rw [Set.mem_singleton_iff] at hmw
      apply hew
      have h1 : m⁻¹ * w * m = w := by
        have := H_commute_w (inv_mem hmH)
        calc m⁻¹ * w * m = (w * m⁻¹) * m := by rw [← this]
          _ = w := by group
      calc e = m⁻¹ * (m * e * m⁻¹) * m := by group
        _ = m⁻¹ * w * m := by rw [hmw]
        _ = w := h1
  have hOcard : 20 ≤ O.ncard := horb e heE heJ
  have hΩ' : (Ω \ {w}).ncard ≤ 20 := by
    rw [Set.ncard_diff_singleton_of_mem hwΩ]
    omega
  have hOeq : O = Ω \ {w} :=
    Set.eq_of_subset_of_ncard_le hOsub (by omega) (Set.toFinite _)
  set t' : K := j * e * j⁻¹ with ht'
  have hv : n₀⁻¹ * t' * n₀ ∈ Ω \ {w} := by
    refine ⟨⟨n₀⁻¹ * j * n₀, mul_mem (mul_mem (inv_mem hn₀) (hJN hj)) hn₀, ?_⟩, ?_⟩
    · rw [ht', ← hne]
      group
    · intro hvw
      rw [Set.mem_singleton_iff] at hvw
      apply hj1
      show t' = e
      rw [← hne]
      calc t' = n₀ * (n₀⁻¹ * t' * n₀) * n₀⁻¹ := by group
        _ = n₀ * w * n₀⁻¹ := by rw [hvw]
  rw [← hOeq] at hv
  obtain ⟨m, hmM, hm⟩ := hv
  obtain ⟨hmN, hmH⟩ := Subgroup.mem_inf.mp hmM
  have hmw : m * w * m⁻¹ = w := by
    have := H_commute_w hmH
    calc m * w * m⁻¹ = (w * m) * m⁻¹ := by rw [this]
      _ = w := by group
  have ht'n : t' = (n₀ * m) * e * (n₀ * m)⁻¹ := by
    calc t' = n₀ * (n₀⁻¹ * t' * n₀) * n₀⁻¹ := by group
      _ = n₀ * (m * e * m⁻¹) * n₀⁻¹ := by rw [hm]
      _ = (n₀ * m) * e * (n₀ * m)⁻¹ := by group
  refine ⟨e, t' * e, heE, heJ, he2, hc, ?_, ?_, ?_⟩
  · have hJn : e * j⁻¹ * e⁻¹ ∈ J w := (mem_normalizer_iff.mp (J_le_normalizer_A heH) j⁻¹).mp
      (inv_mem hj)
    have : t' * e = j * (e * j⁻¹ * e⁻¹) := by
      rw [ht', hei]
      group
    rw [this]
    exact mul_mem hj hJn
  · intro hmem
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hw).mp hmem with h1 | h1
    · apply hj1
      show t' = e
      calc t' = (t' * e) * e⁻¹ := by group
        _ = e := by rw [h1, hei, one_mul]
    · apply hj2
      show t' = e * w
      calc t' = (t' * e) * e⁻¹ := by group
        _ = w * e := by rw [h1, hei]
        _ = e * w := (H_commute_w heH).symm
  · refine isConj_iff.mpr ⟨n₀ * m, ?_⟩
    calc (n₀ * m) * (e * w) * (n₀ * m)⁻¹
        = ((n₀ * m) * e * (n₀ * m)⁻¹) * (n₀ * (m * w * m⁻¹) * n₀⁻¹) := by group
      _ = t' * e := by rw [← ht'n, hmw, ← hne]

end CFSG.RankThree.GF2n.Parrott
