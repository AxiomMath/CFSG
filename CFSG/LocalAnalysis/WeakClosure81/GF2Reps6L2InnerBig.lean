module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L2CaseIIa
public import CFSG.GH74.Generic.BProg.B2.GenLocPsl2Full

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open Subgroup CFSG.GorensteinWalter CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

private lemma outerTorus_div_two_basic (q : ℕ) (hq : Odd q) (h13 : 13 ≤ q) :
    Odd (outerTorusOrder q / 2) ∧ 6 ≤ outerTorusOrder q / 2 ∧
      ((outerTorusOrder q / 2 = (q - 1) / 2 ∧ 13 ≤ q) ∨
        outerTorusOrder q / 2 = (q + 1) / 2) := by
  obtain ⟨k, rfl⟩ := hq
  have hm : outerTorusOrder (2 * k + 1) % 4 = 2 :=
    outerTorusOrder_mod_four (q := 2 * k + 1) (by exact ⟨k, rfl⟩)
  rcases outerTorusOrder_eq (q := 2 * k + 1) with h | h
  · rw [h]
    rw [show 2 * k + 2 = (k + 1) * 2 by omega, Nat.mul_div_left (k + 1) (by norm_num)]
    have hk6 : 6 ≤ k + 1 := by omega
    refine ⟨?_, hk6, Or.inr ?_⟩
    · rw [Nat.odd_iff]
      omega
    · rfl
  · have h' : outerTorusOrder (2 * k + 1) = 2 * k := by omega
    rw [h']
    rw [show 2 * k = k * 2 by omega, Nat.mul_div_left k (by norm_num)]
    have hk6 : 6 ≤ k := by omega
    refine ⟨?_, hk6, Or.inl ⟨?_, by omega⟩⟩
    · rw [Nat.odd_iff]
      omega
    · rw [show (k * 2 + 1 - 1) / 2 = k by
        rw [show k * 2 + 1 - 1 = k * 2 by omega, Nat.mul_div_left k (by norm_num)]]

private lemma mem_closure_inverted {G : Type*} [Group G] [Finite G] {t a x : G}
    (ht : t * t = 1) (hinv : t * a * t⁻¹ = a⁻¹)
    (hx : x ∈ Subgroup.closure ({t, a} : Set G)) :
    x ∈ Subgroup.zpowers a ∨ ∃ k : ℤ, x = t * a ^ k := by
  have hnorm : t ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
    rw [CFSG.GroupTheory.mem_normalizer_zpowers_iff, hinv]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a)
  have hD : Subgroup.closure ({t, a} : Set G) =
      Subgroup.zpowers t ⊔ Subgroup.zpowers a := by
    rw [Set.insert_eq, Subgroup.closure_union, Subgroup.zpowers_eq_closure,
      Subgroup.zpowers_eq_closure]
  rw [hD] at hx
  obtain ⟨l, hl, hxl | hxl⟩ :=
    (mem_zpowers_sup_iff (L := Subgroup.zpowers a) (a := t) hnorm
      (by rw [pow_two]; exact ht)).mp hx
  · exact Or.inl (hxl ▸ hl)
  · right
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hl
    exact ⟨k, hxl⟩

private lemma eq_involution_of_mem_closure_inverted {G : Type*} [Group G] [Finite G]
    {t a u : G}
    (ht : t * t = 1) (hinv : t * a * t⁻¹ = a⁻¹) (hodd : Odd (orderOf a))
    (hu : u * u = 1) (hu1 : u ≠ 1) (hcomm : u * t = t * u)
    (huD : u ∈ Subgroup.closure ({t, a} : Set G)) : u = t := by
  rcases mem_closure_inverted ht hinv huD with h | ⟨k, hk⟩
  · have huord : orderOf u = 2 := orderOf_eq_prime (by simpa [pow_two] using hu) hu1
    have hdvd : orderOf u ∣ orderOf a := orderOf_dvd_of_mem_zpowers h
    rw [huord] at hdvd
    obtain ⟨c, hc⟩ := hdvd
    obtain ⟨m, hm⟩ := hodd
    omega
  · have hcomm' : (t * a ^ k) * t = t * (t * a ^ k) := by
      simpa only [hk] using hcomm
    have hconj : t * a ^ k * t⁻¹ = (a ^ k)⁻¹ := by
      calc t * a ^ k * t⁻¹ = (t * a * t⁻¹) ^ k :=
            (conj_zpow (a := t) (b := a) (i := k)).symm
        _ = (a⁻¹) ^ k := by rw [hinv]
        _ = (a ^ k)⁻¹ := inv_zpow a k
    have h1 : (t * a ^ k) * t = (a ^ k)⁻¹ := by
      calc (t * a ^ k) * t = (t * a ^ k * t⁻¹) * (t * t) := by group
        _ = (a ^ k)⁻¹ * 1 := by rw [hconj, ht]
        _ = (a ^ k)⁻¹ := mul_one _
    have h2 : t * (t * a ^ k) = a ^ k := by
      rw [← mul_assoc, ht, one_mul]
    have hEq : (a ^ k)⁻¹ = a ^ k := by
      calc (a ^ k)⁻¹ = (t * a ^ k) * t := h1.symm
        _ = t * (t * a ^ k) := hcomm'
        _ = a ^ k := h2
    have hsq : (a ^ k) * (a ^ k) = 1 := by
      calc (a ^ k) * (a ^ k) = (a ^ k)⁻¹ * (a ^ k) := by rw [hEq]
        _ = 1 := inv_mul_cancel _
    have hdvd2 : orderOf (a ^ k) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hsq)
    have hdvdn : orderOf (a ^ k) ∣ orderOf a :=
      orderOf_dvd_of_mem_zpowers (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) k)
    have hcop : Nat.Coprime (orderOf a) 2 := (Nat.coprime_two_left.mpr hodd).symm
    have hdvd : orderOf (a ^ k) ∣ (orderOf a).gcd 2 := Nat.dvd_gcd hdvdn hdvd2
    rw [hcop.gcd_eq_one] at hdvd
    have ha1 : a ^ k = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
    rw [hk, ha1, mul_one]

theorem l2InnerFacts_psl2_of_thirteen_le {K : Type} [Field K]
    [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hKcard : Nat.card K = p ^ f)
    (hq : 13 ≤ p ^ f) : L2InnerFacts (PSL2 K) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hK : IsOddPrimePower (Nat.card K) :=
    ⟨p, f, hp, hp.odd_of_ne_two hp2, Nat.one_le_iff_ne_zero.mpr hf0, hKcard⟩
  have hqodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hqcard : 3 < Nat.card K := by rw [hKcard]; omega
  set n : ℕ := outerTorusOrder (p ^ f) / 2 with hn_def
  have harith := outerTorus_div_two_basic (p ^ f) hqodd hq
  have hnodd : Odd n := by rw [hn_def]; exact harith.1
  have hn6 : 6 ≤ n := by rw [hn_def]; exact harith.2.1
  have hcase : (n = (p ^ f - 1) / 2 ∧ 13 ≤ p ^ f) ∨ n = (p ^ f + 1) / 2 := by
    rw [hn_def]
    exact harith.2.2
  have hnp : Nat.Coprime p n := by
    rw [hn_def]
    rcases outerTorusOrder_eq (q := p ^ f) with h | h
    · rw [h]
      exact CFSG.Glauberman.Dickson.MaxUp.coprime_half_add hp2 hf0
    · rw [h]
      exact CFSG.Glauberman.Dickson.MaxUp.coprime_half_sub hp2 hf0
  refine { gen := ?_, cent := ?_ }
  · intro t u ht ht1 hu hu1 hcomm hne
    let φ := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)
    have hφinj : Function.Injective φ := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    have htJ : φ t ∈ pslRange K := ⟨t, rfl⟩
    have ht' : φ t * φ t = 1 := by rw [← map_mul, ht, map_one]
    have ht1' : φ t ≠ 1 := fun h => ht1 (hφinj (by rw [h, map_one]))
    obtain ⟨τ', hτ'J, hτ'ord, hτ'inv⟩ := exists_inverted_of_inner hK hqcard ht' ht1' htJ
    obtain ⟨τ, hτφ⟩ := hτ'J
    subst τ'
    have hτord : orderOf τ = n := by
      rw [← orderOf_injective φ hφinj τ, hn_def, ← hKcard]
      exact hτ'ord
    have hτodd : Odd (orderOf τ) := by rw [hτord]; exact hnodd
    have hτinv : t * τ * t⁻¹ = τ⁻¹ := by
      apply hφinj
      simpa only [map_mul, map_inv] using hτ'inv
    clear ht' ht1' hτ'ord hτ'inv
    let D : Subgroup (PSL2 K) := Subgroup.closure ({t, τ} : Set (PSL2 K))
    have hτD : τ ∈ D := by
      dsimp [D]
      exact Subgroup.subset_closure (by simp)
    have htD : t ∈ D := by
      dsimp [D]
      exact Subgroup.subset_closure (by simp)
    have hDcard : Nat.card D = 2 * n := by
      dsimp [D]
      exact card_closure_of_inverted ht ht1 hτord hτinv hnodd
    have hu_notD : u ∉ D := by
      intro huD
      exact hne (eq_involution_of_mem_closure_inverted ht hτinv hτodd hu hu1 hcomm.symm huD).symm
    let Ksub : Subgroup (PSL2 K) := Subgroup.closure ({t, u, τ} : Set (PSL2 K))
    have hDle : D ≤ Ksub := by
      dsimp [D, Ksub]
      apply Subgroup.closure_mono
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto
    have huK : u ∈ Ksub := by
      dsimp [Ksub]
      exact Subgroup.subset_closure (by simp)
    have hDlt : D < Ksub := by
      refine lt_of_le_of_ne hDle ?_
      intro hEq
      exact hu_notD (hEq ▸ huK)
    have hKtop : Ksub = ⊤ := by
      by_contra hne_top
      exact CFSG.Glauberman.Dickson.MaxUp.no_overgroup_of_inverted hKcard hp2 D Ksub hDlt
        hne_top hτD htD hτinv hτord hDcard hn6 hnp hcase
    refine ⟨τ, Subgroup.mem_top τ, hτodd, hτinv, ?_⟩
    change (⊤ : Subgroup (PSL2 K)) ≤ Ksub
    rw [hKtop]
  · intro t u ht ht1 hu hu1 hcomm hne
    have htord : orderOf t = 2 := orderOf_eq_prime (by simpa [pow_two] using ht) ht1
    have huord : orderOf u = 2 := orderOf_eq_prime (by simpa [pow_two] using hu) hu1
    exact CFSG.GH74.Generic.BProg.B2.psl2_sup_centralizer_eq_top hKcard hp2
      (le_trans (by norm_num) hq) htord huord hne hcomm

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
