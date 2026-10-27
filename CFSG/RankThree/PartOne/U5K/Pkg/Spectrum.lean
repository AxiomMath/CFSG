module

public import CFSG.RankThree.PartOne.CTP.Spectrum4

public section

namespace CFSG.RankThree.PartOne.U5K.Pkg

open Polynomial CFSG.RankThree.PartOne.CTP

section Orbit

private theorem eq_one_of_mul_self_eq_one_charTwo' {K : Type*} [Field K] [CharP K 2] {x : K}
    (h : x * x = 1) : x = 1 := by
  rcases mul_self_eq_one_iff.mp h with h1 | h1
  · exact h1
  · rw [h1, CharTwo.neg_eq]

private theorem iterate_inv_apply' {K : Type*} [Field K] (φ : K ≃+* K) (i : ℕ) (a : K) :
    φ^[i] a⁻¹ = (φ^[i] a)⁻¹ := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_inv₀]

private theorem iterate_mem_of_stable' {K : Type*} [Field K] (φ : K ≃+* K) (S : Finset K)
    (hφS : ∀ s ∈ S, φ s ∈ S) (i : ℕ) {a : K} (ha : a ∈ S) : φ^[i] a ∈ S := by
  induction i with
  | zero => exact ha
  | succ i ih => rw [Function.iterate_succ_apply']; exact hφS _ ih

theorem fixes_of_stable_finset_five {K : Type*} [Field K] [CharP K 2] (φ : K ≃+* K) {p : ℕ}
    (hp : Odd p) (hφ : φ ^ p = 1) (S : Finset K) (hS : S.card ≤ 5)
    (hφS : ∀ s ∈ S, φ s ∈ S) (hinvS : ∀ s ∈ S, s⁻¹ ∈ S) : ∀ s ∈ S, φ s = s := by
  classical
  have hper : ∀ s : K, φ^[p] s = s := fun s => by
    have := congrArg (fun e : K ≃+* K => e s) hφ
    simpa using this
  intro s hs
  by_contra hne
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hne (map_zero φ)
  have hd : Function.minimalPeriod φ s ∣ p := Function.IsPeriodicPt.minimalPeriod_dvd (hper s)
  have hdodd : Odd (Function.minimalPeriod φ s) := Odd.of_dvd_nat hp hd
  have hd1 : Function.minimalPeriod φ s ≠ 1 := fun h =>
    hne (Function.minimalPeriod_eq_one_iff_isFixedPt.mp h)
  have hd3 : 3 ≤ Function.minimalPeriod φ s := by
    obtain ⟨k, hk⟩ := hdodd
    omega
  by_cases hcase : ∃ j : ℕ, φ^[j] s = s⁻¹
  · obtain ⟨j, hj⟩ := hcase
    have hj' : φ^[j] s⁻¹ = s := by rw [iterate_inv_apply', hj, inv_inv]
    have h2j : φ^[2 * j] s = s := by
      rw [two_mul, Function.iterate_add_apply, hj, hj']
    have hdj : Function.minimalPeriod φ s ∣ 2 * j :=
      Function.IsPeriodicPt.minimalPeriod_dvd h2j
    have hcop : Nat.Coprime (Function.minimalPeriod φ s) 2 := by
      obtain ⟨k, hk⟩ := hdodd
      rw [hk]
      simp
    have hdj' : Function.minimalPeriod φ s ∣ j := hcop.dvd_of_dvd_mul_left hdj
    have hfix : φ^[j] s = s := Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr hdj'
    rw [hfix] at hj
    have hss : s * s = 1 := by
      calc s * s = s * s⁻¹ := by rw [← hj]
        _ = 1 := mul_inv_cancel₀ hs0
    have hs1 : s = 1 := eq_one_of_mul_self_eq_one_charTwo' hss
    exact hne (by rw [hs1, map_one])
  · have hcase' : ∀ j : ℕ, φ^[j] s ≠ s⁻¹ := fun j hj => hcase ⟨j, hj⟩
    set d := Function.minimalPeriod φ s with hd_def
    let O : Finset K := (Finset.range d).image fun i => φ^[i] s
    let O' : Finset K := O.image fun a => a⁻¹
    have hOS : O ⊆ S := by
      intro a ha
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
      exact iterate_mem_of_stable' φ S hφS i hs
    have hO'S : O' ⊆ S := by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
      exact hinvS b (hOS hb)
    have hOcard : O.card = d := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro i hi j hj hij
      exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod (by simpa using hi)
        (by simpa using hj)).mp hij
    have hO'card : O'.card = d := by
      rw [Finset.card_image_of_injective _ inv_injective, hOcard]
    have hdisj : Disjoint O O' := by
      rw [Finset.disjoint_left]
      intro a haO haO'
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp haO
      obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp haO'
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨k, hk⟩ := hp
      apply hcase' ((2 * k) * j + i)
      have h1 : φ^[2 * k * j + i] s = φ^[2 * k * j] (φ^[i] s) := by
        rw [Function.iterate_add_apply]
      rw [h1, ← hba, ← iterate_inv_apply', ← Function.iterate_add_apply]
      have h2 : 2 * k * j + j = p * j := by rw [hk]; ring
      rw [h2, Function.iterate_mul]
      have : (φ^[p]) = id := funext hper
      rw [this, Function.iterate_id]
      rfl
    have hcard : (O ∪ O').card = d + d := by
      rw [Finset.card_union_of_disjoint hdisj, hOcard, hO'card]
    have := Finset.card_le_card (Finset.union_subset hOS hO'S)
    omega

end Orbit

section Main

theorem fixes_rootsOfUnity_of_conj_five {K : Type*} [Field K] [Finite K] [CharP K 2] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (hn : Fintype.card ι ≤ 5) (φ : K ≃+* K) {p : ℕ} (hp : Odd p)
    (hφ : φ ^ p = 1) {x : Matrix ι ι K} {m : ℕ} (hm : Odd m) (hmK : m ∣ Nat.card K - 1)
    (hord : orderOf x = m)
    (hrec : ∀ r : K, x.charpoly.IsRoot r → x.charpoly.IsRoot r⁻¹)
    (hconj : ∃ g : Matrix ι ι K, IsUnit g ∧ g * x.map φ = x * g) :
    ∀ r : K, r ^ m = 1 → φ r = r := by
  classical
  have _ := hm
  obtain ⟨g, hg, hgx⟩ := hconj
  obtain ⟨u, rfl⟩ := hg
  have hdet : IsUnit (u : Matrix ι ι K).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp u.isUnit
  have hxconj : x = (u : Matrix ι ι K) * x.map φ *
      (u : Matrix ι ι K)⁻¹ := by
    rw [hgx, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
  have hcp : x.charpoly.map (φ : K →+* K) = x.charpoly := by
    rw [← Matrix.charpoly_map x (φ : K →+* K)]
    conv_rhs => rw [hxconj]
    exact (Matrix.charpoly_units_conj u (x.map φ)).symm
  have hne : x.charpoly ≠ 0 := x.charpoly_monic.ne_zero
  set S : Finset K := x.charpoly.roots.toFinset with hS_def
  have hmemS : ∀ r : K, r ∈ S ↔ x.charpoly.IsRoot r := fun r => by
    rw [hS_def, Multiset.mem_toFinset, mem_roots hne]
  have hScard : S.card ≤ 5 := by
    calc S.card ≤ Multiset.card x.charpoly.roots := Multiset.toFinset_card_le _
      _ ≤ x.charpoly.natDegree := card_roots' _
      _ = Fintype.card ι := Matrix.charpoly_natDegree_eq_dim x
      _ ≤ 5 := hn
  have hφS : ∀ s ∈ S, φ s ∈ S := by
    intro s hs
    rw [hmemS] at hs ⊢
    have := hs.map (f := (φ : K →+* K))
    rwa [hcp] at this
  have hinvS : ∀ s ∈ S, s⁻¹ ∈ S := by
    intro s hs
    rw [hmemS] at hs ⊢
    exact hrec s hs
  have hfix := fixes_of_stable_finset_five φ hp hφ S hScard hφS hinvS
  have hmem := mem_subfield_of_spectrum hmK hord
    (RingHom.eqLocusField (φ : K →+* K) (RingHom.id K)) (fun r hr => hfix r ((hmemS r).mpr hr))
  intro r hr
  exact hmem r hr

end Main

end CFSG.RankThree.PartOne.U5K.Pkg
