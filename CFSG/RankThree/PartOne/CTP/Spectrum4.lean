module

public import CFSG.RankThree.PartOne.KC.CommonEigenbasis
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.TotallySplit

public section

namespace CFSG.RankThree.PartOne.CTP

open Polynomial

section Orbit

private theorem eq_one_of_mul_self_eq_one_charTwo {K : Type*} [Field K] [CharP K 2] {x : K}
    (h : x * x = 1) : x = 1 := by
  rcases mul_self_eq_one_iff.mp h with h1 | h1
  · exact h1
  · rw [h1, CharTwo.neg_eq]

private theorem iterate_inv_apply {K : Type*} [Field K] (φ : K ≃+* K) (i : ℕ) (a : K) :
    φ^[i] a⁻¹ = (φ^[i] a)⁻¹ := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_inv₀]

private theorem iterate_mem_of_stable {K : Type*} [Field K] (φ : K ≃+* K) (S : Finset K)
    (hφS : ∀ s ∈ S, φ s ∈ S) (i : ℕ) {a : K} (ha : a ∈ S) : φ^[i] a ∈ S := by
  induction i with
  | zero => exact ha
  | succ i ih => rw [Function.iterate_succ_apply']; exact hφS _ ih

theorem fixes_of_stable_finset {K : Type*} [Field K] [CharP K 2] (φ : K ≃+* K) {p : ℕ}
    (hp : Odd p) (hφ : φ ^ p = 1) (S : Finset K) (hS : S.card ≤ 4)
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
    have hj' : φ^[j] s⁻¹ = s := by rw [iterate_inv_apply, hj, inv_inv]
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
    have hs1 : s = 1 := eq_one_of_mul_self_eq_one_charTwo hss
    exact hne (by rw [hs1, map_one])
  · have hcase' : ∀ j : ℕ, φ^[j] s ≠ s⁻¹ := fun j hj => hcase ⟨j, hj⟩
    set d := Function.minimalPeriod φ s with hd_def
    let O : Finset K := (Finset.range d).image fun i => φ^[i] s
    let O' : Finset K := O.image fun a => a⁻¹
    have hOS : O ⊆ S := by
      intro a ha
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
      exact iterate_mem_of_stable φ S hφS i hs
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
      rw [h1, ← hba, ← iterate_inv_apply, ← Function.iterate_add_apply]
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

section Spectrum

theorem exists_isPrimitiveRoot_of_dvd_natCard_sub_one {K : Type*} [Field K] [Finite K] {m : ℕ}
    (hmK : m ∣ Nat.card K - 1) : ∃ ζ : K, IsPrimitiveRoot ζ m := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hN : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
  have hg0 : orderOf g ≠ 0 := by
    rw [hg]
    exact Nat.card_pos.ne'
  have hm : m ∣ orderOf g := by rw [hg, hN]; exact hmK
  refine ⟨((g ^ (orderOf g / m) : Kˣ) : K), IsPrimitiveRoot.coe_units_iff.mpr ?_⟩
  have := IsPrimitiveRoot.orderOf (g ^ (orderOf g / m))
  rwa [orderOf_pow_orderOf_div hg0 hm] at this

theorem pow_eq_one_iff_forall_isRoot_charpoly {K : Type*} [Field K] [Finite K] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {m : ℕ} (hmK : m ∣ Nat.card K - 1) {x : Matrix ι ι K}
    (hx : x ^ m = 1) (e : ℕ) :
    x ^ e = 1 ↔ ∀ r : K, x.charpoly.IsRoot r → r ^ e = 1 := by
  classical
  have hm0 : NeZero m := by
    have : 1 < Nat.card K := Finite.one_lt_card
    exact ⟨(Nat.pos_of_dvd_of_pos hmK (by omega)).ne'⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_dvd_natCard_sub_one hmK
  set f : Module.End K (ι → K) := Matrix.toLinAlgEquiv' x with hf_def
  have hf : f ^ m = 1 := by rw [hf_def, ← map_pow, hx, map_one]
  have hroot : ∀ r : K, x.charpoly.IsRoot r ↔ f.HasEigenvalue r := fun r => by
    rw [Module.End.hasEigenvalue_iff_mem_spectrum, hf_def, AlgEquiv.spectrum_eq,
      Matrix.mem_spectrum_iff_isRoot_charpoly]
  constructor
  · intro hxe r hr
    obtain ⟨v, hv⟩ := ((hroot r).mp hr).exists_hasEigenvector
    have hfe : f ^ e = 1 := by rw [hf_def, ← map_pow, hxe, map_one]
    have h1 := hv.pow_apply e
    rw [hfe, Module.End.one_apply] at h1
    have h2 : (r ^ e - 1) • v = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hv.2
  · intro hroots
    have htop := iSup_eigenspace_eq_top_of_pow_eq_one hζ hf
    have hfe : f ^ e = 1 := by
      refine LinearMap.ext fun v => ?_
      have hv : v ∈ ⨆ μ, f.eigenspace μ := by rw [htop]; trivial
      refine Submodule.iSup_induction _ (motive := fun v => (f ^ e) v = v) hv ?_ ?_ ?_
      · intro μ v hv
        by_cases hv0 : v = 0
        · simp [hv0]
        · have hev : f.HasEigenvector μ v := ⟨hv, hv0⟩
          have hμ := hroots μ ((hroot μ).mpr (Module.End.hasEigenvalue_of_hasEigenvector hev))
          rw [hev.pow_apply e, hμ, one_smul]
      · simp
      · intro a b ha hb
        rw [map_add, ha, hb]
    apply Matrix.toLinAlgEquiv'.injective
    rw [map_pow, map_one]
    exact hfe

theorem mem_subfield_of_pow_natCard_sub_one {K : Type*} [Field K] [Finite K] (L : Subfield K)
    {a : K} (ha : a ^ (Nat.card L - 1) = 1) : a ∈ L := by
  classical
  have hLfin : Finite L := inferInstance
  have hfin : Fintype L := Fintype.ofFinite L
  have hcard : Fintype.card L = Nat.card L := (Nat.card_eq_fintype_card).symm
  have hpos : 0 < Nat.card L := Nat.card_pos
  have hlt : 1 < Fintype.card L := Fintype.one_lt_card
  set P : K[X] := X ^ Fintype.card L - X with hP
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hlt
  have hdeg : P.natDegree = Fintype.card L := FiniteField.X_pow_card_sub_X_natDegree_eq K hlt
  have hroots : (Finset.univ.image (fun b : L => (b : K))) ⊆ P.roots.toFinset := by
    intro y hy
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hy
    rw [Multiset.mem_toFinset, mem_roots hP0]
    have hb := FiniteField.pow_card b
    have hb' : (b : K) ^ Fintype.card L = (b : K) := by
      have := congrArg (fun c : L => (c : K)) hb
      simpa using this
    simp [hP, hb']
  have hcardle : P.roots.toFinset.card ≤ Fintype.card L := by
    calc P.roots.toFinset.card ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := card_roots' P
      _ = Fintype.card L := hdeg
  have himg : (Finset.univ.image (fun b : L => (b : K))).card = Fintype.card L := by
    rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ]
  have heq := Finset.eq_of_subset_of_card_le hroots (by rw [himg]; exact hcardle)
  have hmem : a ∈ P.roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hP0]
    have h1 : a ^ Fintype.card L = a := by
      have hc : Fintype.card L = (Nat.card L - 1) + 1 := by omega
      rw [hc, pow_succ, ha, one_mul]
    simp [hP, h1]
  rw [← heq] at hmem
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hmem
  exact b.2

theorem mem_subfield_of_spectrum {K : Type*} [Field K] [Finite K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {m : ℕ} (hmK : m ∣ Nat.card K - 1) {x : Matrix ι ι K} (hord : orderOf x = m)
    (L : Subfield K) (hL : ∀ r : K, x.charpoly.IsRoot r → r ∈ L) :
    ∀ r : K, r ^ m = 1 → r ∈ L := by
  classical
  have hx : x ^ m = 1 := hord ▸ pow_orderOf_eq_one x
  have hm0 : m ≠ 0 := by
    have : 1 < Nat.card K := Finite.one_lt_card
    exact (Nat.pos_of_dvd_of_pos hmK (by omega)).ne'
  have hLfin : Finite L := inferInstance
  have hfin : Fintype L := Fintype.ofFinite L
  have hcard : Fintype.card L = Nat.card L := (Nat.card_eq_fintype_card).symm
  have hspec : ∀ r : K, x.charpoly.IsRoot r → r ^ (Nat.card L - 1) = 1 := by
    intro r hr
    have hrL := hL r hr
    have hrm : r ^ m = 1 := (pow_eq_one_iff_forall_isRoot_charpoly hmK hx m).mp hx r hr
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_pow hm0] at hrm
      exact zero_ne_one hrm
    have hb := FiniteField.pow_card_sub_one_eq_one (⟨r, hrL⟩ : L)
      (fun h => hr0 (congrArg (fun c : L => (c : K)) h))
    rw [hcard] at hb
    have := congrArg (fun c : L => (c : K)) hb
    simpa using this
  have hxL : x ^ (Nat.card L - 1) = 1 :=
    (pow_eq_one_iff_forall_isRoot_charpoly hmK hx _).mpr hspec
  have hmL : m ∣ Nat.card L - 1 := hord ▸ orderOf_dvd_of_pow_eq_one hxL
  intro r hr
  apply mem_subfield_of_pow_natCard_sub_one L
  obtain ⟨c, hc⟩ := hmL
  rw [hc, pow_mul, hr, one_pow]

end Spectrum

section Main

theorem fixes_rootsOfUnity_of_conj {K : Type*} [Field K] [Finite K] [CharP K 2] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (hn : Fintype.card ι ≤ 4) (φ : K ≃+* K) {p : ℕ} (hp : Odd p)
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
  have hScard : S.card ≤ 4 := by
    calc S.card ≤ Multiset.card x.charpoly.roots := Multiset.toFinset_card_le _
      _ ≤ x.charpoly.natDegree := card_roots' _
      _ = Fintype.card ι := Matrix.charpoly_natDegree_eq_dim x
      _ ≤ 4 := hn
  have hφS : ∀ s ∈ S, φ s ∈ S := by
    intro s hs
    rw [hmemS] at hs ⊢
    have := hs.map (f := (φ : K →+* K))
    rwa [hcp] at this
  have hinvS : ∀ s ∈ S, s⁻¹ ∈ S := by
    intro s hs
    rw [hmemS] at hs ⊢
    exact hrec s hs
  have hfix := fixes_of_stable_finset φ hp hφ S hScard hφS hinvS
  have hmem := mem_subfield_of_spectrum hmK hord
    (RingHom.eqLocusField (φ : K →+* K) (RingHom.id K)) (fun r hr => hfix r ((hmemS r).mpr hr))
  intro r hr
  exact hmem r hr

end Main

end CFSG.RankThree.PartOne.CTP
