module

public import CFSG.RankThree.PartTwo.KFacts.KS163P6
import CFSG.GH74.GLS.IVK.Proofs2.Ivk714AltAut
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.KFacts.KF163A10

open Equiv

attribute [local instance] Fintype.ofFinite

private noncomputable def orbitFinset (H : Subgroup (Equiv.Perm (Fin 10))) (w : Fin 10) :
    Finset (Fin 10) := by
  classical
  exact Finset.univ.filter fun p => p ∈ MulAction.orbit H w

variable {T : Subgroup (Equiv.Perm (Fin 10))}

private theorem mem_orbitFinset {w p : Fin 10} :
    p ∈ orbitFinset T w ↔ p ∈ MulAction.orbit T w := by
  classical
  simp [orbitFinset]

private theorem orbitFinset_card (w : Fin 10) :
    (orbitFinset T w).card = Nat.card (MulAction.orbit T w) := by
  have h1 : (orbitFinset T w).card = Fintype.card ↥(orbitFinset T w) :=
    (Fintype.card_coe (orbitFinset T w)).symm
  rw [h1, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun p => mem_orbitFinset)

private theorem mem_orbit_iff_apply {p q : Fin 10} :
    q ∈ MulAction.orbit T p ↔ ∃ τ ∈ T, τ p = q := by
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨τ, hτ⟩
    rw [Subgroup.smul_def, Equiv.Perm.smul_def] at hτ
    exact ⟨(τ : Equiv.Perm (Fin 10)), τ.2, hτ⟩
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨⟨τ, hτ⟩, by rw [Subgroup.smul_def, Equiv.Perm.smul_def]⟩

private theorem image_orbitFinset {σ : Equiv.Perm (Fin 10)}
    (hσ : σ ∈ Subgroup.normalizer (T : Set (Equiv.Perm (Fin 10)))) (p : Fin 10) :
    (orbitFinset T p).image σ = orbitFinset T (σ p) := by
  classical
  ext q
  simp only [Finset.mem_image, mem_orbitFinset, mem_orbit_iff_apply]
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨τ, hτ, rfl⟩ := hr
    exact ⟨σ * τ * σ⁻¹, (Subgroup.mem_normalizer_iff.mp hσ τ).mp hτ,
      by simp [Equiv.Perm.mul_apply]⟩
  · rintro ⟨τ, hτ, rfl⟩
    refine ⟨(σ⁻¹ * τ * σ) p, ?_, ?_⟩
    · refine ⟨σ⁻¹ * τ * σ, ?_, rfl⟩
      refine (Subgroup.mem_normalizer_iff.mp hσ _).mpr ?_
      have h : σ * (σ⁻¹ * τ * σ) * σ⁻¹ = τ := by group
      rw [h]
      exact hτ
    · simp [Equiv.Perm.mul_apply]

private theorem image_support_self (σ : Equiv.Perm (Fin 10)) :
    σ.support.image σ = σ.support := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact Equiv.Perm.apply_mem_support.mpr hq
  · rw [Finset.card_image_of_injective _ σ.injective]

private theorem three_cycle_eq_empty_or_support {σ : Equiv.Perm (Fin 10)}
    (hσ : σ.IsThreeCycle) {S : Finset (Fin 10)} (hS : S ⊆ σ.support)
    (hinv : ∀ p ∈ S, σ p ∈ S) : S = ∅ ∨ S = σ.support := by
  rcases S.eq_empty_or_nonempty with h | ⟨a, ha⟩
  · exact Or.inl h
  right
  have hsupp : σ.support = {a, σ a, σ (σ a)} :=
    (Equiv.Perm.IsThreeCycle.support_eq_iff_mem_support hσ).mpr (hS ha)
  have h1 : σ a ∈ S := hinv a ha
  have h2 : σ (σ a) ∈ S := hinv (σ a) h1
  have hsub : ({a, σ a, σ (σ a)} : Finset (Fin 10)) ⊆ S := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact ha
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact h1
    rw [Finset.mem_singleton] at hp
    exact hp ▸ h2
  rw [hsupp]
  exact Finset.eq_of_subset_of_card_le (hsupp ▸ hS) (Finset.card_le_card hsub)

private theorem pow_two_eq_two_of_le_three {n : ℕ} (h2 : 2 ≤ 2 ^ n) (h3 : 2 ^ n ≤ 3) :
    2 ^ n = 2 := by
  have hn : n ≤ 1 := by
    by_contra h
    have h2n : 2 ≤ n := by omega
    have hle : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2n
    norm_num at hle
    omega
  interval_cases n
  · omega
  · rfl

private theorem pow_two_eq_one_or_four {n : ℕ} (h3 : 3 ∣ 2 ^ n - 1) (hle : 2 ^ n ≤ 10) :
    2 ^ n = 1 ∨ 2 ^ n = 4 := by
  have hn : n ≤ 3 := by
    by_contra h
    have h4 : 4 ≤ n := by omega
    have h2n : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h4
    norm_num at h2n
    omega
  interval_cases n
  · exact Or.inl rfl
  · exact absurd h3 (by decide)
  · exact Or.inr rfl
  · exact absurd h3 (by decide)

private theorem eq_biUnion_of_subset_union {O : Fin 3 → Finset (Fin 10)}
    (hdisj : ∀ i j, i ≠ j → Disjoint (O i) (O j)) {S : Finset (Fin 10)}
    (hsub : S ⊆ O 0 ∪ O 1 ∪ O 2) (hint : ∀ j, S ∩ O j = ∅ ∨ O j ⊆ S) :
    S = (Finset.univ.filter (fun j : Fin 3 => O j ⊆ S)).biUnion O := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨j, hj⟩ : ∃ j : Fin 3, p ∈ O j := by
      have h := hsub hp
      rw [Finset.mem_union, Finset.mem_union] at h
      rcases h with (h | h) | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
    have hne : (S ∩ O j).Nonempty := ⟨p, Finset.mem_inter.mpr ⟨hp, hj⟩⟩
    have hsubj : O j ⊆ S := by
      rcases hint j with h | h
      · rw [h] at hne
        exact absurd hne Finset.not_nonempty_empty
      · exact h
    exact Finset.mem_biUnion.mpr ⟨j, by simp [hsubj], hj⟩
  · intro hp
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
    exact (by simpa using hj : O j ⊆ S) hpj

private theorem three_dvd_card_of_subset_union {O : Fin 3 → Finset (Fin 10)}
    (hO : ∀ i, (O i).card = 3) (hdisj : ∀ i j, i ≠ j → Disjoint (O i) (O j))
    {S : Finset (Fin 10)} (hsub : S ⊆ O 0 ∪ O 1 ∪ O 2)
    (hint : ∀ j, S ∩ O j = ∅ ∨ O j ⊆ S) : 3 ∣ S.card := by
  classical
  have hSeq : S = (Finset.univ.filter (fun j : Fin 3 => O j ⊆ S)).biUnion O :=
    eq_biUnion_of_subset_union hdisj hsub hint
  have hcard : ((Finset.univ.filter (fun j : Fin 3 => O j ⊆ S)).biUnion O).card =
      3 * (Finset.univ.filter (fun j : Fin 3 => O j ⊆ S)).card := by
    rw [Finset.card_biUnion (fun i _ j _ hij => hdisj i j hij),
      Finset.sum_const_nat (fun j _ => hO j), Nat.mul_comm]
  rw [hSeq, hcard]
  exact dvd_mul_right 3 _

private theorem eq_support_of_card_three {O : Fin 3 → Finset (Fin 10)}
    (hO : ∀ i, (O i).card = 3) (hdisj : ∀ i j, i ≠ j → Disjoint (O i) (O j))
    {S : Finset (Fin 10)} (hsub : S ⊆ O 0 ∪ O 1 ∪ O 2)
    (hint : ∀ j, S ∩ O j = ∅ ∨ O j ⊆ S) (hcard : S.card = 3) :
    ∃ i : Fin 3, S = O i := by
  classical
  have hSeq : S = (Finset.univ.filter (fun j : Fin 3 => O j ⊆ S)).biUnion O :=
    eq_biUnion_of_subset_union hdisj hsub hint
  have hcard' : ((Finset.univ.filter (fun j : Fin 3 => O j ⊆ S)).biUnion O).card =
      3 * (Finset.univ.filter (fun j : Fin 3 => O j ⊆ S)).card := by
    rw [Finset.card_biUnion (fun i _ j _ hij => hdisj i j hij),
      Finset.sum_const_nat (fun j _ => hO j), Nat.mul_comm]
  have hK : (Finset.univ.filter (fun j : Fin 3 => O j ⊆ S)).card = 1 := by
    rw [hSeq] at hcard
    omega
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hK
  refine ⟨i, ?_⟩
  rw [hSeq, hi, Finset.singleton_biUnion]

private theorem exists_point_outside (x : Fin 3 → Equiv.Perm (Fin 10))
    (hx : ∀ i, (x i).IsThreeCycle)
    (hdisj : ∀ i j, i ≠ j → Disjoint (x i).support (x j).support) :
    ∃ w : Fin 10, (∀ j, w ∉ (x j).support) ∧
      ∀ p : Fin 10, p ≠ w → p ∈ (x 0).support ∪ (x 1).support ∪ (x 2).support := by
  have hcard : ∀ i, ((x i).support).card = 3 := fun i => (hx i).card_support
  have hd01 : Disjoint ((x 0).support) ((x 1).support) := hdisj 0 1 (by decide)
  have hd02 : Disjoint ((x 0).support) ((x 2).support) := hdisj 0 2 (by decide)
  have hd12 : Disjoint ((x 1).support) ((x 2).support) := hdisj 1 2 (by decide)
  have hdU : Disjoint ((x 0).support ∪ (x 1).support) ((x 2).support) :=
    Finset.disjoint_union_left.mpr ⟨hd02, hd12⟩
  have hUcard : ((x 0).support ∪ (x 1).support ∪ (x 2).support).card = 9 := by
    rw [Finset.card_union_of_disjoint hdU, Finset.card_union_of_disjoint hd01,
      hcard 0, hcard 1, hcard 2]
  obtain ⟨w, -, hwU⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := (x 0).support ∪ (x 1).support ∪ (x 2).support) (t := Finset.univ) (by
      rw [Finset.card_univ, Fintype.card_fin, hUcard]; omega)
  have hw0 : w ∉ (x 0).support := fun h =>
    hwU (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hw1 : w ∉ (x 1).support := fun h =>
    hwU (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hw2 : w ∉ (x 2).support := fun h => hwU (Finset.mem_union_right _ h)
  refine ⟨w, ?_, ?_⟩
  · intro j
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by decide +revert
    rcases hj with rfl | rfl | rfl
    · exact hw0
    · exact hw1
    · exact hw2
  · intro p hp
    by_contra hpU
    have hW : insert w ((x 0).support ∪ (x 1).support ∪ (x 2).support) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_insert_of_notMem hwU, hUcard, Fintype.card_fin]
    have hmem : p ∈ insert w ((x 0).support ∪ (x 1).support ∪ (x 2).support) := by
      rw [hW]
      exact Finset.mem_univ p
    rw [Finset.mem_insert] at hmem
    exact hmem.elim hp hpU

private theorem orbit_inter_support (x : Fin 3 → Equiv.Perm (Fin 10))
    (hx : ∀ i, (x i).IsThreeCycle)
    (hxT : ∀ i, x i ∈ Subgroup.normalizer (T : Set (Equiv.Perm (Fin 10))))
    {w : Fin 10} (hw : ∀ j, w ∉ (x j).support) (j : Fin 3) :
    orbitFinset T w ∩ (x j).support = ∅ ∨ (x j).support ⊆ orbitFinset T w := by
  classical
  have hwfix : x j w = w := Equiv.Perm.notMem_support.mp (hw j)
  have himg : (orbitFinset T w).image (x j) = orbitFinset T w := by
    rw [image_orbitFinset (hxT j) w, hwfix]
  have hinv : ∀ p ∈ orbitFinset T w ∩ (x j).support,
      x j p ∈ orbitFinset T w ∩ (x j).support := by
    intro p hp
    rw [Finset.mem_inter] at hp ⊢
    refine ⟨?_, ?_⟩
    · rw [← himg]
      exact Finset.mem_image_of_mem _ hp.1
    · exact Equiv.Perm.apply_mem_support.mpr hp.2
  rcases three_cycle_eq_empty_or_support (hx j) Finset.inter_subset_right hinv with h | h
  · exact Or.inl h
  · exact Or.inr (h ▸ Finset.inter_subset_left)

private theorem not_orbitFinset_subset_support (hT : IsPGroup 2 T)
    (x : Fin 3 → Equiv.Perm (Fin 10)) (hx : ∀ i, (x i).IsThreeCycle)
    (hxT : ∀ i, x i ∈ Subgroup.normalizer (T : Set (Equiv.Perm (Fin 10))))
    {p : Fin 10} {j : Fin 3} (h2le : 2 ≤ (orbitFinset T p).card)
    (hsub : orbitFinset T p ⊆ (x j).support) : False := by
  classical
  obtain ⟨n, hn⟩ := hT.card_orbit p
  have horbcard : (orbitFinset T p).card = 2 ^ n := by
    rw [orbitFinset_card, hn]
  have hle3 : (orbitFinset T p).card ≤ 3 := by
    rw [← (hx j).card_support]
    exact Finset.card_le_card hsub
  have hcard2 : (orbitFinset T p).card = 2 := by
    rw [horbcard]
    exact pow_two_eq_two_of_le_three (horbcard ▸ h2le) (horbcard ▸ hle3)
  have himgF : orbitFinset T (x j p) = (orbitFinset T p).image (x j) :=
    (image_orbitFinset (hxT j) p).symm
  have hΓcard : (orbitFinset T (x j p)).card = 2 := by
    rw [himgF, Finset.card_image_of_injective _ (x j).injective, hcard2]
  have hΓsub : orbitFinset T (x j p) ⊆ (x j).support := by
    intro a ha
    rw [himgF] at ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    exact Equiv.Perm.apply_mem_support.mpr (hsub hb)
  have hinter : (orbitFinset T (x j p) ∩ orbitFinset T p).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have h4 : (orbitFinset T (x j p) ∪ orbitFinset T p).card = 4 := by
      rw [Finset.card_union_of_disjoint (by rwa [Finset.disjoint_iff_inter_eq_empty]),
        hΓcard, hcard2]
    have hle : (orbitFinset T (x j p) ∪ orbitFinset T p).card ≤ 3 := by
      rw [← (hx j).card_support]
      exact Finset.card_le_card (Finset.union_subset hΓsub hsub)
    omega
  obtain ⟨r, hr⟩ := hinter
  rw [Finset.mem_inter] at hr
  have horbeq : MulAction.orbit T (x j p) = MulAction.orbit T p :=
    (MulAction.orbit_eq_iff.mpr (mem_orbitFinset.mp hr.1)).symm.trans
      (MulAction.orbit_eq_iff.mpr (mem_orbitFinset.mp hr.2))
  have horbeqF : orbitFinset T (x j p) = orbitFinset T p := by
    ext r
    rw [mem_orbitFinset, mem_orbitFinset, horbeq]
  have himgΔ : (orbitFinset T p).image (x j) = orbitFinset T p := by
    rw [image_orbitFinset (hxT j) p, horbeqF]
  have hinv : ∀ q ∈ orbitFinset T p, x j q ∈ orbitFinset T p := by
    intro q hq
    rw [← himgΔ]
    exact Finset.mem_image_of_mem _ hq
  have hS : orbitFinset T p = (x j).support := by
    rcases three_cycle_eq_empty_or_support (hx j) hsub hinv with h | h
    · rw [h] at h2le
      simp at h2le
    · exact h
  rw [hS, (hx j).card_support] at hcard2
  exact absurd hcard2 (by norm_num)

private theorem fixes_of_notMem_orbit (hT : IsPGroup 2 T)
    (x : Fin 3 → Equiv.Perm (Fin 10)) (hx : ∀ i, (x i).IsThreeCycle)
    (hdisj : ∀ i j, i ≠ j → Disjoint (x i).support (x j).support)
    (hxT : ∀ i, x i ∈ Subgroup.normalizer (T : Set (Equiv.Perm (Fin 10))))
    {w : Fin 10} (hcover : ∀ p : Fin 10, p ≠ w →
      p ∈ (x 0).support ∪ (x 1).support ∪ (x 2).support)
    {p : Fin 10} (hw : w ∉ MulAction.orbit T p) {τ : Equiv.Perm (Fin 10)} (hτ : τ ∈ T) :
    τ p = p := by
  classical
  by_contra hne
  have hpair : ({p, τ p} : Finset (Fin 10)) ⊆ orbitFinset T p := by
    intro q hq
    rw [mem_orbitFinset]
    rcases Finset.mem_insert.mp hq with hqp | hq
    · rw [hqp]
      exact (MulAction.mem_orbit_self p : p ∈ MulAction.orbit T p)
    · rw [Finset.mem_singleton] at hq
      rw [hq, mem_orbit_iff_apply]
      exact ⟨τ, hτ, rfl⟩
  have h2le : 2 ≤ (orbitFinset T p).card := by
    have hcard : ({p, τ p} : Finset (Fin 10)).card = 2 :=
      Finset.card_pair_eq_two_iff.mpr (Ne.symm hne)
    rw [← hcard]
    exact Finset.card_le_card hpair
  have hstep : ∀ j : Fin 3, orbitFinset T p ∩ (x j).support = ∅ ∨
      (x j).support ⊆ orbitFinset T p := by
    intro j
    by_cases hsub : orbitFinset T p ⊆ (x j).support
    · exact absurd hsub (not_orbitFinset_subset_support hT x hx hxT h2le)
    · obtain ⟨q, hq, hqO⟩ := Finset.not_subset.mp hsub
      have hqΔ : q ∈ MulAction.orbit T p := mem_orbitFinset.mp hq
      have hqx : q ∈ orbitFinset T (x j p) := by
        rw [← image_orbitFinset (T := T) (σ := x j) (hxT j) p,
          ← Equiv.Perm.notMem_support.mp hqO]
        exact Finset.mem_image_of_mem _ hq
      have horbeqF : orbitFinset T (x j p) = orbitFinset T p := by
        ext r
        rw [mem_orbitFinset, mem_orbitFinset,
          (MulAction.orbit_eq_iff.mpr (mem_orbitFinset.mp hqx)).symm.trans
            (MulAction.orbit_eq_iff.mpr hqΔ)]
      have himg : (orbitFinset T p).image (x j) = orbitFinset T p := by
        rw [image_orbitFinset (hxT j) p, horbeqF]
      have hinv : ∀ r ∈ orbitFinset T p ∩ (x j).support,
          x j r ∈ orbitFinset T p ∩ (x j).support := by
        intro r hr
        rw [Finset.mem_inter] at hr ⊢
        refine ⟨?_, ?_⟩
        · rw [← himg]
          exact Finset.mem_image_of_mem _ hr.1
        · exact Equiv.Perm.apply_mem_support.mpr hr.2
      rcases three_cycle_eq_empty_or_support (hx j) Finset.inter_subset_right hinv with h | h
      · exact Or.inl h
      · exact Or.inr (h ▸ Finset.inter_subset_left)
  have hsubU : orbitFinset T p ⊆ (x 0).support ∪ (x 1).support ∪ (x 2).support := by
    intro q hq
    by_cases hqw : q = w
    · rw [hqw] at hq
      exact absurd (mem_orbitFinset.mp hq) hw
    · exact hcover q hqw
  have h3 : 3 ∣ (orbitFinset T p).card :=
    three_dvd_card_of_subset_union (fun i => (hx i).card_support) hdisj hsubU hstep
  obtain ⟨n, hn⟩ := hT.card_orbit p
  rw [orbitFinset_card, hn] at h3
  have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) h3
  norm_num at h32

private theorem support_subset_of_mem_stabilizer
    (x : Fin 3 → Equiv.Perm (Fin 10)) (hx : ∀ i, (x i).IsThreeCycle)
    {w : Fin 10} (hcover : ∀ p : Fin 10, p ≠ w →
      p ∈ (x 0).support ∪ (x 1).support ∪ (x 2).support)
    (hfix : ∀ p : Fin 10, w ∉ MulAction.orbit T p → ∀ τ ∈ T, τ p = p)
    {i : Fin 3} (hΔ : orbitFinset T w = {w} ∪ (x i).support)
    {τ : T} (hτ : τ ∈ MulAction.stabilizer T w) :
    (τ : Equiv.Perm (Fin 10)).support ⊆ (x i).support := by
  classical
  have hτw : (τ : Equiv.Perm (Fin 10)) w = w := by
    have h := hτ
    rw [MulAction.mem_stabilizer_iff] at h
    rw [Subgroup.smul_def, Equiv.Perm.smul_def] at h
    exact h
  intro p hp
  by_contra hpO
  have hpw : p ≠ w := by
    rintro rfl
    exact (Equiv.Perm.mem_support.mp hp) hτw
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, p ∈ (x j).support := by
    have h := hcover p hpw
    rw [Finset.mem_union, Finset.mem_union] at h
    rcases h with (h | h) | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  have hpΔ : p ∉ MulAction.orbit T w := by
    intro h
    have hmem : p ∈ orbitFinset T w := mem_orbitFinset.mpr h
    rw [hΔ, Finset.mem_union, Finset.mem_singleton] at hmem
    exact hmem.elim hpw hpO
  have hw' : w ∉ MulAction.orbit T p := by
    intro h
    exact hpΔ ((MulAction.orbit_eq_iff.mpr h) ▸
      (MulAction.mem_orbit_self p : p ∈ MulAction.orbit T p))
  exact (Equiv.Perm.mem_support.mp hp) (hfix p hw' τ τ.2)

private theorem isSwap_of_mem_stabilizer (hT : IsPGroup 2 T)
    (x : Fin 3 → Equiv.Perm (Fin 10)) (hx : ∀ i, (x i).IsThreeCycle)
    {i : Fin 3} {τ : T} (hsupp : (τ : Equiv.Perm (Fin 10)).support ⊆ (x i).support)
    (hne : τ ≠ 1) : (τ : Equiv.Perm (Fin 10)).IsSwap := by
  classical
  have hnePerm : (τ : Equiv.Perm (Fin 10)) ≠ 1 := fun h => hne (Subtype.ext h)
  have h2le : 2 ≤ (τ : Equiv.Perm (Fin 10)).support.card :=
    Equiv.Perm.one_lt_card_support_of_ne_one hnePerm
  have hle3 : (τ : Equiv.Perm (Fin 10)).support.card ≤ 3 := by
    rw [← (hx i).card_support]
    exact Finset.card_le_card hsupp
  have hτcard : (τ : Equiv.Perm (Fin 10)).support.card = 2 := by
    have hne3 : (τ : Equiv.Perm (Fin 10)).support.card ≠ 3 := by
      intro h3
      have h3c : (τ : Equiv.Perm (Fin 10)).IsThreeCycle := card_support_eq_three_iff.mp h3
      have h3ord : orderOf ((τ : Equiv.Perm (Fin 10))) = 3 := h3c.orderOf
      have h2dvd : 2 ∣ orderOf ((τ : Equiv.Perm (Fin 10))) := by
        have hneT : (⟨(τ : Equiv.Perm (Fin 10)), τ.2⟩ : T) ≠ 1 := by
          intro h
          exact hnePerm (congrArg Subtype.val h)
        have := hT.dvd_orderOf hneT
        rwa [Subgroup.orderOf_mk] at this
      obtain ⟨k, hk⟩ := h2dvd
      omega
    omega
  exact Equiv.Perm.card_support_eq_two.mp hτcard

private theorem conj_ne_self_of_isSwap (x : Fin 3 → Equiv.Perm (Fin 10))
    (hx : ∀ i, (x i).IsThreeCycle)
    {i : Fin 3} {τ : Equiv.Perm (Fin 10)} (hτswap : τ.IsSwap)
    (hsupp : τ.support ⊆ (x i).support) : x i * τ * (x i)⁻¹ ≠ τ := by
  classical
  have hτcard : τ.support.card = 2 := Equiv.Perm.card_support_eq_two.mpr hτswap
  have hσsupp : (x i * τ * (x i)⁻¹).support = τ.support.image (x i) := by
    rw [Equiv.Perm.support_conj]
    exact Finset.map_eq_image _ _
  intro h
  have himg : τ.support.image (x i) = τ.support := by
    rw [← hσsupp, h]
  have hinv : ∀ p ∈ τ.support, x i p ∈ τ.support := by
    intro p hp
    have hmem : x i p ∈ τ.support.image (x i) := Finset.mem_image_of_mem _ hp
    rwa [himg] at hmem
  rcases three_cycle_eq_empty_or_support (hx i) hsupp hinv with h0 | h3
  · rw [h0] at hτcard
    simp at hτcard
  · rw [h3, (hx i).card_support] at hτcard
    omega

private theorem not_mul_conj_mem (hT : IsPGroup 2 T)
    (x : Fin 3 → Equiv.Perm (Fin 10)) (hx : ∀ i, (x i).IsThreeCycle)
    {i : Fin 3} {τ : Equiv.Perm (Fin 10)} (hτT : τ ∈ T) (hτswap : τ.IsSwap)
    (hsupp : τ.support ⊆ (x i).support)
    (hσsupp : (x i * τ * (x i)⁻¹).support = τ.support.image (x i))
    (hσswap : (x i * τ * (x i)⁻¹).IsSwap) (hσT : x i * τ * (x i)⁻¹ ∈ T)
    (hστ : x i * τ * (x i)⁻¹ ≠ τ) : False := by
  classical
  have hτsign : Equiv.Perm.sign τ = -1 := Equiv.Perm.IsSwap.sign_eq hτswap
  have hσsign : Equiv.Perm.sign (x i * τ * (x i)⁻¹) = -1 :=
    Equiv.Perm.IsSwap.sign_eq hσswap
  have hprodT : τ * (x i * τ * (x i)⁻¹) ∈ T := T.mul_mem hτT hσT
  have hprodne : τ * (x i * τ * (x i)⁻¹) ≠ 1 := by
    intro h
    apply hστ
    have hττ : τ * τ = 1 := by
      rw [← pow_two, ← Equiv.Perm.IsSwap.orderOf hτswap]
      exact pow_orderOf_eq_one _
    calc x i * τ * (x i)⁻¹
        = (1 : Equiv.Perm (Fin 10)) * (x i * τ * (x i)⁻¹) := (one_mul _).symm
      _ = (τ * τ) * (x i * τ * (x i)⁻¹) := by rw [hττ]
      _ = τ * (τ * (x i * τ * (x i)⁻¹)) := mul_assoc _ _ _
      _ = τ * 1 := by rw [h]
      _ = τ := mul_one _
  have hprodsupp : (τ * (x i * τ * (x i)⁻¹)).support ⊆ (x i).support := by
    refine (Equiv.Perm.support_mul_le _ _).trans ?_
    rw [Finset.sup_eq_union]
    refine Finset.union_subset hsupp ?_
    rw [hσsupp]
    calc τ.support.image (x i) ⊆ (x i).support.image (x i) := Finset.image_subset_image hsupp
      _ = (x i).support := image_support_self (x i)
  have hprod2le : 2 ≤ (τ * (x i * τ * (x i)⁻¹)).support.card :=
    Equiv.Perm.one_lt_card_support_of_ne_one hprodne
  have hprod3le : (τ * (x i * τ * (x i)⁻¹)).support.card ≤ 3 := by
    rw [← (hx i).card_support]
    exact Finset.card_le_card hprodsupp
  have hprodne2 : (τ * (x i * τ * (x i)⁻¹)).support.card ≠ 2 := by
    intro h2
    have hsw : (τ * (x i * τ * (x i)⁻¹)).IsSwap := Equiv.Perm.card_support_eq_two.mp h2
    have hsign : Equiv.Perm.sign (τ * (x i * τ * (x i)⁻¹)) = 1 := by
      rw [Equiv.Perm.sign_mul, hτsign, hσsign]
      norm_num
    rw [Equiv.Perm.IsSwap.sign_eq hsw] at hsign
    norm_num at hsign
  have hprod3 : (τ * (x i * τ * (x i)⁻¹)).support.card = 3 := by omega
  have hthree : (τ * (x i * τ * (x i)⁻¹)).IsThreeCycle :=
    card_support_eq_three_iff.mp hprod3
  have hord3 : orderOf (τ * (x i * τ * (x i)⁻¹)) = 3 := hthree.orderOf
  have h2dvd : 2 ∣ orderOf (τ * (x i * τ * (x i)⁻¹)) := by
    have hneT : (⟨_, hprodT⟩ : T) ≠ 1 := fun h => hprodne (congrArg Subtype.val h)
    have := hT.dvd_orderOf hneT
    rwa [Subgroup.orderOf_mk] at this
  obtain ⟨k, hk⟩ := h2dvd
  omega

private theorem stabilizer_eq_bot (hT : IsPGroup 2 T)
    (x : Fin 3 → Equiv.Perm (Fin 10)) (hx : ∀ i, (x i).IsThreeCycle)
    (hxT : ∀ i, x i ∈ Subgroup.normalizer (T : Set (Equiv.Perm (Fin 10))))
    {w : Fin 10} (hw : ∀ j, w ∉ (x j).support)
    (hcover : ∀ p : Fin 10, p ≠ w →
      p ∈ (x 0).support ∪ (x 1).support ∪ (x 2).support)
    (hfix : ∀ p : Fin 10, w ∉ MulAction.orbit T p → ∀ τ ∈ T, τ p = p)
    {i : Fin 3} (hΔ : orbitFinset T w = {w} ∪ (x i).support) :
    MulAction.stabilizer T w = ⊥ := by
  classical
  rw [Subgroup.eq_bot_iff_forall]
  intro τ hτ
  by_contra hne
  have hsupp := support_subset_of_mem_stabilizer x hx hcover hfix hΔ hτ
  have hτswap : (τ : Equiv.Perm (Fin 10)).IsSwap :=
    isSwap_of_mem_stabilizer hT x hx hsupp hne
  have hσT : x i * (τ : Equiv.Perm (Fin 10)) * (x i)⁻¹ ∈ T :=
    (Subgroup.mem_normalizer_iff.mp (hxT i) _).mp τ.2
  have hσsupp : (x i * (τ : Equiv.Perm (Fin 10)) * (x i)⁻¹).support =
      (τ : Equiv.Perm (Fin 10)).support.image (x i) := by
    rw [Equiv.Perm.support_conj]
    exact Finset.map_eq_image _ _
  have hσswap : (x i * (τ : Equiv.Perm (Fin 10)) * (x i)⁻¹).IsSwap := by
    rw [← Equiv.Perm.card_support_eq_two, hσsupp,
      Finset.card_image_of_injective _ (x i).injective,
      Equiv.Perm.card_support_eq_two.mpr hτswap]
  have hστ : x i * (τ : Equiv.Perm (Fin 10)) * (x i)⁻¹ ≠ τ :=
    conj_ne_self_of_isSwap x hx hτswap hsupp
  exact not_mul_conj_mem hT x hx τ.2 hτswap hsupp hσsupp hσswap hσT hστ

private theorem orbitFinset_w_form (hT : IsPGroup 2 T) (x : Fin 3 → Equiv.Perm (Fin 10))
    (hx : ∀ i, (x i).IsThreeCycle)
    (hdisj : ∀ i j, i ≠ j → Disjoint (x i).support (x j).support)
    (hxT : ∀ i, x i ∈ Subgroup.normalizer (T : Set (Equiv.Perm (Fin 10))))
    {w : Fin 10} (hw : ∀ j, w ∉ (x j).support)
    (hcover : ∀ p : Fin 10, p ≠ w →
      p ∈ (x 0).support ∪ (x 1).support ∪ (x 2).support) :
    orbitFinset T w = {w} ∨ ∃ i : Fin 3, orbitFinset T w = {w} ∪ (x i).support := by
  classical
  have hΔinter : ∀ j : Fin 3, orbitFinset T w ∩ (x j).support = ∅ ∨
      (x j).support ⊆ orbitFinset T w := fun j => orbit_inter_support x hx hxT hw j
  have hwmem : w ∈ orbitFinset T w :=
    mem_orbitFinset.mpr (MulAction.mem_orbit_self w : w ∈ MulAction.orbit T w)
  have hsubUw : (orbitFinset T w).erase w ⊆
      (x 0).support ∪ (x 1).support ∪ (x 2).support := by
    intro q hq
    rw [Finset.mem_erase] at hq
    exact hcover q hq.1
  have hintw : ∀ j, (orbitFinset T w).erase w ∩ (x j).support = ∅ ∨
      (x j).support ⊆ (orbitFinset T w).erase w := by
    intro j
    rcases hΔinter j with h | h
    · left
      have hsub : (orbitFinset T w).erase w ∩ (x j).support ⊆
          orbitFinset T w ∩ (x j).support :=
        Finset.inter_subset_inter_right (Finset.erase_subset _ _)
      rw [h] at hsub
      exact Finset.subset_empty.mp hsub
    · right
      intro q hq
      rw [Finset.mem_erase]
      exact ⟨fun hqw => hw j (hqw ▸ hq), h hq⟩
  have h3dvd : 3 ∣ ((orbitFinset T w).erase w).card :=
    three_dvd_card_of_subset_union (fun i => (hx i).card_support) hdisj hsubUw hintw
  have herase : ((orbitFinset T w).erase w).card = (orbitFinset T w).card - 1 :=
    Finset.card_erase_of_mem hwmem
  obtain ⟨n, hn⟩ := hT.card_orbit w
  have hΔcard : (orbitFinset T w).card = 2 ^ n := by
    rw [orbitFinset_card, hn]
  have hcases : 2 ^ n = 1 ∨ 2 ^ n = 4 := by
    refine pow_two_eq_one_or_four ?_ ?_
    · rw [← hΔcard, ← herase]
      exact h3dvd
    · rw [← hΔcard]
      calc (orbitFinset T w).card ≤ Fintype.card (Fin 10) := Finset.card_le_univ _
        _ = 10 := Fintype.card_fin 10
  rcases hcases with h1 | h4
  · left
    have hc : (orbitFinset T w).card = 1 := by rw [hΔcard]; exact h1
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
    have hwp : w = p := by
      have hmem : w ∈ ({p} : Finset (Fin 10)) := hp ▸ hwmem
      simpa using hmem
    rw [hp, ← hwp]
  · right
    have hc3 : ((orbitFinset T w).erase w).card = 3 := by omega
    obtain ⟨i, hi⟩ :=
      eq_support_of_card_three (fun i => (hx i).card_support) hdisj hsubUw hintw hc3
    refine ⟨i, ?_⟩
    rw [Finset.singleton_union, ← Finset.insert_erase hwmem, hi]

private theorem eq_bot_of_orbitFinset_eq_singleton
    (x : Fin 3 → Equiv.Perm (Fin 10)) {w : Fin 10}
    (hfix : ∀ p : Fin 10, w ∉ MulAction.orbit T p → ∀ τ ∈ T, τ p = p)
    (h1 : orbitFinset T w = {w}) : T = ⊥ := by
  classical
  rw [Subgroup.eq_bot_iff_forall]
  intro τ hτ
  apply Equiv.ext
  intro p
  by_cases hp : p = w
  · rw [hp]
    have hmem : τ w ∈ MulAction.orbit T w := by
      rw [mem_orbit_iff_apply]
      exact ⟨τ, hτ, rfl⟩
    have hsingle : τ w ∈ ({w} : Finset (Fin 10)) := by
      rw [← h1]
      exact mem_orbitFinset.mpr hmem
    simpa using hsingle
  · have hpΔ : p ∉ MulAction.orbit T w := by
      intro h
      have hmem : p ∈ orbitFinset T w := mem_orbitFinset.mpr h
      rw [h1, Finset.mem_singleton] at hmem
      exact hp hmem
    have hw' : w ∉ MulAction.orbit T p := by
      intro h
      exact hpΔ ((MulAction.orbit_eq_iff.mpr h) ▸
        (MulAction.mem_orbit_self p : p ∈ MulAction.orbit T p))
    exact hfix p hw' τ hτ

private theorem card_eq_four_of_orbitFinset_eq_insert (hT : IsPGroup 2 T)
    (x : Fin 3 → Equiv.Perm (Fin 10)) (hx : ∀ i, (x i).IsThreeCycle)
    (hxT : ∀ i, x i ∈ Subgroup.normalizer (T : Set (Equiv.Perm (Fin 10))))
    {w : Fin 10} (hw : ∀ j, w ∉ (x j).support)
    (hcover : ∀ p : Fin 10, p ≠ w →
      p ∈ (x 0).support ∪ (x 1).support ∪ (x 2).support)
    (hfix : ∀ p : Fin 10, w ∉ MulAction.orbit T p → ∀ τ ∈ T, τ p = p)
    {i : Fin 3} (hΔ : orbitFinset T w = {w} ∪ (x i).support) : Nat.card T = 4 := by
  classical
  have hstab : MulAction.stabilizer T w = ⊥ :=
    stabilizer_eq_bot hT x hx hxT hw hcover hfix hΔ
  have hΔcard4 : (orbitFinset T w).card = 4 := by
    rw [hΔ, Finset.card_union_of_disjoint, (hx i).card_support]
    · norm_num
    · rw [Finset.disjoint_singleton_left]
      exact hw i
  have horb4 : Fintype.card (MulAction.orbit T w) = 4 := by
    rw [← Nat.card_eq_fintype_card, ← orbitFinset_card, hΔcard4]
  have hstab1 : Fintype.card (MulAction.stabilizer T w) = 1 := by
    rw [← Nat.card_eq_fintype_card, hstab]
    exact Subgroup.card_bot
  have hOS := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := T) (b := w)
  have hTcard : Nat.card T = 4 := by
    rw [Nat.card_eq_fintype_card]
    have h := hOS
    rw [horb4, hstab1, mul_one] at h
    omega
  exact hTcard

theorem card_eq_one_or_four (hT : IsPGroup 2 T) (x : Fin 3 → Equiv.Perm (Fin 10))
    (hx : ∀ i, (x i).IsThreeCycle)
    (hdisj : ∀ i j, i ≠ j → Disjoint (x i).support (x j).support)
    (hxT : ∀ i, x i ∈ Subgroup.normalizer (T : Set (Equiv.Perm (Fin 10)))) :
    Nat.card T = 1 ∨ Nat.card T = 4 := by
  classical
  obtain ⟨w, hw, hcover⟩ := exists_point_outside x hx hdisj
  have hfix : ∀ p : Fin 10, w ∉ MulAction.orbit T p → ∀ τ ∈ T, τ p = p := by
    intro p hp τ hτ
    exact fixes_of_notMem_orbit hT x hx hdisj hxT hcover hp hτ
  rcases orbitFinset_w_form hT x hx hdisj hxT hw hcover with h1 | ⟨i, hi⟩
  · left
    have hbot := eq_bot_of_orbitFinset_eq_singleton x hfix h1
    rw [hbot]
    exact Subgroup.card_bot
  · exact Or.inr (card_eq_four_of_orbitFinset_eq_insert hT x hx hxT hw hcover hfix hi)

theorem ks163P6A10_of_perm
    (h : ∀ B T : Subgroup (Equiv.Perm (Fin 10)), CFSG.Open.IsElemAbelian 3 B →
      Nat.card B = 27 → IsPGroup 2 T →
        B ≤ Subgroup.normalizer (T : Set (Equiv.Perm (Fin 10))) →
          Nat.card T = 1 ∨ Nat.card T = 4) :
    CFSG.RankThree.PartTwo.KFacts.KS163P6A10 := by
  intro K _ _ ⟨e⟩ B hB hBcard T hT hBT
  let φ : MulAut K ≃* Equiv.Perm (Fin 10) :=
    CFSG.GH74.GLS.IVK.Proofs2.altAutEquiv (by norm_num) e
  have hB' : CFSG.Open.IsElemAbelian 3 (B.map φ.toMonoidHom) := hB.map _
  have hBcard' : Nat.card (B.map φ.toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective φ.injective, hBcard]
  have hT' : IsPGroup 2 (T.map φ.toMonoidHom) := hT.map _
  have hle : B.map φ.toMonoidHom ≤
      Subgroup.normalizer (T.map φ.toMonoidHom : Set (Equiv.Perm (Fin 10))) := by
    have h1 : B.map φ.toMonoidHom ≤
        (Subgroup.normalizer (T : Set (MulAut K))).map φ.toMonoidHom :=
      Subgroup.map_mono hBT
    have h2 : (Subgroup.normalizer (T : Set (MulAut K))).map φ.toMonoidHom ≤
        Subgroup.normalizer (T.map φ.toMonoidHom : Set (Equiv.Perm (Fin 10))) :=
      Subgroup.le_normalizer_map φ.toMonoidHom
    exact h1.trans h2
  have hcardmap : Nat.card (T.map φ.toMonoidHom) = Nat.card T :=
    Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective
  have hres := h _ _ hB' hBcard' hT' hle
  rw [hcardmap] at hres
  exact hres

end CFSG.RankThree.PartTwo.KFacts.KF163A10
