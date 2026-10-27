module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import CFSG.Sporadic.Th.Max3.AltNine

public section

open Equiv Equiv.Perm

namespace CFSG.Sporadic.Th.Recog

theorem centralizer_card_transfer (g : alternatingGroup (Fin 9)) :
    Nat.card (Subgroup.centralizer ({g} : Set (alternatingGroup (Fin 9)))) =
      Nat.card ↥(alternatingGroup (Fin 9) ⊓
        Subgroup.centralizer ({(g : Perm (Fin 9))} : Set (Perm (Fin 9)))) := by
  let A := alternatingGroup (Fin 9)
  have hmap : (Subgroup.centralizer ({g} : Set A)).map A.subtype =
      A ⊓ Subgroup.centralizer ({(g : Perm (Fin 9))} : Set (Perm (Fin 9))) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy))⟩
    · rintro ⟨hxA, hx⟩
      exact ⟨⟨x, hxA⟩, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hx)), rfl⟩
  rw [← hmap, Subgroup.card_map_of_injective A.subtype_injective]

theorem two_mul_card_centralizer_of_not_le {g : alternatingGroup (Fin 9)}
    (h : ¬ Subgroup.centralizer ({(g : Perm (Fin 9))} : Set (Perm (Fin 9))) ≤
      alternatingGroup (Fin 9)) :
    2 * Nat.card (Subgroup.centralizer ({g} : Set (alternatingGroup (Fin 9)))) =
      Nat.card (Subgroup.centralizer ({(g : Perm (Fin 9))} : Set (Perm (Fin 9)))) := by
  let A := alternatingGroup (Fin 9)
  let C : Subgroup (Perm (Fin 9)) :=
    Subgroup.centralizer ({(g : Perm (Fin 9))} : Set (Perm (Fin 9)))
  have hrel : A.relIndex C = 2 := by
    have hdvd : A.relIndex C ∣ 2 := by
      rw [← alternatingGroup.index_eq_two (α := Fin 9)]
      exact Subgroup.relIndex_dvd_index_of_normal A C
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
    · exact absurd (Subgroup.relIndex_eq_one.mp h1) h
    · exact h1
  calc 2 * Nat.card (Subgroup.centralizer ({g} : Set (alternatingGroup (Fin 9))))
      = 2 * Nat.card ↥(A ⊓ C) := by rw [centralizer_card_transfer]
    _ = Nat.card ↥C := by rw [← hrel]; exact Subgroup.relIndex_mul_card A C

theorem two_mul_card_centralizer_eq_of_not_le {g : alternatingGroup (Fin 9)} {N : ℕ}
    (hnot : ¬ Subgroup.centralizer ({(g : Perm (Fin 9))} : Set (Perm (Fin 9))) ≤
      alternatingGroup (Fin 9))
    (hS : Nat.card (Subgroup.centralizer
      ({(g : Perm (Fin 9))} : Set (Perm (Fin 9)))) = N) :
    2 * Nat.card (Subgroup.centralizer ({g} : Set (alternatingGroup (Fin 9)))) = N := by
  rw [two_mul_card_centralizer_of_not_le hnot, hS]

theorem not_centralizer_le_alternating_of_cycleType {g : alternatingGroup (Fin 9)}
    {m : Multiset ℕ} (hg : (g : Perm (Fin 9)).cycleType = m)
    (h : ¬ ((∀ c ∈ m, Odd c) ∧ Fintype.card (Fin 9) ≤ m.sum + 1 ∧
      ∀ i, m.count i ≤ 1)) :
    ¬ Subgroup.centralizer ({(g : Perm (Fin 9))} : Set (Perm (Fin 9))) ≤
      alternatingGroup (Fin 9) := by
  intro hle
  apply h
  rw [← hg]
  exact Equiv.Perm.centralizer_le_alternating_iff.mp hle

theorem card_centralizer_of_cycleType_two_two {g : alternatingGroup (Fin 9)}
    (hg : (g : Perm (Fin 9)).cycleType = {2, 2}) :
    Nat.card (Subgroup.centralizer ({g} : Set (alternatingGroup (Fin 9)))) = 480 := by
  have hnot := not_centralizer_le_alternating_of_cycleType hg
    (fun h => absurd (h.1 2 (by decide)) (by decide))
  have h2 := two_mul_card_centralizer_eq_of_not_le (N := 960) hnot
    (by rw [Equiv.Perm.nat_card_centralizer, hg]; decide)
  omega

theorem card_centralizer_of_cycleType_two_two_two_two {g : alternatingGroup (Fin 9)}
    (hg : (g : Perm (Fin 9)).cycleType = {2, 2, 2, 2}) :
    Nat.card (Subgroup.centralizer ({g} : Set (alternatingGroup (Fin 9)))) = 192 := by
  have hnot := not_centralizer_le_alternating_of_cycleType hg
    (fun h => absurd (h.1 2 (by decide)) (by decide))
  have h2 := two_mul_card_centralizer_eq_of_not_le (N := 384) hnot
    (by rw [Equiv.Perm.nat_card_centralizer, hg]; decide)
  omega

theorem card_centralizer_of_cycleType_three_three {g : alternatingGroup (Fin 9)}
    (hg : (g : Perm (Fin 9)).cycleType = {3, 3}) :
    Nat.card (Subgroup.centralizer ({g} : Set (alternatingGroup (Fin 9)))) = 54 := by
  have hnot := not_centralizer_le_alternating_of_cycleType hg
    (fun h => by have := h.2.2 3; norm_num at this)
  have h2 := two_mul_card_centralizer_eq_of_not_le (N := 108) hnot
    (by rw [Equiv.Perm.nat_card_centralizer, hg]; decide)
  omega

theorem card_centralizer_of_cycleType_three_three_three {g : alternatingGroup (Fin 9)}
    (hg : (g : Perm (Fin 9)).cycleType = {3, 3, 3}) :
    Nat.card (Subgroup.centralizer ({g} : Set (alternatingGroup (Fin 9)))) = 81 := by
  have hnot := not_centralizer_le_alternating_of_cycleType hg
    (fun h => by have := h.2.2 3; norm_num at this)
  have h2 := two_mul_card_centralizer_eq_of_not_le (N := 162) hnot
    (by rw [Equiv.Perm.nat_card_centralizer, hg]; decide)
  omega

theorem card_centralizer_of_cycleType_seven {g : alternatingGroup (Fin 9)}
    (hg : (g : Perm (Fin 9)).cycleType = {7}) :
    Nat.card (Subgroup.centralizer ({g} : Set (alternatingGroup (Fin 9)))) = 7 := by
  have hnot := not_centralizer_le_alternating_of_cycleType hg
    (fun h => by have := h.2.1; norm_num at this)
  have h2 := two_mul_card_centralizer_eq_of_not_le (N := 14) hnot
    (by rw [Equiv.Perm.nat_card_centralizer, hg]; decide)
  omega

theorem cycleType_of_orderOf_eq_two {g : alternatingGroup (Fin 9)} (hg : orderOf g = 2) :
    (g : Perm (Fin 9)).cycleType = {2, 2} ∨ (g : Perm (Fin 9)).cycleType = {2, 2, 2, 2} := by
  apply CFSG.Sporadic.Th.Max3.cycleType_of_orderOf_eq_two
  · rwa [Subgroup.orderOf_coe]
  · exact Equiv.Perm.mem_alternatingGroup.mp g.2

theorem cycleType_of_orderOf_eq_three {g : alternatingGroup (Fin 9)} (hg : orderOf g = 3) :
    (g : Perm (Fin 9)).cycleType = {3} ∨ (g : Perm (Fin 9)).cycleType = {3, 3} ∨
      (g : Perm (Fin 9)).cycleType = {3, 3, 3} := by
  have hg' : orderOf (g : Perm (Fin 9)) = 3 := by rwa [Subgroup.orderOf_coe]
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order
    (σ := (g : Perm (Fin 9))) (by rw [hg']; decide)
  rw [hg'] at hn
  have hle : (g : Perm (Fin 9)).cycleType.sum ≤ 9 := by
    rw [Equiv.Perm.sum_cycleType]
    exact (Finset.card_le_univ _).trans (by simp)
  rw [hn, Multiset.sum_replicate, smul_eq_mul] at hle
  have hn' : n + 1 = 1 ∨ n + 1 = 2 ∨ n + 1 = 3 := by omega
  rcases hn' with h | h | h
  · left; rw [hn, h]; rfl
  · right; left; rw [hn, h]; rfl
  · right; right; rw [hn, h]; rfl

theorem cycleType_of_orderOf_eq_seven {g : alternatingGroup (Fin 9)} (hg : orderOf g = 7) :
    (g : Perm (Fin 9)).cycleType = {7} := by
  have hg' : orderOf (g : Perm (Fin 9)) = 7 := by rwa [Subgroup.orderOf_coe]
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order
    (σ := (g : Perm (Fin 9))) (by rw [hg']; decide)
  rw [hg'] at hn
  have hle : (g : Perm (Fin 9)).cycleType.sum ≤ 9 := by
    rw [Equiv.Perm.sum_cycleType]
    exact (Finset.card_le_univ _).trans (by simp)
  rw [hn, Multiset.sum_replicate, smul_eq_mul] at hle
  have hn1 : n + 1 = 1 := by omega
  rw [hn, hn1]; rfl

theorem card_centralizer_le_of_orderOf_eq_two {g : alternatingGroup (Fin 9)}
    (hg : orderOf g = 2) :
    Nat.card (Subgroup.centralizer ({g} : Set (alternatingGroup (Fin 9)))) ≤ 480 := by
  rcases cycleType_of_orderOf_eq_two hg with h | h
  · rw [card_centralizer_of_cycleType_two_two h]
  · rw [card_centralizer_of_cycleType_two_two_two_two h]
    norm_num

theorem card_centralizer_of_orderOf_eq_seven {g : alternatingGroup (Fin 9)}
    (hg : orderOf g = 7) :
    Nat.card (Subgroup.centralizer ({g} : Set (alternatingGroup (Fin 9)))) = 7 :=
  card_centralizer_of_cycleType_seven (cycleType_of_orderOf_eq_seven hg)

theorem exists_odd_mem_centralizer_of_orderOf_eq_three {g : Perm (Fin 9)}
    (hg : orderOf g = 3) :
    ∃ c : Perm (Fin 9), c ∈ Subgroup.centralizer {g} ∧ sign c = -1 := by
  by_contra h
  have hCA : Subgroup.centralizer {g} ≤ alternatingGroup (Fin 9) := by
    intro c hc
    rw [Equiv.Perm.mem_alternatingGroup]
    rcases Int.units_eq_one_or (sign c) with hs | hs
    · exact hs
    · exact absurd ⟨c, hc, hs⟩ h
  obtain ⟨-, hc2, hc3⟩ := Equiv.Perm.centralizer_le_alternating_iff.mp hCA
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (σ := g) (by rw [hg]; decide)
  rw [hg] at hn
  have hsum : g.cycleType.sum = (n + 1) * 3 := by
    rw [hn, Multiset.sum_replicate, smul_eq_mul]
  have hcard : 9 ≤ g.cycleType.sum + 1 := by simpa using hc2
  have hle1 : n + 1 ≤ 1 := by
    have hcnt : g.cycleType.count 3 = n + 1 := by
      rw [hn, Multiset.count_replicate_self]
    have := hc3 3
    omega
  omega

theorem exists_odd_mem_centralizer_of_orderOf_eq_seven {g : Perm (Fin 9)}
    (hg : orderOf g = 7) :
    ∃ c : Perm (Fin 9), c ∈ Subgroup.centralizer {g} ∧ sign c = -1 := by
  by_contra h
  have hCA : Subgroup.centralizer {g} ≤ alternatingGroup (Fin 9) := by
    intro c hc
    rw [Equiv.Perm.mem_alternatingGroup]
    rcases Int.units_eq_one_or (sign c) with hs | hs
    · exact hs
    · exact absurd ⟨c, hc, hs⟩ h
  obtain ⟨-, hc2, -⟩ := Equiv.Perm.centralizer_le_alternating_iff.mp hCA
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (σ := g) (by rw [hg]; decide)
  rw [hg] at hn
  have hsum : g.cycleType.sum = (n + 1) * 7 := by
    rw [hn, Multiset.sum_replicate, smul_eq_mul]
  have hle : g.cycleType.sum ≤ 9 := by
    rw [Equiv.Perm.sum_cycleType]
    exact (Finset.card_le_univ _).trans (by simp)
  have hcard : 9 ≤ g.cycleType.sum + 1 := by simpa using hc2
  omega

theorem exists_conj_in_alternating_of_isConj {σ τ : Perm (Fin 9)}
    (hconj : IsConj σ τ)
    (hodd : ∃ c : Perm (Fin 9), c ∈ Subgroup.centralizer {σ} ∧ sign c = -1) :
    ∃ π : alternatingGroup (Fin 9),
      (π : Perm (Fin 9)) * σ * (π : Perm (Fin 9))⁻¹ = τ := by
  obtain ⟨π, hπ⟩ := isConj_iff.mp hconj
  by_cases hπs : sign π = 1
  · exact ⟨⟨π, Equiv.Perm.mem_alternatingGroup.mpr hπs⟩, hπ⟩
  · obtain ⟨c, hcC, hcs⟩ := hodd
    have hc_conj : c * σ * c⁻¹ = σ := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hcC, mul_assoc, mul_inv_cancel, mul_one]
    refine ⟨⟨π * c, ?_⟩, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, hcs]
      rcases Int.units_eq_one_or (sign π) with h1 | h1
      · exact absurd h1 hπs
      · rw [h1]; decide
    · calc (π * c : Perm (Fin 9)) * σ * (π * c : Perm (Fin 9))⁻¹
          = π * (c * σ * c⁻¹) * π⁻¹ := by group
        _ = π * σ * π⁻¹ := by rw [hc_conj]
        _ = τ := hπ

theorem isConj_iff_cycleType_of_orderOf_eq_three {g h : alternatingGroup (Fin 9)}
    (hg : orderOf g = 3) :
    IsConj g h ↔ (g : Perm (Fin 9)).cycleType = (h : Perm (Fin 9)).cycleType := by
  constructor
  · intro hconj
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    have hc' : (c : Perm (Fin 9)) * (g : Perm (Fin 9)) * (c : Perm (Fin 9))⁻¹ =
        (h : Perm (Fin 9)) := congrArg Subtype.val hc
    exact Equiv.Perm.isConj_iff_cycleType_eq.mp (isConj_iff.mpr ⟨(c : Perm (Fin 9)), hc'⟩)
  · intro hct
    have hg' : orderOf (g : Perm (Fin 9)) = 3 := by rwa [Subgroup.orderOf_coe]
    obtain ⟨π, hπ⟩ := exists_conj_in_alternating_of_isConj
      (Equiv.Perm.isConj_iff_cycleType_eq.mpr hct)
      (exists_odd_mem_centralizer_of_orderOf_eq_three hg')
    exact isConj_iff.mpr ⟨π, Subtype.ext hπ⟩

theorem isConj_of_orderOf_eq_seven {g h : alternatingGroup (Fin 9)}
    (hg : orderOf g = 7) (hh : orderOf h = 7) : IsConj g h := by
  have hg' : (g : Perm (Fin 9)).cycleType = {7} := cycleType_of_orderOf_eq_seven hg
  have hh' : (h : Perm (Fin 9)).cycleType = {7} := cycleType_of_orderOf_eq_seven hh
  have hct : (g : Perm (Fin 9)).cycleType = (h : Perm (Fin 9)).cycleType := by rw [hg', hh']
  have hodd := exists_odd_mem_centralizer_of_orderOf_eq_seven
    (g := (g : Perm (Fin 9))) (by rwa [Subgroup.orderOf_coe])
  obtain ⟨π, hπ⟩ := exists_conj_in_alternating_of_isConj
    (Equiv.Perm.isConj_iff_cycleType_eq.mpr hct) hodd
  exact isConj_iff.mpr ⟨π, Subtype.ext hπ⟩

theorem isCycle_of_orderOf_eq_five {σ : Perm (Fin 9)} (h : orderOf σ = 5) : σ.IsCycle := by
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (σ := σ) (by rw [h]; decide)
  rw [h] at hn
  have hle : σ.cycleType.sum ≤ 9 := by
    rw [Equiv.Perm.sum_cycleType]
    exact (Finset.card_le_univ _).trans (by simp)
  rw [hn, Multiset.sum_replicate, smul_eq_mul] at hle
  have hn1 : n + 1 = 1 := by omega
  have hct : σ.cycleType = {5} := by rw [hn, hn1]; rfl
  exact Equiv.Perm.card_cycleType_eq_one.mp (by rw [hct]; decide)

theorem support_subset_or_compl_of_orderOf_eq_five {T : Finset (Fin 9)}
    {σ : alternatingGroup (Fin 9)} (hσ5 : orderOf σ = 5)
    (hσT : ∀ x, (σ : Perm (Fin 9)) x ∈ T ↔ x ∈ T) :
    (σ : Perm (Fin 9)).support ⊆ T ∨ (σ : Perm (Fin 9)).support ⊆ Tᶜ := by
  have hσ' : orderOf (σ : Perm (Fin 9)) = 5 := by rwa [Subgroup.orderOf_coe]
  have hcyc : (σ : Perm (Fin 9)).IsCycle := isCycle_of_orderOf_eq_five hσ'
  obtain ⟨x, hxne, hxsame⟩ := hcyc
  have hinv : ∀ k y, ((σ : Perm (Fin 9)) ^ k) y ∈ T ↔ y ∈ T := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [pow_succ, Equiv.Perm.mul_apply]
      rw [ih, hσT y]
  by_cases hxT : x ∈ T
  · left
    intro y hy
    have hyne : (σ : Perm (Fin 9)) y ≠ y := Equiv.Perm.mem_support.mp hy
    obtain ⟨i, hi⟩ := Equiv.Perm.IsCycle.exists_pow_eq ⟨x, hxne, hxsame⟩ hxne hyne
    rw [← hi]
    exact (hinv i x).mpr hxT
  · right
    intro y hy
    rw [Finset.mem_compl]
    intro hyT
    have hyne : (σ : Perm (Fin 9)) y ≠ y := Equiv.Perm.mem_support.mp hy
    obtain ⟨i, hi⟩ := Equiv.Perm.IsCycle.exists_pow_eq ⟨x, hxne, hxsame⟩ hxne hyne
    have : y ∈ T ↔ x ∈ T := by
      rw [← hi]
      exact hinv i x
    exact hxT (this.mp hyT)

theorem card_support_le_six_of_orderOf_eq_two_of_cycleType_three {c τ : Perm (Fin 9)}
    (hc : c.cycleType = {3}) (hτ : orderOf τ = 2) (hcomm : Commute τ c) :
    τ.support.card ≤ 6 := by
  have hc3 : c.support.card = 3 := by
    rw [← Equiv.Perm.sum_cycleType, hc]
    decide
  have hccycle : c.IsCycle := by
    rw [← Equiv.Perm.card_cycleType_eq_one, hc]
    decide
  obtain ⟨hpres, hmem⟩ := (Equiv.Perm.IsCycle.commute_iff' hccycle).mp hcomm
  let f : Perm ↥c.support := τ.subtypePerm hpres
  have hf_mem : f ∈ Subgroup.zpowers c.subtypePermOfSupport := hmem
  have hτ2 : τ ^ 2 = 1 := by
    have h := pow_orderOf_eq_one τ
    rwa [hτ] at h
  have hf2 : f * f = 1 := by
    ext x
    have hx := congrFun (congrArg (fun g : Perm (Fin 9) => (g : Fin 9 → Fin 9)) hτ2)
      (x : Fin 9)
    dsimp only [f]
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.subtypePerm_apply]
    rw [show τ (τ ↑x) = ↑x by simpa [pow_two] using hx]
    simp
  have hford : orderOf f ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_two]
    exact hf2
  have hcsub_order : orderOf c.subtypePermOfSupport = 3 := by
    have hof : Equiv.Perm.ofSubtype c.subtypePermOfSupport = c := by
      unfold Equiv.Perm.subtypePermOfSupport
      exact Equiv.Perm.ofSubtype_subtypePerm
        (fun x => Equiv.Perm.mem_support_iff_of_commute (Commute.refl c) x)
        (fun x hx => Equiv.Perm.mem_support.mpr hx)
    have h := orderOf_injective (Equiv.Perm.ofSubtype (p := fun x => x ∈ c.support))
      Equiv.Perm.ofSubtype_injective c.subtypePermOfSupport
    rw [hof, Equiv.Perm.IsCycle.orderOf hccycle, hc3] at h
    exact h.symm
  have hford3 : orderOf f ∣ 3 := by
    rw [← hcsub_order]
    exact orderOf_dvd_of_mem_zpowers hf_mem
  have hf1 : f = 1 := by
    have h1 : orderOf f ∣ 1 := by
      have h := Nat.dvd_gcd hford hford3
      simpa using h
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
  have hsupp : τ.support ⊆ c.supportᶜ := by
    intro x hx
    rw [Finset.mem_compl]
    intro hxc
    have hfix : τ x = x := by
      have happ := congrArg (fun g : Perm ↥c.support => g ⟨x, hxc⟩) hf1
      have := congrArg Subtype.val happ
      simpa [f] using this
    exact (Equiv.Perm.mem_support.mp hx) hfix
  calc τ.support.card ≤ (c.supportᶜ : Finset (Fin 9)).card := Finset.card_le_card hsupp
    _ = 9 - c.support.card := by rw [Finset.card_compl, Fintype.card_fin]
    _ = 6 := by omega

@[expose] def omegaOf (T : Finset (Fin 9)) : Finset (Fin 9) := if 5 ≤ T.card then T else Tᶜ

theorem omegaOf_of_le {T : Finset (Fin 9)} (h : 5 ≤ T.card) : omegaOf T = T := by
  simp [omegaOf, h]

theorem omegaOf_of_not_le {T : Finset (Fin 9)} (h : ¬ 5 ≤ T.card) : omegaOf T = Tᶜ := by
  simp [omegaOf, h]

theorem card_omegaOf {T : Finset (Fin 9)} (hT : Even T.card) (hne : T.Nonempty) :
    5 ≤ (omegaOf T).card ∧ (omegaOf T).card ≤ 8 := by
  by_cases h5 : 5 ≤ T.card
  · rw [omegaOf_of_le h5]
    refine ⟨h5, ?_⟩
    rcases hT with ⟨k, hk⟩
    have hle := Finset.card_le_univ T
    rw [Fintype.card_fin] at hle
    omega
  · rw [omegaOf_of_not_le h5, Finset.card_compl, Fintype.card_fin]
    have hpos : 0 < T.card := Finset.card_pos.mpr hne
    rcases hT with ⟨k, hk⟩
    omega

theorem support_subset_omegaOf {T : Finset (Fin 9)} {σ : alternatingGroup (Fin 9)}
    (hσ5 : orderOf σ = 5)
    (hσT : ∀ x, (σ : Perm (Fin 9)) x ∈ T ↔ x ∈ T) :
    (σ : Perm (Fin 9)).support ⊆ omegaOf T := by
  have hσ' : orderOf (σ : Perm (Fin 9)) = 5 := by rwa [Subgroup.orderOf_coe]
  have hcyc : (σ : Perm (Fin 9)).IsCycle := isCycle_of_orderOf_eq_five hσ'
  have hsuppcard : (σ : Perm (Fin 9)).support.card = 5 := by
    rw [← Equiv.Perm.IsCycle.orderOf hcyc, hσ']
  rcases support_subset_or_compl_of_orderOf_eq_five hσ5 hσT with hsub | hsub
  · have h5 : 5 ≤ T.card := by
      calc 5 = (σ : Perm (Fin 9)).support.card := hsuppcard.symm
        _ ≤ T.card := Finset.card_le_card hsub
    rwa [omegaOf_of_le h5]
  · have h5 : ¬ 5 ≤ T.card := by
      intro h
      have hle : 5 ≤ Tᶜ.card := by
        calc 5 = (σ : Perm (Fin 9)).support.card := hsuppcard.symm
          _ ≤ Tᶜ.card := Finset.card_le_card hsub
      rw [Finset.card_compl, Fintype.card_fin] at hle
      omega
    rwa [omegaOf_of_not_le h5]

@[expose] def altEmbed (Ω : Finset (Fin 9)) : alternatingGroup Ω →* alternatingGroup (Fin 9) where
  toFun f := ⟨Equiv.Perm.ofSubtype (f : Perm Ω), by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_ofSubtype]
    exact f.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' := by
    intro a b
    apply Subtype.ext
    simp

theorem altEmbed_apply (Ω : Finset (Fin 9)) (f : alternatingGroup Ω) :
    (altEmbed Ω f : Perm (Fin 9)) = Equiv.Perm.ofSubtype (f : Perm Ω) := by
  rfl

theorem altEmbed_mem_iff (Ω : Finset (Fin 9)) (f : alternatingGroup Ω) (x : Fin 9) :
    (altEmbed Ω f : Perm (Fin 9)) x ∈ Ω ↔ x ∈ Ω := by
  rw [altEmbed_apply]
  exact Equiv.Perm.ofSubtype_apply_mem_iff_mem (f : Perm Ω) x

theorem altEmbed_injective (Ω : Finset (Fin 9)) : Function.Injective (altEmbed Ω) := by
  intro a b h
  apply Subtype.ext
  exact Equiv.Perm.ofSubtype_injective
    (by simpa only [altEmbed_apply] using congrArg Subtype.val h)

@[expose] def fixingSubgroup (Ω : Finset (Fin 9)) : Subgroup (alternatingGroup (Fin 9)) where
  carrier := {σ | ∀ x, x ∉ Ω → (σ : Perm (Fin 9)) x = x}
  one_mem' := by intro x _; rfl
  mul_mem' := by
    intro a b ha hb x hx
    change ((a : Perm (Fin 9)) * (b : Perm (Fin 9))) x = x
    rw [Equiv.Perm.mul_apply, hb x hx, ha x hx]
  inv_mem' := by
    intro a ha x hx
    change (a : Perm (Fin 9))⁻¹ x = x
    have hmap : ∀ y, y ∈ Ω → (a : Perm (Fin 9)) y ∈ Ω := by
      intro y hy
      by_contra hnot
      have hfix := ha ((a : Perm (Fin 9)) y) hnot
      have hay : (a : Perm (Fin 9)) y = y := (a : Perm (Fin 9)).injective hfix
      exact hnot (by rw [hay]; exact hy)
    have hxinv : (a : Perm (Fin 9))⁻¹ x ∉ Ω := fun hmem => hx (by simpa using hmap _ hmem)
    have hfix := ha ((a : Perm (Fin 9))⁻¹ x) hxinv
    simpa using hfix.symm

theorem mem_fixingSubgroup {Ω : Finset (Fin 9)} {σ : alternatingGroup (Fin 9)} :
    σ ∈ fixingSubgroup Ω ↔ ∀ x, x ∉ Ω → (σ : Perm (Fin 9)) x = x := Iff.rfl

theorem fixingSubgroup_eq_map (Ω : Finset (Fin 9)) :
    fixingSubgroup Ω = (⊤ : Subgroup (alternatingGroup Ω)).map (altEmbed Ω) := by
  ext σ
  constructor
  · intro hσ
    have hpres : ∀ x : Fin 9, (σ : Perm (Fin 9)) x ∈ Ω ↔ x ∈ Ω := by
      intro x
      constructor
      · intro hx
        by_contra hnot
        exact hnot (hσ x hnot ▸ hx)
      · intro hx
        by_contra hnot
        have hfix := hσ ((σ : Perm (Fin 9)) x) hnot
        have hx' : (σ : Perm (Fin 9)) x = x := (σ : Perm (Fin 9)).injective hfix
        exact hnot (by rw [hx']; exact hx)
    let f : Perm ↥Ω := (σ : Perm (Fin 9)).subtypePerm hpres
    have hof : Equiv.Perm.ofSubtype f = (σ : Perm (Fin 9)) := by
      dsimp only [f]
      exact Equiv.Perm.ofSubtype_subtypePerm hpres (fun x hx => by
        by_contra hnot
        exact hx (hσ x hnot))
    have hfA : f ∈ alternatingGroup Ω := by
      rw [Equiv.Perm.mem_alternatingGroup]
      have hsign := Equiv.Perm.sign_ofSubtype f
      rw [hof, Equiv.Perm.mem_alternatingGroup.mp σ.2] at hsign
      exact hsign.symm
    exact ⟨⟨f, hfA⟩, Subgroup.mem_top _, Subtype.ext (by rw [altEmbed_apply]; exact hof)⟩
  · rintro ⟨f, -, rfl⟩
    intro x hx
    rw [altEmbed_apply]
    exact Equiv.Perm.ofSubtype_apply_of_not_mem (f : Perm Ω) hx

theorem closure_orderOf_eq_five_eq_top (Ω : Finset (Fin 9))
    (h5 : 5 ≤ Ω.card) (h8 : Ω.card ≤ 8) :
    Subgroup.closure {σ : alternatingGroup Ω | orderOf σ = 5} = ⊤ := by
  let S : Set (alternatingGroup Ω) := {σ | orderOf σ = 5}
  have hnormal : (Subgroup.closure S).Normal := by
    apply Subgroup.Normal.mk
    intro n hn g
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
        change orderOf x = 5 at hx
        refine Subgroup.subset_closure ?_
        change orderOf (g * x * g⁻¹) = 5
        have hord : orderOf (g * x * g⁻¹) = orderOf x := by
          have hsc : SemiconjBy g x (g * x * g⁻¹) := by
            dsimp [SemiconjBy]
            group
          exact (SemiconjBy.orderOf_eq g hsc).symm
        rw [hord]
        exact hx
    | one => simp
    | mul x y hx hy ihx ihy =>
        rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
        exact Subgroup.mul_mem _ ihx ihy
    | inv x hx ih =>
        rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
        exact Subgroup.inv_mem _ ih
  haveI : (Subgroup.closure S).Normal := hnormal
  have hdvd : 5 ∣ Fintype.card (alternatingGroup Ω) := by
    haveI : Nontrivial ↥Ω :=
      ⟨Fintype.one_lt_card_iff.mp (by rw [Fintype.card_coe]; omega)⟩
    rw [← Nat.card_eq_fintype_card, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_coe]
    interval_cases hc : Ω.card <;> norm_num [Nat.factorial]
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 5 hdvd
  have hxS : x ∈ Subgroup.closure S := Subgroup.subset_closure hx
  have hxne : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx
    norm_num at hx
  have hne : Subgroup.closure S ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hxS
    exact hxne hxS
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top
    (α := ↥Ω) (by rw [Nat.card_eq_fintype_card, Fintype.card_coe]; omega)
    (N := Subgroup.closure S) with h | h
  · exact absurd h hne
  · exact h

theorem closure_fiveCycles_stabilizer_eq_fixingSubgroup {T : Finset (Fin 9)}
    (hT : Even T.card) (hne : T.Nonempty) :
    Subgroup.closure {σ : alternatingGroup (Fin 9) |
        orderOf σ = 5 ∧ ∀ x, (σ : Perm (Fin 9)) x ∈ T ↔ x ∈ T}
      = fixingSubgroup (omegaOf T) := by
  let Ω := omegaOf T
  have hΩ := card_omegaOf hT hne
  have hΩpart : Ω = T ∨ Ω = Tᶜ := by
    change omegaOf T = T ∨ omegaOf T = Tᶜ
    unfold omegaOf
    split_ifs with h
    · exact Or.inl rfl
    · exact Or.inr rfl
  let SΩ : Set (alternatingGroup Ω) := {f | orderOf f = 5}
  let S : Set (alternatingGroup (Fin 9)) :=
    {σ | orderOf σ = 5 ∧ ∀ x, (σ : Perm (Fin 9)) x ∈ T ↔ x ∈ T}
  have hgen : Subgroup.closure SΩ = ⊤ := closure_orderOf_eq_five_eq_top Ω hΩ.1 hΩ.2
  have himage : altEmbed Ω '' SΩ = S := by
    ext σ
    constructor
    · rintro ⟨f, hf, rfl⟩
      refine ⟨?_, ?_⟩
      · dsimp only [SΩ] at hf
        rw [orderOf_injective (altEmbed Ω) (altEmbed_injective Ω) f]
        exact hf
      · intro x
        have hpres := altEmbed_mem_iff Ω f x
        rcases hΩpart with hΩT | hΩT
        · rwa [← hΩT]
        · have hT' : T = Ωᶜ := by rw [hΩT]; simp
          rw [hT']
          simpa [Finset.mem_compl] using not_congr hpres
    · rintro ⟨hσ5, hσT⟩
      have hsupp := support_subset_omegaOf hσ5 hσT
      have hfix : σ ∈ fixingSubgroup Ω := by
        rw [mem_fixingSubgroup]
        intro x hx
        by_contra hne'
        exact hx (hsupp (Equiv.Perm.mem_support.mpr hne'))
      rw [fixingSubgroup_eq_map] at hfix
      obtain ⟨f, -, hfσ⟩ := Subgroup.mem_map.mp hfix
      refine ⟨f, ?_, hfσ⟩
      dsimp only [SΩ]
      show orderOf f = 5
      rw [← orderOf_injective (altEmbed Ω) (altEmbed_injective Ω) f]
      rwa [hfσ]
  change Subgroup.closure S = fixingSubgroup Ω
  rw [fixingSubgroup_eq_map, ← hgen, MonoidHom.map_closure, himage]

def conjA (σ : Perm (Fin 9)) : alternatingGroup (Fin 9) ≃* alternatingGroup (Fin 9) :=
  MulAut.conjNormal (H := alternatingGroup (Fin 9)) σ

theorem conjA_apply (σ : Perm (Fin 9)) (g : alternatingGroup (Fin 9)) :
    (conjA σ g : Perm (Fin 9)) = σ * (g : Perm (Fin 9)) * σ⁻¹ :=
  MulAut.conjNormal_apply σ g

end CFSG.Sporadic.Th.Recog
