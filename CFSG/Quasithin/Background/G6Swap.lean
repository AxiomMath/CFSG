module

public import CFSG.Quasithin.Background.G6Natural
public import CFSG.Quasithin.Background.G6PGroup
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Quasithin

namespace G6

open Finset Equiv


private theorem card_symmDiff_le' {α : Type*} [DecidableEq α] (s t : Finset α) :
    (symmDiff s t).card ≤ s.card + t.card := by
  calc (symmDiff s t).card ≤ (s ∪ t).card := by
        apply Finset.card_le_card
        rw [symmDiff_def]
        exact Finset.union_subset_union Finset.sdiff_subset Finset.sdiff_subset
    _ ≤ s.card + t.card := Finset.card_union_le s t

private theorem case1 {n : ℕ} {σ : Equiv.Perm (Fin n)} (p : Fin n) (hp : σ (σ p) ≠ p) :
    ∃ S₁ S₂ : Finset (Fin n), S₁.card = 2 ∧ S₂.card = 2 ∧
      (symmDiff (S₁.image σ) S₁).Nonempty ∧
      (symmDiff (S₂.image σ) S₂).Nonempty ∧
      (symmDiff (symmDiff (S₁.image σ) S₁) (symmDiff (S₂.image σ) S₂)).Nonempty ∧
      (symmDiff (symmDiff (S₁.image σ) S₁) (symmDiff (S₂.image σ) S₂)).card ≤ 4 := by
  classical
  obtain ⟨q, hq⟩ : ∃ q, σ p = q := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, σ q = r := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, σ r = s := ⟨_, rfl⟩
  have hrp : r ≠ p := by
    intro h; apply hp; rw [hq, hr]; exact h
  have hqp : q ≠ p := by
    intro h; apply hp
    have h1 : σ p = p := hq.trans h
    rw [h1, h1]
  have hrq : r ≠ q := by
    intro h; apply hqp; apply σ.injective; rw [hq]; rw [hr]; exact h
  have hsq : s ≠ q := by
    intro h; apply hrp; apply σ.injective; rw [hs, hq]; exact h
  have hsr : s ≠ r := by
    intro h; apply hrq; apply σ.injective; rw [hs, hr]; exact h
  have hpq : p ≠ q := hqp.symm
  have hpr : p ≠ r := hrp.symm
  have hqr : q ≠ r := hrq.symm
  have hqs : q ≠ s := hsq.symm
  have hrs : r ≠ s := hsr.symm
  have i1 : Finset.image σ {p, q} = {q, r} := by
    rw [Finset.image_insert, Finset.image_singleton, hq, hr]
  have i2 : Finset.image σ {q, r} = {r, s} := by
    rw [Finset.image_insert, Finset.image_singleton, hr, hs]
  refine ⟨{p, q}, {q, r}, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Finset.card_insert_of_notMem, hpq]
  · simp [Finset.card_insert_of_notMem, hqr]
  · rw [i1]
    exact ⟨p, by simp [Finset.mem_symmDiff, hpq, hpr]⟩
  · rw [i2]
    exact ⟨q, by simp [Finset.mem_symmDiff, hqr, hqs]⟩
  · rw [i1, i2]
    exact ⟨r, by simp [Finset.mem_symmDiff, hrp, hrq, hrs]⟩
  · rw [i1, i2]
    have hsub : symmDiff (symmDiff ({q, r} : Finset (Fin n)) {p, q}) (symmDiff {r, s} {q, r}) ⊆ ({p, q, r, s} : Finset (Fin n)) := by
      intro i hi
      simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      tauto
    exact (Finset.card_le_card hsub).trans Finset.card_le_four

private theorem case2 {n : ℕ} (hn : 5 ≤ n) {σ : Equiv.Perm (Fin n)} (h1 : σ ≠ 1) (h2 : ¬ σ.IsSwap)
    (hinv : ∀ p, σ (σ p) = p) :
    ∃ S₁ S₂ : Finset (Fin n), S₁.card = 2 ∧ S₂.card = 2 ∧
      (symmDiff (S₁.image σ) S₁).Nonempty ∧
      (symmDiff (S₂.image σ) S₂).Nonempty ∧
      (symmDiff (symmDiff (S₁.image σ) S₁) (symmDiff (S₂.image σ) S₂)).Nonempty ∧
      (symmDiff (symmDiff (S₁.image σ) S₁) (symmDiff (S₂.image σ) S₂)).card ≤ 4 := by
  classical
  obtain ⟨p, hp⟩ : ∃ p, σ p ≠ p := by
    by_contra hcon
    push Not at hcon
    exact h1 (Equiv.ext hcon)
  obtain ⟨q, hq⟩ : ∃ q, σ p = q := ⟨_, rfl⟩
  have hqp : q ≠ p := fun h => hp (hq.trans h)
  have hqq : σ q = p := by rw [← hq, hinv]
  have hpq : p ≠ q := hqp.symm
  obtain ⟨r, hrs, hrp, hrq⟩ : ∃ r, σ r ≠ r ∧ r ≠ p ∧ r ≠ q := by
    by_contra hcon
    push Not at hcon
    apply h2
    refine ⟨p, q, hpq, Equiv.ext fun i => ?_⟩
    by_cases hip : i = p
    · subst hip
      rw [hq, Equiv.swap_apply_left]
    · by_cases hiq : i = q
      · subst hiq
        rw [hqq, Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne hip hiq]
        by_contra hne
        exact hiq (hcon i hne hip)
  obtain ⟨s, hs⟩ : ∃ s, σ r = s := ⟨_, rfl⟩
  have hss : σ s = r := by rw [← hs, hinv]
  have hsr : s ≠ r := fun h => hrs (hs.trans h)
  have hsp : s ≠ p := by
    intro h; apply hrq
    rw [← hss, h, hq]
  have hsq : s ≠ q := by
    intro h; apply hrp
    rw [← hss, h, hqq]
  obtain ⟨t, ht⟩ : ∃ t : Fin n, t ∉ ({p, q, r, s} : Finset (Fin n)) := by
    have hlt : ({p, q, r, s} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      exact lt_of_le_of_lt Finset.card_le_four (by omega)
    exact Finset.exists_mem_notMem_of_card_lt_card hlt |>.imp fun t ht => ht.2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
  obtain ⟨htp, htq, htr, hts⟩ := ht
  obtain ⟨t', ht'⟩ : ∃ t', σ t = t' := ⟨_, rfl⟩
  have ht't : σ t' = t := by rw [← ht', hinv]
  have ht'p : t' ≠ p := by
    intro h; apply htq; rw [← ht't, h, hq]
  have ht'q : t' ≠ q := by
    intro h; apply htp; rw [← ht't, h, hqq]
  have ht'r : t' ≠ r := by
    intro h; apply hts; rw [← ht't, h, hs]
  have ht's : t' ≠ s := by
    intro h; apply htr; rw [← ht't, h, hss]
  have i1 : Finset.image σ {p, r} = {q, s} := by
    rw [Finset.image_insert, Finset.image_singleton, hq, hs]
  have i2 : Finset.image σ {p, t} = {q, t'} := by
    rw [Finset.image_insert, Finset.image_singleton, hq, ht']
  have hpt : p ≠ t := fun h => htp h.symm
  have hrt : r ≠ t := fun h => htr h.symm
  have hpr : p ≠ r := hrp.symm
  have hqr : q ≠ r := hrq.symm
  have hps : p ≠ s := hsp.symm
  have hqs : q ≠ s := hsq.symm
  have hrs' : r ≠ s := hsr.symm
  refine ⟨{p, r}, {p, t}, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Finset.card_insert_of_notMem, hpr]
  · simp [Finset.card_insert_of_notMem, hpt]
  · rw [i1]
    exact ⟨p, by simp [Finset.mem_symmDiff, hpq, hps]⟩
  · rw [i2]
    exact ⟨p, by simp [Finset.mem_symmDiff, hpq, ht'p.symm]⟩
  · rw [i1, i2]
    exact ⟨r, by simp [Finset.mem_symmDiff, hrq, hrs', hrp, hrt, ht'r.symm]⟩
  · rw [i1, i2]
    have hsub : symmDiff (symmDiff ({q, s} : Finset (Fin n)) {p, r}) (symmDiff {q, t'} {p, t}) ⊆
        ({r, s, t, t'} : Finset (Fin n)) := by
      intro i hi
      simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      clear hinv h1 h2 hq hqq hs hss ht' ht't i1 i2
      grind
    exact (Finset.card_le_card hsub).trans Finset.card_le_four

theorem exists_commutator_pair {n : ℕ} (hn : 5 ≤ n) {σ : Equiv.Perm (Fin n)} (h1 : σ ≠ 1)
    (h2 : ¬ σ.IsSwap) :
    ∃ S₁ S₂ : Finset (Fin n), S₁.card = 2 ∧ S₂.card = 2 ∧
      (symmDiff (S₁.image σ) S₁).Nonempty ∧
      (symmDiff (S₂.image σ) S₂).Nonempty ∧
      (symmDiff (symmDiff (S₁.image σ) S₁) (symmDiff (S₂.image σ) S₂)).Nonempty ∧
      (symmDiff (symmDiff (S₁.image σ) S₁) (symmDiff (S₂.image σ) S₂)).card ≤ 4 := by
  classical
  by_cases h : ∃ p, σ (σ p) ≠ p
  · obtain ⟨p, hp⟩ := h
    exact case1 p hp
  · push Not at h
    exact case2 hn h1 h2 h

@[expose] def indVec (n : ℕ) (S : Finset (Fin n)) : PermMod n :=
  Multiplicative.ofAdd (fun i => if i ∈ S then (1 : ZMod 2) else 0)

theorem indVec_apply {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    Multiplicative.toAdd (indVec n S) i = if i ∈ S then 1 else 0 := rfl

theorem permMod_mul_self {n : ℕ} (x : PermMod n) : x * x = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  have : ∀ z : ZMod 2, z + z = 0 := by decide
  simp [this]

theorem permMod_inv_eq {n : ℕ} (x : PermMod n) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (permMod_mul_self x)

theorem indVec_mul {n : ℕ} (S T : Finset (Fin n)) :
    indVec n S * indVec n T = indVec n (symmDiff S T) := by
  apply Multiplicative.toAdd.injective
  funext i
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [indVec, Finset.mem_symmDiff, hS, hT, h11]

theorem indVec_eq_one_iff {n : ℕ} (S : Finset (Fin n)) : indVec n S = 1 ↔ S = ∅ := by
  constructor
  · intro h
    ext i
    have := congrFun (congrArg Multiplicative.toAdd h) i
    simp only [indVec_apply] at this
    by_contra hi
    have hi' : i ∈ S := by simpa using hi
    simp [hi'] at this
  · rintro rfl
    apply Multiplicative.toAdd.injective
    funext i
    simp [indVec]

theorem indVec_eq_allOnes_iff {n : ℕ} (S : Finset (Fin n)) :
    indVec n S = allOnes n ↔ S = Finset.univ := by
  constructor
  · intro h
    ext i
    have := congrFun (congrArg Multiplicative.toAdd h) i
    simp only [indVec_apply, allOnes] at this
    simp only [Finset.mem_univ, iff_true]
    by_contra hi
    simp [hi] at this
  · rintro rfl
    apply Multiplicative.toAdd.injective
    funext i
    simp [indVec, allOnes]

theorem permAct_indVec {n : ℕ} (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    permAct n σ (indVec n S) = indVec n (S.image σ) := by
  apply Multiplicative.toAdd.injective
  funext i
  have hmem : i ∈ S.image σ ↔ σ⁻¹ i ∈ S := by
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨s, hs, rfl⟩
      simpa using hs
    · intro h
      exact ⟨σ⁻¹ i, h, by simp⟩
  simp [permAct_apply, indVec_apply, hmem]

theorem indVec_mem_coreMod {n : ℕ} {S : Finset (Fin n)} (hS : Even S.card) :
    indVec n S ∈ coreMod n := by
  rw [mem_coreMod]
  simp only [indVec_apply]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have : (Finset.univ.filter fun i => i ∈ S) = S := by ext; simp
  rw [this]
  exact (ZMod.natCast_eq_zero_iff_even).2 hS

private theorem zpow_eq_one_or_self {G : Type*} [Group G] {g : G} (hg : g * g = 1) (k : ℤ) :
    g ^ k = 1 ∨ g ^ k = g := by
  have hg2 : g ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hg
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [← Int.mul_ediv_add_emod k 2, h0, add_zero, zpow_mul, hg2, one_zpow]
  · right
    rw [← Int.mul_ediv_add_emod k 2, h1, zpow_add, zpow_mul, hg2, one_zpow, one_mul, zpow_one]

theorem false_of_card_two {G : Type*} [Group G] {A : Subgroup G} (h : Nat.card A = 2)
    {e₁ e₂ : G} (h₁ : e₁ ∈ A) (h₂ : e₂ ∈ A) (h1 : e₁ ≠ 1) (h2 : e₂ ≠ 1) (h12 : e₁ ≠ e₂) :
    False := by
  obtain ⟨x, y, hxy, hset⟩ := Nat.card_eq_two_iff.1 h
  have mem : ∀ z : A, z = x ∨ z = y := fun z => by
    have : z ∈ ({x, y} : Set A) := hset ▸ Set.mem_univ z
    simpa using this
  have n1 : (⟨e₁, h₁⟩ : A) ≠ 1 := fun h => h1 (congrArg Subtype.val h)
  have n2 : (⟨e₂, h₂⟩ : A) ≠ 1 := fun h => h2 (congrArg Subtype.val h)
  have n12 : (⟨e₁, h₁⟩ : A) ≠ ⟨e₂, h₂⟩ := fun h => h12 (congrArg Subtype.val h)
  rcases mem ⟨e₁, h₁⟩ with a | a <;> rcases mem ⟨e₂, h₂⟩ with b | b <;> rcases mem 1 with c | c <;>
    simp_all

theorem isSwap_of_card_commV_eq_two {V : Type*} [CommGroup V] {n : ℕ} (hn : 5 ≤ n)
    {X : Subgroup (MulAut V)} (θ : X ≃* Equiv.Perm (Fin n)) (β : coreMod n →* V)
    (hequiv : ∀ (x : X) (u : coreMod n), β (coreAct n (θ x) u) = (x : MulAut V) (β u))
    (hker : β.ker ≤ natKer n) {a : MulAut V} (ha : a ∈ X)
    (hcard : Nat.card (commV (Subgroup.zpowers a)) = 2) : (θ ⟨a, ha⟩).IsSwap := by
  classical
  by_contra hns
  set σ := θ ⟨a, ha⟩ with hσ
  have hσ1 : σ ≠ 1 := by
    intro h1
    have h2 : (⟨a, ha⟩ : X) = 1 := θ.injective (by rw [← hσ, h1, map_one])
    have ha1 : a = 1 := congrArg Subtype.val h2
    subst ha1
    have : commV (Subgroup.zpowers (1 : MulAut V)) = ⊥ := by
      rw [eq_bot_iff, commV_le_iff]
      intro x hx v
      rw [Subgroup.mem_zpowers_iff] at hx
      obtain ⟨k, rfl⟩ := hx
      simp
    rw [this] at hcard
    simp at hcard
  obtain ⟨S₁, S₂, h₁, h₂, hD₁, hD₂, hD₁₂, hc⟩ := exists_commutator_pair hn hσ1 hns
  let c : coreMod n → coreMod n := fun u => coreAct n σ u * u⁻¹
  have hcomm : ∀ u : coreMod n, β (c u) ∈ commV (Subgroup.zpowers a) := by
    intro u
    have : β (c u) = a (β u) * (β u)⁻¹ := by
      show β (coreAct n σ u * u⁻¹) = _
      rw [map_mul, map_inv, hσ, hequiv]
    rw [this]
    exact mem_commV_of_mem (Subgroup.mem_zpowers a) (β u)
  have he₁ : Even S₁.card := by rw [h₁]; exact even_two
  have he₂ : Even S₂.card := by rw [h₂]; exact even_two
  let u₁ : coreMod n := ⟨indVec n S₁, indVec_mem_coreMod he₁⟩
  let u₂ : coreMod n := ⟨indVec n S₂, indVec_mem_coreMod he₂⟩
  have hval : ∀ (u : coreMod n), ((c u : coreMod n) : PermMod n) =
      permAct n σ u * (u : PermMod n)⁻¹ := fun u => rfl
  have hval₁ : ((c u₁ : coreMod n) : PermMod n) = indVec n (symmDiff (S₁.image σ) S₁) := by
    rw [hval, permAct_indVec, permMod_inv_eq, indVec_mul]
  have hval₂ : ((c u₂ : coreMod n) : PermMod n) = indVec n (symmDiff (S₂.image σ) S₂) := by
    rw [hval, permAct_indVec, permMod_inv_eq, indVec_mul]
  set D₁ := symmDiff (S₁.image σ) S₁ with hD₁def
  set D₂ := symmDiff (S₂.image σ) S₂ with hD₂def
  have hne : ∀ z : coreMod n, (z : PermMod n) ≠ 1 → (z : PermMod n) ≠ allOnes n → β z ≠ 1 := by
    intro z hz1 hz2 hβ
    have hz : z ∈ β.ker := hβ
    have hz' : (z : PermMod n) ∈ Subgroup.zpowers (allOnes n) := hker hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz'
    rcases zpow_eq_one_or_self (permMod_mul_self (allOnes n)) k with h | h
    · exact hz1 (hk.symm.trans h)
    · exact hz2 (hk.symm.trans h)
  have hcard4 : ∀ S : Finset (Fin n), S.card = 2 →
      (symmDiff (S.image σ) S).card ≤ 4 := by
    intro S hS
    calc (symmDiff (S.image σ) S).card ≤ (S.image σ).card + S.card := card_symmDiff_le' _ _
      _ ≤ 4 := by
        have := Finset.card_image_le (s := S) (f := σ)
        omega
  have hne_univ : ∀ T : Finset (Fin n), T.card ≤ 4 → T ≠ Finset.univ := by
    intro T hT hTu
    rw [hTu, Finset.card_univ, Fintype.card_fin] at hT
    omega
  have hD₁ne : indVec n D₁ ≠ 1 := by
    rw [Ne, indVec_eq_one_iff]
    exact hD₁.ne_empty
  have hD₂ne : indVec n D₂ ≠ 1 := by
    rw [Ne, indVec_eq_one_iff]
    exact hD₂.ne_empty
  have hD₁₂ne : indVec n (symmDiff D₁ D₂) ≠ 1 := by
    rw [Ne, indVec_eq_one_iff]
    exact hD₁₂.ne_empty
  have hD₁u : indVec n D₁ ≠ allOnes n := by
    rw [Ne, indVec_eq_allOnes_iff]
    exact hne_univ _ (hcard4 S₁ h₁)
  have hD₂u : indVec n D₂ ≠ allOnes n := by
    rw [Ne, indVec_eq_allOnes_iff]
    exact hne_univ _ (hcard4 S₂ h₂)
  have hD₁₂u : indVec n (symmDiff D₁ D₂) ≠ allOnes n := by
    rw [Ne, indVec_eq_allOnes_iff]
    exact hne_univ _ hc
  have e1 : β (c u₁) ≠ 1 := hne _ (by rw [hval₁]; exact hD₁ne) (by rw [hval₁]; exact hD₁u)
  have e2 : β (c u₂) ≠ 1 := hne _ (by rw [hval₂]; exact hD₂ne) (by rw [hval₂]; exact hD₂u)
  have e12 : β (c u₁) ≠ β (c u₂) := by
    intro h
    have hz : β (c u₁ * (c u₂)⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    refine hne (c u₁ * (c u₂)⁻¹) ?_ ?_ hz
    · show ((c u₁ : coreMod n) : PermMod n) * ((c u₂ : coreMod n) : PermMod n)⁻¹ ≠ 1
      rw [hval₁, hval₂, permMod_inv_eq, indVec_mul]
      exact hD₁₂ne
    · show ((c u₁ : coreMod n) : PermMod n) * ((c u₂ : coreMod n) : PermMod n)⁻¹ ≠ allOnes n
      rw [hval₁, hval₂, permMod_inv_eq, indVec_mul]
      exact hD₁₂u
  exact false_of_card_two hcard (hcomm u₁) (hcomm u₂) e1 e2 e12

open Nat in
private theorem card_centralizer_swap (n : ℕ) {x y : Fin n} (h : x ≠ y) :
    Nat.card (Subgroup.centralizer ({Equiv.swap x y} : Set (Equiv.Perm (Fin n)))) =
      (n - 2)! * 2 := by
  have hc : (Equiv.swap x y).cycleType = {2} := by
    rw [(Equiv.Perm.isCycle_swap h).cycleType, Equiv.Perm.card_support_swap h]
  rw [Equiv.Perm.nat_card_centralizer, hc]
  simp

theorem not_central_in_sylow_of_isSwap {V : Type*} [CommGroup V] {n : ℕ} (hn : n = 5 ∨ n = 8)
    {X : Subgroup (MulAut V)} (θ : X ≃* Equiv.Perm (Fin n)) {a : MulAut V} (ha : a ∈ X)
    (hsw : (θ ⟨a, ha⟩).IsSwap) {T : Subgroup (MulAut V)} (hTX : T ≤ X) (hTp : IsPGroup 2 T)
    (hTi : ¬ 2 ∣ (T.subgroupOf X).index) (hcent : ∀ t ∈ T, t * a = a * t) :
    False := by
  classical
  obtain ⟨x, y, hxy, hσ⟩ := hsw
  set σ := θ ⟨a, ha⟩ with hσdef
  set T' : Subgroup (Equiv.Perm (Fin n)) := (T.subgroupOf X).map θ.toMonoidHom with hT'
  have hTp' : IsPGroup 2 T' := by
    refine IsPGroup.map ?_ θ.toMonoidHom
    exact hTp.of_equiv (Subgroup.subgroupOfEquivOfLe hTX).symm
  have hidx : T'.index = (T.subgroupOf X).index := Subgroup.index_map_equiv _ θ
  have hcentr : T' ≤ Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin n))) := by
    intro g hg
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : t * (⟨a, ha⟩ : X) = ⟨a, ha⟩ * t := by
      apply Subtype.ext
      exact hcent (t : MulAut V) ht
    show θ t * θ ⟨a, ha⟩ = θ ⟨a, ha⟩ * θ t
    rw [← map_mul, ← map_mul, h1]
  have hdvd : Nat.card T' ∣
      Nat.card (Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin n)))) :=
    Subgroup.card_dvd_of_le hcentr
  rw [hσ, card_centralizer_swap n hxy] at hdvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hTp'
  have hmul : Nat.card T' * T'.index = Nat.card (Equiv.Perm (Fin n)) := Subgroup.card_mul_index T'
  have hperm : Nat.card (Equiv.Perm (Fin n)) = n.factorial := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]
  rw [hperm] at hmul
  have hodd : ¬ 2 ∣ T'.index := by rw [hidx]; exact hTi
  rw [hk] at hdvd hmul
  rcases hn with rfl | rfl
  · norm_num [Nat.factorial] at hdvd hmul
    have hk4 : k < 4 := by
      by_contra hcon
      have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.1 hcon)
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    interval_cases k <;> omega
  · norm_num [Nat.factorial] at hdvd hmul
    have hk11 : k < 11 := by
      by_contra hcon
      have : 2 ^ 11 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.1 hcon)
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    interval_cases k <;> omega

end G6

end CFSG.Quasithin
