module

public import CFSG.LocalAnalysis.StandardType.FS81.SpMatAlg
public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

section Pow

variable {k : ℕ}

theorem exists_spMat_pow (σ : Equiv.Perm (Fin k)) {s : Fin k → ZMod 3} (hs : IsSign s) (n : ℕ) :
    ∃ t : Fin k → ZMod 3, IsSign t ∧ spMat σ s ^ n = spMat (σ ^ n) t := by
  induction n with
  | zero => exact ⟨fun _ => 1, fun _ => Or.inl rfl, by rw [pow_zero, pow_zero, spMat_one]⟩
  | succ n ih =>
    obtain ⟨t, ht, h⟩ := ih
    refine ⟨fun j => s ((σ ^ n) j) * t j, fun j => ?_, ?_⟩
    · show s ((σ ^ n) j) * t j = 1 ∨ s ((σ ^ n) j) * t j = -1
      rcases hs ((σ ^ n) j) with h1 | h1 <;> rcases ht j with h2 | h2 <;> rw [h1, h2] <;> decide
    · rw [pow_succ' (spMat σ s), h, spMat_mul, ← pow_succ' σ]

theorem perm_eq_one_of_spMat_eq_one {σ : Equiv.Perm (Fin k)} {s : Fin k → ZMod 3}
    (h : spMat σ s = 1) : σ = 1 := by
  ext j
  by_contra hne
  have e := congrFun (congrFun h j) j
  rw [spMat_apply, if_neg (fun h' => hne (by rw [← h']; rfl)), Matrix.one_apply_eq] at e
  exact zero_ne_one e

theorem perm_eq_of_spMat_eq {σ τ : Equiv.Perm (Fin k)} {s t : Fin k → ZMod 3} (hs : IsSign s)
    (h : spMat σ s = spMat τ t) : σ = τ := by
  ext j
  by_contra hne
  have e := congrFun (congrFun h (σ j)) j
  rw [spMat_apply, spMat_apply, if_pos rfl, if_neg (fun h' => hne (congrArg Fin.val h'))] at e
  rcases hs j with h1 | h1 <;> rw [h1] at e <;> exact absurd e (by decide)

theorem spMat_one_mul_self {s : Fin k → ZMod 3} (hs : IsSign s) :
    spMat (1 : Equiv.Perm (Fin k)) s * spMat 1 s = 1 := by
  rw [spMat_mul, mul_one, ← spMat_one]
  congr 1
  funext j
  rcases hs j with h1 | h1 <;> simp only [Equiv.Perm.one_apply, h1] <;> decide

theorem spMat_one_pow (σ : Equiv.Perm (Fin k)) (n : ℕ) : spMat σ 1 ^ n = spMat (σ ^ n) 1 := by
  induction n with
  | zero => rw [pow_zero, pow_zero, ← spMat_one]; rfl
  | succ n ih =>
    rw [pow_succ' (spMat σ 1), ih, spMat_mul, ← pow_succ' σ]
    exact congrArg _ (funext fun j => by simp)

theorem pow_conj_of_mul_self {D P : Matrix (Fin k) (Fin k) (ZMod 3)} (hD : D * D = 1) (n : ℕ) :
    (D * P * D) ^ n = D * P ^ n * D := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Matrix.mul_one, hD]
  | succ n ih =>
    rw [pow_succ', ih, pow_succ']
    calc D * P * D * (D * P ^ n * D) = D * P * (D * D) * P ^ n * D := by
          simp only [Matrix.mul_assoc]
      _ = D * (P * P ^ n) * D := by rw [hD, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem perm_pow_of_spMat_pow {σ : Equiv.Perm (Fin k)} {s : Fin k → ZMod 3} (hs : IsSign s)
    (h15 : spMat σ s ^ 15 = 1) (h5 : spMat σ s ^ 5 ≠ 1) (h3 : spMat σ s ^ 3 ≠ 1) :
    σ ^ 15 = 1 ∧ σ ^ 5 ≠ 1 ∧ σ ^ 3 ≠ 1 := by
  refine ⟨?_, fun h => h5 ?_, fun h => h3 ?_⟩
  · obtain ⟨t, -, ht⟩ := exists_spMat_pow σ hs 15
    exact perm_eq_one_of_spMat_eq_one (ht ▸ h15)
  · obtain ⟨t, htt, ht⟩ := exists_spMat_pow σ hs 5
    rw [h] at ht
    have h10 : spMat σ s ^ 10 = 1 := by
      rw [show (10 : ℕ) = 5 + 5 from rfl, pow_add, ht, spMat_one_mul_self htt]
    have e : spMat σ s ^ 15 = spMat σ s ^ 10 * spMat σ s ^ 5 := by rw [← pow_add]
    rw [h10, one_mul, h15] at e
    exact e.symm
  · obtain ⟨t, htt, ht⟩ := exists_spMat_pow σ hs 3
    rw [h] at ht
    have h6 : spMat σ s ^ 6 = 1 := by
      rw [show (6 : ℕ) = 3 + 3 from rfl, pow_add, ht, spMat_one_mul_self htt]
    have e : spMat σ s ^ 15 = spMat σ s ^ 6 * spMat σ s ^ 6 * spMat σ s ^ 3 := by
      rw [← pow_add, ← pow_add]
    rw [h6, one_mul, one_mul, h15] at e
    exact e.symm

end Pow

section Fifteen

theorem false_of_perm_order_fifteen (σ : Equiv.Perm (Fin 8)) (h0 : σ 0 = 0) (h15 : σ ^ 15 = 1)
    (h5 : σ ^ 5 ≠ 1) (h3 : σ ^ 3 ≠ 1) : False := by
  have hord : orderOf σ = 15 := by
    have hd : orderOf σ ∣ 15 := orderOf_dvd_of_pow_eq_one h15
    have hle : orderOf σ ≤ 15 := Nat.le_of_dvd (by norm_num) hd
    have hpos : 0 < orderOf σ := orderOf_pos σ
    interval_cases h : orderOf σ <;> norm_num at hd
    · exact absurd (by rw [orderOf_eq_one_iff.mp h, one_pow]) h3
    · exact absurd (h ▸ pow_orderOf_eq_one σ) h3
    · exact absurd (h ▸ pow_orderOf_eq_one σ) h5
    · rfl
  have hsupp : σ.support.card ≤ 7 := by
    have hsub : σ.support ⊆ Finset.univ.erase 0 := fun x hx =>
      Finset.mem_erase.mpr ⟨fun h => Equiv.Perm.mem_support.mp hx (h ▸ h0), Finset.mem_univ _⟩
    calc σ.support.card ≤ (Finset.univ.erase (0 : Fin 8)).card := Finset.card_le_card hsub
      _ = 7 := by simp
  have hmem : ∀ a ∈ σ.cycleType, a = 3 ∨ a = 5 := by
    intro a ha
    have h1 : a ∣ 15 := hord ▸ Equiv.Perm.dvd_of_mem_cycleType ha
    have h2 := Equiv.Perm.two_le_of_mem_cycleType ha
    have h7 : a ≤ 7 := (Equiv.Perm.le_card_support_of_mem_cycleType ha).trans hsupp
    interval_cases a <;> first | exact Or.inl rfl | exact Or.inr rfl | norm_num at h1
  have hlcm := σ.lcm_cycleType
  have h3m : 3 ∈ σ.cycleType := by
    by_contra h
    have : σ.cycleType.lcm ∣ 5 := Multiset.lcm_dvd.mpr fun b hb => by
      rcases hmem b hb with rfl | rfl
      · exact absurd hb h
      · exact dvd_rfl
    rw [hlcm, hord] at this
    norm_num at this
  have h5m : 5 ∈ σ.cycleType := by
    by_contra h
    have : σ.cycleType.lcm ∣ 3 := Multiset.lcm_dvd.mpr fun b hb => by
      rcases hmem b hb with rfl | rfl
      · exact dvd_rfl
      · exact absurd hb h
    rw [hlcm, hord] at this
    norm_num at this
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem h3m
  have h5t : 5 ∈ t := by
    rw [ht] at h5m
    exact (Multiset.mem_cons.mp h5m).resolve_left (by norm_num)
  have hle5 : 5 ≤ t.sum := Multiset.le_sum_of_mem h5t
  have hsum : σ.cycleType.sum = 3 + t.sum := by rw [ht, Multiset.sum_cons]
  rw [Equiv.Perm.sum_cycleType] at hsum
  omega

end Fifteen

section Rep

@[expose] def repW (w : ℕ) : Fin 8 → ZMod 3 := fun i => if (i : ℕ) < w then 1 else 0

@[expose] def rep8 (ε : ZMod 3) : Fin 8 → ZMod 3 := fun i => if i = 0 then ε else 1

theorem mul_self_of_ne_zero {a : ZMod 3} (ha : a ≠ 0) : a * a = 1 := by
  revert a
  decide

theorem eq_one_or_of_ne_zero {a : ZMod 3} (ha : a ≠ 0) : a = 1 ∨ a = -1 := by
  revert a
  decide

theorem card_filter_val_lt (w : ℕ) (hw : w ≤ 8) :
    (Finset.univ.filter fun i : Fin 8 => (i : ℕ) < w).card = w := by
  interval_cases w <;> decide

theorem exists_spMat_mulVec_eq_repW (v : Fin 8 → ZMod 3) (hv : wt v ≤ 7) :
    ∃ σ s, IsSign s ∧ ∏ i, s i = 1 ∧ spMat σ s *ᵥ v = repW (wt v) := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin 8), S = Finset.univ.filter fun i => v i ≠ 0 := ⟨_, rfl⟩
  have hmemS : ∀ i, i ∈ S ↔ v i ≠ 0 := fun i => by rw [hS, Finset.mem_filter]; simp
  have hwS : wt v = S.card := by rw [hS]; rfl
  obtain ⟨T, hT⟩ : ∃ T : Finset (Fin 8), T = Finset.univ.filter fun i : Fin 8 => (i : ℕ) < wt v :=
    ⟨_, rfl⟩
  have hmemT : ∀ i, i ∈ T ↔ (i : ℕ) < wt v := fun i => by rw [hT, Finset.mem_filter]; simp
  have hST : Fintype.card {x // x ∈ S} = Fintype.card {x // x ∈ T} := by
    rw [Fintype.card_coe, Fintype.card_coe, hT, card_filter_val_lt _ (by omega), hwS]
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin 8),
      σ = (Fintype.equivOfCardEq hST).extendSubtype := ⟨_, rfl⟩
  have hσS : ∀ x, x ∈ S ↔ σ x ∈ T := fun x => by
    constructor
    · intro hx
      rw [hσ]
      exact Equiv.extendSubtype_mem _ x hx
    · intro hx
      by_contra hx'
      rw [hσ] at hx
      exact Equiv.extendSubtype_not_mem _ x hx' hx
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, j₀ ∉ S := by
    by_contra h
    push Not at h
    have : S = Finset.univ := Finset.eq_univ_of_forall h
    rw [this, Finset.card_univ, Fintype.card_fin] at hwS
    omega
  have hP : (∏ i ∈ S, v i) * (∏ i ∈ S, v i) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i hi => mul_self_of_ne_zero ((hmemS i).mp hi)
  refine ⟨σ, fun x => (if x ∈ S then v x else 1) * (if x = j₀ then ∏ i ∈ S, v i else 1),
    fun x => ?_, ?_, ?_⟩
  · show _ * _ = 1 ∨ _ * _ = -1
    have h1 : (if x ∈ S then v x else 1) = 1 ∨ (if x ∈ S then v x else 1) = -1 := by
      split_ifs with hx
      · exact eq_one_or_of_ne_zero ((hmemS x).mp hx)
      · exact Or.inl rfl
    have h2 : (if x = j₀ then ∏ i ∈ S, v i else 1) = 1 ∨
        (if x = j₀ then ∏ i ∈ S, v i else 1) = -1 := by
      split_ifs
      · exact eq_one_or_of_ne_zero (fun h0 => by rw [h0, zero_mul] at hP; exact zero_ne_one hP)
      · exact Or.inl rfl
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> decide
  · rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_ite_eq']
    simp only [Finset.mem_univ, if_true]
    exact hP
  · rw [spMat_mulVec]
    funext i
    have hi : σ (σ.symm i) = i := Equiv.apply_symm_apply σ i
    by_cases hy : σ.symm i ∈ S
    · have hiT : i ∈ T := hi ▸ (hσS _).mp hy
      have hne : σ.symm i ≠ j₀ := fun h => hj₀ (h ▸ hy)
      rw [if_pos hy, if_neg hne, mul_one, mul_self_of_ne_zero ((hmemS _).mp hy)]
      exact (if_pos ((hmemT i).mp hiT)).symm
    · have hiT : i ∉ T := fun h => hy ((hσS _).mpr (hi.symm ▸ h))
      have hv0 : v (σ.symm i) = 0 := by
        by_contra h
        exact hy ((hmemS _).mpr h)
      rw [hv0, mul_zero]
      exact (if_neg (fun h => hiT ((hmemT i).mpr h))).symm

theorem exists_spMat_mulVec_eq_rep8 (v : Fin 8 → ZMod 3) (hv : wt v = 8) :
    ∃ σ s, IsSign s ∧ ∏ i, s i = 1 ∧ spMat σ s *ᵥ v = rep8 (∏ i, v i) := by
  have hv0 : ∀ i, v i ≠ 0 := by
    intro i hi
    have hlt : wt v < 8 := by
      calc wt v ≤ (Finset.univ.erase i).card := Finset.card_le_card fun x hx =>
            Finset.mem_erase.mpr ⟨fun h => (Finset.mem_filter.mp hx).2 (h ▸ hi), Finset.mem_univ _⟩
        _ = 7 := by simp
        _ < 8 := by norm_num
    omega
  have hP : (∏ i, v i) * (∏ i, v i) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => mul_self_of_ne_zero (hv0 i)
  refine ⟨1, fun x => (if x = 0 then ∏ i, v i else 1) * v x, fun x => ?_, ?_, ?_⟩
  · show _ * _ = 1 ∨ _ * _ = -1
    have h1 : (if x = 0 then ∏ i, v i else 1) = 1 ∨ (if x = 0 then ∏ i, v i else 1) = -1 := by
      split_ifs
      · exact eq_one_or_of_ne_zero (fun h0 => by rw [h0, zero_mul] at hP; exact zero_ne_one hP)
      · exact Or.inl rfl
    rcases h1 with h1 | h1 <;> rcases eq_one_or_of_ne_zero (hv0 x) with h2 | h2 <;>
      rw [h1, h2] <;> decide
  · rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ (0 : Fin 8), if_pos (Finset.mem_univ _)]
    exact hP
  · rw [spMat_mulVec]
    funext i
    simp only [Equiv.Perm.one_symm, Equiv.Perm.one_apply]
    rw [mul_assoc, mul_self_of_ne_zero (hv0 i), mul_one]
    first | rfl | simp [rep8]

theorem card_wt_one : (Finset.univ.filter fun v : Fin 8 → ZMod 3 => wt v = 1).card = 16 := by
  decide +kernel

end Rep

section Weight

variable {k : ℕ}

theorem wt_add_le (a b : Fin k → ZMod 3) : wt (a + b) ≤ wt a + wt b := by
  unfold wt
  calc (Finset.univ.filter fun i => (a + b) i ≠ 0).card ≤
      ((Finset.univ.filter fun i => a i ≠ 0) ∪ (Finset.univ.filter fun i => b i ≠ 0)).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
          Pi.add_apply] at hi ⊢
        by_contra hc
        push Not at hc
        exact hi (by rw [hc.1, hc.2, add_zero])
    _ ≤ _ := Finset.card_union_le _ _

theorem wt_smul {c : ZMod 3} (hc : c ≠ 0) (v : Fin k → ZMod 3) : wt (c • v) = wt v := by
  unfold wt
  congr 1
  ext i
  simp [hc]

theorem wt_neg (v : Fin k → ZMod 3) : wt (-v) = wt v := by
  unfold wt
  congr 1
  ext i
  simp

theorem wt_eq_iff_forall_ne_zero (v : Fin k → ZMod 3) : wt v = k ↔ ∀ i, v i ≠ 0 := by
  unfold wt
  constructor
  · intro h i hi
    have : (Finset.univ.filter fun i => v i ≠ 0).card ≤ (Finset.univ.erase i).card :=
      Finset.card_le_card fun x hx =>
        Finset.mem_erase.mpr ⟨fun hxi => (Finset.mem_filter.mp hx).2 (hxi ▸ hi), Finset.mem_univ _⟩
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at this
    have hk : 0 < k := Fin.pos i
    omega
  · intro h
    rw [Finset.filter_true_of_mem (fun i _ => h i), Finset.card_univ, Fintype.card_fin]

theorem wt_single_add_smul {u : Fin k → ZMod 3} {j : Fin k} (huj : u j ≠ 0) {c : ZMod 3}
    (hc : c ≠ 0) :
    wt (Pi.single j 1 + c • u) = if 1 + c * u j = 0 then wt u - 1 else wt u := by
  unfold wt
  have hS : (Finset.univ.filter fun i : Fin k => (Pi.single j 1 + c • u : Fin k → ZMod 3) i ≠ 0) =
      if 1 + c * u j = 0 then (Finset.univ.filter fun i : Fin k => u i ≠ 0).erase j
      else Finset.univ.filter fun i : Fin k => u i ≠ 0 := by
    split_ifs with h1
    · ext i
      by_cases hi : i = j
      · subst hi
        simp [h1]
      · simp [hi, Pi.single_eq_of_ne hi, hc]
    · ext i
      by_cases hi : i = j
      · subst hi
        simp [h1, huj]
      · simp [Pi.single_eq_of_ne hi, hc]
  rw [hS]
  split_ifs
  · rw [Finset.card_erase_of_mem (by simp [huj])]
  · rfl

end Weight

end CFSG.StandardType.FrameRoute.FS81

end
