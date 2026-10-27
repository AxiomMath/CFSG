module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5ArithLab

public import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.Stroth.G5

variable {n : ℕ}

theorem sgn_false : sgn (n := n) false = 1 := rfl

theorem sgn_true : sgn (n := n) true = -1 := rfl

theorem contrib_eq_map (k₀ m₀ : ZMod (2 ^ n - 1)) (b : Bool) (l : ℤ) (d : ℕ) :
    Pattern.contrib k₀ m₀ (sgn b) l d = (labContrib b l d).map (Lab.val k₀ m₀) := by
  unfold Pattern.contrib labContrib
  split_ifs <;> simp [Lab.val, smul_smul, mul_comm]

namespace Pattern

theorem chainR_eq_map (p : Pattern) (k₀ m₀ : ZMod (2 ^ n - 1)) (i j : ℤ) :
    p.chainR k₀ m₀ i j = (p.labR i j).map (Lab.val k₀ m₀) := by
  rw [chainR, labR, ← Multiset.mapAddMonoidHom_apply, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Multiset.mapAddMonoidHom_apply, ← contrib_eq_map]
  rfl

theorem chainL_eq_map (p : Pattern) (k₀ m₀ : ZMod (2 ^ n - 1)) (i j : ℤ) :
    p.chainL k₀ m₀ i j = (p.labL i j).map (Lab.val k₀ m₀) := by
  rw [chainL, labL, ← Multiset.mapAddMonoidHom_apply, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Multiset.mapAddMonoidHom_apply, ← contrib_eq_map]
  rfl

end Pattern

theorem map_eq_map_of_factor {α β γ : Type*} {s t : Multiset α} {f : α → β} {k : α → γ}
    (h : ∀ a ∈ s + t, ∀ b ∈ s + t, f a = f b → k a = k b) (hst : s.map f = t.map f) :
    s.map k = t.map k := by
  classical
  by_cases h0 : ∃ a, a ∈ s + t
  swap
  · simp only [not_exists] at h0
    have hs0 : s = 0 := Multiset.eq_zero_of_forall_notMem fun a ha =>
      h0 a (Multiset.mem_add.mpr (Or.inl ha))
    have ht0 : t = 0 := Multiset.eq_zero_of_forall_notMem fun a ha =>
      h0 a (Multiset.mem_add.mpr (Or.inr ha))
    rw [hs0, ht0]
  obtain ⟨a₀, -⟩ := h0
  let g : β → γ := fun y => if hy : ∃ a ∈ s + t, f a = y then k hy.choose else k a₀
  have hg : ∀ a ∈ s + t, g (f a) = k a := by
    intro a ha
    have hy : ∃ b ∈ s + t, f b = f a := ⟨a, ha, rfl⟩
    simp only [g, dif_pos hy]
    exact h _ hy.choose_spec.1 _ ha hy.choose_spec.2
  have hs : s.map k = (s.map f).map g := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun a ha => (hg a (Multiset.mem_add.mpr (Or.inl ha))).symm
  have ht : t.map k = (t.map f).map g := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun a ha => (hg a (Multiset.mem_add.mpr (Or.inr ha))).symm
  rw [hs, ht, hst]

private theorem two_mul_t_of_mem_labContrib {b : Bool} {x : ℤ} {d : ℕ} {l : Lab}
    (hl : l ∈ labContrib b x d) : x - 1 ≤ 2 * l.t ∧ 2 * l.t ≤ x := by
  unfold labContrib at hl
  split_ifs at hl with h1 h2 h3 h4 <;>
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton,
      Multiset.notMem_zero] at hl
  · obtain ⟨m, rfl⟩ := h1
    rcases hl with rfl | rfl <;> dsimp only <;> omega
  · obtain ⟨m, rfl⟩ := h1
    subst hl
    dsimp only
    omega
  · subst hl
    obtain ⟨m, rfl⟩ := Int.not_even_iff_odd.mp h1
    dsimp only
    omega

namespace Pattern

theorem two_mul_t_mem_labR {p : Pattern} {i j : ℤ} (hi : 0 ≤ i) (hi1 : i ≤ 1) (hij : i ≤ j)
    {l : Lab} (hl : l ∈ p.labR i j) : -(p.J : ℤ) - 1 ≤ 2 * l.t ∧ 2 * l.t ≤ p.J + 1 := by
  obtain ⟨x, hx, hlx⟩ := Multiset.mem_sum.mp hl
  rw [Finset.mem_Ioc] at hx
  have := two_mul_t_of_mem_labContrib hlx
  omega

theorem two_mul_t_mem_labL {p : Pattern} {i j : ℤ} (hi : 0 ≤ i) (hi1 : i ≤ 1) (hij : i ≤ j)
    {l : Lab} (hl : l ∈ p.labL i j) : -(p.J : ℤ) - 1 ≤ 2 * l.t ∧ 2 * l.t ≤ p.J + 1 := by
  obtain ⟨x, hx, hlx⟩ := Multiset.mem_sum.mp hl
  rw [Finset.mem_Ico] at hx
  have := two_mul_t_of_mem_labContrib hlx
  omega

theorem passAll_of_pass {p : Pattern} {k₀ m₀ : ZMod (2 ^ n - 1)} {τ : AType} {Δ : ℕ}
    (hΔ : p.J + 1 ≤ Δ)
    (hτ : ∀ l₁ l₂ : Lab, |l₁.t - l₂.t| ≤ (Δ : ℤ) → cls (l₁.val k₀ m₀) = cls (l₂.val k₀ m₀) →
      τ.canon l₁ = τ.canon l₂)
    (hpass : ∀ i j : ℤ, i ≤ j → j ≤ i + p.J → p.Pass k₀ m₀ i j) : τ.passAll p = true := by
  unfold AType.passAll windowLabs
  rw [List.all_eq_true]
  intro w hw
  obtain ⟨i, hi, hw⟩ := List.mem_flatMap.mp hw
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hw
  obtain ⟨d, hd, rfl⟩ : ∃ a : ℕ, a ≤ p.J ∧ d = (a : ℤ) := by simpa using hd
  have hi' : 0 ≤ i ∧ i ≤ 1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> omega
  have h := hpass i (i + d) (by omega) (by omega)
  rw [Pass, chainR_eq_map, chainL_eq_map, Multiset.map_map, Multiset.map_map] at h
  refine decide_eq_true (map_eq_map_of_factor (fun a ha b hb hab => hτ a b ?_ hab) h)
  have hb' : ∀ c ∈ p.labR i (i + d) + p.labL i (i + d),
      -(p.J : ℤ) - 1 ≤ 2 * c.t ∧ 2 * c.t ≤ p.J + 1 := by
    intro c hc
    rcases Multiset.mem_add.mp hc with hc | hc
    · exact two_mul_t_mem_labR hi'.1 hi'.2 (by omega) hc
    · exact two_mul_t_mem_labL hi'.1 hi'.2 (by omega) hc
  have h1 := hb' a ha
  have h2 := hb' b hb
  rw [abs_le]
  omega

theorem passAllConc_of_pass {p : Pattern} {k₀ m₀ : ZMod (2 ^ n - 1)}
    (hpass : ∀ i j : ℤ, i ≤ j → j ≤ i + p.J → p.Pass k₀ m₀ i j) :
    passAllConc p k₀ m₀ = true := by
  unfold passAllConc
  rw [List.all_eq_true]
  intro i hi
  rw [List.all_eq_true]
  intro d hd
  rw [List.mem_range] at hd
  have hi' : 0 ≤ i := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> omega
  exact decide_eq_true (hpass i (i + d) (by omega) (by omega))

private theorem eS_add_oS (p : Pattern) (m : ℕ) :
    p.eS m + p.oS m = 21 - ∑ j ∈ Finset.Ico 1 m, ((p.dS j : ℤ) + p.dL j) := by
  have h : ∀ j ∈ Finset.Ico 1 m, ((if Even j then (p.dS j : ℤ) else p.dL j) +
      (if Even j then (p.dL j : ℤ) else p.dS j)) = (p.dS j : ℤ) + p.dL j := by
    intro j _
    split_ifs <;> ring
  rw [eS, oS, ← Finset.sum_congr rfl h, Finset.sum_add_distrib]
  ring

private theorem le_sum_drops (p : Pattern) {m : ℕ} (hm : m ≤ p.s1 ∨ m ≤ p.l1) :
    (m : ℤ) ≤ ∑ j ∈ Finset.Ico 1 (m + 1), ((p.dS j : ℤ) + p.dL j) := by
  have h : ∀ j ∈ Finset.Ico 1 (m + 1), (1 : ℤ) ≤ (p.dS j : ℤ) + p.dL j := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    unfold dS dL
    split_ifs <;> push_cast <;> omega
  calc (m : ℤ) = ∑ _j ∈ Finset.Ico 1 (m + 1), (1 : ℤ) := by simp
    _ ≤ _ := Finset.sum_le_sum h

private theorem le_twentyOne_of_admissible {p : Pattern} (hp : p.Admissible) {m : ℕ}
    (hm : m ≤ p.s1 ∨ m ≤ p.l1) : m ≤ 21 := by
  have h1 := hp.2.2.2.1 (m + 1) (by omega)
  have h2 := hp.2.2.2.2.1 (m + 1) (by omega)
  have h3 := eS_add_oS p (m + 1)
  have h4 := le_sum_drops p hm
  omega

theorem mem_admissibleList {p : Pattern} (hp : p.Admissible) : p ∈ admissibleList () := by
  have hs1 := le_twentyOne_of_admissible hp (m := p.s1) (Or.inl le_rfl)
  have hl1 := le_twentyOne_of_admissible hp (m := p.l1) (Or.inr le_rfl)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp
  unfold admissibleList
  rw [List.mem_filter]
  refine ⟨?_, ?_⟩
  · simp only [List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨p.s1, by omega, p.s2, by omega, p.l1, by omega, rfl⟩
  · unfold admissibleB
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_false_iff_not]
    refine ⟨⟨⟨h1, h2⟩, h3⟩, fun m _ => ?_⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact Or.inl rfl
    · refine Or.inr ⟨⟨h4 m hm, h5 m hm⟩, ?_⟩
      by_cases he : Even m
      · exact Or.inr (h6 m hm he)
      · exact Or.inl he

end Pattern

theorem exists_natCast_of_isUnit_three {k₀ : ZMod (2 ^ 3 - 1)} (hk : IsUnit k₀) :
    ∃ k < 6, k₀ = ((k + 1 : ℕ) : ZMod (2 ^ 3 - 1)) := by
  have h7 : (2 ^ 3 - 1 : ℕ) = 7 := by norm_num
  have : NeZero (2 ^ 3 - 1 : ℕ) := ⟨by norm_num⟩
  have hv : k₀.val < 7 := h7 ▸ ZMod.val_lt k₀
  have hne : k₀ ≠ 0 := by
    rintro rfl
    have : Nontrivial (ZMod (2 ^ 3 - 1)) := ZMod.nontrivial_iff.mpr (by norm_num)
    exact not_isUnit_zero hk
  have hv0 : k₀.val ≠ 0 := by rwa [Ne, ZMod.val_eq_zero]
  refine ⟨k₀.val - 1, by omega, ?_⟩
  rw [Nat.sub_add_cancel (by omega), ZMod.natCast_zmod_val]

end CFSG.Quasithin.Stroth.G5

end
