module

public import CFSG.GroupTheory.SwapCommute
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.StandardType

private lemma ggQ2s08r6_swap_eq_of_apply_ne {σ : Equiv.Perm (Fin 6)} (hσ : σ.IsSwap)
    {a : Fin 6} (ha : σ a ≠ a) : σ = Equiv.swap a (σ a) := by
  obtain ⟨x, y, _hxy, heq⟩ := hσ
  rw [heq] at ha ⊢
  have hax : a = x ∨ a = y := Equiv.eq_or_eq_of_swap_apply_ne_self ha
  rcases hax with h | h
  · rw [h, Equiv.swap_apply_left]
  · rw [h, Equiv.swap_apply_right]
    exact Equiv.swap_comm x y

private lemma ggQ2s08r6_fixes_of_commute_swap {σ : Equiv.Perm (Fin 6)} {i j : Fin 6}
    (hij : i ≠ j) (hσ : σ.IsSwap) (hc : Commute σ (Equiv.swap i j))
    (hne : σ ≠ Equiv.swap i j) : σ i = i ∧ σ j = j := by
  have h1 : σ i = i ∨ σ i = j :=
    CFSG.GroupTheory.apply_mem_pair_of_commute hij hc
  have h2 : σ j = j ∨ σ j = i :=
    CFSG.GroupTheory.apply_mem_pair_of_commute (i := j) (j := i) hij.symm (by
      simpa [Equiv.swap_comm] using hc)
  have hfixi : σ i = i := by
    rcases h1 with h | h
    · exact h
    · exfalso
      have hnei : σ i ≠ i := by rw [h]; exact hij.symm
      have heq : σ = Equiv.swap i j := by
        rw [ggQ2s08r6_swap_eq_of_apply_ne hσ hnei, h]
      exact hne heq
  have hfixj : σ j = j := by
    rcases h2 with h | h
    · exact h
    · exfalso
      have hnej : σ j ≠ j := by rw [h]; exact hij
      have heq : σ = Equiv.swap j i := by
        rw [ggQ2s08r6_swap_eq_of_apply_ne hσ hnej, h]
      exact hne (by rw [heq, Equiv.swap_comm])
  exact ⟨hfixi, hfixj⟩

private lemma ggQ2s08r6_exists_swap_succ {σ ρ : Equiv.Perm (Fin 6)} {a b : Fin 6}
    (hab : a ≠ b) (hσ : σ = Equiv.swap a b) (hρ : ρ.IsSwap) (hfix : ρ a = a)
    (hnc : ¬ Commute σ ρ) :
    ∃ c : Fin 6, c ≠ a ∧ c ≠ b ∧ ρ = Equiv.swap b c := by
  have hb : ρ b ≠ b := by
    intro hb'
    have hdisj : Equiv.Perm.Disjoint ρ (Equiv.swap a b) := by
      intro x
      by_cases hx : x = a ∨ x = b
      · rcases hx with rfl | rfl
        · left; exact hfix
        · left; exact hb'
      · push Not at hx
        right
        exact Equiv.swap_apply_of_ne_of_ne hx.1 hx.2
    have hcomm : Commute σ ρ := by
      rw [hσ]
      exact (Equiv.Perm.Disjoint.commute hdisj).symm
    exact hnc hcomm
  refine ⟨ρ b, ?_, hb, ggQ2s08r6_swap_eq_of_apply_ne hρ hb⟩
  intro h
  have hinj : ρ b = ρ a := by rw [h, hfix]
  exact hab (ρ.injective hinj).symm

private lemma ggQ2s08r6_vec_inj {a0 a1 a2 a3 a4 a5 : Fin 6}
    (h01 : a0 ≠ a1) (h02 : a0 ≠ a2) (h03 : a0 ≠ a3) (h04 : a0 ≠ a4) (h05 : a0 ≠ a5)
    (h12 : a1 ≠ a2) (h13 : a1 ≠ a3) (h14 : a1 ≠ a4) (h15 : a1 ≠ a5)
    (h23 : a2 ≠ a3) (h24 : a2 ≠ a4) (h25 : a2 ≠ a5)
    (h34 : a3 ≠ a4) (h35 : a3 ≠ a5) (h45 : a4 ≠ a5) :
    Function.Injective ![a0, a1, a2, a3, a4, a5] := by
  let b : Fin 6 → Fin 6 := fun x =>
    if x = a0 then 0 else if x = a1 then 1 else if x = a2 then 2 else
      if x = a3 then 3 else if x = a4 then 4 else 5
  have hleft : ∀ i : Fin 6, b (![a0, a1, a2, a3, a4, a5] i) = i := by
    intro i
    fin_cases i <;>
      simp [b, h01, h01.symm, h02, h02.symm, h03, h03.symm, h04, h04.symm,
        h05, h05.symm, h12, h12.symm, h13, h13.symm, h14, h14.symm, h15, h15.symm,
        h23, h23.symm, h24, h24.symm, h25, h25.symm, h34, h34.symm, h35, h35.symm,
        h45, h45.symm]
  intro i j hij
  have h := congrArg b hij
  rwa [hleft i, hleft j] at h

theorem ggQ2s08r6_path {τ : Fin 5 → Equiv.Perm (Fin 6)} (hswap : ∀ i, (τ i).IsSwap)
    (hadj : ∀ i j : Fin 5, (i : ℕ) + 1 = j → τ i * τ j ≠ τ j * τ i)
    (hfar : ∀ i j : Fin 5, i ≠ j → (i : ℕ) + 1 ≠ j → (j : ℕ) + 1 ≠ i →
      τ i * τ j = τ j * τ i ∧ τ i ≠ τ j) :
    ∃ a : Fin 6 ≃ Fin 6, ∀ i : Fin 5, τ i = Equiv.swap (a i.castSucc) (a i.succ) := by
  classical
  let p : Fin 5 → Fin 6 := fun i => Classical.choose (hswap i)
  let q : Fin 5 → Fin 6 := fun i => Classical.choose (Classical.choose_spec (hswap i))
  have hpq : ∀ i, p i ≠ q i := fun i =>
    (Classical.choose_spec (Classical.choose_spec (hswap i))).1
  have hτ : ∀ i, τ i = Equiv.swap (p i) (q i) := fun i =>
    (Classical.choose_spec (Classical.choose_spec (hswap i))).2
  have hnc01 : ¬ Commute (τ 0) (τ 1) := fun hc => hadj 0 1 rfl hc.eq
  obtain ⟨a0, a1, a2, ha01, ha12, ha02, hτ0', hτ1'⟩ :=
    CFSG.GroupTheory.exists_swap_swap_of_not_commute (hpq 0) (hpq 1) (by
      simpa [hτ 0, hτ 1] using hnc01)
  have hτ0 : τ 0 = Equiv.swap a0 a1 := (hτ 0).trans hτ0'
  have hτ1 : τ 1 = Equiv.swap a1 a2 := (hτ 1).trans hτ1'
  have hfar02 := hfar 0 2 (by decide) (by decide) (by decide)
  have hfix20 : τ 2 a0 = a0 ∧ τ 2 a1 = a1 := by
    have hc : Commute (τ 2) (Equiv.swap a0 a1) := by
      have h := hfar02.1.symm
      rwa [hτ0] at h
    have hne : τ 2 ≠ Equiv.swap a0 a1 := by
      have h := hfar02.2.symm
      rwa [hτ0] at h
    exact ggQ2s08r6_fixes_of_commute_swap ha01 (hswap 2) hc hne
  have hnc12 : ¬ Commute (τ 1) (τ 2) := fun hc => hadj 1 2 rfl hc.eq
  obtain ⟨a3, ha3a1, ha3a2, hτ2⟩ :=
    ggQ2s08r6_exists_swap_succ ha12 hτ1 (hswap 2) hfix20.2 hnc12
  have ha23 : a2 ≠ a3 := ha3a2.symm
  have ha3a0 : a3 ≠ a0 := by
    intro h
    have hfix := hfix20.1
    rw [hτ2, ← h] at hfix
    rw [Equiv.swap_apply_right] at hfix
    exact ha3a2 hfix.symm
  have hfar03 := hfar 0 3 (by decide) (by decide) (by decide)
  have hfar13 := hfar 1 3 (by decide) (by decide) (by decide)
  have hfix30 : τ 3 a0 = a0 ∧ τ 3 a1 = a1 := by
    have hc : Commute (τ 3) (Equiv.swap a0 a1) := by
      have h := hfar03.1.symm
      rwa [hτ0] at h
    have hne : τ 3 ≠ Equiv.swap a0 a1 := by
      have h := hfar03.2.symm
      rwa [hτ0] at h
    exact ggQ2s08r6_fixes_of_commute_swap ha01 (hswap 3) hc hne
  have hfix31 : τ 3 a1 = a1 ∧ τ 3 a2 = a2 := by
    have hc : Commute (τ 3) (Equiv.swap a1 a2) := by
      have h := hfar13.1.symm
      rwa [hτ1] at h
    have hne : τ 3 ≠ Equiv.swap a1 a2 := by
      have h := hfar13.2.symm
      rwa [hτ1] at h
    exact ggQ2s08r6_fixes_of_commute_swap ha12 (hswap 3) hc hne
  have hnc23 : ¬ Commute (τ 2) (τ 3) := fun hc => hadj 2 3 rfl hc.eq
  obtain ⟨a4, ha4a2, ha4a3, hτ3⟩ :=
    ggQ2s08r6_exists_swap_succ ha3a2.symm hτ2 (hswap 3) hfix31.2 hnc23
  have ha4a0 : a4 ≠ a0 := by
    intro h
    have hfix := hfix30.1
    rw [hτ3, ← h] at hfix
    rw [Equiv.swap_apply_right] at hfix
    exact ha4a3 hfix.symm
  have ha4a1 : a4 ≠ a1 := by
    intro h
    have hfix := hfix30.2
    rw [hτ3, ← h] at hfix
    rw [Equiv.swap_apply_right] at hfix
    exact ha4a3 hfix.symm
  have hfar04 := hfar 0 4 (by decide) (by decide) (by decide)
  have hfar14 := hfar 1 4 (by decide) (by decide) (by decide)
  have hfar24 := hfar 2 4 (by decide) (by decide) (by decide)
  have hfix40 : τ 4 a0 = a0 ∧ τ 4 a1 = a1 := by
    have hc : Commute (τ 4) (Equiv.swap a0 a1) := by
      have h := hfar04.1.symm
      rwa [hτ0] at h
    have hne : τ 4 ≠ Equiv.swap a0 a1 := by
      have h := hfar04.2.symm
      rwa [hτ0] at h
    exact ggQ2s08r6_fixes_of_commute_swap ha01 (hswap 4) hc hne
  have hfix41 : τ 4 a1 = a1 ∧ τ 4 a2 = a2 := by
    have hc : Commute (τ 4) (Equiv.swap a1 a2) := by
      have h := hfar14.1.symm
      rwa [hτ1] at h
    have hne : τ 4 ≠ Equiv.swap a1 a2 := by
      have h := hfar14.2.symm
      rwa [hτ1] at h
    exact ggQ2s08r6_fixes_of_commute_swap ha12 (hswap 4) hc hne
  have hfix42 : τ 4 a2 = a2 ∧ τ 4 a3 = a3 := by
    have hc : Commute (τ 4) (Equiv.swap a2 a3) := by
      have h := hfar24.1.symm
      rwa [hτ2] at h
    have hne : τ 4 ≠ Equiv.swap a2 a3 := by
      have h := hfar24.2.symm
      rwa [hτ2] at h
    exact ggQ2s08r6_fixes_of_commute_swap ha23 (hswap 4) hc hne
  have hnc34 : ¬ Commute (τ 3) (τ 4) := fun hc => hadj 3 4 rfl hc.eq
  obtain ⟨a5, ha5a3, ha5a4, hτ4⟩ :=
    ggQ2s08r6_exists_swap_succ ha4a3.symm hτ3 (hswap 4) hfix42.2 hnc34
  have ha5a0 : a5 ≠ a0 := by
    intro h
    have hfix := hfix40.1
    rw [hτ4, ← h] at hfix
    rw [Equiv.swap_apply_right] at hfix
    exact ha5a4 hfix.symm
  have ha5a1 : a5 ≠ a1 := by
    intro h
    have hfix := hfix40.2
    rw [hτ4, ← h] at hfix
    rw [Equiv.swap_apply_right] at hfix
    exact ha5a4 hfix.symm
  have ha5a2 : a5 ≠ a2 := by
    intro h
    have hfix := hfix41.2
    rw [hτ4, ← h] at hfix
    rw [Equiv.swap_apply_right] at hfix
    exact ha5a4 hfix.symm
  let aFun : Fin 6 → Fin 6 := ![a0, a1, a2, a3, a4, a5]
  have ha_inj : Function.Injective aFun := by
    have h03 : a0 ≠ a3 := ha3a0.symm
    have h04 : a0 ≠ a4 := ha4a0.symm
    have h05 : a0 ≠ a5 := ha5a0.symm
    have h13 : a1 ≠ a3 := ha3a1.symm
    have h14 : a1 ≠ a4 := ha4a1.symm
    have h15 : a1 ≠ a5 := ha5a1.symm
    have h24 : a2 ≠ a4 := ha4a2.symm
    have h25 : a2 ≠ a5 := ha5a2.symm
    have h34 : a3 ≠ a4 := ha4a3.symm
    have h35 : a3 ≠ a5 := ha5a3.symm
    have h45 : a4 ≠ a5 := ha5a4.symm
    exact ggQ2s08r6_vec_inj ha01 ha02 h03 h04 h05 ha12 h13 h14 h15
      ha23 h24 h25 h34 h35 h45
  let a : Fin 6 ≃ Fin 6 := Equiv.ofBijective aFun (Finite.injective_iff_bijective.mp ha_inj)
  have ha0 : a 0 = a0 := by
    change aFun 0 = a0
    rfl
  have ha1 : a 1 = a1 := by
    change aFun 1 = a1
    rfl
  have ha2 : a 2 = a2 := by
    change aFun 2 = a2
    rfl
  have ha3 : a 3 = a3 := by
    change aFun 3 = a3
    rfl
  have ha4 : a 4 = a4 := by
    change aFun 4 = a4
    rfl
  have ha5 : a 5 = a5 := by
    change aFun 5 = a5
    rfl
  refine ⟨a, ?_⟩
  intro i
  fin_cases i
  · simpa [ha0, ha1] using hτ0
  · simpa [ha1, ha2] using hτ1
  · simpa [ha2, ha3] using hτ2
  · simpa [ha3, ha4] using hτ3
  · simpa [ha4, ha5] using hτ4

private instance ggQ2s08r6_instDecidablePredIsSwap :
    DecidablePred (fun σ : Equiv.Perm (Fin 6) => σ.IsSwap) :=
  fun σ => decidable_of_iff (∃ x y : Fin 6, x ≠ y ∧ σ = Equiv.swap x y) Iff.rfl

end CFSG.StandardType
