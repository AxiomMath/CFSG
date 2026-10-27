module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.ClosedGoodPathExists

public section

open scoped Pointwise commutatorElement

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]

structure ClosedGoodPath (H : Type) [Group H] [MulAction H V] (Γ : SimpleGraph V)
    [GraphAction H Γ] where
  period : ℕ
  period_pos : 0 < period
  x : ℤ → V
  periodic : ∀ i, x (i + period) = x i
  adj : ∀ i, Γ.Adj (x i) (x (i + 1))
  ne_add_two : ∀ i, x i ≠ x (i + 2)
  good : ∀ (i : ℤ) (s : ℕ) (q : GPath Γ s), (∀ j : ℕ, j ≤ s → q j = x (i + j)) →
    IsGoodPath H q

namespace ClosedGoodPath

variable (W : ClosedGoodPath H Γ)

@[expose] def window (i : ℤ) (s : ℕ) : GPath Γ s where
  toFun j := W.x (i + ((min j s : ℕ) : ℤ))
  adj j hj := by
    have h1 : min j s = j := min_eq_left hj.le
    have h2 : min (j + 1) s = j + 1 := min_eq_left hj
    rw [h1, h2]
    have := W.adj (i + j)
    simpa [add_assoc] using this
  tail j hj := by
    simp [min_eq_right hj]

@[expose] def stab : Subgroup H := ⨅ i, MulAction.stabilizer H (W.x i)

@[expose] def kernelAt (k : ℤ) : Subgroup H :=
  fixingSubgroup H (Γ.neighborSet (W.x k)) ⊓ W.stab

@[expose] def HasThirdFix (K : Subgroup H) (i : ℤ) : Prop :=
  ∃ z, Γ.Adj (W.x i) z ∧ z ≠ W.x (i - 1) ∧ z ≠ W.x (i + 1) ∧ ∀ g ∈ K, g • z = z

@[expose] def shift (k : ℤ) : ClosedGoodPath H Γ where
  period := W.period
  period_pos := W.period_pos
  x i := W.x (i + k)
  periodic i := by
    show W.x (i + W.period + k) = W.x (i + k)
    rw [add_right_comm]
    exact W.periodic (i + k)
  adj i := by
    show Γ.Adj (W.x (i + k)) (W.x (i + 1 + k))
    rw [add_right_comm i 1 k]
    exact W.adj (i + k)
  ne_add_two i := by
    show W.x (i + k) ≠ W.x (i + 2 + k)
    rw [add_right_comm i 2 k]
    exact W.ne_add_two (i + k)
  good i s q hq := W.good (i + k) s q fun j hj => by
    rw [hq j hj]
    show W.x (i + j + k) = W.x (i + k + j)
    rw [add_right_comm]

@[simp] theorem shift_x (k i : ℤ) : (W.shift k).x i = W.x (i + k) := rfl

theorem window_apply (i : ℤ) {s j : ℕ} (hj : j ≤ s) : W.window i s j = W.x (i + (j : ℤ)) := by
  show W.x (i + ((min j s : ℕ) : ℤ)) = W.x (i + (j : ℤ))
  rw [min_eq_left hj]

theorem window_noBack (i : ℤ) (s : ℕ) : (W.window i s).NoBack := by
  intro j hj
  show W.x (i + ((min j s : ℕ) : ℤ)) ≠ W.x (i + ((min (j + 2) s : ℕ) : ℤ))
  rw [min_eq_left (by omega : j ≤ s), min_eq_left hj]
  have h := W.ne_add_two (i + (j : ℤ))
  rwa [show i + (j : ℤ) + 2 = i + ((j + 2 : ℕ) : ℤ) by push_cast; ring] at h

variable {W} in
theorem mem_stab_iff {g : H} : g ∈ W.stab ↔ ∀ i : ℤ, g • W.x i = W.x i := by
  rw [stab, Subgroup.mem_iInf]
  exact forall_congr' fun _ => MulAction.mem_stabilizer_iff

theorem stab_le_stabPath_window (i : ℤ) (s : ℕ) :
    W.stab ≤ GPath.stabPath (H := H) (W.window i s) := by
  intro g hg
  rw [GPath.mem_stabPath_iff]
  intro j hj
  rw [W.window_apply i hj]
  exact (W.mem_stab_iff.mp hg) (i + (j : ℤ))

@[expose] def smul (g : H) : ClosedGoodPath H Γ where
  period := W.period
  period_pos := W.period_pos
  x i := g • W.x i
  periodic i := by
    show g • W.x (i + W.period) = g • W.x i
    rw [W.periodic i]
  adj i := (GraphAction.adj_smul g (W.x i) (W.x (i + 1))).mpr (W.adj i)
  ne_add_two i := by
    intro h
    apply W.ne_add_two i
    have := congrArg (fun v => g⁻¹ • v) h
    simpa using this
  good i s q hq := by
    have hq' : IsGoodPath H (g⁻¹ • q) := by
      apply W.good i s (g⁻¹ • q)
      intro j hj
      rw [GPath.smul_apply, hq j hj]
      exact inv_smul_smul g (W.x (i + (j : ℤ)))
    have hgq : g • (g⁻¹ • q) = q := by
      apply GPath.ext'
      intro j hj
      rw [GPath.smul_apply, GPath.smul_apply]
      simp
    have hgood : IsGoodPath H (g • (g⁻¹ • q)) := hq'.smul g
    rwa [hgq] at hgood

theorem smul_x (g : H) (i : ℤ) : (W.smul g).x i = g • W.x i := rfl

end ClosedGoodPath

theorem ClosedGoodPath.exists_of_noBack [Finite V] [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n) (hW : WeissFree H Γ n)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w) (hL : ∀ z, LocalFacts H Γ z)
    {p : GPath Γ (n + 1)} (hp : p.NoBack) :
    ∃ W : ClosedGoodPath H Γ, ∀ i : ℕ, i ≤ n + 1 → W.x i = p i := by
  obtain ⟨t, x, ht, hper, hadj, hne2, hbase, hgood⟩ :=
    exists_closed_isGoodPath hn hM hW hne hL hp
  exact ⟨⟨t, ht, x, hper, hadj, hne2, hgood⟩, hbase⟩

theorem ClosedGoodPath.x_eq_of_window [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hW : WeissFree H Γ n) (hL : ∀ z, LocalFacts H Γ z) (W W' : ClosedGoodPath H Γ) (k : ℤ)
    (h : ∀ j : ℕ, j ≤ n + 1 → W.x (k + j) = W'.x (k + j)) : ∀ i, W.x i = W'.x i := by
  classical
  have window_apply : ∀ (W : ClosedGoodPath H Γ) (i : ℤ) (j : ℕ), j ≤ n + 1 →
      W.window i (n + 1) j = W.x (i + (j : ℤ)) := by
    intro W i j hj
    show W.x (i + ((min j (n + 1) : ℕ) : ℤ)) = W.x (i + (j : ℤ))
    rw [min_eq_left hj]
  have window_succ_apply : ∀ (W : ClosedGoodPath H Γ) (i : ℤ) (j : ℕ), j ≤ n + 2 →
      W.window i (n + 2) j = W.x (i + (j : ℤ)) := by
    intro W i j hj
    show W.x (i + ((min j (n + 2) : ℕ) : ℤ)) = W.x (i + (j : ℤ))
    rw [min_eq_left hj]
  have step_fwd : ∀ m : ℤ, (∀ j : ℕ, j ≤ n + 1 → W.x (m + j) = W'.x (m + j)) →
      W.x (m + (n + 2)) = W'.x (m + (n + 2)) := by
    intro m hm
    let p : GPath Γ (n + 1) := W.window m (n + 1)
    have hp_eq : p = W'.window m (n + 1) := by
      apply GPath.ext'
      intro j hj
      rw [window_apply W m j hj, window_apply W' m j hj]
      exact hm j hj
    have hadjW : Γ.Adj (p (n + 1)) (W.x (m + (n + 2))) := by
      have h1 : p (n + 1) = W.x (m + (n + 1)) := by
        rw [show p = W.window m (n + 1) from rfl]
        exact window_apply W m (n + 1) (by omega)
      rw [h1]
      have h2 := W.adj (m + ((n + 1 : ℕ) : ℤ))
      have hidx : m + ((n + 1 : ℕ) : ℤ) + 1 = m + (n + 2) := by
        push_cast
        ring
      rwa [hidx] at h2
    have hadjW' : Γ.Adj (p (n + 1)) (W'.x (m + (n + 2))) := by
      have h1 : p (n + 1) = W'.x (m + (n + 1)) := by
        rw [hp_eq]
        exact window_apply W' m (n + 1) (by omega)
      rw [h1]
      have h2 := W'.adj (m + ((n + 1 : ℕ) : ℤ))
      have hidx : m + ((n + 1 : ℕ) : ℤ) + 1 = m + (n + 2) := by
        push_cast
        ring
      rwa [hidx] at h2
    have hgoodW : IsGoodPath H (p.snoc (W.x (m + (n + 2))) hadjW) := by
      have heq : p.snoc (W.x (m + (n + 2))) hadjW = W.window m (n + 2) := by
        apply GPath.ext'
        intro j hj
        by_cases hjn : j ≤ n + 1
        · rw [GPath.snoc_of_le _ _ _ hjn]
          rw [show p j = W.x (m + (j : ℤ)) from window_apply W m j hjn]
          exact (window_succ_apply W m j (by omega)).symm
        · have hj' : j = n + 2 := by omega
          subst hj'
          rw [GPath.snoc_last]
          exact (window_succ_apply W m (n + 2) le_rfl).symm
      rw [heq]
      exact W.good m (n + 2) (W.window m (n + 2)) fun j hj => by
        rw [window_succ_apply W m j hj]
    have hgoodW' : IsGoodPath H (p.snoc (W'.x (m + (n + 2))) hadjW') := by
      have heq : p.snoc (W'.x (m + (n + 2))) hadjW' = W'.window m (n + 2) := by
        apply GPath.ext'
        intro j hj
        by_cases hjn : j ≤ n + 1
        · rw [GPath.snoc_of_le _ _ _ hjn]
          rw [show p j = W'.x (m + (j : ℤ)) from by
            rw [hp_eq]
            exact window_apply W' m j hjn]
          rw [window_succ_apply W' m j (by omega)]
        · have hj' : j = n + 2 := by omega
          subst hj'
          rw [GPath.snoc_last]
          exact (window_succ_apply W' m (n + 2) le_rfl).symm
      rw [heq]
      exact W'.good m (n + 2) (W'.window m (n + 2)) fun j hj => by
        rw [window_succ_apply W' m j hj]
    exact isGoodPath_snoc_unique hn hW hL (s := n + 1) (by omega) hadjW hadjW' hgoodW hgoodW'
  have step_bwd : ∀ m : ℤ, (∀ j : ℕ, j ≤ n + 1 → W.x (m + j) = W'.x (m + j)) →
      W.x (m - 1) = W'.x (m - 1) := by
    intro m hm
    let p : GPath Γ (n + 1) := (W.window m (n + 1)).rev
    have hp_eq : p = (W'.window m (n + 1)).rev := by
      rw [show p = (W.window m (n + 1)).rev from rfl]
      congr 1
      apply GPath.ext'
      intro j hj
      rw [window_apply W m j hj, window_apply W' m j hj]
      exact hm j hj
    have hadjW : Γ.Adj (p (n + 1)) (W.x (m - 1)) := by
      have h1 : p (n + 1) = W.x m := by
        rw [show p = (W.window m (n + 1)).rev from rfl, GPath.rev_apply _ (by omega)]
        rw [show n + 1 - (n + 1) = 0 by omega]
        rw [window_apply W m 0 (by omega)]
        simp
      rw [h1]
      have h2 := W.adj (m - 1)
      rw [show m - 1 + 1 = m by omega] at h2
      exact h2.symm
    have hadjW' : Γ.Adj (p (n + 1)) (W'.x (m - 1)) := by
      have h1 : p (n + 1) = W'.x m := by
        rw [show p = (W'.window m (n + 1)).rev from hp_eq, GPath.rev_apply _ (by omega)]
        rw [show n + 1 - (n + 1) = 0 by omega]
        rw [window_apply W' m 0 (by omega)]
        simp
      rw [h1]
      have h2 := W'.adj (m - 1)
      rw [show m - 1 + 1 = m by omega] at h2
      exact h2.symm
    have hgoodW : IsGoodPath H (p.snoc (W.x (m - 1)) hadjW) := by
      have heq : p.snoc (W.x (m - 1)) hadjW = (W.window (m - 1) (n + 2)).rev := by
        apply GPath.ext'
        intro j hj
        by_cases hjn : j ≤ n + 1
        · rw [GPath.snoc_of_le _ _ _ hjn]
          show (W.window m (n + 1)).rev j = (W.window (m - 1) (n + 2)).rev j
          rw [GPath.rev_apply _ hjn, GPath.rev_apply _ (by omega)]
          rw [window_apply W m (n + 1 - j) (by omega)]
          rw [window_succ_apply W (m - 1) (n + 2 - j) (by omega)]
          congr 1
          omega
        · have hj' : j = n + 2 := by omega
          subst hj'
          rw [GPath.snoc_last, GPath.rev_apply _ (by omega)]
          rw [window_succ_apply W (m - 1) (n + 2 - (n + 2)) (by omega)]
          congr 1
          omega
      rw [heq]
      exact (W.good (m - 1) (n + 2) (W.window (m - 1) (n + 2)) fun j hj => by
        rw [window_succ_apply W (m - 1) j hj]).rev
    have hgoodW' : IsGoodPath H (p.snoc (W'.x (m - 1)) hadjW') := by
      have heq : p.snoc (W'.x (m - 1)) hadjW' = (W'.window (m - 1) (n + 2)).rev := by
        apply GPath.ext'
        intro j hj
        by_cases hjn : j ≤ n + 1
        · rw [GPath.snoc_of_le _ _ _ hjn]
          rw [show p j = (W'.window m (n + 1)).rev j from by rw [hp_eq]]
          rw [GPath.rev_apply _ hjn, GPath.rev_apply _ (by omega)]
          rw [window_apply W' m (n + 1 - j) (by omega)]
          rw [window_succ_apply W' (m - 1) (n + 2 - j) (by omega)]
          congr 1
          omega
        · have hj' : j = n + 2 := by omega
          subst hj'
          rw [GPath.snoc_last, GPath.rev_apply _ (by omega)]
          rw [window_succ_apply W' (m - 1) (n + 2 - (n + 2)) (by omega)]
          congr 1
          omega
      rw [heq]
      exact (W'.good (m - 1) (n + 2) (W'.window (m - 1) (n + 2)) fun j hj => by
        rw [window_succ_apply W' (m - 1) j hj]).rev
    exact isGoodPath_snoc_unique hn hW hL (s := n + 1) (by omega) hadjW hadjW' hgoodW hgoodW'
  have window_fwd : ∀ m : ℕ, (∀ j : ℕ, j ≤ n + 1 → W.x ((k + m) + j) = W'.x ((k + m) + j)) := by
    intro m
    induction m with
    | zero => simpa using h
    | succ m ih =>
      intro j hj
      by_cases hjn : j ≤ n
      · have hprev := ih (j + 1) (by omega)
        have hcast : (k + (m + 1 : ℕ)) + (j : ℤ) = (k + m) + ((j + 1 : ℕ) : ℤ) := by
          push_cast
          ring
        rw [hcast]
        exact hprev
      · have hj' : j = n + 1 := by omega
        subst hj'
        have hs := step_fwd (k + (m : ℤ)) ih
        have hcast : (k + (m + 1 : ℕ)) + ((n + 1 : ℕ) : ℤ) =
            (k + m) + ((n : ℤ) + 2) := by
          push_cast
          ring
        rw [hcast]
        exact hs
  have window_bwd : ∀ m : ℕ, (∀ j : ℕ, j ≤ n + 1 → W.x ((k - m) + j) = W'.x ((k - m) + j)) := by
    intro m
    induction m with
    | zero => simpa using h
    | succ m ih =>
      intro j hj
      by_cases hj0 : j = 0
      · subst hj0
        have hs := step_bwd (k - (m : ℤ)) ih
        have hcast : (k - ((m + 1 : ℕ) : ℤ)) + ((0 : ℕ) : ℤ) = (k - (m : ℤ)) - 1 := by
          push_cast
          ring
        rw [hcast]
        exact hs
      · have hj1 : 1 ≤ j := by omega
        have hprev : W.x ((k - m) + ((j : ℤ) - 1)) = W'.x ((k - m) + ((j : ℤ) - 1)) := by
          have h := ih (j - 1) (by omega)
          simpa [Nat.cast_sub hj1] using h
        have hcast : (k - (m + 1 : ℕ)) + (j : ℤ) = (k - m) + ((j : ℤ) - 1) := by
          push_cast
          ring
        rw [hcast]
        exact hprev
  intro i
  by_cases hik : k ≤ i
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, i = k + m := by
      refine ⟨(i - k).toNat, ?_⟩
      have hnonneg : 0 ≤ i - k := by omega
      have hcast : (((i - k).toNat : ℕ) : ℤ) = i - k := Int.toNat_of_nonneg hnonneg
      rw [hcast]
      ring
    rw [hm]
    simpa using window_fwd m 0 (by omega)
  · have hik' : i ≤ k - 1 := by omega
    obtain ⟨m, hm⟩ : ∃ m : ℕ, i = k - m := by
      refine ⟨(k - i).toNat, ?_⟩
      have hnonneg : 0 ≤ k - i := by omega
      have hcast : (((k - i).toNat : ℕ) : ℤ) = k - i := Int.toNat_of_nonneg hnonneg
      rw [hcast]
      ring
    rw [hm]
    simpa using window_bwd m 0 (by omega)

theorem ClosedGoodPath.stabPath_window [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hW : WeissFree H Γ n) (hL : ∀ z, LocalFacts H Γ z) (W : ClosedGoodPath H Γ) (i : ℤ) :
    GPath.stabPath (H := H) (W.window i (n + 1)) = W.stab := by
  apply le_antisymm
  · intro g hg
    rw [ClosedGoodPath.stab, Subgroup.mem_iInf]
    intro m
    rw [MulAction.mem_stabilizer_iff]
    have hsame : ∀ j : ℕ, j ≤ n + 1 →
        W.x (i + j) = (ClosedGoodPath.smul W g).x (i + j) := by
      intro j hj
      show W.x (i + (j : ℤ)) = g • W.x (i + (j : ℤ))
      have hfix := GPath.mem_stabPath_iff.mp hg j hj
      rw [show W.window i (n + 1) j = W.x (i + (j : ℤ)) from by
        show W.x (i + ((min j (n + 1) : ℕ) : ℤ)) = W.x (i + (j : ℤ))
        rw [min_eq_left hj]] at hfix
      exact hfix.symm
    have hx := ClosedGoodPath.x_eq_of_window hn hW hL W (ClosedGoodPath.smul W g) i hsame m
    exact hx.symm
  · intro g hg
    rw [GPath.mem_stabPath_iff]
    intro j hj
    have hfix : g ∈ W.stab := hg
    rw [ClosedGoodPath.stab, Subgroup.mem_iInf] at hfix
    have h := hfix (i + (j : ℤ))
    rw [MulAction.mem_stabilizer_iff] at h
    rw [show W.window i (n + 1) j = W.x (i + (j : ℤ)) from by
      show W.x (i + ((min j (n + 1) : ℕ) : ℤ)) = W.x (i + (j : ℤ))
      rw [min_eq_left hj]]
    exact h

theorem ClosedGoodPath.kernelAt_eq_map_conj (W W' : ClosedGoodPath H Γ) {g : H}
    (hg : ∀ i, g • W.x i = W'.x i) (k : ℤ) :
    W'.kernelAt k = (W.kernelAt k).map (MulAut.conj g).toMonoidHom := by
  have hstab : W'.stab = W.stab.map (MulAut.conj g).toMonoidHom := by
    rw [ClosedGoodPath.stab, ClosedGoodPath.stab,
      Subgroup.map_iInf _ (MulAut.conj g).injective]
    apply iInf_congr
    intro i
    rw [← hg i]
    exact MulAction.stabilizer_smul_eq_stabilizer_map_conj g (W.x i)
  rw [ClosedGoodPath.kernelAt, ClosedGoodPath.kernelAt, ← hg k,
    fixingSubgroup_neighborSet_smul, hstab,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective]

end CFSG.Quasithin.Stroth.WeissDelta

end
