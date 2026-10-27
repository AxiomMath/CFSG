module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Tactic.NormNum.Ineq

public section

namespace CFSG.StandardType

private lemma sum_orbit_mul_eq {ι : Type*} [DecidableEq ι] (σ : Equiv.Perm ι)
    {m s : ι → ℕ} (hm : ∀ i, m (σ i) = m i) (hs : ∀ i, s (σ i) = s i) (i : ι) :
    ∑ x ∈ (Finset.range (Function.minimalPeriod σ i)).image (fun j => σ^[j] i), m x * s x =
      Function.minimalPeriod σ i * (m i * s i) := by
  have hinj : Set.InjOn (fun j => σ^[j] i) ↑(Finset.range (Function.minimalPeriod σ i)) := by
    simpa using (Function.iterate_injOn_Iio_minimalPeriod (f := σ) (x := i))
  rw [Finset.sum_image hinj]
  calc ∑ j ∈ Finset.range (Function.minimalPeriod σ i), m (σ^[j] i) * s (σ^[j] i)
      = ∑ j ∈ Finset.range (Function.minimalPeriod σ i), m i * s i := by
        refine Finset.sum_congr rfl ?_
        intro j _
        have hmj : m (σ^[j] i) = m i :=
          congrFun (Function.iterate_invariant (funext hm) j) i
        have hsj : s (σ^[j] i) = s i :=
          congrFun (Function.iterate_invariant (funext hs) j) i
        rw [hmj, hsj]
    _ = Function.minimalPeriod σ i * (m i * s i) := by
        rw [Finset.sum_const_nat (fun j _ => rfl), Finset.card_range]

private lemma sdiff_orbit_stable {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι)
    (i : ι)
    {S O : Finset ι}
    (hO : O = (Finset.range (Function.minimalPeriod σ i)).image (fun j => σ^[j] i))
    (hS : ∀ x ∈ S, σ x ∈ S) : ∀ x ∈ S \ O, σ x ∈ S \ O := by
  have hkpos : 0 < Function.minimalPeriod σ i :=
    Function.minimalPeriod_pos_of_mem_periodicPts
      (Function.Injective.mem_periodicPts σ.injective i)
  have hkper : σ^[Function.minimalPeriod σ i] i = i := Function.iterate_minimalPeriod
  intro x hx
  rw [Finset.mem_sdiff] at hx ⊢
  refine ⟨hS x hx.1, ?_⟩
  intro hxO
  rw [hO, Finset.mem_image] at hxO
  obtain ⟨j, hj, hxj⟩ := hxO
  rw [Finset.mem_range] at hj
  have hmem : x ∈ O := by
    rw [hO, Finset.mem_image]
    cases j with
    | zero =>
        have hstep : σ (σ^[Function.minimalPeriod σ i - 1] i) =
            σ^[Function.minimalPeriod σ i - 1 + 1] i :=
          (Function.iterate_succ_apply' (f := σ)
            (n := Function.minimalPeriod σ i - 1) (x := i)).symm
        have hlast : σ (σ^[Function.minimalPeriod σ i - 1] i) = i := by
          rw [hstep, Nat.sub_one_add_one hkpos.ne', hkper]
        have hx_eq : σ^[Function.minimalPeriod σ i - 1] i = x := by
          apply σ.injective
          rw [← hxj]
          simpa using hlast
        exact ⟨_, Finset.mem_range.mpr (by omega), hx_eq⟩
    | succ j' =>
        have hx_eq : σ^[j'] i = x := by
          apply σ.injective
          rw [Function.iterate_succ_apply'] at hxj
          exact hxj
        exact ⟨j', Finset.mem_range.mpr (by omega), hx_eq⟩
  exact hx.2 hmem

private lemma dvd_sum_mul_of_stable_of_nonempty {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) {m s : ι → ℕ} (hm : ∀ i, m (σ i) = m i) (hs : ∀ i, s (σ i) = s i)
    {g : ℕ} (hg : ∀ i, s i ≠ 0 → g ∣ Function.minimalPeriod σ i * m i)
    (S : Finset ι) (hS : ∀ i ∈ S, σ i ∈ S) (hne : S.Nonempty)
    (ih : ∀ T : Finset ι, T ⊂ S → (∀ i ∈ T, σ i ∈ T) → g ∣ ∑ i ∈ T, m i * s i) :
    g ∣ ∑ i ∈ S, m i * s i := by
  classical
  obtain ⟨i, hi⟩ := hne
  let O : Finset ι := (Finset.range (Function.minimalPeriod σ i)).image (fun j => σ^[j] i)
  have hO : O = (Finset.range (Function.minimalPeriod σ i)).image (fun j => σ^[j] i) := rfl
  have hkpos : 0 < Function.minimalPeriod σ i :=
    Function.minimalPeriod_pos_of_mem_periodicPts
      (Function.Injective.mem_periodicPts σ.injective i)
  have hOsub : O ⊆ S := by
    intro x hx
    rw [hO, Finset.mem_image] at hx
    obtain ⟨j, -, rfl⟩ := hx
    induction j with
    | zero => simpa using hi
    | succ j ihj =>
        rw [Function.iterate_succ_apply']
        exact hS _ ihj
  have hiO : i ∈ O := by
    rw [hO, Finset.mem_image]
    exact ⟨0, Finset.mem_range.mpr hkpos, by simp⟩
  have hOsum : ∑ x ∈ O, m x * s x =
      Function.minimalPeriod σ i * (m i * s i) := by
    rw [hO]
    exact sum_orbit_mul_eq σ hm hs i
  have hstable : ∀ x ∈ S \ O, σ x ∈ S \ O := sdiff_orbit_stable σ i hO hS
  have hsplit : ∑ x ∈ S \ O, m x * s x + ∑ x ∈ O, m x * s x = ∑ x ∈ S, m x * s x :=
    Finset.sum_sdiff hOsub
  have hproper : S \ O ⊂ S := Finset.sdiff_ssubset hOsub ⟨i, hiO⟩
  rw [← hsplit, hOsum]
  refine Nat.dvd_add (ih (S \ O) hproper hstable) ?_
  by_cases hsi : s i = 0
  · simp [hsi]
  · obtain ⟨c, hc⟩ := hg i hsi
    refine ⟨c * s i, ?_⟩
    rw [← mul_assoc, hc, mul_assoc]

private lemma dvd_sum_mul_of_stable_finset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) {m s : ι → ℕ} (hm : ∀ i, m (σ i) = m i) (hs : ∀ i, s (σ i) = s i)
    {g : ℕ} (hg : ∀ i, s i ≠ 0 → g ∣ Function.minimalPeriod σ i * m i)
    (S : Finset ι) : (∀ i ∈ S, σ i ∈ S) → g ∣ ∑ i ∈ S, m i * s i := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro hS
    by_cases hne : S.Nonempty
    · exact dvd_sum_mul_of_stable_of_nonempty σ hm hs hg S hS hne ih
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      simp [hne]

theorem dvd_sum_mul_of_perm_invariant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) {m s : ι → ℕ} (hm : ∀ i, m (σ i) = m i) (hs : ∀ i, s (σ i) = s i)
    {g : ℕ} (hg : ∀ i, s i ≠ 0 → g ∣ Function.minimalPeriod σ i * m i) :
    g ∣ ∑ i, m i * s i := by
  simpa using dvd_sum_mul_of_stable_finset σ hm hs hg Finset.univ
    (fun i _ => Finset.mem_univ (σ i))

end CFSG.StandardType
