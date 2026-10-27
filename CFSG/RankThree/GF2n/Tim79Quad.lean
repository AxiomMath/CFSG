module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.RankThree.GF2n.Tim79

open Finset

section Idempotents

variable {K : Type*} [Field K] [Fintype K] [CharP K 2] {E : Type*} [AddCommGroup E] [Module K E]

private noncomputable def idem (τ : E →ₗ[K] E) (μ : K) : E →ₗ[K] E :=
  ∑ i ∈ range (Nat.card K - 1), μ ^ (Nat.card K - 1 - i) • τ ^ i

private theorem idem_apply (τ : E →ₗ[K] E) (μ : K) (x : E) :
    idem τ μ x = ∑ i ∈ range (Nat.card K - 1), μ ^ (Nat.card K - 1 - i) • (τ ^ i) x := by
  simp [idem, LinearMap.sum_apply]

private theorem card_sub_one_cast : ((Nat.card K - 1 : ℕ) : K) = 1 := by
  have h1 : 1 ≤ Nat.card K := Nat.card_pos
  rw [Nat.cast_sub h1, Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero, zero_sub,
    Nat.cast_one, CharTwo.neg_eq]

private theorem pow_card_sub_one (μ : K) (hμ : μ ≠ 0) : μ ^ (Nat.card K - 1) = 1 := by
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.pow_card_sub_one_eq_one μ hμ

private theorem pow_apply_eigen (τ : E →ₗ[K] E) {x : E} {ν : K} (hx : τ x = ν • x) (i : ℕ) :
    (τ ^ i) x = ν ^ i • x := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, Module.End.mul_apply, hx, map_smul, ih, smul_smul, ← pow_succ']

private theorem idem_apply_ne (τ : E →ₗ[K] E) {x : E} {ν : K} (hν : ν ≠ 0) (hx : τ x = ν • x)
    {μ : K} (hμ : μ ≠ 0) (hne : μ ≠ ν) : idem τ μ x = 0 := by
  set m := Nat.card K - 1 with hmdef
  rw [idem_apply]
  simp_rw [pow_apply_eigen τ hx, smul_smul]
  rw [← Finset.sum_smul]
  have hgeom := geom_sum₂_mul ν μ m
  rw [hmdef, pow_card_sub_one ν hν, pow_card_sub_one μ hμ, sub_self] at hgeom
  have hsum : ∑ i ∈ range m, ν ^ i * μ ^ (m - 1 - i) = 0 := by
    rcases mul_eq_zero.mp hgeom with h0 | h0
    · exact h0
    · exact absurd (sub_eq_zero.mp h0).symm hne
  have : ∑ i ∈ range m, μ ^ (m - i) * ν ^ i = 0 := by
    calc ∑ i ∈ range m, μ ^ (m - i) * ν ^ i
        = μ * ∑ i ∈ range m, ν ^ i * μ ^ (m - 1 - i) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          have hi' := Finset.mem_range.mp hi
          have : m - i = (m - 1 - i) + 1 := by omega
          rw [this, pow_succ']
          ring
      _ = 0 := by rw [hsum, mul_zero]
  rw [this, zero_smul]

private theorem apply_idem (τ : E →ₗ[K] E) (hτ : ∀ x, (τ ^ (Nat.card K - 1)) x = x) {μ : K}
    (hμ : μ ≠ 0) (x : E) : τ (idem τ μ x) = μ • idem τ μ x := by
  set m := Nat.card K - 1 with hmdef
  have hμm : μ ^ m = 1 := pow_card_sub_one μ hμ
  set a : ℕ → E := fun i => μ ^ (m + 1 - i) • (τ ^ i) x with ha
  have h0 : a 0 = μ • x := by
    simp only [ha, pow_zero, Nat.sub_zero, pow_succ, hμm, one_mul, Module.End.one_apply]
  have hlast : a m = μ • x := by
    simp only [ha, hτ, Nat.add_sub_cancel_left, pow_one]
  have key1 : τ (idem τ μ x) = ∑ i ∈ range m, a (i + 1) := by
    rw [idem_apply, ← hmdef, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, ← Module.End.mul_apply, ← pow_succ' τ i]
    simp only [ha, Nat.add_sub_add_right]
  have key2 : μ • idem τ μ x = ∑ i ∈ range m, a i := by
    rw [idem_apply, ← hmdef, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    have : m + 1 - i = (m - i) + 1 := by omega
    simp only [ha, smul_smul, this, pow_succ']
  rw [key1, key2]
  have e1 := Finset.sum_range_succ a m
  have e2 := Finset.sum_range_succ' a m
  have e3 := e2.symm.trans e1
  rw [h0, hlast] at e3
  exact add_right_cancel e3

private theorem sum_idem [DecidableEq K] (τ : E →ₗ[K] E) (x : E) :
    ∑ μ : Kˣ, idem τ (μ : K) x = x := by
  set m := Nat.card K - 1 with hmdef
  have hm : 1 ≤ m := by
    have : 2 ≤ Nat.card K := Finite.one_lt_card
    omega
  have hcoef : ∀ i ∈ range m, (∑ μ : Kˣ, ((μ : K) ^ (m - i))) =
      if i = 0 then (-1 : K) else 0 := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [FiniteField.sum_pow_units K (m - i), ← Nat.card_eq_fintype_card, ← hmdef]
    by_cases h0 : i = 0
    · subst h0
      simp
    · have : ¬ m ∣ m - i := fun hd => by
        have := Nat.le_of_dvd (by omega) hd
        omega
      simp [this, h0]
  simp_rw [idem_apply, ← hmdef]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  rw [Finset.sum_congr rfl (fun i hi => by rw [hcoef i hi])]
  rw [Finset.sum_eq_single 0]
  · simp [CharTwo.neg_eq]
  · intro i _ hi
    simp [hi]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

private theorem idem_mem (τ : E →ₗ[K] E) (μ : K) {P : Submodule K E}
    (hP : ∀ x ∈ P, τ x ∈ P) {x : E} (hx : x ∈ P) : idem τ μ x ∈ P := by
  have hpow : ∀ i : ℕ, (τ ^ i) x ∈ P := by
    intro i
    induction i with
    | zero => simpa using hx
    | succ i ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hP _ ih
  rw [idem_apply]
  exact Submodule.sum_mem _ fun i _ => P.smul_mem _ (hpow i)

private theorem idem_idem_ne (τ : E →ₗ[K] E) (hτ : ∀ x, (τ ^ (Nat.card K - 1)) x = x) {μ ν : K}
    (hμ : μ ≠ 0) (hν : ν ≠ 0) (hne : μ ≠ ν) (x : E) : idem τ μ (idem τ ν x) = 0 :=
  idem_apply_ne τ hν (apply_idem τ hτ hν x) hμ hne

end Idempotents

section QuadFacts

variable {K : Type*} [Field K] [CharP K 2] {E : Type*} [AddCommGroup E] [Module K E]
  (B : LinearMap.BilinForm K E) (Qf : E → K)

private theorem bilin_symm (hBalt : ∀ x, B x x = 0) (x y : E) : B x y = B y x := by
  have h := hBalt (x + y)
  simp only [map_add, LinearMap.add_apply, hBalt, zero_add, add_zero] at h
  exact (CharTwo.add_eq_zero.mp h).symm

private theorem eig_orth (τ : E →ₗ[K] E) (c : K) (hτB : ∀ x y, B (τ x) (τ y) = c * B x y)
    {x y : E} {μ ν : K} (hx : τ x = μ • x) (hy : τ y = ν • y) (h : μ * ν ≠ c) : B x y = 0 := by
  have h1 := hτB x y
  rw [hx, hy] at h1
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
  have h2 : (μ * ν - c) * B x y = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) h
  · exact h3

private theorem eig_sing (τ : E →ₗ[K] E) (c : K) (hQ : ∀ (a : K) x, Qf (a • x) = a ^ 2 * Qf x)
    (hτQ : ∀ x, Qf (τ x) = c * Qf x) {x : E} {μ : K} (hx : τ x = μ • x) (h : μ ^ 2 ≠ c) :
    Qf x = 0 := by
  have h1 := hτQ x
  rw [hx, hQ] at h1
  have h2 : (μ ^ 2 - c) * Qf x = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) h
  · exact h3

private theorem eq_of_sq_eq {μ ν : K} (h : μ ^ 2 = ν ^ 2) : μ = ν := by
  have h1 : (μ + ν) ^ 2 = 0 := by rw [CharTwo.add_sq, h, CharTwo.add_self_eq_zero]
  exact CharTwo.add_eq_zero.mp (pow_eq_zero_iff (two_ne_zero)|>.mp h1)

private theorem qf_sum_eq_zero (hQB : ∀ x y, Qf (x + y) = Qf x + Qf y + B x y)
    (hQ0 : Qf 0 = 0) {ι : Type*} (s : Finset ι) (y : ι → E) (h1 : ∀ i ∈ s, Qf (y i) = 0)
    (h2 : ∀ i ∈ s, ∀ j ∈ s, B (y i) (y j) = 0) : Qf (∑ i ∈ s, y i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hQ0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, hQB, h1 a (Finset.mem_insert_self a s),
      ih (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
        (fun i hi j hj => h2 i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))]
    rw [map_sum]
    rw [Finset.sum_eq_zero (fun j hj => h2 a (Finset.mem_insert_self a s) j
      (Finset.mem_insert_of_mem hj))]
    simp

end QuadFacts

private theorem sq_cpow_half {K : Type*} [Field K] [Finite K] [CharP K 2] (c : K) :
    (c ^ (Nat.card K / 2)) ^ 2 = c := by
  haveI : Fintype K := Fintype.ofFinite K
  have h2 : Fintype.card K % 2 = 0 :=
    FiniteField.even_card_iff_char_two.mp (ringChar.eq K 2)
  rw [← pow_mul, Nat.card_eq_fintype_card, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h2)]
  exact FiniteField.pow_card c

theorem exists_isCompl_totallySingular_of_stable
    {K : Type*} [Field K] [Finite K] [CharP K 2] {E : Type*} [AddCommGroup E] [Module K E]
    (B : LinearMap.BilinForm K E) (Qf : E → K) (hBalt : ∀ x, B x x = 0)
    (hQ : ∀ (a : K) x, Qf (a • x) = a ^ 2 * Qf x)
    (hQB : ∀ x y, Qf (x + y) = Qf x + Qf y + B x y)
    (τ : E →ₗ[K] E) (c : K) (hc : c ≠ 0) (hτB : ∀ x y, B (τ x) (τ y) = c * B x y)
    (hτQ : ∀ x, Qf (τ x) = c * Qf x) (hτ : ∀ x, (τ ^ (Nat.card K - 1)) x = x)
    (P : Submodule K E) (hPτ : ∀ x ∈ P, τ x ∈ P)
    (hBnd : ∀ x ∈ P, (∀ y ∈ P, B x y = 0) → x = 0)
    (hiso : ∀ x ∈ P, ∀ y ∈ P, τ x = c ^ (Nat.card K / 2) • x →
      τ y = c ^ (Nat.card K / 2) • y → B x y = 0) :
    ∃ S₁ S₂ : Submodule K E, S₁ ≤ P ∧ S₂ ≤ P ∧ Disjoint S₁ S₂ ∧ S₁ ⊔ S₂ = P ∧
      (∀ x ∈ S₁, Qf x = 0) ∧ (∀ x ∈ S₂, Qf x = 0) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  set μ₀ : K := c ^ (Nat.card K / 2) with hμ₀def
  have hμ₀sq : μ₀ ^ 2 = c := sq_cpow_half c
  have hμ₀ne : μ₀ ≠ 0 := fun h => hc (by rw [← hμ₀sq, h]; simp)
  obtain ⟨u₀, hu₀⟩ : ∃ u : Kˣ, (u : K) = μ₀ := ⟨Units.mk0 μ₀ hμ₀ne, rfl⟩
  have hQ0 : Qf 0 = 0 := by simpa using hQ 0 0
  have hy_mem : ∀ {x : E}, x ∈ P → ∀ ν : Kˣ, idem τ (ν : K) x ∈ P :=
    fun hx ν => idem_mem τ (ν : K) hPτ hx
  have hy_eig : ∀ (x : E) (ν : Kˣ), τ (idem τ (ν : K) x) = (ν : K) • idem τ (ν : K) x :=
    fun x ν => apply_idem τ hτ ν.ne_zero x
  have hdec : ∀ x : E, ∑ ν : Kˣ, idem τ (ν : K) x = x := fun x => sum_idem τ x
  have hy0 : ∀ x ∈ P, idem τ (u₀ : K) x = 0 := by
    intro x hx
    refine hBnd _ (hy_mem hx u₀) fun z hz => ?_
    rw [← hdec z, map_sum]
    refine Finset.sum_eq_zero fun ν _ => ?_
    by_cases hν : ν = u₀
    · subst hν
      exact hiso _ (hy_mem hx ν) _ (hy_mem hz ν) (by rw [hy_eig, hu₀]) (by rw [hy_eig, hu₀])
    · refine eig_orth B τ c hτB (hy_eig x u₀) (hy_eig z ν) ?_
      intro h
      apply hν
      apply Units.ext
      rw [hu₀]
      apply mul_left_cancel₀ hμ₀ne
      rw [← hμ₀sq, sq] at h
      rw [hu₀] at h
      exact h
  obtain ⟨e, he⟩ := Countable.exists_injective_nat K
  let a : Kˣ → Prop := fun ν => e (ν : K) < e (c / (ν : K))
  let b : Kˣ → Prop := fun ν => e (c / (ν : K)) < e (ν : K)
  have hab : ∀ ν, ¬ (a ν ∧ b ν) := fun ν h => lt_asymm h.1 h.2
  have hnab : ∀ ν : Kˣ, ¬ a ν → ¬ b ν → ν = u₀ := by
    intro ν h1 h2
    have h3 : (ν : K) = c / ν := he (le_antisymm (not_lt.mp h2) (not_lt.mp h1))
    have h4 : c = (ν : K) * ν := (div_eq_iff ν.ne_zero).mp h3.symm
    have h5 : (ν : K) ^ 2 = μ₀ ^ 2 := by rw [hμ₀sq, h4, sq]
    exact Units.ext (by rw [hu₀]; exact eq_of_sq_eq h5)
  let S : (Kˣ → Prop) → Submodule K E := fun A =>
    P ⊓ ⨅ ν : Kˣ, ⨅ (_ : ¬ A ν), LinearMap.ker (idem τ (ν : K))
  have memS : ∀ (A : Kˣ → Prop) (x : E),
      x ∈ S A ↔ x ∈ P ∧ ∀ ν : Kˣ, ¬ A ν → idem τ (ν : K) x = 0 := by
    intro A x
    simp [S, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
  have hF1 : ∀ (A : Kˣ → Prop) [DecidablePred A] (x : E), x ∈ S A →
      x = ∑ ν ∈ Finset.univ.filter A, idem τ (ν : K) x := by
    intro A _ x hx
    obtain ⟨-, hxz⟩ := (memS A x).mp hx
    conv_lhs => rw [← hdec x]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ A,
      Finset.sum_eq_zero (fun ν hν => hxz ν (Finset.mem_filter.mp hν).2), add_zero]
  have hF3 : ∀ (A : Kˣ → Prop) [DecidablePred A] (x : E), x ∈ P →
      ∑ ν ∈ Finset.univ.filter A, idem τ (ν : K) x ∈ S A := by
    intro A _ x hx
    rw [memS]
    refine ⟨Submodule.sum_mem _ fun ν _ => hy_mem hx ν, fun ν' hν' => ?_⟩
    rw [map_sum]
    refine Finset.sum_eq_zero fun ν hν => ?_
    have hne : ν' ≠ ν := fun h => hν' (h ▸ (Finset.mem_filter.mp hν).2)
    exact idem_idem_ne τ hτ ν'.ne_zero ν.ne_zero (fun h => hne (Units.ext h)) x
  have hF4 : ∀ (A : Kˣ → Prop) [DecidablePred A], (∀ ν, A ν → (ν : K) ^ 2 ≠ c) →
      (∀ ν ν', A ν → A ν' → (ν : K) * ν' ≠ c) → ∀ x ∈ S A, Qf x = 0 := by
    intro A _ hA1 hA2 x hx
    rw [hF1 A x hx]
    refine qf_sum_eq_zero B Qf hQB hQ0 _ _ (fun ν hν => ?_) (fun ν hν ν' hν' => ?_)
    · exact eig_sing Qf τ c hQ hτQ (hy_eig x ν) (hA1 ν (Finset.mem_filter.mp hν).2)
    · exact eig_orth B τ c hτB (hy_eig x ν) (hy_eig x ν')
        (hA2 ν ν' (Finset.mem_filter.mp hν).2 (Finset.mem_filter.mp hν').2)
  have ha1 : ∀ ν, a ν → (ν : K) ^ 2 ≠ c := by
    intro ν hν h
    have h3 : c / (ν : K) = ν := by rw [div_eq_iff ν.ne_zero, ← h, sq]
    have hν' : e (ν : K) < e (c / (ν : K)) := hν
    rw [h3] at hν'
    exact lt_irrefl _ hν'
  have hb1 : ∀ ν, b ν → (ν : K) ^ 2 ≠ c := by
    intro ν hν h
    have h3 : c / (ν : K) = ν := by rw [div_eq_iff ν.ne_zero, ← h, sq]
    have hν' : e (c / (ν : K)) < e (ν : K) := hν
    rw [h3] at hν'
    exact lt_irrefl _ hν'
  have ha2 : ∀ ν ν', a ν → a ν' → (ν : K) * ν' ≠ c := by
    intro ν ν' h1 h2 h
    have h3 : c / (ν : K) = ν' := by rw [div_eq_iff ν.ne_zero, ← h, mul_comm]
    have h4 : c / (ν' : K) = ν := by rw [div_eq_iff ν'.ne_zero, ← h]
    have h1' : e (ν : K) < e (ν' : K) := by rw [← h3]; exact h1
    have h2' : e (ν' : K) < e (ν : K) := by rw [← h4]; exact h2
    exact lt_asymm h1' h2'
  have hb2 : ∀ ν ν', b ν → b ν' → (ν : K) * ν' ≠ c := by
    intro ν ν' h1 h2 h
    have h3 : c / (ν : K) = ν' := by rw [div_eq_iff ν.ne_zero, ← h, mul_comm]
    have h4 : c / (ν' : K) = ν := by rw [div_eq_iff ν'.ne_zero, ← h]
    have h1' : e (ν' : K) < e (ν : K) := by rw [← h3]; exact h1
    have h2' : e (ν : K) < e (ν' : K) := by rw [← h4]; exact h2
    exact lt_asymm h1' h2'
  refine ⟨S a, S b, inf_le_left, inf_le_left, ?_, ?_, hF4 a ha1 ha2, hF4 b hb1 hb2⟩
  · rw [Submodule.disjoint_def]
    intro x hx1 hx2
    obtain ⟨-, hz1⟩ := (memS a x).mp hx1
    obtain ⟨-, hz2⟩ := (memS b x).mp hx2
    rw [← hdec x]
    refine Finset.sum_eq_zero fun ν _ => ?_
    by_cases h : a ν
    · exact hz2 ν (fun hb => hab ν ⟨h, hb⟩)
    · exact hz1 ν h
  · refine le_antisymm (sup_le inf_le_left inf_le_left) fun x hx => ?_
    rw [Submodule.mem_sup]
    refine ⟨∑ ν ∈ Finset.univ.filter a, idem τ (ν : K) x, hF3 a x hx,
      ∑ ν ∈ Finset.univ.filter b, idem τ (ν : K) x, hF3 b x hx, ?_⟩
    conv_rhs => rw [← hdec x]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ a]
    congr 1
    refine Finset.sum_subset ?_ fun ν hν hνb => ?_
    · intro ν hν
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ ν, fun ha => hab ν ⟨ha, (Finset.mem_filter.mp hν).2⟩⟩
    · have hna := (Finset.mem_filter.mp hν).2
      have hnb : ¬ b ν := fun h => hνb (Finset.mem_filter.mpr ⟨Finset.mem_univ ν, h⟩)
      rw [hnab ν hna hnb]
      exact hy0 x hx

theorem exists_isCompl_totallySingular_of_eigenvector {K : Type*} [Field K] [Finite K]
    [CharP K 2] {E : Type*} [AddCommGroup E] [Module K E] (B : LinearMap.BilinForm K E)
    (Qf : E → K) (hBalt : ∀ x, B x x = 0) (hBnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hQ : ∀ (a : K) x, Qf (a • x) = a ^ 2 * Qf x)
    (hQB : ∀ x y, Qf (x + y) = Qf x + Qf y + B x y) (τ : E →ₗ[K] E) (c : K) (hc : c ≠ 0)
    (hτB : ∀ x y, B (τ x) (τ y) = c * B x y) (hτQ : ∀ x, Qf (τ x) = c * Qf x)
    (hτ : ∀ x, (τ ^ (Nat.card K - 1)) x = x) (e₀ : E) (κ : K) (he₀ : e₀ ≠ 0)
    (hQe₀ : Qf e₀ = 0) (hτe₀ : τ e₀ = κ • e₀)
    (hiso : ∀ x y, B e₀ x = 0 → B e₀ y = 0 → τ x = c ^ (Nat.card K / 2) • x →
      τ y = c ^ (Nat.card K / 2) • y → B x y = 0) :
    ∃ S₁ S₂ : Submodule K E, IsCompl S₁ S₂ ∧ (∀ x ∈ S₁, Qf x = 0) ∧ (∀ x ∈ S₂, Qf x = 0) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hsymm := bilin_symm B hBalt
  have hm : 1 ≤ Nat.card K - 1 := by
    have : 1 < Nat.card K := Finite.one_lt_card
    omega
  have hκ : κ ≠ 0 := by
    intro h
    have h1 := pow_apply_eigen τ hτe₀ (Nat.card K - 1)
    rw [hτ e₀, h, zero_pow (by omega), zero_smul] at h1
    exact he₀ h1
  set ρ : K := c / κ with hρ
  have hρne : ρ ≠ 0 := div_ne_zero hc hκ
  have hℓτ : ∀ x, B e₀ (τ x) = ρ * B e₀ x := by
    intro x
    have h := hτB e₀ x
    rw [hτe₀] at h
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    rw [hρ, div_mul_eq_mul_div, eq_div_iff hκ]
    linear_combination h
  have hℓpow : ∀ (i : ℕ) (x : E), B e₀ ((τ ^ i) x) = ρ ^ i * B e₀ x := by
    intro i
    induction i with
    | zero => intro x; simp
    | succ i ih =>
      intro x
      rw [pow_succ, Module.End.mul_apply, ih, hℓτ, pow_succ]
      ring
  obtain ⟨y₀, hy₀⟩ : ∃ y, B e₀ y ≠ 0 := by
    by_contra h
    push Not at h
    exact he₀ (hBnd e₀ h)
  set y₁ : E := (B e₀ y₀)⁻¹ • y₀ with hy₁
  have hy₁1 : B e₀ y₁ = 1 := by
    rw [hy₁, map_smul, smul_eq_mul, inv_mul_cancel₀ hy₀]
  set x₂ : E := idem τ ρ y₁ with hx₂
  have hx₂τ : τ x₂ = ρ • x₂ := apply_idem τ hτ hρne y₁
  have hx₂1 : B e₀ x₂ = 1 := by
    rw [hx₂, idem_apply]
    simp only [map_sum, map_smul, smul_eq_mul, hℓpow, hy₁1, mul_one]
    have : ∀ i ∈ range (Nat.card K - 1), ρ ^ (Nat.card K - 1 - i) * ρ ^ i = 1 := by
      intro i hi
      rw [← pow_add, Nat.sub_add_cancel (Finset.mem_range.mp hi).le, pow_card_sub_one ρ hρne]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      card_sub_one_cast]
  have hBe₀e₀ : B e₀ e₀ = 0 := hBalt e₀
  have hBx₂e₀ : B x₂ e₀ = 1 := by rw [hsymm, hx₂1]
  have hBx₂x₂ : B x₂ x₂ = 0 := hBalt x₂
  set x₂' : E := x₂ + Qf x₂ • e₀ with hx₂'
  have hBe₀x₂' : B e₀ x₂' = 1 := by
    rw [hx₂', map_add, map_smul, hBe₀e₀, smul_zero, add_zero, hx₂1]
  have hBx₂'e₀ : B x₂' e₀ = 1 := by rw [hsymm, hBe₀x₂']
  have hQx₂' : Qf x₂' = 0 := by
    rw [hx₂', hQB, hQ, hQe₀, mul_zero, map_smul, smul_eq_mul, hBx₂e₀, mul_one, add_zero,
      CharTwo.add_self_eq_zero]
  set P : Submodule K E := LinearMap.ker (B e₀) ⊓ LinearMap.ker (B x₂) with hP
  have memP : ∀ x, x ∈ P ↔ B e₀ x = 0 ∧ B x₂ x = 0 := by
    intro x
    simp [hP, Submodule.mem_inf, LinearMap.mem_ker]
  have hdecomp : ∀ w : E, w - (B x₂ w) • e₀ - (B e₀ w) • x₂ ∈ P := by
    intro w
    rw [memP]
    constructor
    · simp only [map_sub, map_smul, smul_eq_mul, hBe₀e₀, hx₂1]
      ring
    · simp only [map_sub, map_smul, smul_eq_mul, hBx₂e₀, hBx₂x₂]
      ring
  have hPτ : ∀ x ∈ P, τ x ∈ P := by
    intro x hx
    rw [memP] at hx ⊢
    refine ⟨by rw [hℓτ, hx.1, mul_zero], ?_⟩
    have h := hτB x₂ x
    rw [hx₂τ] at h
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hx.2, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hρne
  have hBndP : ∀ x ∈ P, (∀ y ∈ P, B x y = 0) → x = 0 := by
    intro x hx hxy
    obtain ⟨hx1, hx2⟩ := (memP x).mp hx
    refine hBnd x fun w => ?_
    have hp := hxy _ (hdecomp w)
    have key : B x w = B x (w - (B x₂ w) • e₀ - (B e₀ w) • x₂) + (B x₂ w) * B x e₀ +
        (B e₀ w) * B x x₂ := by
      simp only [map_sub, map_smul, smul_eq_mul]
      ring
    rw [key, hp, hsymm x e₀, hx1, hsymm x x₂, hx2]
    simp
  have hisoP : ∀ x ∈ P, ∀ y ∈ P, τ x = c ^ (Nat.card K / 2) • x →
      τ y = c ^ (Nat.card K / 2) • y → B x y = 0 :=
    fun x hx y hy hxτ hyτ => hiso x y ((memP x).mp hx).1 ((memP y).mp hy).1 hxτ hyτ
  obtain ⟨T₁, T₂, hT₁P, hT₂P, hdisj, hsup, hT₁, hT₂⟩ :=
    exists_isCompl_totallySingular_of_stable B Qf hBalt hQ hQB τ c hc hτB hτQ hτ P hPτ hBndP hisoP
  have hBe₀P : ∀ s ∈ P, B e₀ s = 0 := fun s hs => ((memP s).mp hs).1
  have hBx₂'P : ∀ s ∈ P, B x₂' s = 0 := by
    intro s hs
    obtain ⟨h1, h2⟩ := (memP s).mp hs
    rw [hx₂', map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, h1, h2]
    simp
  refine ⟨Submodule.span K {e₀} ⊔ T₁, Submodule.span K {x₂'} ⊔ T₂, ⟨?_, ?_⟩, ?_, ?_⟩
  ·
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    obtain ⟨u₁, hu₁, t₁, ht₁, rfl⟩ := Submodule.mem_sup.mp hx1
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hu₁
    obtain ⟨u₂, hu₂, t₂, ht₂, h⟩ := Submodule.mem_sup.mp hx2
    obtain ⟨r', rfl⟩ := Submodule.mem_span_singleton.mp hu₂
    have h1 := congrArg (B e₀) h
    simp only [map_add, map_smul, smul_eq_mul, hBe₀x₂', hBe₀e₀, hBe₀P t₁ (hT₁P ht₁),
      hBe₀P t₂ (hT₂P ht₂), mul_one, mul_zero, add_zero] at h1
    have h2 := congrArg (B x₂') h
    simp only [map_add, map_smul, smul_eq_mul, hBx₂'e₀, hBx₂'P t₁ (hT₁P ht₁),
      hBx₂'P t₂ (hT₂P ht₂), hBalt, mul_one, mul_zero, add_zero] at h2
    rw [h1, ← h2] at h
    simp only [zero_smul, zero_add] at h
    have h0 : t₁ = 0 := by
      have : t₁ ∈ T₁ ⊓ T₂ := ⟨ht₁, h ▸ ht₂⟩
      rwa [disjoint_iff.mp hdisj, Submodule.mem_bot] at this
    rw [← h2, h0]
    simp
  ·
    rw [codisjoint_iff, eq_top_iff]
    intro w _
    have hw : w = (w - (B x₂ w) • e₀ - (B e₀ w) • x₂) + (B x₂ w) • e₀ + (B e₀ w) • x₂ := by
      abel
    have he₀S : e₀ ∈ Submodule.span K {e₀} ⊔ T₁ :=
      Submodule.mem_sup_left (Submodule.mem_span_singleton_self e₀)
    have hx₂'S : x₂' ∈ Submodule.span K {x₂'} ⊔ T₂ :=
      Submodule.mem_sup_left (Submodule.mem_span_singleton_self x₂')
    have hx₂S : x₂ ∈ Submodule.span K {e₀} ⊔ T₁ ⊔ (Submodule.span K {x₂'} ⊔ T₂) := by
      have : x₂ = x₂' - (Qf x₂) • e₀ := by rw [hx₂']; abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.mem_sup_right hx₂'S)
        (Submodule.smul_mem _ _ (Submodule.mem_sup_left he₀S))
    have hp : (w - (B x₂ w) • e₀ - (B e₀ w) • x₂) ∈
        Submodule.span K {e₀} ⊔ T₁ ⊔ (Submodule.span K {x₂'} ⊔ T₂) := by
      obtain ⟨t₁, ht₁, t₂, ht₂, hpt⟩ := Submodule.mem_sup.mp (hsup ▸ hdecomp w)
      rw [← hpt]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_sup_right ht₁))
        (Submodule.mem_sup_right (Submodule.mem_sup_right ht₂))
    rw [hw]
    exact Submodule.add_mem _ (Submodule.add_mem _ hp
      (Submodule.smul_mem _ _ (Submodule.mem_sup_left he₀S)))
      (Submodule.smul_mem _ _ hx₂S)
  · intro x hx
    obtain ⟨u, hu, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [hQB, hQ, hQe₀, hT₁ t ht]
    simp [hBe₀P t (hT₁P ht)]
  · intro x hx
    obtain ⟨u, hu, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [hQB, hQ, hQx₂', hT₂ t ht]
    simp [hBx₂'P t (hT₂P ht)]

end CFSG.RankThree.GF2n.Tim79
