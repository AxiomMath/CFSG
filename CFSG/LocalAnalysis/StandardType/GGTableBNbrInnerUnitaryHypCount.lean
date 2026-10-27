module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.UnitaryFlag

theorem exists_perm_ne_zero_of_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*}
    [CommRing R] {M : Matrix ι ι R} (h : M.det ≠ 0) :
    ∃ σ : Equiv.Perm ι, ∀ i, M (σ i) i ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply h
  rw [Matrix.det_apply]
  refine Finset.sum_eq_zero fun σ _ => ?_
  obtain ⟨i, hi⟩ := hcon σ
  rw [Finset.prod_eq_zero (f := fun j => M (σ j) j) (Finset.mem_univ i) hi, smul_zero]

lemma eq_one_of_sq_eq_one_of_odd {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x : G} (h2 : x ^ 2 = 1) (hp' : x ^ p = 1) : x = 1 := by
  have hdvd2 : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
  have hdvdp : orderOf x ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hp'
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (h ▸ hdvdp) fun h2p =>
      (Nat.dvd_prime hp).mp h2p |>.elim (fun h1 => absurd h1 (by norm_num)) fun h1 => hp2 h1.symm

lemma apply_iterate_eq_ite {K : Type*} [Group K] {ι : Type*} (τ : Equiv.Perm ι) (t : ι → K)
    (hτ : ∀ i, t (τ i) = (t i)⁻¹) (i : ι) (k : ℕ) :
    t (τ^[k] i) = if Even k then t i else (t i)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', hτ, ih]
    by_cases hk : Even k <;> simp [Nat.even_add_one, hk]

lemma apply_eq_of_sameCycle {K : Type*} [Group K] {ι : Type*} [Fintype ι] (τ : Equiv.Perm ι)
    {t t' : ι → K} (ht : ∀ i, t (τ i) = (t i)⁻¹) (ht' : ∀ i, t' (τ i) = (t' i)⁻¹)
    {i j : ι} (hij : τ.SameCycle i j) (h : t i = t' i) : t j = t' j := by
  obtain ⟨k, hk⟩ := hij.exists_nat_pow_eq
  rw [← hk, show (τ ^ k) i = τ^[k] i from congrFun (Equiv.Perm.coe_pow τ k) i,
    apply_iterate_eq_ite τ t ht i k, apply_iterate_eq_ite τ t' ht' i k, h]

lemma minimalPeriod_eq_of_sameCycle {ι : Type*} [Fintype ι] (τ : Equiv.Perm ι) {i j : ι}
    (h : τ.SameCycle i j) :
    Function.minimalPeriod τ i = Function.minimalPeriod τ j := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  obtain ⟨m, hm⟩ := h.symm.exists_nat_pow_eq
  have hji : Function.IsPeriodicPt τ (Function.minimalPeriod τ i) j := by
    show τ^[Function.minimalPeriod τ i] j = j
    rw [← hn, show (τ ^ n) i = τ^[n] i from congrFun (Equiv.Perm.coe_pow τ n) i,
      ← Function.iterate_add_apply, Nat.add_comm, Function.iterate_add_apply,
      Function.iterate_minimalPeriod]
  have hij : Function.IsPeriodicPt τ (Function.minimalPeriod τ j) i := by
    show τ^[Function.minimalPeriod τ j] i = i
    rw [← hm, show (τ ^ m) j = τ^[m] j from congrFun (Equiv.Perm.coe_pow τ m) j,
      ← Function.iterate_add_apply, Nat.add_comm, Function.iterate_add_apply,
      Function.iterate_minimalPeriod]
  exact Nat.dvd_antisymm (Function.isPeriodicPt_iff_minimalPeriod_dvd.mp hij)
    (Function.isPeriodicPt_iff_minimalPeriod_dvd.mp hji)

lemma eq_one_of_odd_cycle {K : Type*} [Group K] {ι : Type*} [Fintype ι] (τ : Equiv.Perm ι)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {t : ι → K} (hpow : ∀ i, t i ^ p = 1)
    (ht : ∀ i, t (τ i) = (t i)⁻¹) {i : ι} (hodd : Odd (Function.minimalPeriod τ i)) :
    t i = 1 := by
  have h1 : t i = (t i)⁻¹ := by
    have h := apply_iterate_eq_ite τ t ht i (Function.minimalPeriod τ i)
    rw [Function.iterate_minimalPeriod] at h
    rwa [if_neg (Nat.not_even_iff_odd.mpr hodd)] at h
  have h2 : t i ^ 2 = 1 := by
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.mpr h1
  exact eq_one_of_sq_eq_one_of_odd hp hp2 h2 (hpow i)

@[simp] lemma mk_apply_eq_mk {ι : Type*} (τ : Equiv.Perm ι) (y : ι) :
    Quotient.mk (Equiv.Perm.SameCycle.setoid τ) (τ y) =
      Quotient.mk (Equiv.Perm.SameCycle.setoid τ) y :=
  (Quotient.sound (show τ.SameCycle y (τ y) from ⟨1, by simp⟩)).symm

noncomputable def evenClass {ι : Type*} (τ : Equiv.Perm ι)
    (q : Quotient (Equiv.Perm.SameCycle.setoid τ)) : Prop :=
  Even (Function.minimalPeriod τ (Quotient.out q))

lemma ne_apply_self_of_evenClass {ι : Type*} (τ : Equiv.Perm ι)
    {q : Quotient (Equiv.Perm.SameCycle.setoid τ)} (hq : evenClass τ q) :
    τ (Quotient.out q) ≠ Quotient.out q := by
  intro h
  have h1 : Function.minimalPeriod τ (Quotient.out q) = 1 :=
    Function.minimalPeriod_eq_one_iff_isFixedPt.mpr h
  exact Nat.not_even_one (h1 ▸ hq)

noncomputable def evenClassPair {ι : Type*} (τ : Equiv.Perm ι) :
    {q : Quotient (Equiv.Perm.SameCycle.setoid τ) // evenClass τ q} × Bool → ι
  | (q, false) => Quotient.out q.val
  | (q, true) => τ (Quotient.out q.val)

lemma evenClassPair_injective {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : Equiv.Perm ι) :
    Function.Injective (evenClassPair τ) := by
  rintro ⟨q, b⟩ ⟨q', b'⟩ h
  cases b <;> cases b'
  · have h1 : Quotient.out q.val = Quotient.out q'.val := h
    have hq : q = q' := by
      apply Subtype.ext
      rw [← Quotient.out_eq q.val, ← Quotient.out_eq q'.val, h1]
    exact Prod.ext hq rfl
  · have h1 : Quotient.out q.val = τ (Quotient.out q'.val) := h
    have hq : q = q' := by
      apply Subtype.ext
      rw [← Quotient.out_eq q.val, h1, mk_apply_eq_mk τ (Quotient.out q'.val),
        Quotient.out_eq q'.val]
    exact absurd ((Subtype.ext_iff.mp hq) ▸ h1)
      (Ne.symm (ne_apply_self_of_evenClass τ q'.property))
  · have h1 : τ (Quotient.out q.val) = Quotient.out q'.val := h
    have hq : q = q' := by
      apply Subtype.ext
      rw [← Quotient.out_eq q.val, ← Quotient.out_eq q'.val, ← h1,
        mk_apply_eq_mk τ (Quotient.out q.val)]
    exact absurd ((Subtype.ext_iff.mp hq) ▸ h1)
      (ne_apply_self_of_evenClass τ q'.property)
  · have h1 : τ (Quotient.out q.val) = τ (Quotient.out q'.val) := h
    have h2 : Quotient.out q.val = Quotient.out q'.val := τ.injective h1
    have hq : q = q' := by
      apply Subtype.ext
      rw [← Quotient.out_eq q.val, ← Quotient.out_eq q'.val, h2]
    exact Prod.ext hq rfl

lemma card_evenClass_le_half {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : Equiv.Perm ι) :
    Nat.card {q : Quotient (Equiv.Perm.SameCycle.setoid τ) // evenClass τ q} ≤
      Fintype.card ι / 2 := by
  classical
  have h2 : 2 * Fintype.card {q : Quotient (Equiv.Perm.SameCycle.setoid τ) // evenClass τ q} ≤
      Fintype.card ι := by
    have h := Fintype.card_le_of_injective (evenClassPair τ) (evenClassPair_injective τ)
    rw [Fintype.card_prod, Fintype.card_bool] at h
    omega
  have h3 : 2 * Nat.card {q : Quotient (Equiv.Perm.SameCycle.setoid τ) // evenClass τ q} ≤
      Fintype.card ι := by
    rwa [Nat.card_eq_fintype_card]
  exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by rwa [Nat.mul_comm])

noncomputable def evenClassEval {K : Type*} [Field K] {ι : Type*} (τ : Equiv.Perm ι)
    {p : ℕ} (E : Subgroup (ι → Kˣ)) (hE : ∀ t ∈ E, ∀ i, t i ^ p = 1) :
    E → ({q : Quotient (Equiv.Perm.SameCycle.setoid τ) // evenClass τ q} →
      rootsOfUnity p K) :=
  fun t q =>
    ⟨t.val (Quotient.out q.val), by
      rw [mem_rootsOfUnity]
      exact hE t.val t.property (Quotient.out q.val)⟩

lemma evenClassEval_injective {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (τ : Equiv.Perm ι) (E : Subgroup (ι → Kˣ))
    (hE : ∀ t ∈ E, ∀ i, t i ^ p = 1) (hτ : ∀ t ∈ E, ∀ i, t (τ i) = (t i)⁻¹) :
    Function.Injective (evenClassEval τ E hE) := by
  classical
  intro t t' h
  apply Subtype.ext
  funext i
  have hq : ∀ q : {q : Quotient (Equiv.Perm.SameCycle.setoid τ) // evenClass τ q},
      t.val (Quotient.out q.val) = t'.val (Quotient.out q.val) := by
    intro q
    exact Subtype.ext_iff.mp (congrFun h q)
  let q0 : Quotient (Equiv.Perm.SameCycle.setoid τ) := Quotient.mk _ i
  have hs : τ.SameCycle (Quotient.out q0) i := by
    change (Equiv.Perm.SameCycle.setoid τ).r (Quotient.out q0) i
    exact Quotient.exact (Quotient.out_eq q0)
  by_cases hq0 : evenClass τ q0
  · exact apply_eq_of_sameCycle τ (hτ t.val t.property) (hτ t'.val t'.property) hs
      (hq ⟨q0, hq0⟩)
  · have hodd : Odd (Function.minimalPeriod τ i) := by
      have hne : ¬ Even (Function.minimalPeriod τ i) := by
        rw [← minimalPeriod_eq_of_sameCycle τ hs]
        exact hq0
      exact Nat.not_even_iff_odd.mp hne
    rw [eq_one_of_odd_cycle τ hp hp2 (hE t.val t.property) (hτ t.val t.property) hodd,
      eq_one_of_odd_cycle τ hp hp2 (hE t'.val t'.property) (hτ t'.val t'.property) hodd]

lemma card_le_card_evenClass_fun {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (τ : Equiv.Perm ι) (E : Subgroup (ι → Kˣ))
    (hE : ∀ t ∈ E, ∀ i, t i ^ p = 1) (hτ : ∀ t ∈ E, ∀ i, t (τ i) = (t i)⁻¹) :
    Nat.card E ≤ Nat.card ({q : Quotient (Equiv.Perm.SameCycle.setoid τ) // evenClass τ q} →
      rootsOfUnity p K) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fintype (rootsOfUnity p K) := Fintype.ofFinite _
  haveI : Fintype {q : Quotient (Equiv.Perm.SameCycle.setoid τ) // evenClass τ q} :=
    Fintype.ofFinite _
  exact Nat.card_le_card_of_injective (evenClassEval τ E hE)
    (evenClassEval_injective hp hp2 τ E hE hτ)

theorem card_le_pow_of_inv_perm {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (τ : Equiv.Perm ι) (E : Subgroup (ι → Kˣ))
    (hE : ∀ t ∈ E, ∀ i, t i ^ p = 1) (hτ : ∀ t ∈ E, ∀ i, t (τ i) = (t i)⁻¹) :
    Nat.card E ≤ p ^ (Fintype.card ι / 2) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fintype (rootsOfUnity p K) := Fintype.ofFinite _
  calc Nat.card E
      ≤ Nat.card ({q : Quotient (Equiv.Perm.SameCycle.setoid τ) // evenClass τ q} →
          rootsOfUnity p K) := card_le_card_evenClass_fun hp hp2 τ E hE hτ
    _ = Nat.card (rootsOfUnity p K) ^ Nat.card {q // evenClass τ q} := Nat.card_fun
    _ ≤ p ^ Nat.card {q // evenClass τ q} := pow_le_pow_left' (card_rootsOfUnity K p) _
    _ ≤ p ^ (Fintype.card ι / 2) := Nat.pow_le_pow_right hp.pos (card_evenClass_le_half τ)

lemma fpf_involution_of_pair_surjective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : Equiv.Perm ι) (hsurj : Function.Surjective (evenClassPair τ)) :
    (∀ i, τ i ≠ i) ∧ (∀ i, τ (τ i) = i) := by
  classical
  let s := Equiv.Perm.SameCycle.setoid τ
  have hallEven : ∀ q : Quotient s, evenClass τ q := by
    intro q
    obtain ⟨x, hx⟩ := hsurj (Quotient.out q)
    rcases x with ⟨⟨q', hq'⟩, b⟩
    cases b
    · have h1 : Quotient.out q' = Quotient.out q := hx
      have hqq : q = q' := by rw [← Quotient.out_eq q, ← h1, Quotient.out_eq q']
      rwa [hqq]
    · have h1 : τ (Quotient.out q') = Quotient.out q := hx
      have hqq : q = q' := by
        rw [← Quotient.out_eq q, ← h1, mk_apply_eq_mk τ (Quotient.out q'), Quotient.out_eq q']
      rwa [hqq]
  have hcls : ∀ (q : Quotient s) (x : ι), Quotient.mk s x = q →
      x = Quotient.out q ∨ x = τ (Quotient.out q) := by
    intro q x hx
    obtain ⟨y, hy⟩ := hsurj x
    rcases y with ⟨⟨q', hq'⟩, b⟩
    cases b
    · have h1 : Quotient.out q' = x := hy
      left
      have hqq : q' = q := by rw [← Quotient.out_eq q', h1, hx]
      rw [hqq] at h1
      exact h1.symm
    · have h1 : τ (Quotient.out q') = x := hy
      right
      have hqq : q' = q := by
        rw [← Quotient.out_eq q', ← mk_apply_eq_mk τ (Quotient.out q'), h1, hx]
      rw [hqq] at h1
      exact h1.symm
  have htau2 : ∀ q : Quotient s, τ (τ (Quotient.out q)) = Quotient.out q := by
    intro q
    have hmem := hcls q (τ (τ (Quotient.out q)))
      (by rw [mk_apply_eq_mk, mk_apply_eq_mk, Quotient.out_eq])
    rcases hmem with h | h
    · exact h
    · exact absurd (Equiv.Perm.SameCycle.eq_of_left
        (show τ.SameCycle (τ (Quotient.out q)) (Quotient.out q)
        from ⟨-1, by simp⟩) h) (ne_apply_self_of_evenClass τ (hallEven q))
  have hinv : ∀ i, τ (τ i) = i := by
    intro i
    have hi := hcls (Quotient.mk s i) i rfl
    rcases hi with hi | hi
    · rw [hi, htau2 (Quotient.mk s i)]
    · rw [hi]
      show τ (τ (τ (Quotient.out (Quotient.mk s i)))) = τ (Quotient.out (Quotient.mk s i))
      rw [htau2 (Quotient.mk s i)]
  refine ⟨fun i hfix => ?_, hinv⟩
  have hi := hcls (Quotient.mk s i) i rfl
  rcases hi with hi | hi
  · exact (ne_apply_self_of_evenClass τ (hallEven (Quotient.mk s i))) (by rwa [hi] at hfix)
  · have h2 := htau2 (Quotient.mk s i)
    refine (ne_apply_self_of_evenClass τ (hallEven (Quotient.mk s i))) ?_
    rw [hi] at hfix
    rw [h2] at hfix
    exact hfix.symm

theorem fpf_involution_of_card_ge {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hι : Fintype.card ι = 2 * r) (τ : Equiv.Perm ι)
    (E : Subgroup (ι → Kˣ)) (hE : ∀ t ∈ E, ∀ i, t i ^ p = 1)
    (hτ : ∀ t ∈ E, ∀ i, t (τ i) = (t i)⁻¹) (hcard : p ^ r ≤ Nat.card E) :
    (∀ i, τ i ≠ i) ∧ (∀ i, τ (τ i) = i) ∧
      ∀ t : ι → Kˣ, (∀ i, t i ^ p = 1) → (∀ i, t (τ i) = (t i)⁻¹) → t ∈ E := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fintype (rootsOfUnity p K) := Fintype.ofFinite _
  haveI : Fintype {q : Quotient (Equiv.Perm.SameCycle.setoid τ) // evenClass τ q} :=
    Fintype.ofFinite _
  let s := Equiv.Perm.SameCycle.setoid τ
  let μ := rootsOfUnity p K
  let a := Nat.card {q : Quotient s // evenClass τ q}
  have hbound : Nat.card E ≤ Nat.card μ ^ a := by
    calc Nat.card E
        ≤ Nat.card ({q : Quotient s // evenClass τ q} → μ) :=
          card_le_card_evenClass_fun hp hp2 τ E hE hτ
      _ = Nat.card μ ^ a := Nat.card_fun
  have hμ : Nat.card μ ≤ p := card_rootsOfUnity K p
  have hra : r ≤ a := by
    have h : p ^ r ≤ p ^ a := le_trans hcard (le_trans hbound (pow_le_pow_left' hμ a))
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h
  have h2a : 2 * a ≤ Fintype.card ι := by
    have hf : a = Fintype.card {q : Quotient s // evenClass τ q} := Nat.card_eq_fintype_card
    rw [hf]
    have h := Fintype.card_le_of_injective (evenClassPair τ) (evenClassPair_injective τ)
    rw [Fintype.card_prod, Fintype.card_bool] at h
    calc 2 * Fintype.card {q : Quotient s // evenClass τ q}
        = Fintype.card {q : Quotient s // evenClass τ q} * 2 := Nat.mul_comm 2 _
      _ ≤ Fintype.card ι := h
  have har : a ≤ r := by
    have h := h2a
    rw [hι] at h
    exact Nat.le_of_mul_le_mul_left h (by norm_num)
  have ha : a = r := le_antisymm har hra
  have ha' : Fintype.card {q : Quotient s // evenClass τ q} = r := by
    rw [← Nat.card_eq_fintype_card, ← ha]
  have hbij : Function.Bijective (evenClassPair τ) := by
    refine (Fintype.bijective_iff_injective_and_card (evenClassPair τ)).mpr
      ⟨evenClassPair_injective τ, ?_⟩
    rw [Fintype.card_prod, Fintype.card_bool, ha', hι, Nat.mul_comm]
  obtain ⟨hfpf, hinv⟩ := fpf_involution_of_pair_surjective τ hbij.2
  refine ⟨hfpf, hinv, fun t ht1 ht2 => ?_⟩
  let W : Subgroup (ι → Kˣ) :=
    { carrier := {t : ι → Kˣ | (∀ i, t i ^ p = 1) ∧ (∀ i, t (τ i) = (t i)⁻¹)}
      mul_mem' := by
        rintro s t ⟨hs1, hs2⟩ ⟨ht1, ht2⟩
        constructor
        · intro i
          change (s i * t i) ^ p = 1
          rw [mul_pow, hs1 i, ht1 i, one_mul]
        · intro i
          change s (τ i) * t (τ i) = (s i * t i)⁻¹
          rw [hs2 i, ht2 i, mul_inv_rev, mul_comm]
      one_mem' := ⟨fun i => by simp, fun i => by simp⟩
      inv_mem' := by
        rintro t ⟨ht1, ht2⟩
        constructor
        · intro i
          change (t i)⁻¹ ^ p = 1
          rw [inv_pow, ht1 i, inv_one]
        · intro i
          change (t (τ i))⁻¹ = ((t i)⁻¹)⁻¹
          rw [ht2 i, inv_inv] }
  have hW1 : ∀ t ∈ W, ∀ i, t i ^ p = 1 := fun t ht => ht.1
  have hW2 : ∀ t ∈ W, ∀ i, t (τ i) = (t i)⁻¹ := fun t ht => ht.2
  have hcardW : Nat.card W ≤ p ^ r := by
    calc Nat.card W
        ≤ Nat.card ({q : Quotient s // evenClass τ q} → μ) :=
          card_le_card_evenClass_fun hp hp2 τ W hW1 hW2
      _ = Nat.card μ ^ a := Nat.card_fun
      _ ≤ p ^ a := pow_le_pow_left' hμ a
      _ = p ^ r := by rw [ha]
  haveI : Finite W := Finite.of_injective (evenClassEval τ W hW1)
    (evenClassEval_injective hp hp2 τ W hW1 hW2)
  have hEW : E ≤ W := fun t ht => ⟨hE t ht, hτ t ht⟩
  have hEq : E = W := Subgroup.eq_of_le_of_card_ge hEW (le_trans hcardW hcard)
  have htW : t ∈ W := ⟨ht1, ht2⟩
  rwa [← hEq] at htW

theorem exists_mem_of_fpf_involution {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Kˣ} (hζ : orderOf ζ = p)
    (τ : Equiv.Perm ι) (hτ1 : ∀ i, τ i ≠ i) (hτ2 : ∀ i, τ (τ i) = i) (i j : ι) (hj : j ≠ τ i) :
    ∃ t : ι → Kˣ, (∀ k, t k ^ p = 1) ∧ (∀ k, t (τ k) = (t k)⁻¹) ∧ t i * t j ≠ 1 := by
  classical
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hζne : ζ ≠ 1 := fun h => hp.ne_one (by simp [← hζ, h])
  have hζ2 : ζ ^ 2 ≠ 1 := by
    intro h
    have hdvd : p ∣ 2 := by rw [← hζ]; exact orderOf_dvd_iff_pow_eq_one.mpr h
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact hp.ne_one h1
    · exact hp2 h1
  let t : ι → Kˣ := fun k => if k = i then ζ else if k = τ i then ζ⁻¹ else 1
  refine ⟨t, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : k = i
    · rw [hk]; simp [t, hζp]
    · by_cases hk' : k = τ i
      · rw [hk']; simp [t, hτ1 i, inv_pow, hζp]
      · simp [t, hk, hk']
  · intro k
    by_cases hk : k = i
    · rw [hk]; simp [t, hτ1 i]
    · by_cases hk' : k = τ i
      · rw [hk', hτ2 i]; simp [t, hτ1 i]
      · have hne1 : τ k ≠ i := fun h => hk' (by rw [← hτ2 k, h])
        have hne2 : τ k ≠ τ i := fun h => hk (τ.injective h)
        simp [t, hk, hk', hne1, hne2]
  · by_cases hj' : j = i
    · rw [hj']
      simpa [t, pow_two] using hζ2
    · have hji : j ≠ i := hj'
      have hjt : j ≠ τ i := hj
      have hti : t i = ζ := by simp [t]
      have htj : t j = 1 := by simp [t, hji, hjt]
      rw [hti, htj, mul_one]
      exact hζne

lemma card_quotient_sameCycle {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : Equiv.Perm ι)
    {r : ℕ} (hι : Fintype.card ι = 2 * r) (hτ1 : ∀ i, τ i ≠ i) (hτ2 : ∀ i, τ (τ i) = i) :
    Nat.card (Quotient (Equiv.Perm.SameCycle.setoid τ)) = r := by
  classical
  let s := Equiv.Perm.SameCycle.setoid τ
  haveI : Fintype (Quotient s) := Fintype.ofFinite _
  have hfiber : ∀ q : Quotient s, Fintype.card {x : ι // Quotient.mk s x = q} = 2 := by
    intro q
    haveI : Nonempty ι := ⟨Quotient.out q⟩
    have horder : orderOf τ = 2 := by
      have hmul : τ * τ = 1 := Equiv.ext hτ2
      have hdvd : orderOf τ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
      have hne : orderOf τ ≠ 1 := by
        intro h
        have h1 : τ = 1 := orderOf_eq_one_iff.mp h
        exact hτ1 (Quotient.out q) (by rw [h1]; rfl)
      exact (Nat.dvd_prime Nat.prime_two).mp hdvd |>.resolve_left hne
    have hset : (Finset.univ.filter (fun x : ι => Quotient.mk s x = q)) =
        {Quotient.out q, τ (Quotient.out q)} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro hx
        have hsc : τ.SameCycle x (Quotient.out q) := by
          change s.r x (Quotient.out q)
          exact Quotient.exact (by rw [hx, Quotient.out_eq])
        obtain ⟨k, hk, hkx⟩ := hsc.exists_pow_eq'
        rw [horder] at hk
        rcases (show k = 0 ∨ k = 1 by omega) with hk0 | hk1
        · left
          simpa [hk0] using hkx
        · right
          simp only [hk1, pow_one] at hkx
          rw [← hτ2 x, hkx]
      · rintro (hx | hx)
        · rw [hx, Quotient.out_eq]
        · rw [hx, mk_apply_eq_mk, Quotient.out_eq]
    rw [Fintype.card_subtype (fun x : ι => Quotient.mk s x = q), hset,
      Finset.card_pair_eq_two_iff]
    exact Ne.symm (hτ1 (Quotient.out q))
  have hsum : Fintype.card ι = ∑ q : Quotient s, Fintype.card {x : ι // Quotient.mk s x = q} := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv (Quotient.mk s)), Fintype.card_sigma]
  have hsum2 : Fintype.card ι = ∑ _q : Quotient s, 2 := by
    rw [hsum]
    exact Finset.sum_congr rfl fun q _ => hfiber q
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum2
  have hfc : Nat.card (Quotient s) = Fintype.card (Quotient s) := Nat.card_eq_fintype_card
  change Nat.card (Quotient s) = r
  have : 2 * r = Fintype.card (Quotient s) * 2 := by rw [← hι, hsum2]
  omega

theorem exists_equiv_hypIndex_of_fpf_involution {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (hι : Fintype.card ι = 2 * r) (τ : Equiv.Perm ι) (hτ1 : ∀ i, τ i ≠ i)
    (hτ2 : ∀ i, τ (τ i) = i) :
    ∃ e : HypIndex r 0 ≃ ι, ∀ a, e (hypPartner a) = τ (e a) := by
  classical
  let s := Equiv.Perm.SameCycle.setoid τ
  haveI : Fintype (Quotient s) := Fintype.ofFinite _
  have hcardQ : Nat.card (Quotient s) = r := card_quotient_sameCycle τ hι hτ1 hτ2
  have hcardQ' : Fintype.card (Quotient s) = r := by rwa [Nat.card_eq_fintype_card] at hcardQ
  let qe : Quotient s ≃ Fin r := Fintype.equivFinOfCardEq hcardQ'
  let c : Fin r → ι := fun k => Quotient.out (qe.symm k)
  let e0 : HypIndex r 0 → ι := fun a => match a with
    | .inl k => c k
    | .inr (.inl z) => Fin.elim0 z
    | .inr (.inr k) => τ (c k)
  have hc : ∀ k, Quotient.mk s (c k) = qe.symm k := fun k => Quotient.out_eq (qe.symm k)
  have hc_inj : Function.Injective c := by
    intro k k' h
    exact qe.symm.injective (by rw [← hc k, ← hc k', h])
  have hc_ne : ∀ k k', c k ≠ τ (c k') := by
    intro k k' h
    have hq : qe.symm k = qe.symm k' := by rw [← hc k, h, mk_apply_eq_mk, hc k']
    have hk : k = k' := qe.symm.injective hq
    exact hτ1 (c k) (by rw [← hk] at h; exact h.symm)
  have hinj : Function.Injective e0 := by
    intro a b hab
    rcases a with k | z | k <;> rcases b with k' | z' | k'
    · exact congrArg Sum.inl (hc_inj hab)
    · exact z'.elim0
    · exact absurd hab (hc_ne k k')
    · exact z.elim0
    · exact z.elim0
    · exact z.elim0
    · exact absurd hab.symm (hc_ne k' k)
    · exact z'.elim0
    · exact congrArg Sum.inr (congrArg Sum.inr (hc_inj (τ.injective hab)))
  have hcard : Fintype.card (HypIndex r 0) = Fintype.card ι := by
    rw [hι]
    simp only [HypIndex, Fintype.card_sum, Fintype.card_fin]
    omega
  refine ⟨Equiv.ofBijective e0
    ((Fintype.bijective_iff_injective_and_card e0).mpr ⟨hinj, hcard⟩), ?_⟩
  intro a
  show e0 (hypPartner a) = τ (e0 a)
  rcases a with k | z | k
  · rfl
  · exact z.elim0
  · show c k = τ (τ (c k))
    rw [hτ2]

end CFSG.StandardType

end
