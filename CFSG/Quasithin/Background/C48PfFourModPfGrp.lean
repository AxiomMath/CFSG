module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL4L5
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C48Pf.FMod

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Vol2Native.A312L
open scoped commutatorElement

@[expose] def IsCross (a m : ℕ) {n : ℕ} (k l : Fin n) : Prop :=
  ((k : ℕ) < a ∧ a ≤ (l : ℕ) ∧ (l : ℕ) < a + m) ∨
    (a ≤ (k : ℕ) ∧ (k : ℕ) < a + m ∧ a + m ≤ (l : ℕ))

theorem IsCross.ne {a m n : ℕ} {k l : Fin n} (h : IsCross a m k l) : k ≠ l := by
  intro e
  subst e
  rcases h with h | h <;> omega

@[expose] def BlockForm (a m : ℕ) {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) : Prop :=
  (∀ i j : Fin n, a ≤ (i : ℕ) → (j : ℕ) < a → A i j = 0) ∧
    (∀ i j : Fin n, a + m ≤ (i : ℕ) → (j : ℕ) < a + m → A i j = 0) ∧
    (∀ i j : Fin n, (i : ℕ) < a → (j : ℕ) < a → A i j = if i = j then 1 else 0) ∧
    (∀ i j : Fin n, a + m ≤ (i : ℕ) → a + m ≤ (j : ℕ) → A i j = if i = j then 1 else 0)

theorem entry_of_blkAt_eq_one {n a m : ℕ} (h : a + m ≤ n) {A : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hA : blkAt a m h A = 1) (i j : Fin n) (hi1 : a ≤ (i : ℕ)) (hi2 : (i : ℕ) < a + m)
    (hj1 : a ≤ (j : ℕ)) (hj2 : (j : ℕ) < a + m) : A i j = if i = j then 1 else 0 := by
  have h1 := congrFun (congrFun hA ⟨(i : ℕ) - a, by omega⟩) ⟨(j : ℕ) - a, by omega⟩
  rw [blkAt_apply, Matrix.one_apply] at h1
  have hi : (⟨a + ((i : ℕ) - a), by omega⟩ : Fin n) = i := Fin.ext (by simp; omega)
  have hj : (⟨a + ((j : ℕ) - a), by omega⟩ : Fin n) = j := Fin.ext (by simp; omega)
  have h2 : ((⟨(i : ℕ) - a, by omega⟩ : Fin m) = ⟨(j : ℕ) - a, by omega⟩) ↔ i = j := by
    rw [Fin.mk.injEq, Fin.ext_iff]
    omega
  simp only [hi, hj] at h1
  rw [h1]
  exact if_congr h2 rfl rfl

variable {n : ℕ}

theorem blockForm_of_mem (hn5 : n ≤ 5) {I : Set ℕ} {a m : ℕ} (h : a + m ≤ n) (hm3 : 3 ≤ m)
    (ha : a = 0 ∨ a ∈ I) (hb : a + m = n ∨ a + m ∈ I)
    {x : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hx : x ∈ perfectCore (flagStabilizer n (ZMod 2) I)) :
    BlockForm a m (x : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  have hK : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hxQ : x ∈ flagStabilizer n (ZMod 2) I := perfectCore_le _ hx
  have hperf : Group.IsPerfect ↥(perfectCore (flagStabilizer n (ZMod 2) I)) :=
    Subgroup.isPerfect_iff.mpr (perfectCore_perfect _)
  refine ⟨fun i j hi hj => ?_, fun i j hi hj => ?_, fun i j hi hj => ?_, fun i j hi hj => ?_⟩
  · rcases ha with rfl | ha
    · exact absurd hj (Nat.not_lt_zero _)
    · exact stabilizer_entries (mem_flagStabilizer.mp hxQ a ha) hj hi
  · rcases hb with hb | hb
    · exact absurd i.isLt (by omega)
    · exact stabilizer_entries (mem_flagStabilizer.mp hxQ (a + m) hb) hj hi
  · rcases ha with rfl | ha
    · exact absurd hj (Nat.not_lt_zero _)
    · have h1 := blkAt_eq_one_of_small hK (a := 0) (m := a) (by omega) (Or.inl rfl)
        (Or.inr (by simpa using ha)) (by omega) (perfectCore_le _) hperf ⟨x, hx⟩
      exact entry_of_blkAt_eq_one _ h1 i j (Nat.zero_le _) (by omega) (Nat.zero_le _) (by omega)
  · rcases hb with hb | hb
    · exact absurd i.isLt (by omega)
    · have h1 := blkAt_eq_one_of_small hK (a := a + m) (m := n - (a + m)) (by omega) (Or.inr hb)
        (Or.inl (by omega)) (by omega) (perfectCore_le _) hperf ⟨x, hx⟩
      exact entry_of_blkAt_eq_one _ h1 i j hi (by omega) hj (by omega)

theorem transvection_mem_unitriangular {k l : Fin n} (hkl : k < l) :
    SpecialLinearGroup.transvection (ne_of_lt hkl) (1 : ZMod 2) ∈ unitriangular n (ZMod 2) := by
  rw [mem_unitriangular, CFSG.LinearGroups.coe_transvection]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hn : ¬ (k = i ∧ l = j) := by
      rintro ⟨rfl, rfl⟩
      exact absurd (hij.trans hkl) (lt_irrefl _)
    simp only [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij), Matrix.single_apply, hn,
      zero_add, ite_false]
  · have hn : ¬ (k = i ∧ l = i) := by
      rintro ⟨rfl, e⟩
      exact absurd e.symm (ne_of_lt hkl)
    simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply, hn, ite_false,
      add_zero]

theorem liftT_mem_perfectCore {I : Set ℕ} {a m : ℕ} (h : a + m ≤ n) (hm3 : 3 ≤ m)
    (hno : ∀ c ∈ I, ¬ (a < c ∧ c < a + m)) {i j : Fin m} (hij : i ≠ j) :
    (liftT a m h hij : SpecialLinearGroup (Fin n) (ZMod 2)) ∈
      perfectCore (flagStabilizer n (ZMod 2) I) := by
  classical
  set P₀ : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2)) :=
    Subgroup.closure {x | ∃ (i j : Fin m) (hij : i ≠ j), x = liftT a m h hij} with hP₀
  have hP₀H : P₀ ≤ flagStabilizer n (ZMod 2) I := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, j, hij, rfl⟩
    exact liftT_mem_flagStabilizer a m h hno hij
  have hgen : ∀ (i j : Fin m) (hij : i ≠ j), liftT a m h hij ∈ P₀ := fun i j hij =>
    Subgroup.subset_closure ⟨i, j, hij, rfl⟩
  have hP₀perf : ⁅P₀, P₀⁆ = P₀ := by
    refine le_antisymm (A3.commutator_self_le _) ?_
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, j, hij, rfl⟩
    obtain ⟨k, hki, hkj⟩ : ∃ k : Fin m, k ≠ i ∧ k ≠ j := by
      by_contra hcon
      push Not at hcon
      have hsub : (Finset.univ : Finset (Fin m)) ⊆ {i, j} := fun k _ => by
        by_cases hki : k = i
        · simp [hki]
        · simp [hcon k hki]
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_le_two (a := i) (b := j)
      simp only [Finset.card_univ, Fintype.card_fin] at h1
      omega
    have hcomm : ⁅(liftT a m h (Ne.symm hki) : SpecialLinearGroup (Fin n) (ZMod 2)),
        (liftT a m h hkj : SpecialLinearGroup (Fin n) (ZMod 2))⁆ = liftT a m h hij := by
      have := SpecialLinearGroup.commutatorElement_transvection
        (blkIdxN_ne (h := h) (Ne.symm hki)) (blkIdxN_ne (h := h) hkj)
        (blkIdxN_ne (h := h) hij) (1 : ZMod 2) 1
      rw [mul_one] at this
      exact this
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator (hgen _ _ _) (hgen _ _ _)
  exact le_perfectCore_of_perfect hP₀H hP₀perf (hgen i j hij)

theorem conj_mem_perfectCore {I : Set ℕ} {y z : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hy : y ∈ flagStabilizer n (ZMod 2) I) (hz : z ∈ perfectCore (flagStabilizer n (ZMod 2) I)) :
    y * z * y⁻¹ ∈ perfectCore (flagStabilizer n (ZMod 2) I) :=
  (Subgroup.mem_normalizer_iff.1
    (normalizer_le_normalizer_perfectCore _ (Subgroup.le_normalizer hy)) z).1 hz

theorem transvection_mem_perfectCore {I : Set ℕ} {a m : ℕ} (h : a + m ≤ n) (hm3 : 3 ≤ m)
    (hno : ∀ c ∈ I, ¬ (a < c ∧ c < a + m)) {k l : Fin n} (hc : IsCross a m k l) :
    SpecialLinearGroup.transvection hc.ne (1 : ZMod 2) ∈
      perfectCore (flagStabilizer n (ZMod 2) I) := by
  have hUQ : unitriangular n (ZMod 2) ≤ flagStabilizer n (ZMod 2) I := fun x hx =>
    upperTriangular_le_flagStabilizer (n := n) (K := ZMod 2) I
      (unitriangular_le_upperTriangular n (ZMod 2) hx)
  rcases hc with ⟨hk, hl1, hl2⟩ | ⟨hk1, hk2, hl⟩
  ·
    set l' : Fin m := ⟨(l : ℕ) - a, by omega⟩
    obtain ⟨j', hj'⟩ : ∃ j' : Fin m, j' ≠ l' := by
      by_cases h0 : (l' : ℕ) = 0
      · exact ⟨⟨1, by omega⟩, fun e => by rw [← e] at h0; simp at h0⟩
      · exact ⟨⟨0, by omega⟩, fun e => h0 (by rw [← e])⟩
    set j : Fin n := blkIdxN a m h j'
    have hjl : j ≠ l := by
      intro e
      apply hj'
      apply Fin.ext
      have := congrArg Fin.val e
      simp only [j, blkIdxN, l'] at this ⊢
      omega
    have hkj : k < j := by
      show (k : ℕ) < a + j'
      omega
    have hljT : (liftT a m h hj' : SpecialLinearGroup (Fin n) (ZMod 2)) =
        SpecialLinearGroup.transvection hjl (1 : ZMod 2) := by
      apply Subtype.ext
      rw [coe_liftT, CFSG.LinearGroups.coe_transvection]
      congr 2
      apply Fin.ext
      simp only [blkIdxN, l']
      omega
    have hcomm := SpecialLinearGroup.commutatorElement_transvection (ne_of_lt hkj) hjl
      (IsCross.ne (Or.inl ⟨hk, hl1, hl2⟩)) (1 : ZMod 2) 1
    rw [mul_one] at hcomm
    have hmem : SpecialLinearGroup.transvection (ne_of_lt hkj) (1 : ZMod 2) *
        SpecialLinearGroup.transvection hjl (1 : ZMod 2) *
        (SpecialLinearGroup.transvection (ne_of_lt hkj) (1 : ZMod 2))⁻¹ *
        (SpecialLinearGroup.transvection hjl (1 : ZMod 2))⁻¹ ∈
          perfectCore (flagStabilizer n (ZMod 2) I) := by
      refine Subgroup.mul_mem _ (conj_mem_perfectCore (hUQ
        (transvection_mem_unitriangular hkj)) ?_) (Subgroup.inv_mem _ ?_)
      · rw [← hljT]
        exact liftT_mem_perfectCore h hm3 hno hj'
      · rw [← hljT]
        exact liftT_mem_perfectCore h hm3 hno hj'
    rw [commutatorElement_def] at hcomm
    rw [← hcomm]
    exact hmem
  ·
    set k' : Fin m := ⟨(k : ℕ) - a, by omega⟩
    obtain ⟨j', hj'⟩ : ∃ j' : Fin m, j' ≠ k' := by
      by_cases h0 : (k' : ℕ) = 0
      · exact ⟨⟨1, by omega⟩, fun e => by rw [← e] at h0; simp at h0⟩
      · exact ⟨⟨0, by omega⟩, fun e => h0 (by rw [← e])⟩
    set j : Fin n := blkIdxN a m h j'
    have hkj : k ≠ j := by
      intro e
      apply hj'
      apply Fin.ext
      have := congrArg Fin.val e
      simp only [j, blkIdxN, k'] at this ⊢
      omega
    have hjl : j < l := by
      show a + (j' : ℕ) < l
      omega
    have hkjT : (liftT a m h (Ne.symm hj') : SpecialLinearGroup (Fin n) (ZMod 2)) =
        SpecialLinearGroup.transvection hkj (1 : ZMod 2) := by
      apply Subtype.ext
      rw [coe_liftT, CFSG.LinearGroups.coe_transvection]
      congr 2
      apply Fin.ext
      simp only [blkIdxN, k']
      omega
    have hcomm := SpecialLinearGroup.commutatorElement_transvection hkj (ne_of_lt hjl)
      (IsCross.ne (Or.inr ⟨hk1, hk2, hl⟩)) (1 : ZMod 2) 1
    rw [mul_one] at hcomm
    have hx : SpecialLinearGroup.transvection hkj (1 : ZMod 2) ∈
        perfectCore (flagStabilizer n (ZMod 2) I) := by
      rw [← hkjT]
      exact liftT_mem_perfectCore h hm3 hno (Ne.symm hj')
    have hmem : SpecialLinearGroup.transvection hkj (1 : ZMod 2) *
        (SpecialLinearGroup.transvection (ne_of_lt hjl) (1 : ZMod 2) *
          (SpecialLinearGroup.transvection hkj (1 : ZMod 2))⁻¹ *
          (SpecialLinearGroup.transvection (ne_of_lt hjl) (1 : ZMod 2))⁻¹) ∈
          perfectCore (flagStabilizer n (ZMod 2) I) :=
      Subgroup.mul_mem _ hx (conj_mem_perfectCore (hUQ (transvection_mem_unitriangular hjl))
        (Subgroup.inv_mem _ hx))
    rw [commutatorElement_def] at hcomm
    rw [← hcomm, mul_assoc, mul_assoc, ← mul_assoc _ _ (SpecialLinearGroup.transvection
      (ne_of_lt hjl) (1 : ZMod 2))⁻¹]
    simpa only [mul_assoc] using hmem

theorem blkAt_transvection_cross {a m : ℕ} (h : a + m ≤ n) {k l : Fin n} (hc : IsCross a m k l) :
    blkAt a m h ((SpecialLinearGroup.transvection hc.ne (1 : ZMod 2) :
      SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
  ext i j
  have hn : ¬ (k = (⟨a + i, by have := i.isLt; omega⟩ : Fin n) ∧
      l = (⟨a + j, by have := j.isLt; omega⟩ : Fin n)) := by
    rintro ⟨e1, e2⟩
    have h1 := congrArg Fin.val e1
    have h2 := congrArg Fin.val e2
    simp only at h1 h2
    have := i.isLt
    have := j.isLt
    rcases hc with hc | hc <;> omega
  have hij : ((⟨a + i, by have := i.isLt; omega⟩ : Fin n) =
      ⟨a + j, by have := j.isLt; omega⟩) ↔ i = j := by
    rw [Fin.mk.injEq, Fin.ext_iff]
    omega
  simp only [blkAt_apply, CFSG.LinearGroups.coe_transvection, Matrix.add_apply,
    Matrix.single_apply, hn, ite_false, add_zero, Matrix.one_apply, hij]


theorem subsingleton_of_perfect_of_isPGroup {X : Type*} [Group X] [Finite X]
    [hperf : Group.IsPerfect X] (hp : IsPGroup 2 X) : Subsingleton X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hp.isNilpotent
  by_contra h
  have : Nontrivial X := not_subsingleton_iff_nontrivial.mp h
  exact Group.IsPerfect.not_isNilpotent X inferInstance

theorem eq_bot_of_perfect_of_isPGroup {X : Type*} [Group X] [Finite X] {R : Subgroup X}
    (hR : ⁅R, R⁆ = R) (hp : IsPGroup 2 R) : R = ⊥ := by
  have : Group.IsPerfect ↥R := Subgroup.isPerfect_iff.mpr hR
  have := subsingleton_of_perfect_of_isPGroup hp
  rw [eq_bot_iff]
  intro x hx
  have h1 : (⟨x, hx⟩ : ↥R) = 1 := Subsingleton.elim _ _
  exact congrArg Subtype.val h1

theorem eq_perfectCore_of_normal (hn5 : n ≤ 5) (hn1 : 1 ≤ n) {I : Set ℕ} {a m : ℕ}
    (h : a + m ≤ n) (hm3 : 3 ≤ m) (ha : a = 0 ∨ a ∈ I) (hb : a + m = n ∨ a + m ∈ I)
    (hno : ∀ c ∈ I, ¬ (a < c ∧ c < a + m))
    {R : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))} (hRQ : R ≤ flagStabilizer n (ZMod 2) I)
    (hRN : flagStabilizer n (ZMod 2) I ≤
      Subgroup.normalizer (R : Set (SpecialLinearGroup (Fin n) (ZMod 2))))
    (hR : ⁅R, R⁆ = R) (hR1 : R ≠ ⊥) : R = perfectCore (flagStabilizer n (ZMod 2) I) := by
  classical
  have hK : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := perfectCore (flagStabilizer n (ZMod 2) I) with hQ
  have hRle : R ≤ Q := le_perfectCore_of_perfect hRQ hR
  set bb := bigBlockHom (K := ZMod 2) I a m h ha hb with hbb
  have hbbs : Function.Surjective bb := bigBlockHom_surjective hK h hm3 ha hb hno
  have hbbk : ∀ x, bb x = 1 → (x : SpecialLinearGroup (Fin n) (ZMod 2)) ∈
      unitriangular n (ZMod 2) := fun x hx =>
    unitriangular_of_bigBlockHom hK hn5 h hm3 ha hb hno x hx
  set R' : Subgroup ↥Q := R.subgroupOf Q with hR'
  have hR'n : R'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRle).2 ((perfectCore_le _).trans hRN)
  have := sl_isSimple_of_card_two hK hm3
  rcases (Subgroup.Normal.map hR'n bb hbbs).eq_bot_or_eq_top with hbot | htop
  · exfalso
    apply hR1
    refine eq_bot_of_perfect_of_isPGroup hR ?_
    have hRU : R ≤ unitriangular n (ZMod 2) := fun r hr => by
      have h1 : bb ⟨r, hRle hr⟩ ∈ R'.map bb := ⟨⟨r, hRle hr⟩, hr, rfl⟩
      rw [hbot] at h1
      exact hbbk _ h1
    exact (isPGroup_unitriangular_charTwo hn1).to_le hRU
  · refine le_antisymm hRle fun x hx => ?_
    have hp : IsPGroup 2 (↥Q ⧸ R') := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R' y
      obtain ⟨r, hr, hrx⟩ : bb x ∈ R'.map bb := by rw [htop]; trivial
      have hk : bb (r⁻¹ * x) = 1 := by rw [map_mul, map_inv, hrx, inv_mul_cancel]
      obtain ⟨j, hj⟩ := isPGroup_unitriangular_charTwo (K := ZMod 2) hn1 ⟨_, hbbk _ hk⟩
      refine ⟨j, ?_⟩
      have hr1 : QuotientGroup.mk' R' r = 1 := by
        rw [QuotientGroup.mk'_apply]
        exact (QuotientGroup.eq_one_iff r).2 hr
      have h1 : QuotientGroup.mk' R' x = QuotientGroup.mk' R' (r⁻¹ * x) := by
        rw [map_mul, map_inv, hr1, inv_one, one_mul]
      have h2 : (r⁻¹ * x) ^ 2 ^ j = 1 := by
        apply Subtype.ext
        have := congrArg Subtype.val hj
        simpa using this
      rw [h1, ← map_pow, h2, map_one]
    have : Group.IsPerfect ↥Q := Subgroup.isPerfect_iff.mpr (perfectCore_perfect _)
    have := subsingleton_of_perfect_of_isPGroup hp
    have h1 : QuotientGroup.mk' R' (⟨x, hx⟩ : ↥Q) = 1 := Subsingleton.elim _ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1

theorem card_of_isPSL_two_one {n : ℕ} (hn : n = 3 ∨ n = 4) {X : Type} [Group X]
    (hX : IsPSL n 2 1 X) : (n = 3 → Nat.card X = 168) ∧ (n = 4 → Nat.card X = 20160) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  rw [Nat.card_congr e.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by omega : 1 ≤ n), hK]
  rcases hn with rfl | rfl
  · exact ⟨fun _ => by decide, fun h => absurd h (by norm_num)⟩
  · exact ⟨fun h => absurd h (by norm_num), fun _ => by decide⟩

theorem eq_of_isPSL_two_one' {m m' : ℕ} (hm : m = 3 ∨ m = 4) (hm' : m' = 3 ∨ m' = 4) {X : Type}
    [Group X] (h : IsPSL m 2 1 X) (h' : IsPSL m' 2 1 X) : m = m' := by
  have k1 := card_of_isPSL_two_one hm h
  have k2 := card_of_isPSL_two_one hm' h'
  rcases hm with rfl | rfl <;> rcases hm' with rfl | rfl
  · rfl
  · have := (k1.1 rfl).symm.trans (k2.2 rfl)
    norm_num at this
  · have := (k1.2 rfl).symm.trans (k2.1 rfl)
    norm_num at this
  · rfl

theorem isPSL_of_mulEquiv_sl {m : ℕ} (hm : 3 ≤ m) {X : Type} [Group X]
    (e : X ≃* SpecialLinearGroup (Fin m) (ZMod 2)) : IsPSL m 2 1 X := by
  have hK : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  refine ⟨⟨Nat.prime_two, le_rfl, by omega, ?_, ?_⟩, ZMod 2, inferInstance, inferInstance,
    by rw [hK]; norm_num, ⟨e.trans (slEquivStatedProj hK m)⟩⟩
  · intro h2
    have := congrArg Prod.fst h2
    simp only at this
    omega
  · intro h2
    have := congrArg Prod.fst h2
    simp only at this
    omega


section Config

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem exists_config {K P P₀ : Subgroup G} {n m : ℕ} (hn4 : 4 ≤ n) (hn5 : n ≤ 5)
    (ψ : ↥K →* SpecialLinearGroup (Fin n) (ZMod 2)) (hψs : Function.Surjective ψ)
    (hψker : ∀ k : ↥K, ψ k = 1 → (k : G) ∈ pCoreOf 2 K)
    (hpar : IsParabolic2 K P) (hPK : P ≠ K) (hP₀P : P₀ ≤ P)
    (hPN : P ≤ Subgroup.normalizer (P₀ : Set G)) (hperf : ⁅P₀, P₀⁆ = P₀)
    (hm : m = 3 ∨ m = 4) (hpsl : IsPSL m 2 1 (ModO2 P₀)) :
    ∃ (g : SpecialLinearGroup (Fin n) (ZMod 2)) (a : ℕ) (hamn : a + m ≤ n)
      (α : ↥P₀ →* SpecialLinearGroup (Fin m) (ZMod 2)),
      (0 < a ∨ a + m < n) ∧ Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥P₀ ∧
      (∀ x : ↥P₀,
        blkAt a m hamn ((g⁻¹ * ψ ⟨x, hP₀P.trans hpar.1 x.2⟩ * g :
          SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
            ((α x : SpecialLinearGroup (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) ∧
        BlockForm a m ((g⁻¹ * ψ ⟨x, hP₀P.trans hpar.1 x.2⟩ * g :
          SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) ∧
      (∀ (k l : Fin n) (hc : IsCross a m k l), ∃ p : ↥P₀, p ∈ CFSG.pCore 2 ↥P₀ ∧
        g⁻¹ * ψ ⟨p, hP₀P.trans hpar.1 p.2⟩ * g =
          SpecialLinearGroup.transvection hc.ne (1 : ZMod 2)) := by
  classical
  have hK2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPK', S, hS, hSP⟩ := hpar
  have hP₀K : P₀ ≤ K := hP₀P.trans hPK'
  have hO2S : pCoreOf 2 K ≤ S :=
    CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS
  have hSP' : S ≤ P := fun s hs => hSP ⟨hS.1 hs, Subgroup.le_normalizer hs⟩
  set S' : Subgroup ↥K := S.subgroupOf K with hS'
  have hS'syl : CFSG.QuasithinUnique.IsSylowTwoOf (S'.map ψ) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · have hSp : IsPGroup 2 ↥S' := hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
      exact hSp.map ψ
    · show ¬ 2 ∣ (S'.map ψ).relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      intro h2
      exact hS.2.2 (h2.trans (Subgroup.index_map_dvd _ hψs))
  obtain ⟨Pu, hPu⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (n := n) (by omega)
  have hUsyl : CFSG.QuasithinUnique.IsSylowTwoOf (unitriangular n (ZMod 2)) ⊤ :=
    hPu ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow Pu
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf hUsyl hS'syl
  set θ₀ : ↥K →* SpecialLinearGroup (Fin n) (ZMod 2) :=
    (MulAut.conj g⁻¹).toMonoidHom.comp ψ with hθ₀def
  have hθ₀ : ∀ k, θ₀ k = g⁻¹ * ψ k * g := fun k => by
    simp [θ₀]
  have hθ₀ker : ∀ k, θ₀ k = 1 → (k : G) ∈ pCoreOf 2 K := fun k hk => by
    apply hψker
    rw [hθ₀] at hk
    have : ψ k = g * (g⁻¹ * ψ k * g) * g⁻¹ := by group
    rw [this, hk]
    group
  have hθS : S'.map θ₀ = unitriangular n (ZMod 2) := by
    rw [hθ₀def, ← Subgroup.map_map, ← hg, Subgroup.map_map]
    have hid : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id (SpecialLinearGroup (Fin n) (ZMod 2)) := by
      ext x : 1
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    rw [hid, Subgroup.map_id]
  set P' : Subgroup ↥K := P.subgroupOf K with hP'
  set Q := P'.map θ₀ with hQ
  have hUQ : upperTriangular n (ZMod 2) ≤ Q := by
    refine (upperTriangular_le_unitriangular hK2).trans ?_
    rw [← hθS]
    exact Subgroup.map_mono fun x hx => hSP' hx
  obtain ⟨hQI, -⟩ := borel_overgroups Q hUQ
  set I := borelOvergroupCuts Q with hI
  have hIcuts : ∀ c ∈ I, 1 ≤ c ∧ c < n := fun c hc => by
    obtain ⟨h1, h2, -⟩ := hc
    exact ⟨h1, h2⟩
  have hQtop : Q ≠ ⊤ := by
    intro hQt
    apply hPK
    refine le_antisymm hPK' fun k hk => ?_
    obtain ⟨p, hp, hpk⟩ : θ₀ ⟨k, hk⟩ ∈ Q := hQt ▸ Subgroup.mem_top _
    have h1 : θ₀ (p⁻¹ * ⟨k, hk⟩) = 1 := by rw [map_mul, map_inv, hpk, inv_mul_cancel]
    have h3 : ((p⁻¹ * ⟨k, hk⟩ : ↥K) : G) ∈ P := hSP' (hO2S (hθ₀ker _ h1))
    have h4 : (p : G) ∈ P := hp
    have := P.mul_mem h4 h3
    simpa using this
  set P₀' : Subgroup ↥K := P₀.subgroupOf K with hP₀'
  set R₀ := P₀'.map θ₀ with hR₀
  have hR₀Q : R₀ ≤ Q := Subgroup.map_mono fun x hx => hP₀P hx
  have hR₀N : Q ≤ Subgroup.normalizer (R₀ : Set (SpecialLinearGroup (Fin n) (ZMod 2))) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨p * x * p⁻¹, ?_, by simp⟩
      exact (Subgroup.mem_normalizer_iff.1 (hPN hp) x).1 hx
    · rintro ⟨x, hx, hxy⟩
      refine ⟨p⁻¹ * x * p, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.1 (hPN (P.inv_mem hp)) x).1 hx
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
        simpa using this
      · rw [map_mul, map_mul, map_inv, hxy]
        group
  have hR₀perf : ⁅R₀, R₀⁆ = R₀ := by
    have hP₀'perf : ⁅P₀', P₀'⁆ = P₀' := by
      apply Subgroup.map_injective K.subtype_injective
      rw [Subgroup.map_commutator, hP₀', Subgroup.map_subgroupOf_eq_of_le hP₀K, hperf]
    rw [hR₀, ← Subgroup.map_commutator, hP₀'perf]
  have hP₀ne : ¬ P₀ ≤ pCoreOf 2 K := by
    intro hle
    have hp : IsPGroup 2 ↥P₀ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le hle
    have htop : CFSG.pCore 2 ↥P₀ = ⊤ := by
      refine le_antisymm le_top (le_sSup ⟨inferInstance, ?_⟩)
      exact hp.of_equiv Subgroup.topEquiv.symm
    have hc : Nat.card (ModO2 P₀) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => ?_⟩, inferInstance⟩
      induction a using QuotientGroup.induction_on
      induction b using QuotientGroup.induction_on
      rw [QuotientGroup.eq, htop]
      exact Subgroup.mem_top _
    have k := card_of_isPSL_two_one hm hpsl
    rcases hm with rfl | rfl
    · rw [k.1 rfl] at hc
      norm_num at hc
    · rw [k.2 rfl] at hc
      norm_num at hc
  have hR₀ne : R₀ ≠ ⊥ := by
    intro hbot
    apply hP₀ne
    intro x hx
    have h1 : θ₀ ⟨x, hP₀K hx⟩ = 1 := by
      have : θ₀ ⟨x, hP₀K hx⟩ ∈ R₀ := ⟨⟨x, hP₀K hx⟩, hx, rfl⟩
      rw [hbot] at this
      exact this
    exact hθ₀ker _ h1
  rcases exists_big_or_small (n := n) (I := I) with hsmall | ⟨a, m', h, hm3, ha, hb, hno⟩
  · exfalso
    have hbot := perfectCore_eq_bot_of_small hK2 (by omega) hsmall
    apply hR₀ne
    rw [eq_bot_iff, ← hbot]
    exact le_perfectCore_of_perfect (hR₀Q.trans hQI.le) hR₀perf
  have hmn : m' < n := by
    by_contra hmn
    apply hQtop
    have hIe : I = ∅ := by
      ext c
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hc
      obtain ⟨h1, h2⟩ := hIcuts c hc
      exact hno c hc ⟨by omega, by omega⟩
    rw [hQI, hIe, flagStabilizer_empty]
  have hR₀eq : R₀ = perfectCore (flagStabilizer n (ZMod 2) I) :=
    eq_perfectCore_of_normal hn5 (by omega) h hm3 ha hb hno (hR₀Q.trans hQI.le)
      (hQI.ge.trans hR₀N) hR₀perf hR₀ne
  set bb := bigBlockHom (K := ZMod 2) I a m' h ha hb with hbb
  have hbbs : Function.Surjective bb := bigBlockHom_surjective hK2 h hm3 ha hb hno
  have hθmem : ∀ x : ↥P₀, θ₀ ⟨x, hP₀K x.2⟩ ∈ perfectCore (flagStabilizer n (ZMod 2) I) :=
    fun x => hR₀eq ▸ ⟨⟨x, hP₀K x.2⟩, x.2, rfl⟩
  set α' : ↥P₀ →* ↥(perfectCore (flagStabilizer n (ZMod 2) I)) :=
    (θ₀.comp (Subgroup.inclusion hP₀K)).codRestrict _ hθmem with hα'
  have hα'v : ∀ x, ((α' x : ↥(perfectCore (flagStabilizer n (ZMod 2) I))) :
      SpecialLinearGroup (Fin n) (ZMod 2)) = θ₀ ⟨x, hP₀K x.2⟩ := fun x => rfl
  have hα's : Function.Surjective α' := by
    rintro ⟨y, hy⟩
    rw [← hR₀eq] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    exact ⟨⟨p, hp⟩, rfl⟩
  set α := bb.comp α' with hα
  have hαs : Function.Surjective α := hbbs.comp hα's
  have hker2 : IsPGroup 2 ↥α.ker := by
    rintro ⟨x, hx⟩
    have hU := unitriangular_of_bigBlockHom hK2 hn5 h hm3 ha hb hno (α' x) hx
    obtain ⟨j, hj⟩ := isPGroup_unitriangular_charTwo (K := ZMod 2) (n := n) (by omega) ⟨_, hU⟩
    have hj' : θ₀ ⟨x, hP₀K x.2⟩ ^ 2 ^ j = 1 := by
      have := congrArg Subtype.val hj
      simpa [hα'v] using this
    have h1 : θ₀ (⟨x, hP₀K x.2⟩ ^ 2 ^ j) = 1 := by rw [map_pow, hj']
    obtain ⟨i, hi⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨_, hθ₀ker _ h1⟩
    refine ⟨j + i, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg Subtype.val hi
    simp only [Subgroup.coe_pow, OneMemClass.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    simpa using this
  have hsimp := sl_isSimple_of_card_two hK2 hm3
  have hnab := sl_nonabelian_of_card_two hK2 hm3
  have hkerα : α.ker = CFSG.pCore 2 ↥P₀ := (pCore_two_eq_ker hnab α hαs hker2).symm
  have hm' : m' = 3 ∨ m' = 4 := by omega
  have hmm : m = m' := eq_of_isPSL_two_one' hm hm' hpsl
    (isPSL_of_mulEquiv_sl hm3 (modO2EquivOfHom hnab α hαs hker2))
  subst hmm
  refine ⟨g, a, h, α, by omega, hαs, hkerα, fun x => ⟨?_, ?_⟩, fun k l hc => ?_⟩
  · rw [← hθ₀]
    exact (bigBlockHom_coe I a m h ha hb (α' x)).symm
  · rw [← hθ₀]
    exact blockForm_of_mem hn5 h hm3 ha hb (hθmem x)
  · obtain ⟨p, hp⟩ := hα's ⟨_, transvection_mem_perfectCore h hm3 hno hc⟩
    refine ⟨p, ?_, ?_⟩
    · rw [← hkerα, MonoidHom.mem_ker]
      show bb (α' p) = 1
      rw [hp]
      apply Subtype.ext
      rw [bigBlockHom_coe]
      exact blkAt_transvection_cross h hc
    · rw [← hθ₀, ← hα'v, hp]

end Config

end CFSG.Quasithin.C48Pf.FMod
