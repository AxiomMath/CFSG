module

public import CFSG.LocalAnalysis.StandardType.GGQ2PlaneRaw

public section

namespace CFSG.StandardType.GGQ2Frame.PlaneRaw

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma eq_one_or_eq_neg_one_of_ne_zero (a : F) (ha : a ≠ 0) : a = 1 ∨ a = -1 := by
  revert a
  decide

private lemma sq_eq_one_of_ne_zero (a : F) (ha : a ≠ 0) : a * a = 1 := by
  revert a
  decide

theorem occurs_zero_span_iff {r : ℕ} {S : Finset (Fin r)} {u : V r} :
    occurs (Submodule.span F ({u} : Set (V r))) (.zero S) ↔ ∀ i, (i ∈ S ↔ u i = 0) := by
  classical
  have hu_mem : u ∈ Submodule.span F ({u} : Set (V r)) := Submodule.mem_span_singleton_self u
  constructor
  · intro h i
    rw [h i]
    constructor
    · intro h0
      exact h0 ⟨u, hu_mem⟩
    · intro h0 x
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp x.2
      have hx : (x : V r) i = a * u i := by rw [← ha]; simp [Pi.smul_apply]
      rw [hx, h0, mul_zero]
  · intro h i
    constructor
    · intro hi x
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp x.2
      have hx : (x : V r) i = a * u i := by rw [← ha]; simp [Pi.smul_apply]
      rw [hx, (h i).mp hi, mul_zero]
    · intro h0
      exact (h i).mpr (h0 ⟨u, hu_mem⟩)

private lemma eq_smul_of_occurs_span_extension {r : ℕ} {u e : V r}
    (hocc : occurs (Submodule.span F ({u} : Set (V r))) (.extension e)) :
    ∃ a : F, a ≠ 0 ∧ e = a • u := by
  classical
  obtain ⟨-, χ, hχ, hev, hne⟩ := hocc
  have hu_mem : u ∈ Submodule.span F ({u} : Set (V r)) := Submodule.mem_span_singleton_self u
  set a : F := χ ⟨u, hu_mem⟩ with ha
  have ha0 : a ≠ 0 := by
    intro h0
    apply hχ
    ext x
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp x.2
    have hx : x = c • (⟨u, hu_mem⟩ : Submodule.span F ({u} : Set (V r))) :=
      Subtype.ext (by rw [← hc]; simp)
    rw [hx, map_smul, ← ha, h0, smul_zero]
    rfl
  have hval : ∀ j : Fin r,
      evalRestr (Submodule.span F ({u} : Set (V r))) j = (u j * a) • χ := by
    intro j
    ext x
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp x.2
    have hx : x = c • (⟨u, hu_mem⟩ : Submodule.span F ({u} : Set (V r))) :=
      Subtype.ext (by rw [← hc]; simp)
    have h1 : c * u j = (u j * a) * (c * a) := by
      rw [show (u j * a) * (c * a) = c * u j * (a * a) by ring,
        sq_eq_one_of_ne_zero a ha0, mul_one]
    rw [hx, LinearMap.smul_apply, smul_eq_mul]
    simp only [evalRestr, LinearMap.comp_apply, Submodule.coe_subtype, coordProj_apply,
      map_smul, smul_eq_mul]
    rw [← ha]
    exact h1
  have hsupp : ∀ i : Fin r, e i ≠ 0 → u i = e i * a := by
    intro i hi
    simpa [evalRestr, smul_eq_mul, ← ha] using congrArg (fun f => f ⟨u, hu_mem⟩) (hev i hi)
  have hzero : ∀ j : Fin r, e j = 0 → u j = 0 := by
    intro j hj
    by_contra hj0
    have h1 := hval j; have h2 := hne j hj
    rcases eq_one_or_eq_neg_one_of_ne_zero (u j * a) (mul_ne_zero hj0 ha0) with h | h
    · exact h2.1 (by rw [h1, h]; exact one_smul F χ)
    · exact h2.2 (by rw [h1, h]; exact neg_one_smul F χ)
  refine ⟨a, ha0, ?_⟩
  ext i
  by_cases hi : e i = 0
  · rw [hi, Pi.smul_apply, smul_eq_mul, hzero i hi, mul_zero]
  · have h := hsupp i hi
    rw [Pi.smul_apply, smul_eq_mul, h]
    rw [show a * (e i * a) = e i by
      rw [show a * (e i * a) = e i * (a * a) by ring,
        sq_eq_one_of_ne_zero a ha0, mul_one]]

private lemma eq_or_eq_neg_of_occurs_span_extension {r : ℕ} {u e : V r}
    (hocc : occurs (Submodule.span F ({u} : Set (V r))) (.extension e)) :
    e = u ∨ e = -u := by
  obtain ⟨a, ha0, heu⟩ := eq_smul_of_occurs_span_extension hocc
  rcases eq_one_or_eq_neg_one_of_ne_zero a ha0 with h | h
  · left
    rw [heu, h, one_smul]
  · right
    rw [heu, h]
    simp

private lemma eq_zero_or_eq_or_eq_neg_of_card_three {r : ℕ} {X : Submodule F (V r)}
    (hX : Nat.card ↥X = 3) {x : V r} (hx0 : x ≠ 0) (hx : x ∈ X)
    {y : V r} (hy : y ∈ X) : y = 0 ∨ y = x ∨ y = -x := by
  classical
  have hxe : x ≠ -x := by
    intro h
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h'
      exact hx0 (funext fun i => by by_contra hi; exact h' ⟨i, hi⟩)
    have h1 : x i = -x i := congrFun h i
    rcases eq_one_or_eq_neg_one_of_ne_zero (x i) hi with h2 | h2
    · rw [h2] at h1
      exact absurd h1 (by decide)
    · rw [h2] at h1
      exact absurd h1 (by decide)
  have hx0' : (⟨0, X.zero_mem⟩ : ↥X) ≠ ⟨x, hx⟩ := by
    intro h
    exact hx0 (congrArg Subtype.val h).symm
  have hxn0 : (⟨0, X.zero_mem⟩ : ↥X) ≠ ⟨-x, X.neg_mem hx⟩ := by
    intro h
    exact (neg_ne_zero.mpr hx0) (congrArg Subtype.val h).symm
  have hxne : (⟨x, hx⟩ : ↥X) ≠ ⟨-x, X.neg_mem hx⟩ := by
    intro h
    exact hxe (congrArg Subtype.val h)
  let T : Finset ↥X := {⟨0, X.zero_mem⟩, ⟨x, hx⟩, ⟨-x, X.neg_mem hx⟩}
  have hT : T.card = 3 := by
    have hTa : T = {⟨0, X.zero_mem⟩, ⟨x, hx⟩, ⟨-x, X.neg_mem hx⟩} := rfl
    rw [hTa, Finset.card_insert_of_notMem (by simp [hx0', hxn0]),
      Finset.card_insert_of_notMem (by simpa using hxne), Finset.card_singleton]
  have huniv : T = Finset.univ := by
    refine Finset.eq_univ_of_card T ?_
    rw [hT, ← Nat.card_eq_fintype_card, hX]
  have hyT : (⟨y, hy⟩ : ↥X) ∈ T := by rw [huniv]; exact Finset.mem_univ _
  simp only [T, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq] at hyT
  rcases hyT with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

private lemma eq_or_eq_neg_of_mem_of_card_three {r : ℕ} {X : Submodule F (V r)}
    (hX : Nat.card ↥X = 3) {x : V r} (hx0 : x ≠ 0) (hx : x ∈ X)
    {y : V r} (hy0 : y ≠ 0) (hy : y ∈ X) : y = x ∨ y = -x := by
  rcases eq_zero_or_eq_or_eq_neg_of_card_three hX hx0 hx hy with h | h | h
  · exact absurd h hy0
  · exact Or.inl h
  · exact Or.inr h

private lemma exists_support_singleton_of_card_three {r : ℕ} {X : Submodule F (V r)}
    (hX : Nat.card ↥X = 3) {u : V r} (hu : u ≠ 0)
    (hmem : ∀ i, u i ≠ 0 → (Pi.single i 1 : V r) ∈ X) :
    ∃ i, u i ≠ 0 ∧ ∀ j, j ≠ i → u j = 0 := by
  classical
  have huniq : ∀ i j : Fin r, u i ≠ 0 → u j ≠ 0 → i = j := by
    intro i j hi hj
    by_contra hij
    have hx0 : (Pi.single i 1 : V r) ≠ 0 := Pi.single_ne_zero_iff.mpr one_ne_zero
    have hy0 : (Pi.single j 1 : V r) ≠ 0 := Pi.single_ne_zero_iff.mpr one_ne_zero
    rcases eq_or_eq_neg_of_mem_of_card_three hX hx0 (hmem i hi) hy0 (hmem j hj) with h | h
    · have h2 := congrFun h i
      rw [Pi.single_eq_of_ne hij, Pi.single_eq_same] at h2
      exact absurd h2 (by decide)
    · have h2 := congrFun h i
      rw [Pi.single_eq_of_ne hij, Pi.neg_apply, Pi.single_eq_same] at h2
      exact absurd h2 (by decide)
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h'
    exact hu (funext fun i => by by_contra hi; exact h' ⟨i, hi⟩)
  exact ⟨i, hi, fun j hj => by by_contra hj0; exact hj (huniq j i hj0 hi)⟩

private lemma eq_single_or_neg_and_eq_erase {r : ℕ} {S : Finset (Fin r)} {u : V r} {i : Fin r}
    (hS : ∀ j, j ∈ S ↔ u j = 0) (hi : u i ≠ 0) (huniq : ∀ j, j ≠ i → u j = 0) :
    (u = Pi.single i 1 ∨ u = -Pi.single i 1) ∧ S = Finset.univ.erase i := by
  have hue : u = u i • (Pi.single i 1 : V r) := by
    funext j
    by_cases hji : j = i
    · subst hji; simp
    · rw [Pi.smul_apply, Pi.single_eq_of_ne hji, smul_zero, huniq j hji]
  have hS' : S = Finset.univ.erase i := by
    ext j
    rw [hS j, Finset.mem_erase]
    constructor
    · intro hj
      exact ⟨fun hji => hi (hji ▸ hj), Finset.mem_univ j⟩
    · rintro ⟨hji, -⟩
      exact huniq j hji
  refine ⟨?_, hS'⟩
  rcases eq_one_or_eq_neg_one_of_ne_zero (u i) hi with h | h
  · left; rw [hue, h, one_smul]
  · right; rw [hue, h]; simp

private lemma mem_cent_extension_self {r : ℕ} {e u : V r} (h : e = u ∨ e = -u) :
    u ∈ cent .symplectic (.extension e) := by
  rcases h with h | h
  · rw [h, mem_cent_extension]
    intro i hi j hj
    rw [mem_extSupport] at hi hj
    rw [sq_eq_one_of_ne_zero (u i) hi, sq_eq_one_of_ne_zero (u j) hj]
  · rw [h, mem_cent_extension]
    intro i hi j hj
    rw [mem_extSupport] at hi hj
    rw [Pi.neg_apply] at hi hj
    rw [neg_ne_zero] at hi hj
    simp only [Pi.neg_apply, neg_mul, sq_eq_one_of_ne_zero (u i) hi,
      sq_eq_one_of_ne_zero (u j) hj]

private lemma single_mem_cent_extension_self {r : ℕ} {e u : V r} (h : e = u ∨ e = -u)
    {j : Fin r} (hj : u j = 0) :
    (Pi.single j 1 : V r) ∈ cent .symplectic (.extension e) := by
  have hej : e j = 0 := by rcases h with rfl | rfl <;> simp [hj]
  rw [mem_cent_extension]
  intro i hi i' hi'
  have hji : i ≠ j := by
    intro h'
    exact (mem_extSupport e i).mp hi (by rw [h']; exact hej)
  have hji' : i' ≠ j := by
    intro h'
    exact (mem_extSupport e i').mp hi' (by rw [h']; exact hej)
  rw [Pi.single_eq_of_ne hji, Pi.single_eq_of_ne hji', mul_zero, mul_zero]

private lemma single_mem_cent_zero {r : ℕ} {S : Finset (Fin r)} {u : V r}
    (hS : ∀ i, i ∈ S ↔ u i = 0) {i : Fin r} (hi : u i ≠ 0) :
    (Pi.single i 1 : V r) ∈ cent .symplectic (.zero S) := by
  rw [mem_cent_zero]
  intro j hj
  have hji : j ≠ i := by
    intro h'
    exact hi ((hS i).mp (h' ▸ hj))
  exact Pi.single_eq_of_ne hji 1

private lemma row_one_of_zero {r : ℕ} {W : Submodule F (V r)} {S : Finset (Fin r)} {u : V r}
    (hu : u ≠ 0) (hS : ∀ i, i ∈ S ↔ u i = 0)
    (hcard : Nat.card ↥(cent .symplectic (Code.zero S) ⊓ W) = 3)
    (hmemW : ∀ i, u i ≠ 0 → (Pi.single i 1 : V r) ∈ W) :
    ∃ i, Pi.single i 1 ∈ W ∧ (u = Pi.single i 1 ∨ u = -Pi.single i 1) ∧
      Code.zero S = Code.zero (Finset.univ.erase i) := by
  have hmem : ∀ i, u i ≠ 0 → (Pi.single i 1 : V r) ∈ cent .symplectic (Code.zero S) ⊓ W :=
    fun i hi => Submodule.mem_inf.mpr ⟨single_mem_cent_zero hS hi, hmemW i hi⟩
  obtain ⟨i, hi, huniq⟩ := exists_support_singleton_of_card_three hcard hu hmem
  obtain ⟨hue, hS'⟩ := eq_single_or_neg_and_eq_erase hS hi huniq
  exact ⟨i, hmemW i hi, hue, by rw [hS']⟩

private lemma support_subset_pair_of_card_three {r : ℕ} {W : Submodule F (V r)} {k l : Fin r}
    (hkl : k ≠ l) {s : F} (hs : s ≠ 0) (hWkl : ∀ v, v ∈ W ↔ v k = s * v l) {u : V r}
    (huk : u k ≠ 0) (hul : u l ≠ 0) {S : Finset (Fin r)} (hS : ∀ i, i ∈ S ↔ u i = 0)
    (hcard : Nat.card ↥(cent .symplectic (Code.zero S) ⊓ W) = 3) :
    ∀ i, u i ≠ 0 → i = k ∨ i = l := by
  classical
  have hkS : k ∉ S := fun h => huk ((hS k).mp h)
  have hlS : l ∉ S := fun h => hul ((hS l).mp h)
  have hsingleW : ∀ i, i ≠ k → i ≠ l → (Pi.single i 1 : V r) ∈ W := by
    intro i hik hil
    rw [hWkl]
    simp [Pi.single_eq_of_ne (Ne.symm hik), Pi.single_eq_of_ne (Ne.symm hil)]
  set y : V r := (Pi.single k 1 : V r) + s • (Pi.single l 1 : V r) with hydef
  have hy0 : y ≠ 0 := by
    intro h
    have h1 := congrFun h k
    rw [hydef] at h1
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hkl,
      smul_eq_mul, mul_zero, add_zero] at h1
    exact one_ne_zero h1
  have hyW : y ∈ W := by
    rw [hWkl]
    simp [hydef, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hkl,
      Pi.single_eq_of_ne (Ne.symm hkl), smul_eq_mul, sq_eq_one_of_ne_zero s hs]
  have hyCent : y ∈ cent .symplectic (Code.zero S) := by
    rw [mem_cent_zero]
    intro i hi
    have hik : i ≠ k := fun h => hkS (h ▸ hi)
    have hil : i ≠ l := fun h => hlS (h ▸ hi)
    simp [hydef, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hik, Pi.single_eq_of_ne hil]
  intro i hi
  by_contra hcon
  obtain ⟨hik, hil⟩ := not_or.mp hcon
  have hx0 : (Pi.single i 1 : V r) ≠ 0 := Pi.single_ne_zero_iff.mpr one_ne_zero
  have hxX : (Pi.single i 1 : V r) ∈ cent .symplectic (Code.zero S) ⊓ W :=
    Submodule.mem_inf.mpr ⟨single_mem_cent_zero hS hi, hsingleW i hik hil⟩
  have hyX : y ∈ cent .symplectic (Code.zero S) ⊓ W := Submodule.mem_inf.mpr ⟨hyCent, hyW⟩
  rcases eq_or_eq_neg_of_mem_of_card_three hcard hx0 hxX hy0 hyX with h | h
  · have h2 := congrFun h i
    simp only [hydef, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hik,
      Pi.single_eq_of_ne hil, smul_eq_mul, mul_zero, add_zero] at h2
    exact one_ne_zero h2.symm
  · have h2 := congrFun h i
    simp only [hydef, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne hik, Pi.single_eq_of_ne hil, smul_eq_mul, mul_zero, add_zero] at h2
    exact absurd h2 (by decide)

private lemma row_two_of_zero {r : ℕ} (hr : 4 ≤ r) {W : Submodule F (V r)} {k l : Fin r}
    (hkl : k ≠ l) {s : F} (hs : s ≠ 0) (hWkl : ∀ v, v ∈ W ↔ v k = s * v l) {u : V r}
    (huk : u k ≠ 0) (hul : u l ≠ 0) {S : Finset (Fin r)} (hS : ∀ i, i ∈ S ↔ u i = 0)
    (hcard : Nat.card ↥(cent .symplectic (Code.zero S) ⊓ W) = 3)
    (hns : label .symplectic (Code.zero S) ≠ ⟨.B2der, 0, 1⟩) :
    ∃ k l, k ≠ l ∧ ∃ s : F, s ≠ 0 ∧ (∀ v, v ∈ W ↔ v k = s * v l) ∧
      (∀ i, u i ≠ 0 ↔ i = k ∨ i = l) ∧
      Code.zero S = Code.zero ((Finset.univ.erase k).erase l) ∧ 5 ≤ r := by
  have hsupp : ∀ i, u i ≠ 0 ↔ i = k ∨ i = l := fun i =>
    ⟨support_subset_pair_of_card_three hkl hs hWkl huk hul hS hcard i,
      fun h => h.elim (fun hk => hk ▸ huk) (fun hl => hl ▸ hul)⟩
  have hS' : S = (Finset.univ.erase k).erase l := by
    ext i
    rw [hS i, Finset.mem_erase, Finset.mem_erase]
    constructor
    · intro hi
      exact ⟨fun h => hul (by rw [← h]; exact hi), fun h => huk (by rw [← h]; exact hi),
        Finset.mem_univ i⟩
    · rintro ⟨hil, hik, -⟩
      by_contra hui
      exact ((hsupp i).mp hui).elim hik hil
  have hScard : S.card = r - 2 := by
    rw [hS', Finset.card_erase_of_mem (by simp [Ne.symm hkl]),
      Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
    omega
  have h5 : 5 ≤ r := by
    by_contra hlt
    have hr4 : r = 4 := by omega
    apply hns
    have hS2 : S.card = 2 := by rw [hScard, hr4]
    simp only [label]
    rw [if_pos hS2]
  refine ⟨k, l, hkl, s, hs, hWkl, hsupp, ?_, h5⟩
  rw [hS']

private lemma row_three_of_extension_W_eq {r : ℕ} (hr : 4 ≤ r) {W : Submodule F (V r)}
    {k l : Fin r} {s : F} (hWkl : ∀ v, v ∈ W ↔ v k = s * v l) {u e : V r}
    (hu : u ≠ 0) (huW : u ∈ W) (huk : u k ≠ 0) (hul : u l ≠ 0) (hue : e = u ∨ e = -u)
    (hcard : Nat.card ↥(cent .symplectic (Code.extension e) ⊓ W) = 3)
    (hns : label .symplectic (Code.extension e) ≠ ⟨.twA, 3, 1⟩) :
    (∀ i, u i ≠ 0) ∧
      (Code.extension e = Code.extension u ∨ Code.extension e = Code.extension (-u)) ∧ 5 ≤ r := by
  have hsingleW : ∀ j, j ≠ k → j ≠ l → (Pi.single j 1 : V r) ∈ W := by
    intro j hjk hjl
    rw [hWkl]
    simp [Pi.single_eq_of_ne (Ne.symm hjk), Pi.single_eq_of_ne (Ne.symm hjl)]
  have hfull : ∀ j, u j ≠ 0 := by
    intro j
    by_contra hj
    have hj0 : u j = 0 := by simpa using hj
    have hjk : j ≠ k := fun h => huk (by rw [← h]; exact hj0)
    have hjl : j ≠ l := fun h => hul (by rw [← h]; exact hj0)
    have hx0 : (Pi.single j 1 : V r) ≠ 0 := Pi.single_ne_zero_iff.mpr one_ne_zero
    have hxX : (Pi.single j 1 : V r) ∈ cent .symplectic (Code.extension e) ⊓ W :=
      Submodule.mem_inf.mpr ⟨single_mem_cent_extension_self hue hj0, hsingleW j hjk hjl⟩
    have hyX : u ∈ cent .symplectic (Code.extension e) ⊓ W :=
      Submodule.mem_inf.mpr ⟨mem_cent_extension_self hue, huW⟩
    rcases eq_or_eq_neg_of_mem_of_card_three hcard hx0 hxX hu hyX with h | h
    · have h2 := congrFun h j
      rw [hj0, Pi.single_eq_same] at h2
      exact one_ne_zero h2.symm
    · have h2 := congrFun h j
      rw [hj0, Pi.neg_apply, Pi.single_eq_same] at h2
      exact absurd h2.symm (by decide)
  have hsuppE : Code.extSupport e = Finset.univ := by
    have heu : Code.extSupport e = Code.extSupport u := by
      rcases hue with h | h
      · rw [h]
      · rw [h]
        ext i
        simp [Pi.neg_apply]
    have hu_supp : Code.extSupport u = Finset.univ := by ext i; simp [hfull i]
    rw [heu, hu_supp]
  have hcardE : (Code.extSupport e).card = r := by
    rw [hsuppE, Finset.card_univ, Fintype.card_fin]
  have h5 : 5 ≤ r := by
    by_contra hlt
    have hr4 : r = 4 := by omega
    apply hns
    have hcard4 : (Code.extSupport e).card = 4 := by rw [hcardE, hr4]
    simp only [label, hcard4]
  refine ⟨hfull, ?_, h5⟩
  rcases hue with h | h
  · left; rw [h]
  · right; rw [h]

private lemma false_of_extension_W_eq_outside {r : ℕ} {W : Submodule F (V r)} {k l : Fin r}
    (hkl : k ≠ l) {s : F} (hs : s ≠ 0) (hWkl : ∀ v, v ∈ W ↔ v k = s * v l) {u e : V r}
    (hu : u ≠ 0) (huk : u k = 0) (hul : u l = 0) (hue : e = u ∨ e = -u)
    (hcard : Nat.card ↥(cent .symplectic (Code.extension e) ⊓ W) = 3) : False := by
  have heu : Code.extSupport e = Code.extSupport u := by
    rcases hue with h | h
    · rw [h]
    · rw [h]
      ext i
      simp [Pi.neg_apply]
  set y : V r := (Pi.single k 1 : V r) + s • (Pi.single l 1 : V r) with hydef
  have hyk : y k = 1 := by
    simp [hydef, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hkl,
      smul_eq_mul]
  have hy0 : y ≠ 0 := by
    intro h
    have h1 := congrFun h k
    rw [hyk] at h1
    exact one_ne_zero h1
  have hyW : y ∈ W := by
    rw [hWkl]
    simp [hydef, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hkl,
      Pi.single_eq_of_ne (Ne.symm hkl), smul_eq_mul, sq_eq_one_of_ne_zero s hs]
  have hyCent : y ∈ cent .symplectic (Code.extension e) := by
    rw [mem_cent_extension]
    intro i hi i' hi'
    rw [heu] at hi hi'
    rw [mem_extSupport] at hi hi'
    have hik : i ≠ k := fun h => hi (h ▸ huk)
    have hil : i ≠ l := fun h => hi (h ▸ hul)
    have hi'k : i' ≠ k := fun h => hi' (h ▸ huk)
    have hi'l : i' ≠ l := fun h => hi' (h ▸ hul)
    have hyi : y i = 0 := by
      simp [hydef, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hik, Pi.single_eq_of_ne hil]
    have hyi' : y i' = 0 := by
      simp [hydef, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hi'k, Pi.single_eq_of_ne hi'l]
    rw [hyi, hyi', mul_zero, mul_zero]
  have huW : u ∈ W := (hWkl u).mpr (by rw [huk, hul, mul_zero])
  have hyX : y ∈ cent .symplectic (Code.extension e) ⊓ W :=
    Submodule.mem_inf.mpr ⟨hyCent, hyW⟩
  have huX : u ∈ cent .symplectic (Code.extension e) ⊓ W :=
    Submodule.mem_inf.mpr ⟨mem_cent_extension_self hue, huW⟩
  rcases eq_or_eq_neg_of_mem_of_card_three hcard hy0 hyX hu huX with h | h
  · have h2 := congrFun h k
    rw [huk, hyk] at h2
    exact one_ne_zero h2.symm
  · have h2 := congrFun h k
    rw [huk, Pi.neg_apply, hyk] at h2
    exact absurd h2 (by decide)

private lemma extension_support_erase_of_W_zero {r : ℕ} {W : Submodule F (V r)} {k : Fin r}
    (hWk : ∀ v, v ∈ W ↔ v k = 0) {u e : V r} (hu : u ≠ 0) (huW : u ∈ W)
    (hue : e = u ∨ e = -u)
    (hcard : Nat.card ↥(cent .symplectic (Code.extension e) ⊓ W) = 3) :
    (∀ i, u i = 0 ↔ i = k) ∧ Code.extSupport e = Finset.univ.erase k := by
  have huk : u k = 0 := (hWk u).mp huW
  have hsingleW : ∀ j, j ≠ k → (Pi.single j 1 : V r) ∈ W := by
    intro j hjk
    rw [hWk]
    simp [Pi.single_eq_of_ne (Ne.symm hjk)]
  have hsupp : ∀ j, j ≠ k → u j ≠ 0 := by
    intro j hjk
    by_contra hj
    have hj0 : u j = 0 := by simpa using hj
    have hx0 : (Pi.single j 1 : V r) ≠ 0 := Pi.single_ne_zero_iff.mpr one_ne_zero
    have hxX : (Pi.single j 1 : V r) ∈ cent .symplectic (Code.extension e) ⊓ W :=
      Submodule.mem_inf.mpr ⟨single_mem_cent_extension_self hue hj0, hsingleW j hjk⟩
    have huX : u ∈ cent .symplectic (Code.extension e) ⊓ W :=
      Submodule.mem_inf.mpr ⟨mem_cent_extension_self hue, huW⟩
    rcases eq_or_eq_neg_of_mem_of_card_three hcard hx0 hxX hu huX with h | h
    · have h2 := congrFun h j
      rw [hj0, Pi.single_eq_same] at h2
      exact one_ne_zero h2.symm
    · have h2 := congrFun h j
      rw [hj0, Pi.neg_apply, Pi.single_eq_same] at h2
      exact absurd h2.symm (by decide)
  have hzeros : ∀ i, u i = 0 ↔ i = k := by
    intro i
    exact ⟨fun hi => by_contra fun hik => hsupp i hik hi, fun h => by rw [h]; exact huk⟩
  have heu : Code.extSupport e = Code.extSupport u := by
    rcases hue with h | h
    · rw [h]
    · rw [h]
      ext i
      simp [Pi.neg_apply]
  refine ⟨hzeros, ?_⟩
  have hu_supp : Code.extSupport u = Finset.univ.erase k := by
    ext i
    rw [mem_extSupport, Finset.mem_erase]
    exact ⟨fun hi => ⟨fun h => hi ((hzeros i).mpr h), Finset.mem_univ i⟩,
      fun h => fun hi => h.1 ((hzeros i).mp hi)⟩
  rw [heu, hu_supp]

private lemma row_four_of_extension_W_zero {r : ℕ} {W : Submodule F (V r)} {k : Fin r}
    (hWk : ∀ v, v ∈ W ↔ v k = 0) {u e : V r} (hu : u ≠ 0) (huW : u ∈ W) (hue : e = u ∨ e = -u)
    (hcard : Nat.card ↥(cent .symplectic (Code.extension e) ⊓ W) = 3)
    (h4 : 4 ≤ (Code.extSupport e).card)
    (hns : label .symplectic (Code.extension e) ≠ ⟨.twA, 3, 1⟩) :
    ∃ k, (∀ v, v ∈ W ↔ v k = 0) ∧ (∀ i, u i = 0 ↔ i = k) ∧
      (Code.extension e = Code.extension u ∨ Code.extension e = Code.extension (-u)) ∧ 6 ≤ r := by
  obtain ⟨hzeros, hsuppE⟩ := extension_support_erase_of_W_zero hWk hu huW hue hcard
  have hcardE : (Code.extSupport e).card = r - 1 := by
    rw [hsuppE, Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ,
      Fintype.card_fin]
  have h5 : 5 ≤ r := by
    have := h4
    rw [hcardE] at this
    omega
  have h6 : 6 ≤ r := by
    by_contra hlt
    have hr5 : r = 5 := by omega
    apply hns
    have hcard5 : (Code.extSupport e).card = 4 := by rw [hcardE, hr5]
    simp only [label, hcard5]
  refine ⟨k, hWk, hzeros, ?_, h6⟩
  rcases hue with h | h
  · left; rw [h]
  · right; rw [h]

private lemma corner_zero_W_zero {r : ℕ} {W : Submodule F (V r)} {k : Fin r}
    (hWk : ∀ v, v ∈ W ↔ v k = 0) {u : V r} (hu : u ≠ 0) (huW : u ∈ W)
    {S : Finset (Fin r)} (hS : ∀ i, i ∈ S ↔ u i = 0)
    (hcard : Nat.card ↥(cent .symplectic (Code.zero S) ⊓ W) = 3) :
    ∃ i, Pi.single i 1 ∈ W ∧ (u = Pi.single i 1 ∨ u = -Pi.single i 1) ∧
      Code.zero S = Code.zero (Finset.univ.erase i) := by
  have huk : u k = 0 := (hWk u).mp huW
  refine row_one_of_zero hu hS hcard fun i hi => ?_
  have hik : i ≠ k := fun h => hi (by rw [h]; exact huk)
  rw [hWk]
  simp [Pi.single_eq_of_ne (Ne.symm hik)]

private lemma corner_zero_W_eq {r : ℕ} (hr : 4 ≤ r) {W : Submodule F (V r)} {k l : Fin r}
    (hkl : k ≠ l) {s : F} (hs : s ≠ 0) (hWkl : ∀ v, v ∈ W ↔ v k = s * v l) {u : V r}
    (hu : u ≠ 0) (huW : u ∈ W) {S : Finset (Fin r)} (hS : ∀ i, i ∈ S ↔ u i = 0)
    (hcard : Nat.card ↥(cent .symplectic (Code.zero S) ⊓ W) = 3)
    (hns : label .symplectic (Code.zero S) ≠ ⟨.B2der, 0, 1⟩) :
    (∃ i, Pi.single i 1 ∈ W ∧ (u = Pi.single i 1 ∨ u = -Pi.single i 1) ∧
        Code.zero S = Code.zero (Finset.univ.erase i)) ∨
      (∃ k l, k ≠ l ∧ ∃ s : F, s ≠ 0 ∧ (∀ v, v ∈ W ↔ v k = s * v l) ∧
        (∀ i, u i ≠ 0 ↔ i = k ∨ i = l) ∧
        Code.zero S = Code.zero ((Finset.univ.erase k).erase l) ∧ 5 ≤ r) := by
  have hukl : u k = s * u l := (hWkl u).mp huW
  by_cases huk0 : u k = 0
  · have hul0 : u l = 0 := by
      have h : s * u l = 0 := by rw [← hukl, huk0]
      exact (mul_eq_zero.mp h).resolve_left hs
    refine Or.inl (row_one_of_zero hu hS hcard fun i hi => ?_)
    have hik : i ≠ k := fun h => hi (by rw [h]; exact huk0)
    have hil : i ≠ l := fun h => hi (by rw [h]; exact hul0)
    rw [hWkl]
    simp [Pi.single_eq_of_ne (Ne.symm hik), Pi.single_eq_of_ne (Ne.symm hil)]
  · have hul : u l ≠ 0 := by
      intro h0
      exact huk0 (by rw [hukl, h0, mul_zero])
    exact Or.inr (row_two_of_zero hr hkl hs hWkl huk0 hul hS hcard hns)

private lemma corner_extension_W_eq {r : ℕ} (hr : 4 ≤ r) {W : Submodule F (V r)}
    {k l : Fin r} (hkl : k ≠ l) {s : F} (hs : s ≠ 0) (hWkl : ∀ v, v ∈ W ↔ v k = s * v l)
    {u e : V r} (hu : u ≠ 0) (huW : u ∈ W) (hue : e = u ∨ e = -u)
    (hcard : Nat.card ↥(cent .symplectic (Code.extension e) ⊓ W) = 3)
    (hns : label .symplectic (Code.extension e) ≠ ⟨.twA, 3, 1⟩) :
    ∃ k l, k ≠ l ∧ ∃ s : F, s ≠ 0 ∧ (∀ v, v ∈ W ↔ v k = s * v l) ∧
      (∀ i, u i ≠ 0) ∧
      (Code.extension e = Code.extension u ∨ Code.extension e = Code.extension (-u)) ∧ 5 ≤ r := by
  have hukl : u k = s * u l := (hWkl u).mp huW
  by_cases huk0 : u k = 0
  · have hul0 : u l = 0 := by
      have h : s * u l = 0 := by rw [← hukl, huk0]
      exact (mul_eq_zero.mp h).resolve_left hs
    exact (false_of_extension_W_eq_outside hkl hs hWkl hu huk0 hul0 hue hcard).elim
  · have hul : u l ≠ 0 := by
      intro h0
      exact huk0 (by rw [hukl, h0, mul_zero])
    obtain ⟨hfull, hext, h5⟩ :=
      row_three_of_extension_W_eq hr hWkl hu huW huk0 hul hue hcard hns
    exact ⟨k, l, hkl, s, hs, hWkl, hfull, hext, h5⟩

theorem corner_rows_of_occurs_span {r : ℕ} (hr : 4 ≤ r) {W : Submodule F (V r)}
    (hW : (∃ k, ∀ v, v ∈ W ↔ v k = 0) ∨
      ∃ k l, k ≠ l ∧ ∃ s : F, s ≠ 0 ∧ ∀ v, v ∈ W ↔ v k = s * v l)
    {u : V r} (hu : u ≠ 0) (huW : u ∈ W) {c : Code r}
    (hc : admissible .symplectic c) (hocc : occurs (Submodule.span F {u}) c)
    (hcard : Nat.card ↥(cent .symplectic c ⊓ W) = 3)
    (hns : label .symplectic c ≠ ⟨.B2der, 0, 1⟩ ∧ label .symplectic c ≠ ⟨.twA, 3, 1⟩) :
    (∃ i, Pi.single i 1 ∈ W ∧ (u = Pi.single i 1 ∨ u = -Pi.single i 1) ∧
        c = .zero (Finset.univ.erase i)) ∨
      (∃ k l, k ≠ l ∧ ∃ s : F, s ≠ 0 ∧ (∀ v, v ∈ W ↔ v k = s * v l) ∧
        (∀ i, u i ≠ 0 ↔ i = k ∨ i = l) ∧ c = .zero ((Finset.univ.erase k).erase l) ∧ 5 ≤ r) ∨
      (∃ k l, k ≠ l ∧ ∃ s : F, s ≠ 0 ∧ (∀ v, v ∈ W ↔ v k = s * v l) ∧ (∀ i, u i ≠ 0) ∧
        (c = .extension u ∨ c = .extension (-u)) ∧ 5 ≤ r) ∨
      (∃ k, (∀ v, v ∈ W ↔ v k = 0) ∧ (∀ i, u i = 0 ↔ i = k) ∧
        (c = .extension u ∨ c = .extension (-u)) ∧ 6 ≤ r) := by
  rcases hW with ⟨k, hWk⟩ | ⟨k, l, hkl, s, hs, hWkl⟩
  · cases c with
    | zero S =>
        exact Or.inl (corner_zero_W_zero hWk hu huW (occurs_zero_span_iff.mp hocc) hcard)
    | extension e =>
        have h4 : 4 ≤ (Code.extSupport e).card := hc.2
        have hue : e = u ∨ e = -u := eq_or_eq_neg_of_occurs_span_extension hocc
        exact Or.inr (Or.inr (Or.inr
          (row_four_of_extension_W_zero hWk hu huW hue hcard h4 hns.2)))
  · cases c with
    | zero S =>
        have hS : ∀ i, i ∈ S ↔ u i = 0 := occurs_zero_span_iff.mp hocc
        rcases corner_zero_W_eq hr hkl hs hWkl hu huW hS hcard hns.1 with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
    | extension e =>
        have h4 : 4 ≤ (Code.extSupport e).card := hc.2
        have hue : e = u ∨ e = -u := eq_or_eq_neg_of_occurs_span_extension hocc
        exact Or.inr (Or.inr (Or.inl
          (corner_extension_W_eq hr hkl hs hWkl hu huW hue hcard hns.2)))

end CFSG.StandardType.GGQ2Frame.PlaneRaw

end
