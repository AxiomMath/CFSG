module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpWeylOrbit

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Universal.Symplectic
open CFSG.StandardType

@[expose] def spLabelVec {n : ℕ} (a : Fin n → ℕ) : Fin n → ℤ :=
  fun j => ∑ i ∈ Finset.univ.filter (j ≤ ·), (a i : ℤ)

private theorem spLO_spLabelVec_nonneg {n : ℕ} (a : Fin n → ℕ) (j : Fin n) :
    0 ≤ spLabelVec a j := by
  unfold spLabelVec
  exact Finset.sum_nonneg fun i _ => by positivity

private theorem spLO_spLabelVec_anti {n : ℕ} (a : Fin n → ℕ) :
    Antitone (spLabelVec a) := by
  intro x y hxy
  unfold spLabelVec
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun z hz => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact le_trans hxy hz)
    (fun z _ _ => by positivity)

private theorem spLO_spLabelVec_succ {n : ℕ} (a : Fin n → ℕ) (k : Fin n)
    (hlt : k.val + 1 < n) :
    spLabelVec a k = spLabelVec a ⟨k.val + 1, hlt⟩ + (a k : ℤ) := by
  unfold spLabelVec
  have hins : Finset.univ.filter (fun i : Fin n => k ≤ i) =
      insert k (Finset.univ.filter fun i : Fin n => (⟨k.val + 1, hlt⟩ : Fin n) ≤ i) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hx
      rw [Fin.le_def] at hx
      rcases eq_or_lt_of_le hx with h | h
      · exact Or.inl (Fin.ext h.symm)
      · exact Or.inr h
    · rintro (rfl | hx)
      · exact le_rfl
      · exact le_trans (Fin.le_def.mpr (Nat.le_succ k.val)) hx
  have hknot : k ∉ Finset.univ.filter fun i : Fin n => (⟨k.val + 1, hlt⟩ : Fin n) ≤ i := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
    exact Fin.lt_def.mpr (by simp)
  rw [hins, Finset.sum_insert hknot]
  ring

private theorem spLO_spLabelVec_swap_succ {n : ℕ} {a : Fin n → ℕ} {k : Fin n}
    (hk : a k = 0) (hlt : k.val + 1 < n) :
    spLabelVec a k = spLabelVec a ⟨k.val + 1, hlt⟩ := by
  simpa [hk] using spLO_spLabelVec_succ a k hlt

private theorem spLO_spLabelVec_swap_succ_apply {n : ℕ} {a : Fin n → ℕ} {k : Fin n}
    (hk : a k = 0) (hlt : k.val + 1 < n) (b : Fin n) :
    spLabelVec a (Equiv.swap k ⟨k.val + 1, hlt⟩ b) = spLabelVec a b := by
  by_cases hb : b = k
  · subst hb
    rw [Equiv.swap_apply_left]
    exact (spLO_spLabelVec_swap_succ hk hlt).symm
  · by_cases hb' : b = ⟨k.val + 1, hlt⟩
    · subst hb'
      rw [Equiv.swap_apply_right]
      exact spLO_spLabelVec_swap_succ hk hlt
    · rw [Equiv.swap_apply_of_ne_of_ne hb hb']

private theorem spLO_spLabelVec_last_eq_zero {n : ℕ} {a : Fin n → ℕ} {k : Fin n}
    (hk : a k = 0) (hlast : k.val + 1 = n) : spLabelVec a k = 0 := by
  have h : Finset.univ.filter (fun i : Fin n => k ≤ i) = {k} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hx
      apply Fin.ext
      rw [Fin.le_def] at hx
      have := x.isLt
      omega
    · intro hx
      rw [hx]
  unfold spLabelVec
  rw [h, Finset.sum_singleton, hk]
  norm_num

private theorem spLO_spLabelVec_pos {n : ℕ} {a : Fin n → ℕ} {j : Fin n} {i : Fin n}
    (hi : j ≤ i) (hipos : 0 < a i) : 0 < spLabelVec a j := by
  have hmem : i ∈ Finset.univ.filter fun x : Fin n => j ≤ x := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi
  have hle := Finset.single_le_sum
    (s := Finset.univ.filter fun x : Fin n => j ≤ x)
    (f := fun x => (a x : ℤ)) (fun x _ => by positivity) hmem
  have hpos : (0 : ℤ) < (a i : ℤ) := by exact_mod_cast hipos
  exact lt_of_lt_of_le hpos (by simpa [spLabelVec] using hle)

private theorem spLO_spLabelVec_cube {n : ℕ} (hn : n = 3) {a : Fin n → ℕ}
    (h : a ⟨0, by omega⟩ ≠ 0 ∨ a ⟨1, by omega⟩ ≠ 0) :
    spLabelVec a ⟨2, by omega⟩ ≠ spLabelVec a ⟨0, by omega⟩ := by
  subst hn
  intro heq
  have hs0 := spLO_spLabelVec_succ a (⟨0, by omega⟩ : Fin 3) (by norm_num)
  have hs1 := spLO_spLabelVec_succ a (⟨1, by omega⟩ : Fin 3) (by norm_num)
  have hsum : (a ⟨0, by omega⟩ : ℤ) + (a ⟨1, by omega⟩ : ℤ) = 0 := by
    have h' := hs0
    rw [hs1, heq] at h'
    omega
  rcases h with h0 | h1
  · apply h0
    have hz : (a ⟨0, by omega⟩ : ℤ) = 0 := by
      have := Int.natCast_nonneg (a ⟨1, by omega⟩)
      omega
    exact_mod_cast hz
  · apply h1
    have hz : (a ⟨1, by omega⟩ : ℤ) = 0 := by
      have := Int.natCast_nonneg (a ⟨0, by omega⟩)
      omega
    exact_mod_cast hz

private theorem spLO_toStd_weylAction_spFromStd2 {n : ℕ} {c : Fin n → ℤ}
    {w : (coxeterMatrix (isFiniteType_cartanC n)).Group} {π : Equiv.Perm (Fin n)}
    {s : Fin n → ℤ} (h : SpRealizes n w π s) :
    toStd n (weylAction (isFiniteType_cartanC n) w (spFromStd2 n c)) =
      fun b => 2 * spAct π s c b := by
  rw [h (spFromStd2 n c), toStd_spFromStd2 n c]
  funext b
  simp only [spAct]
  ring

private theorem spLO_act_ne {n : ℕ} (hn : 2 ≤ n) {π : Equiv.Perm (Fin n)} {s : Fin n → ℤ}
    (hx : (π ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧ s ⟨0, by omega⟩ = -1) ∨
      (π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧ π ⟨1, by omega⟩ = ⟨0, by omega⟩ ∧
        s ⟨0, by omega⟩ = -1 ∧ s ⟨1, by omega⟩ = -1))
    {v w : Fin n → ℤ} (hv : 0 < v ⟨0, by omega⟩) (hw0 : 0 < w ⟨0, by omega⟩)
    (hw1 : 0 < w ⟨1, by omega⟩) :
    v ≠ spAct π s w := by
  rcases hx with ⟨hπ0, hs0⟩ | ⟨hπ01, hπ10, hs0, hs1⟩
  · intro h
    have h0 := congrFun h ⟨0, by omega⟩
    have hπ0' : π.symm ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
      simpa [hπ0] using Equiv.symm_apply_apply π (⟨0, by omega⟩ : Fin n)
    have e : spAct π s w ⟨0, by omega⟩ = - w ⟨0, by omega⟩ := by
      simp [spAct, hπ0', hs0]
    rw [e] at h0
    omega
  · intro h
    have h0 := congrFun h ⟨0, by omega⟩
    have hπ1' : π.symm ⟨0, by omega⟩ = ⟨1, by omega⟩ := by
      simpa [hπ10] using Equiv.symm_apply_apply π (⟨1, by omega⟩ : Fin n)
    have e : spAct π s w ⟨0, by omega⟩ = - w ⟨1, by omega⟩ := by
      simp [spAct, hπ1', hs1]
    rw [e] at h0
    omega

theorem weylAction_simple_spLabelVec {n : ℕ} (a : Fin n → ℕ) {k : Fin n} (hk : a k = 0) :
    weylAction (isFiniteType_cartanC n)
      ((coxeterMatrix (isFiniteType_cartanC n)).toCoxeterSystem.simple k)
        (spFromStd2 n (spLabelVec a)) = spFromStd2 n (spLabelVec a) := by
  by_cases hlt : k.val + 1 < n
  · refine SpRealizes.fix (spRealizes_simple_of_lt hlt) ?_
    intro b
    rw [Equiv.symm_swap, toStd_spFromStd2]
    dsimp only
    rw [spLO_spLabelVec_swap_succ_apply hk hlt b]
    simp only [Pi.one_apply]
    ring
  · refine SpRealizes.fix (spRealizes_simple_of_not_lt hlt) ?_
    intro b
    have hlast : k.val + 1 = n := by have := k.isLt; omega
    change spSgn k b * toStd n (spFromStd2 n (spLabelVec a)) b =
      toStd n (spFromStd2 n (spLabelVec a)) b
    rw [toStd_spFromStd2]
    dsimp only
    by_cases hb : b = k
    · subst hb
      rw [spLO_spLabelVec_last_eq_zero hk hlast]
      unfold spSgn
      rw [if_pos rfl]
      ring
    · unfold spSgn
      rw [if_neg hb]
      ring

private def spLO_v2 {n : ℕ} (hn : 3 ≤ n) (a : Fin n → ℕ) : Fin 2 → Fin n → ℤ :=
  ![spLabelVec a, spAct 1 (spSgn ⟨2, by omega⟩) (spLabelVec a)]

private noncomputable def spLO_u2 {n : ℕ} (w : (coxeterMatrix (isFiniteType_cartanC n)).Group)
    (c : Fin n → ℤ) : Fin 2 → Fin n → ℤ :=
  ![spFromStd2 n c, weylAction (isFiniteType_cartanC n) w (spFromStd2 n c)]

private theorem spLO_u2_zero {n : ℕ} (w : (coxeterMatrix (isFiniteType_cartanC n)).Group)
    (c : Fin n → ℤ) : spLO_u2 w c 0 = spFromStd2 n c := rfl

private theorem spLO_u2_one {n : ℕ} (w : (coxeterMatrix (isFiniteType_cartanC n)).Group)
    (c : Fin n → ℤ) :
    spLO_u2 w c 1 = weylAction (isFiniteType_cartanC n) w (spFromStd2 n c) := rfl

private theorem spLO_v2_zero {n : ℕ} (hn : 3 ≤ n) (a : Fin n → ℕ) :
    spLO_v2 hn a 0 = spLabelVec a := rfl

private theorem spLO_v2_one {n : ℕ} (hn : 3 ≤ n) (a : Fin n → ℕ) :
    spLO_v2 hn a 1 = spAct 1 (spSgn ⟨2, by omega⟩) (spLabelVec a) := rfl

private theorem spLO_u2_toStd {n : ℕ} (hn : 3 ≤ n) {a : Fin n → ℕ}
    {w : (coxeterMatrix (isFiniteType_cartanC n)).Group}
    (hw : SpRealizes n w 1 (spSgn ⟨2, by omega⟩)) :
    ∀ i : Fin 2, toStd n (spLO_u2 w (spLabelVec a) i) = fun b => 2 * spLO_v2 hn a i b := by
  rw [Fin.forall_fin_two]
  constructor
  · rw [spLO_u2_zero, spLO_v2_zero]
    exact toStd_spFromStd2 n (spLabelVec a)
  · rw [spLO_u2_one, spLO_v2_one]
    exact spLO_toStd_weylAction_spFromStd2 (h := hw)

private theorem spLO_v2_pos {n : ℕ} (hn : 3 ≤ n) {a : Fin n → ℕ}
    (hc0 : 0 < spLabelVec a ⟨0, by omega⟩) (hc1 : 0 < spLabelVec a ⟨1, by omega⟩) :
    ∀ i : Fin 2, 0 < spLO_v2 hn a i ⟨0, by omega⟩ ∧
      0 < spLO_v2 hn a i ⟨1, by omega⟩ := by
  rw [Fin.forall_fin_two]
  constructor
  · rw [spLO_v2_zero]
    exact ⟨hc0, hc1⟩
  · rw [spLO_v2_one]
    have h02 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by
      intro he
      have := congrArg Fin.val he
      simp at this
    have h12 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by
      intro he
      have := congrArg Fin.val he
      simp at this
    exact ⟨by simpa [spAct, spSgn, h02, Equiv.Perm.one_def, Equiv.refl_symm] using hc0,
      by simpa [spAct, spSgn, h12, Equiv.Perm.one_def, Equiv.refl_symm] using hc1⟩

private theorem spLO_u2_injective {n : ℕ} (hn : 3 ≤ n) {a : Fin n → ℕ}
    {w : (coxeterMatrix (isFiniteType_cartanC n)).Group}
    (hw : SpRealizes n w 1 (spSgn ⟨2, by omega⟩))
    (hc2 : 0 < spLabelVec a ⟨2, by omega⟩) :
    Function.Injective (spLO_u2 w (spLabelVec a)) := by
  have hne : spLO_u2 w (spLabelVec a) 0 ≠ spLO_u2 w (spLabelVec a) 1 := by
    intro h
    have key := congrArg (fun f => toStd n f ⟨2, by omega⟩) h
    rw [spLO_u2_toStd hn hw 0, spLO_u2_toStd hn hw 1] at key
    dsimp only at key
    have e0 : spLO_v2 hn a 0 ⟨2, by omega⟩ = spLabelVec a ⟨2, by omega⟩ := by
      rw [spLO_v2_zero]
    have e1 : spLO_v2 hn a 1 ⟨2, by omega⟩ = - spLabelVec a ⟨2, by omega⟩ := by
      rw [spLO_v2_one]
      simp [spAct, spSgn, Equiv.Perm.one_def, Equiv.refl_symm]
    rw [e0, e1] at key
    omega
  rw [spLO_u2, Matrix.injective_pair_iff_ne]
  exact hne

private theorem spLO_u2_moved {n : ℕ} (hn : 3 ≤ n) {a : Fin n → ℕ}
    {w : (coxeterMatrix (isFiniteType_cartanC n)).Group}
    (hw : SpRealizes n w 1 (spSgn ⟨2, by omega⟩))
    {x : (coxeterMatrix (isFiniteType_cartanC n)).Group} {π : Equiv.Perm (Fin n)}
    {s : Fin n → ℤ} (hxr : SpRealizes n x π s)
    (hx : (π ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧ s ⟨0, by omega⟩ = -1) ∨
      (π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧ π ⟨1, by omega⟩ = ⟨0, by omega⟩ ∧
        s ⟨0, by omega⟩ = -1 ∧ s ⟨1, by omega⟩ = -1))
    (hc0 : 0 < spLabelVec a ⟨0, by omega⟩) (hc1 : 0 < spLabelVec a ⟨1, by omega⟩) :
    ∀ i j, spLO_u2 w (spLabelVec a) i ≠
      weylAction (isFiniteType_cartanC n) x (spLO_u2 w (spLabelVec a) j) := by
  intro i j hij
  have hpos := spLO_v2_pos hn hc0 hc1
  have hne := spLO_act_ne (n := n) (by omega) hx (hpos i).1 (hpos j).1 (hpos j).2
  apply hne
  have key : (fun b => 2 * spLO_v2 hn a i b) =
      fun b => 2 * spAct π s (spLO_v2 hn a j) b := by
    calc (fun b => 2 * spLO_v2 hn a i b) = toStd n (spLO_u2 w (spLabelVec a) i) :=
          (spLO_u2_toStd hn hw i).symm
      _ = toStd n (weylAction (isFiniteType_cartanC n) x (spLO_u2 w (spLabelVec a) j)) :=
          congrArg (toStd n) hij
      _ = fun b => 2 * spAct π s (spLO_v2 hn a j) b := by
          rw [hxr (spLO_u2 w (spLabelVec a) j), spLO_u2_toStd hn hw j]
          funext b
          simp only [spAct]
          ring
  funext b
  exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) (congrFun key b)

private theorem spLO_four_witness_move {n : ℕ} {c : Fin n → ℤ}
    {x : (coxeterMatrix (isFiniteType_cartanC n)).Group} {π : Equiv.Perm (Fin n)}
    {s : Fin n → ℤ} (hxr : SpRealizes n x π s)
    {w : Fin 4 → (coxeterMatrix (isFiniteType_cartanC n)).Group}
    {σ : Fin 4 → Equiv.Perm (Fin n)} {t : Fin 4 → Fin n → ℤ}
    (hw : ∀ i, SpRealizes n (w i) (σ i) (t i))
    (hinj : Function.Injective (fun i => spAct (σ i) (t i) c))
    (hmove : ∀ i j, spAct (σ i) (t i) c ≠ spAct π s (spAct (σ j) (t j) c)) :
    Function.Injective (fun i => weylAction (isFiniteType_cartanC n) (w i) (spFromStd2 n c)) ∧
      ∀ i j, weylAction (isFiniteType_cartanC n) (w i) (spFromStd2 n c) ≠
        weylAction (isFiniteType_cartanC n) x
          (weylAction (isFiniteType_cartanC n) (w j) (spFromStd2 n c)) := by
  constructor
  · intro i j hij
    apply hinj
    have key := congrArg (toStd n) hij
    rw [spLO_toStd_weylAction_spFromStd2 (h := hw i),
      spLO_toStd_weylAction_spFromStd2 (h := hw j)] at key
    funext b
    exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) (congrFun key b)
  · intro i j hij
    apply hmove i j
    have hux : toStd n (weylAction (isFiniteType_cartanC n) x
        (weylAction (isFiniteType_cartanC n) (w j) (spFromStd2 n c))) =
        fun b => 2 * spAct π s (spAct (σ j) (t j) c) b := by
      rw [hxr (weylAction (isFiniteType_cartanC n) (w j) (spFromStd2 n c)),
        spLO_toStd_weylAction_spFromStd2 (h := hw j)]
      funext b
      simp only [spAct]
      ring
    have key := congrArg (toStd n) hij
    rw [spLO_toStd_weylAction_spFromStd2 (h := hw i)] at key
    rw [hux] at key
    funext b
    exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) (congrFun key b)

theorem exists_four_orbit_spLabelVec {n : ℕ} (hn : 3 ≤ n) {a : Fin n → ℕ}
    (h1 : ∃ i : Fin n, 1 ≤ i.val ∧ 0 < a i)
    (hcube : n = 3 → a ⟨0, by omega⟩ ≠ 0 ∨ a ⟨1, by omega⟩ ≠ 0)
    {x : (coxeterMatrix (isFiniteType_cartanC n)).Group} {π : Equiv.Perm (Fin n)}
    {s : Fin n → ℤ} (hxr : SpRealizes n x π s)
    (hx : (π ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧ s ⟨0, by omega⟩ = -1) ∨
      (π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧ π ⟨1, by omega⟩ = ⟨0, by omega⟩ ∧
        s ⟨0, by omega⟩ = -1 ∧ s ⟨1, by omega⟩ = -1)) :
    ∃ u : Fin 4 → Fin n → ℤ,
      (∀ i, ∃ w, u i = weylAction (isFiniteType_cartanC n) w (spFromStd2 n (spLabelVec a))) ∧
      Function.Injective u ∧ ∀ i j, u i ≠ weylAction (isFiniteType_cartanC n) x (u j) := by
  obtain ⟨i, hi1, hipos⟩ := h1
  have hanti : Antitone (spLabelVec a) := spLO_spLabelVec_anti a
  have hnonneg : ∀ b, 0 ≤ spLabelVec a b := fun b => spLO_spLabelVec_nonneg a b
  have h1pos : 0 < spLabelVec a ⟨1, by omega⟩ :=
    spLO_spLabelVec_pos (j := ⟨1, by omega⟩) (by rw [Fin.le_def]; exact hi1) hipos
  have hcube' : n = 3 → spLabelVec a ⟨2, by omega⟩ ≠ spLabelVec a ⟨0, by omega⟩ :=
    fun h3 => spLO_spLabelVec_cube h3 (hcube h3)
  obtain ⟨σ, t, ht, hinj, hmove⟩ :=
    exists_four_spWitness_of_antitone hn hanti hnonneg h1pos hcube' hx
  choose w hw using fun i => exists_spRealizes_of_spIsSign (σ i) (ht i)
  obtain ⟨hinj', hmove'⟩ := spLO_four_witness_move (c := spLabelVec a) hxr hw hinj hmove
  refine ⟨fun i => weylAction (isFiniteType_cartanC n) (w i) (spFromStd2 n (spLabelVec a)),
    ?_, hinj', hmove'⟩
  · intro i
    exact ⟨w i, rfl⟩

theorem exists_two_orbit_spLabelVec {n : ℕ} (hn : 3 ≤ n) {a : Fin n → ℕ}
    (h2 : ∃ i : Fin n, 2 ≤ i.val ∧ 0 < a i)
    {x : (coxeterMatrix (isFiniteType_cartanC n)).Group} {π : Equiv.Perm (Fin n)}
    {s : Fin n → ℤ} (hxr : SpRealizes n x π s)
    (hx : (π ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧ s ⟨0, by omega⟩ = -1) ∨
      (π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧ π ⟨1, by omega⟩ = ⟨0, by omega⟩ ∧
        s ⟨0, by omega⟩ = -1 ∧ s ⟨1, by omega⟩ = -1)) :
    ∃ u : Fin 2 → Fin n → ℤ,
      (∀ i, ∃ w, u i = weylAction (isFiniteType_cartanC n) w (spFromStd2 n (spLabelVec a))) ∧
      Function.Injective u ∧ ∀ i j, u i ≠ weylAction (isFiniteType_cartanC n) x (u j) := by
  obtain ⟨i, hi2, hipos⟩ := h2
  have hc2 : 0 < spLabelVec a ⟨2, by omega⟩ :=
    spLO_spLabelVec_pos (j := ⟨2, by omega⟩) (by rw [Fin.le_def]; exact hi2) hipos
  have hanti := spLO_spLabelVec_anti a
  have hc1 : 0 < spLabelVec a ⟨1, by omega⟩ :=
    lt_of_lt_of_le hc2 (hanti (by rw [Fin.le_iff_val_le_val]; norm_num))
  have hc0 : 0 < spLabelVec a ⟨0, by omega⟩ :=
    lt_of_lt_of_le hc1 (hanti (by rw [Fin.le_iff_val_le_val]; norm_num))
  obtain ⟨w1, hw1⟩ := exists_spRealizes_of_spIsSign (1 : Equiv.Perm (Fin n))
    (spIsSign_spSgn (⟨2, by omega⟩ : Fin n))
  refine ⟨spLO_u2 w1 (spLabelVec a), ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ⟨1, by simp [spLO_u2_zero]⟩
    · exact ⟨w1, rfl⟩
  · exact spLO_u2_injective hn hw1 hc2
  · exact spLO_u2_moved hn hw1 hxr hx hc0 hc1

end CFSG.LocalAnalysis.WeakClosure81
