module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpWitness

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Universal.Symplectic
open CFSG.StandardType

@[expose] def spFromStd2 (n : ℕ) (c : Fin n → ℤ) : Fin n → ℤ := fun a =>
  if a.val + 1 = n then ∑ b, c b else 2 * ∑ b ∈ Finset.Iic a, c b

private theorem spFromStd2_apply_of_ne {n : ℕ} {c : Fin n → ℤ} {a : Fin n}
    (h : a.val + 1 ≠ n) : spFromStd2 n c a = 2 * ∑ b ∈ Finset.Iic a, c b := by
  unfold spFromStd2
  rw [if_neg h]

private theorem spFromStd2_apply_of_eq {n : ℕ} {c : Fin n → ℤ} {a : Fin n}
    (h : a.val + 1 = n) : spFromStd2 n c a = ∑ b, c b := by
  unfold spFromStd2
  rw [if_pos h]

private theorem sum_Iic_eq_sum_Iic_pred {n : ℕ} (c : Fin n → ℤ) {a : Fin n}
    (ha : 0 < a.val) :
    ∑ b ∈ Finset.Iic a, c b =
      c a + ∑ b ∈ Finset.Iic (⟨a.val - 1, by omega⟩ : Fin n), c b := by
  have hIio : Finset.Iio a = Finset.Iic (⟨a.val - 1, by omega⟩ : Fin n) := by
    ext x
    simp only [Finset.mem_Iio, Finset.mem_Iic, Fin.lt_def, Fin.le_def]
    omega
  rw [← Finset.Iio_insert a, Finset.sum_insert (by simp), hIio]

private theorem Iic_eq_univ_of_last {n : ℕ} {a : Fin n} (h : a.val + 1 = n) :
    Finset.Iic a = Finset.univ := by
  ext b
  simp only [Finset.mem_Iic, Finset.mem_univ, Fin.le_def]
  constructor
  · intro _; trivial
  · intro _
    have := b.isLt
    omega

private theorem univ_eq_singleton_of_last_val_zero {n : ℕ} {a : Fin n}
    (hlast : a.val + 1 = n) (ha : a.val = 0) :
    (Finset.univ : Finset (Fin n)) = {a} := by
  ext b
  simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
  apply Fin.ext
  have := b.isLt
  omega

private theorem Iic_eq_singleton_of_val_eq_zero {n : ℕ} {a : Fin n} (ha : a.val = 0) :
    Finset.Iic a = {a} := by
  ext b
  simp only [Finset.mem_Iic, Finset.mem_singleton, Fin.le_def]
  constructor
  · intro h
    apply Fin.ext
    omega
  · rintro rfl
    exact le_rfl

theorem toStd_spFromStd2 (n : ℕ) (c : Fin n → ℤ) :
    toStd n (spFromStd2 n c) = fun a => 2 * c a := by
  funext a
  unfold toStd
  by_cases hlast : a.val + 1 = n
  · rw [if_pos hlast, spFromStd2_apply_of_eq hlast]
    by_cases h0 : 0 < a.val
    · have hpred : (⟨a.val - 1, by omega⟩ : Fin n).val + 1 ≠ n := by
        dsimp only
        omega
      rw [dif_pos h0, spFromStd2_apply_of_ne hpred,
        ← Iic_eq_univ_of_last hlast, sum_Iic_eq_sum_Iic_pred c h0]
      ring
    · have ha : a.val = 0 := by omega
      rw [dif_neg h0, univ_eq_singleton_of_last_val_zero hlast ha, Finset.sum_singleton]
      ring
  · rw [if_neg hlast, spFromStd2_apply_of_ne hlast]
    by_cases h0 : 0 < a.val
    · have hpred : (⟨a.val - 1, by omega⟩ : Fin n).val + 1 ≠ n := by
        dsimp only
        omega
      rw [dif_pos h0, spFromStd2_apply_of_ne hpred, sum_Iic_eq_sum_Iic_pred c h0]
      ring
    · have ha : a.val = 0 := by omega
      rw [dif_neg h0, Iic_eq_singleton_of_val_eq_zero ha, Finset.sum_singleton]
      ring

@[expose] def spWeight2 {n : ℕ} (S : Finset (Fin n)) : Fin n → ℤ := spFromStd2 n (spTypeVec S)

private theorem le_swap_succ_iff {n : ℕ} {S : Finset (Fin n)} {k : Fin n}
    (hk : k ∉ S) (hlt : k.val + 1 < n) {j : Fin n} (hj : j ∈ S) :
    k ≤ j ↔ (⟨k.val + 1, hlt⟩ : Fin n) ≤ j := by
  simp only [Fin.le_def]
  constructor
  · intro h
    have hjk : j ≠ k := fun e => hk (e ▸ hj)
    have : j.val ≠ k.val := fun e => hjk (Fin.ext e)
    omega
  · intro h
    omega

private theorem spTypeVec_swap_succ {n : ℕ} {S : Finset (Fin n)} {k : Fin n}
    (hk : k ∉ S) (hlt : k.val + 1 < n) :
    spTypeVec S k = spTypeVec S ⟨k.val + 1, hlt⟩ := by
  have h : S.filter (k ≤ ·) = S.filter ((⟨k.val + 1, hlt⟩ : Fin n) ≤ ·) :=
    Finset.filter_congr fun j hj => le_swap_succ_iff hk hlt hj
  unfold spTypeVec
  rw [h]

private theorem spTypeVec_swap_succ_apply {n : ℕ} {S : Finset (Fin n)} {k : Fin n}
    (hk : k ∉ S) (hlt : k.val + 1 < n) (b : Fin n) :
    spTypeVec S (Equiv.swap k ⟨k.val + 1, hlt⟩ b) = spTypeVec S b := by
  by_cases hb : b = k
  · subst hb
    rw [Equiv.swap_apply_left]
    exact (spTypeVec_swap_succ hk hlt).symm
  · by_cases hb' : b = ⟨k.val + 1, hlt⟩
    · subst hb'
      rw [Equiv.swap_apply_right]
      exact spTypeVec_swap_succ hk hlt
    · rw [Equiv.swap_apply_of_ne_of_ne hb hb']

private theorem spTypeVec_eq_zero_of_last_not_mem {n : ℕ} {S : Finset (Fin n)} {k : Fin n}
    (hk : k ∉ S) (hlast : k.val + 1 = n) : spTypeVec S k = 0 := by
  have h : S.filter (k ≤ ·) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro j hj hkj
    have hjk : j = k := by
      simp only [Fin.le_def] at hkj
      apply Fin.ext
      have := j.isLt
      omega
    exact hk (hjk ▸ hj)
  unfold spTypeVec
  rw [h]
  simp

private theorem toStd_spWeight2 {n : ℕ} (S : Finset (Fin n)) :
    toStd n (spWeight2 S) = fun a => 2 * spTypeVec S a := by
  rw [show spWeight2 S = spFromStd2 n (spTypeVec S) from rfl]
  exact toStd_spFromStd2 n (spTypeVec S)

theorem weylAction_simple_spWeight2 {n : ℕ} (S : Finset (Fin n)) {k : Fin n} (hk : k ∉ S) :
    weylAction (isFiniteType_cartanC n)
      ((coxeterMatrix (isFiniteType_cartanC n)).toCoxeterSystem.simple k) (spWeight2 S) =
      spWeight2 S := by
  by_cases hlt : k.val + 1 < n
  · refine SpRealizes.fix (spRealizes_simple_of_lt hlt) ?_
    intro b
    rw [Equiv.symm_swap, toStd_spWeight2]
    dsimp only
    rw [spTypeVec_swap_succ_apply hk hlt b]
    simp only [Pi.one_apply]
    ring
  · refine SpRealizes.fix (spRealizes_simple_of_not_lt hlt) ?_
    intro b
    have hlast : k.val + 1 = n := by have := k.isLt; omega
    change spSgn k b * toStd n (spWeight2 S) b = toStd n (spWeight2 S) b
    rw [toStd_spWeight2]
    dsimp only
    by_cases hb : b = k
    · subst hb
      rw [spTypeVec_eq_zero_of_last_not_mem hk hlast]
      unfold spSgn
      rw [if_pos rfl]
      ring
    · unfold spSgn
      rw [if_neg hb]
      ring

private theorem exists_spRealizes_spZeroSwap (k : ℕ) (hn : 1 ≤ k + 1) (c : Fin (k + 2)) :
    ∃ u : (coxeterMatrix (isFiniteType_cartanC (k + 2))).Group,
      SpRealizes (k + 2) u (Equiv.swap 0 c) 1 := by
  by_cases hc : c = 0
  · exact ⟨1, spRealizes_one.congr (by rw [hc, Equiv.swap_self]; rfl) rfl⟩
  · have hc1 : 1 ≤ c.val := by
      have := Fin.val_ne_of_ne hc
      simp only [Fin.val_zero] at this
      omega
    obtain ⟨v0, _, _, hvr⟩ := exists_spZeroSwap (n := k + 1) hn c hc1
    exact ⟨_, hvr⟩

private theorem exists_spRealizes_of_spIsSign_succ_pos {k : ℕ}
    (π : Equiv.Perm (Fin (k + 2))) {s : Fin (k + 2) → ℤ} (hs : SpIsSign s) (hs0 : s 0 = 1) :
    ∃ w : (coxeterMatrix (isFiniteType_cartanC (k + 2))).Group, SpRealizes (k + 2) w π s := by
  have hn : 1 ≤ k + 1 := by omega
  let c : Fin (k + 2) := π 0
  let π' : Equiv.Perm (Fin (k + 2)) := Equiv.swap 0 c * π
  have hπ'0 : π' 0 = 0 := by
    dsimp only [π', c]
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  obtain ⟨u, hu⟩ := exists_spRealizes_spZeroSwap k hn c
  obtain ⟨v, _, hv⟩ := exists_spLeviW_of_fix (n := k + 1) hn hs hπ'0 hs0
  refine ⟨u * v, (hu.mul hv).congr ?_ ?_⟩
  · show Equiv.swap 0 c * π' = π
    dsimp only [π']
    rw [Equiv.swap_mul_self_mul]
  · funext b
    simp

private theorem exists_spRealizes_of_spIsSign_succ_neg {k : ℕ}
    (π : Equiv.Perm (Fin (k + 2))) {s : Fin (k + 2) → ℤ} (hs : SpIsSign s) (hs0 : s 0 = -1) :
    ∃ w : (coxeterMatrix (isFiniteType_cartanC (k + 2))).Group, SpRealizes (k + 2) w π s := by
  have hn : 1 ≤ k + 1 := by omega
  let c : Fin (k + 2) := π 0
  let π' : Equiv.Perm (Fin (k + 2)) := Equiv.swap 0 c * π
  have hπ'0 : π' 0 = 0 := by
    dsimp only [π', c]
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  obtain ⟨u, hu⟩ := exists_spRealizes_spZeroSwap k hn c
  let s' : Fin (k + 2) → ℤ := fun b => s b * spSgn 0 (π' b)
  have hs' : SpIsSign s' := hs.mul (spIsSign_spSgn 0) π'
  have hs'0 : s' 0 = 1 := by
    dsimp only [s']
    rw [hπ'0, hs0]
    unfold spSgn
    rw [if_pos rfl]
    norm_num
  obtain ⟨v, _, hv⟩ := exists_spLeviW_of_fix (n := k + 1) hn hs' hπ'0 hs'0
  obtain ⟨z, hz⟩ := exists_spZeroSign (n := k + 1) hn
  have huz : SpRealizes (k + 2) (u * z) (Equiv.swap 0 c) (spSgn 0) :=
    (hu.mul hz).congr (mul_one _) (by funext b; simp)
  refine ⟨(u * z) * v, (huz.mul hv).congr ?_ ?_⟩
  · show Equiv.swap 0 c * π' = π
    dsimp only [π']
    rw [Equiv.swap_mul_self_mul]
  · funext b
    dsimp only [s']
    rw [mul_assoc, (spIsSign_spSgn (0 : Fin (k + 2))).mul_self (π' b), mul_one]

theorem exists_spRealizes_of_spIsSign {m : ℕ} (π : Equiv.Perm (Fin m)) {s : Fin m → ℤ}
    (hs : SpIsSign s) :
    ∃ w : (coxeterMatrix (isFiniteType_cartanC m)).Group, SpRealizes m w π s := by
  rcases m with _ | _ | k
  · refine ⟨1, spRealizes_one.congr (Equiv.ext fun x => Fin.elim0 x) ?_⟩
    funext x
    exact Fin.elim0 x
  · have hπ : π = 1 := by
      apply Equiv.ext
      intro x
      apply Fin.ext
      have hx : x.val < 1 := x.isLt
      have hpx : (π x).val < 1 := (π x).isLt
      simp only [Equiv.Perm.coe_one, id_eq]
      omega
    rcases hs 0 with h | h
    · refine ⟨1, spRealizes_one.congr hπ.symm ?_⟩
      funext x
      have hx : x = 0 := by
        apply Fin.ext
        have := x.isLt
        omega
      subst hx
      change (1 : ℤ) = s 0
      exact h.symm
    · refine ⟨_, (spRealizes_simple_of_not_lt (k := (0 : Fin 1)) (by simp)).congr hπ.symm ?_⟩
      funext x
      have hx : x = 0 := by
        apply Fin.ext
        have := x.isLt
        omega
      subst hx
      unfold spSgn
      rw [if_pos rfl, h]
  · rcases hs 0 with hs0 | hs0
    · exact exists_spRealizes_of_spIsSign_succ_pos π hs hs0
    · exact exists_spRealizes_of_spIsSign_succ_neg π hs hs0

theorem spRealizes_unique {m : ℕ} {w : (coxeterMatrix (isFiniteType_cartanC m)).Group}
    {π π' : Equiv.Perm (Fin m)} {s s' : Fin m → ℤ} (h : SpRealizes m w π s)
    (h' : SpRealizes m w π' s') (hs : SpIsSign s) : π = π' ∧ s = s' := by
  have hπ : π = π' := by
    apply Equiv.ext
    intro b
    have htoStd : ∀ a, toStd m (spFromStd2 m (Pi.single b (1 : ℤ))) a =
        if a = b then 2 else 0 := by
      intro a
      rw [toStd_spFromStd2 m (Pi.single b (1 : ℤ))]
      simp only [Pi.single_apply]
      split_ifs <;> ring
    have hb2 : toStd m (spFromStd2 m (Pi.single b (1 : ℤ))) b = 2 := by
      rw [htoStd b, if_pos rfl]
    have e1 := congrFun (h (spFromStd2 m (Pi.single b (1 : ℤ)))) (π b)
    have e2 := congrFun (h' (spFromStd2 m (Pi.single b (1 : ℤ)))) (π b)
    simp only [Equiv.symm_apply_apply] at e1
    have key : s b * toStd m (spFromStd2 m (Pi.single b (1 : ℤ))) b =
        s' (π'.symm (π b)) * toStd m (spFromStd2 m (Pi.single b (1 : ℤ)))
          (π'.symm (π b)) := e1.symm.trans e2
    by_contra hne
    have hne' : π'.symm (π b) ≠ b := by
      intro hh
      apply hne
      simpa using congrArg π' hh
    have hz : toStd m (spFromStd2 m (Pi.single b (1 : ℤ))) (π'.symm (π b)) = 0 := by
      rw [htoStd, if_neg hne']
    rw [hb2, hz, mul_zero] at key
    rcases hs b with hb | hb <;> rw [hb] at key <;> norm_num at key
  rw [← hπ] at h'
  refine ⟨hπ, ?_⟩
  funext b
  have htoStd : toStd m (spFromStd2 m (Pi.single b (1 : ℤ))) b = 2 := by
    rw [toStd_spFromStd2 m (Pi.single b (1 : ℤ))]
    simp
  have e1 := congrFun (h (spFromStd2 m (Pi.single b (1 : ℤ)))) (π b)
  have e2 := congrFun (h' (spFromStd2 m (Pi.single b (1 : ℤ)))) (π b)
  simp only [Equiv.symm_apply_apply] at e1 e2
  exact mul_right_cancel₀ (by rw [htoStd]; norm_num) (e1.symm.trans e2)

private theorem toStd_weylAction_spWeight2 {n : ℕ} {S : Finset (Fin n)}
    {w : (coxeterMatrix (isFiniteType_cartanC n)).Group} {π : Equiv.Perm (Fin n)}
    {s : Fin n → ℤ} (h : SpRealizes n w π s) :
    toStd n (weylAction (isFiniteType_cartanC n) w (spWeight2 S)) =
      fun b => 2 * spAct π s (spTypeVec S) b := by
  rw [h (spWeight2 S)]
  have hstd : toStd n (spWeight2 S) = fun a => 2 * spTypeVec S a :=
    toStd_spFromStd2 n (spTypeVec S)
  rw [hstd]
  funext b
  simp only [spAct]
  ring

theorem exists_four_orbit_spWeight2 {n : ℕ} (hn : 3 ≤ n) {S : Finset (Fin n)} (hS : S.Nonempty)
    (hS0 : S ≠ {⟨0, by omega⟩}) (hspin : n = 3 → S ≠ {⟨2, by omega⟩})
    {x : (coxeterMatrix (isFiniteType_cartanC n)).Group} {π : Equiv.Perm (Fin n)}
    {s : Fin n → ℤ} (hxr : SpRealizes n x π s)
    (hx : (π ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧ s ⟨0, by omega⟩ = -1) ∨
      (π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧ π ⟨1, by omega⟩ = ⟨0, by omega⟩ ∧
        s ⟨0, by omega⟩ = -1 ∧ s ⟨1, by omega⟩ = -1)) :
    ∃ u : Fin 4 → Fin n → ℤ,
      (∀ i, ∃ w, u i = weylAction (isFiniteType_cartanC n) w (spWeight2 S)) ∧
      Function.Injective u ∧ ∀ i j, u i ≠ weylAction (isFiniteType_cartanC n) x (u j) := by
  obtain ⟨σ, t, ht, hinj, hmove⟩ := exists_four_spWitness hn hS hS0 hspin hx
  choose w hw using fun i => exists_spRealizes_of_spIsSign (σ i) (ht i)
  refine ⟨fun i => weylAction (isFiniteType_cartanC n) (w i) (spWeight2 S), ?_, ?_, ?_⟩
  · intro i
    exact ⟨w i, rfl⟩
  · intro i j hij
    apply hinj
    have key := congrArg (toStd n) hij
    rw [toStd_weylAction_spWeight2 (S := S) (h := hw i),
      toStd_weylAction_spWeight2 (S := S) (h := hw j)] at key
    funext b
    exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) (congrFun key b)
  · intro i j hij
    apply hmove i j
    have hux : toStd n (weylAction (isFiniteType_cartanC n) x
        (weylAction (isFiniteType_cartanC n) (w j) (spWeight2 S))) =
        fun b => 2 * spAct π s (spAct (σ j) (t j) (spTypeVec S)) b := by
      rw [hxr (weylAction (isFiniteType_cartanC n) (w j) (spWeight2 S)),
        toStd_weylAction_spWeight2 (S := S) (h := hw j)]
      funext b
      simp only [spAct]
      ring
    have key := congrArg (toStd n) hij
    rw [toStd_weylAction_spWeight2 (S := S) (h := hw i)] at key
    rw [hux] at key
    funext b
    exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) (congrFun key b)

end CFSG.LocalAnalysis.WeakClosure81
