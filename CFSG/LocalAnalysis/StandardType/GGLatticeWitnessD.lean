module

public import CFSG.LocalAnalysis.StandardType.GGDRootOrbit
public import CFSG.LocalAnalysis.StandardType.GGLatticeWitness

public section

namespace CFSG.StandardType

private def lwd_root0 : ℕ → ℤ := fun i => if i = 0 then 1 else 0

private theorem lwd_GGDRoot_root0 {m : ℕ} (hm : 5 ≤ m) : GGDRoot m lwd_root0 := by
  refine ⟨0, 1, by omega, by omega, by omega, 1, -1, Or.inl rfl, Or.inr rfl, ?_⟩
  intro k
  unfold ggDeps lwd_root0
  split_ifs <;> omega

private theorem lwd_getD_range_map (f : ℕ → ℤ) {m i : ℕ} (hi : i < m) :
    ((List.range m).map f).getD i 0 = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

private theorem lwd_dvd_foldl_gcd {p : ℕ} (init : ℕ) (hp : p ∣ init) (l : List ℕ)
    (h : ∀ x ∈ l, p ∣ x) : p ∣ l.foldl Nat.gcd init := by
  induction l generalizing init with
  | nil => simpa using hp
  | cons a t ih =>
    rw [List.foldl_cons]
    exact ih (Nat.gcd init a) (Nat.dvd_gcd hp (h a (by simp)))
      (fun x hx => h x (by simp [hx]))

private theorem lwd_dvd_ggLWminors {p : ℕ} {u v : List ℤ}
    (h : ∀ i j, i < u.length → j < u.length →
      (p : ℤ) ∣ (u.getD i 0 * v.getD j 0 - u.getD j 0 * v.getD i 0)) :
    p ∣ ggLWminors u v := by
  rw [ggLWminors]
  refine lwd_dvd_foldl_gcd 0 (by simp) _ ?_
  intro x hx
  rw [List.mem_flatMap] at hx
  obtain ⟨i, hi, hx⟩ := hx
  rw [List.mem_filterMap] at hx
  obtain ⟨j, hj, hx⟩ := hx
  rw [List.mem_range] at hi hj
  by_cases hij : i < j
  · rw [if_pos hij] at hx
    have hx' : x = (u.getD i 0 * v.getD j 0 - u.getD j 0 * v.getD i 0).natAbs :=
      (Option.some.inj hx).symm
    rw [hx']
    exact (Int.natCast_dvd).mp (h i j hi hj)
  · rw [if_neg hij] at hx
    exact absurd hx (by simp)

private theorem lwd_prime_not_dvd_twelve {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : ¬ p ∣ 12 := by
  intro h
  have hp12 : p ∣ 2 * (2 * 3) := by norm_num; exact h
  rcases hp.dvd_mul.mp hp12 with h2 | h23
  · have : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    omega
  · rcases hp.dvd_mul.mp h23 with h2 | h3
    · have : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
      omega
    · have : p ≤ 3 := Nat.le_of_dvd (by norm_num) h3
      omega

theorem ggD_nonprop {n b₀ : ℕ} (hb₀ : 5 ≤ b₀) (hn : b₀ ≤ n) {w : ℕ → ℤ}
    (hw : ∀ i < n - b₀, w i = 0)
    (hblock : ∀ u ∈ ggDRootList b₀,
      12 % ggLWminors ((List.range b₀).map fun i => w (n - b₀ + i)) u = 0)
    {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {v : ℕ → ℤ} (hv : GGDRoot n v) (t : ZMod p) :
    ¬ ∀ i < n, ((w i : ℤ) : ZMod p) = t * ((v i : ℤ) : ZMod p) := by
  intro hprop
  haveI : Fact p.Prime := ⟨hp⟩
  have hn5 : 5 ≤ n := le_trans hb₀ hn
  have hp12 : p ∣ 12 := by
    by_cases ht : t = 0
    · have hwp : ∀ i < n, (p : ℤ) ∣ w i := by
        intro i hi
        have h := hprop i hi
        rw [ht, zero_mul] at h
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd (w i) p).mp h
      have hmem : (List.range b₀).map lwd_root0 ∈ ggDRootList b₀ :=
        ggDRoot_mem_ggDRootList (by omega) (lwd_GGDRoot_root0 hb₀)
      have hblk := hblock _ hmem
      refine dvd_trans ?_ (Nat.dvd_of_mod_eq_zero hblk)
      apply lwd_dvd_ggLWminors
      intro i j hi hj
      have hi' : i < b₀ := by simpa using hi
      have hj' : j < b₀ := by simpa using hj
      rw [lwd_getD_range_map (f := fun i => w (n - b₀ + i)) hi',
        lwd_getD_range_map (f := fun i => w (n - b₀ + i)) hj']
      exact dvd_sub (dvd_mul_of_dvd_left (hwp (n - b₀ + i) (by omega)) _)
        (dvd_mul_of_dvd_left (hwp (n - b₀ + j) (by omega)) _)
    · have hv0 : ∀ i < n - b₀, v i = 0 := by
        intro i hi
        have h := hprop i (by omega)
        rw [hw i hi] at h
        simp only [Int.cast_zero] at h
        have hz : ((v i : ℤ) : ZMod p) = 0 := by
          have h' : t * ((v i : ℤ) : ZMod p) = 0 := h.symm
          rcases mul_eq_zero.mp h' with h0 | h0
          · exact absurd h0 ht
          · exact h0
        have hdvd : (p : ℤ) ∣ v i := (ZMod.intCast_zmod_eq_zero_iff_dvd (v i) p).mp hz
        have hle : |v i| ≤ (2 : ℤ) := ggDRoot_abs_le hn5 hv (by omega)
        by_contra hne
        have hz2 : (v i).natAbs ≤ 2 := by
          have h1 : v i ≤ 2 := (abs_le.mp hle).2
          have h2 : -2 ≤ v i := (abs_le.mp hle).1
          rcases Int.eq_nat_or_neg (v i) with ⟨k, hk | hk⟩
          · rw [hk]; simp only [Int.natAbs_natCast]; omega
          · rw [hk]; rw [Int.natAbs_neg, Int.natAbs_natCast]; omega
        have hdvd' : p ∣ (v i).natAbs := (Int.natCast_dvd).mp hdvd
        have hpos : 0 < (v i).natAbs := Int.natAbs_pos.mpr hne
        have : p ≤ (v i).natAbs := Nat.le_of_dvd hpos hdvd'
        omega
      have htail := ggDRoot_tail (n := n) (m := n - b₀) (by omega) hv hv0
      have hb_eq : n - (n - b₀) = b₀ := by omega
      rw [hb_eq] at htail
      have hmem : (List.range b₀).map (fun i => v (n - b₀ + i)) ∈ ggDRootList b₀ :=
        ggDRoot_mem_ggDRootList (by omega) htail
      have hblk := hblock _ hmem
      refine dvd_trans ?_ (Nat.dvd_of_mod_eq_zero hblk)
      apply lwd_dvd_ggLWminors
      intro i j hi hj
      have hi' : i < b₀ := by simpa using hi
      have hj' : j < b₀ := by simpa using hj
      rw [lwd_getD_range_map (f := fun i => w (n - b₀ + i)) hi',
        lwd_getD_range_map (f := fun i => w (n - b₀ + i)) hj',
        lwd_getD_range_map (f := fun i => v (n - b₀ + i)) hi',
        lwd_getD_range_map (f := fun i => v (n - b₀ + i)) hj']
      have hz : (((w (n - b₀ + i) * v (n - b₀ + j)
          - w (n - b₀ + j) * v (n - b₀ + i)) : ℤ) : ZMod p) = 0 := by
        have hi2 := hprop (n - b₀ + i) (by omega)
        have hj2 := hprop (n - b₀ + j) (by omega)
        push_cast
        rw [hi2, hj2]
        ring
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz
  exact lwd_prime_not_dvd_twelve hp h5 hp12

@[expose] def lwd_shift {n b₀ : ℕ} (hn : b₀ ≤ n) : Option (Fin b₀) → Option (Fin n)
  | none => none
  | some i => some ⟨n - b₀ + i, by have := i.isLt; omega⟩

private theorem lwd_shift_inj {n b₀ : ℕ} (hn : b₀ ≤ n) :
    Function.Injective (lwd_shift hn) := by
  intro x y h
  rcases x with _ | x <;> rcases y with _ | y
  · rfl
  · simp only [lwd_shift] at h
    exact absurd h (by simp)
  · simp only [lwd_shift] at h
    exact absurd h (by simp)
  · simp only [lwd_shift, Option.some.injEq] at h
    have hv : (n - b₀ + x : ℕ) = n - b₀ + y := congrArg Fin.val h
    have hx : (x : ℕ) = y := by omega
    exact congrArg some (Fin.ext hx)

@[expose] def lwd_single {n b₀ : ℕ} (hn : b₀ ≤ n) (j : Option (Fin b₀)) :
    Option (Fin n) → ℤ :=
  Pi.single (lwd_shift hn j) (1 : ℤ)

@[expose] def lwd_extend {n b₀ : ℕ} (hn : b₀ ≤ n) (m : Option (Fin b₀) → ℤ) :
    Option (Fin n) → ℤ :=
  ∑ j, m j • lwd_single hn j

theorem lwd_extend_shift {n b₀ : ℕ} (hn : b₀ ≤ n) (m : Option (Fin b₀) → ℤ)
    (x : Option (Fin b₀)) : lwd_extend hn m (lwd_shift hn x) = m x := by
  unfold lwd_extend lwd_single
  rw [Finset.sum_apply, Fintype.sum_eq_single x]
  · rw [Pi.smul_apply, smul_eq_mul, Pi.single_apply, if_pos rfl, mul_one]
  · intro j hj
    rw [Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      if_neg (fun h => hj (lwd_shift_inj hn h).symm), mul_zero]

theorem lwd_extend_single {n b₀ : ℕ} (hn : b₀ ≤ n) (x : Option (Fin b₀)) :
    lwd_extend hn (Pi.single x 1) = lwd_single hn x := by
  unfold lwd_extend lwd_single
  rw [Fintype.sum_eq_single x]
  · rw [Pi.single_eq_same, one_smul]
  · intro j hj
    rw [Pi.single_eq_of_ne hj, zero_smul]

private theorem lwd_extend_add {n b₀ : ℕ} (hn : b₀ ≤ n) (m m' : Option (Fin b₀) → ℤ) :
    lwd_extend hn (m + m') = lwd_extend hn m + lwd_extend hn m' := by
  unfold lwd_extend
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [Pi.add_apply, add_smul]

theorem lwd_extend_sub_smul {n b₀ : ℕ} (hn : b₀ ≤ n) (m m' : Option (Fin b₀) → ℤ)
    (r : ℤ) : lwd_extend hn (m - r • m') = lwd_extend hn m - r • lwd_extend hn m' := by
  unfold lwd_extend
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_smul, mul_smul]

theorem lwd_dot_extend {n b₀ : ℕ} (hn : b₀ ≤ n)
    {Xn : Matrix (Option (Fin n)) (Option (Fin n)) ℤ}
    {Xb : Matrix (Option (Fin b₀)) (Option (Fin b₀)) ℤ}
    (hX : ∀ i j, Xn (lwd_shift hn i) (lwd_shift hn j) = Xb i j)
    (m : Option (Fin b₀) → ℤ) (i : Option (Fin b₀)) :
    (∑ y, Xn (lwd_shift hn i) y * lwd_extend hn m y) = ∑ j, Xb i j * m j := by
  have hstep : ∀ y, lwd_extend hn m y = ∑ j, m j * lwd_single hn j y := by
    intro y
    unfold lwd_extend
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [Pi.smul_apply, smul_eq_mul]
  calc ∑ y, Xn (lwd_shift hn i) y * lwd_extend hn m y
      = ∑ y, ∑ j, Xn (lwd_shift hn i) y * (m j * lwd_single hn j y) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [hstep y, Finset.mul_sum]
    _ = ∑ j, ∑ y, Xn (lwd_shift hn i) y * (m j * lwd_single hn j y) :=
          Finset.sum_comm
    _ = ∑ j, m j * Xn (lwd_shift hn i) (lwd_shift hn j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [show (∑ y, Xn (lwd_shift hn i) y * (m j * lwd_single hn j y))
              = m j * ∑ y, Xn (lwd_shift hn i) y * lwd_single hn j y by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro y _
                ring]
          rw [show (∑ y, Xn (lwd_shift hn i) y * lwd_single hn j y)
              = Xn (lwd_shift hn i) (lwd_shift hn j) by
                unfold lwd_single
                rw [Fintype.sum_eq_single (lwd_shift hn j)
                  (fun y hy => by rw [Pi.single_eq_of_ne hy, mul_zero])]
                rw [Pi.single_eq_same, mul_one]]
    _ = ∑ j, Xb i j * m j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hX i j]
          ring

theorem lwd_dot_extendR {n b₀ : ℕ} (hn : b₀ ≤ n)
    {Xn : Matrix (Option (Fin n)) (Option (Fin n)) ℤ}
    {Xb : Matrix (Option (Fin b₀)) (Option (Fin b₀)) ℤ}
    (hX : ∀ i j, Xn (lwd_shift hn i) (lwd_shift hn j) = Xb i j)
    (m : Option (Fin b₀) → ℤ) (i : Option (Fin b₀)) :
    (∑ y, lwd_extend hn m y * Xn y (lwd_shift hn i)) = ∑ j, m j * Xb j i := by
  have hstep : ∀ y, lwd_extend hn m y = ∑ j, m j * lwd_single hn j y := by
    intro y
    unfold lwd_extend
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [Pi.smul_apply, smul_eq_mul]
  calc ∑ y, lwd_extend hn m y * Xn y (lwd_shift hn i)
      = ∑ y, ∑ j, m j * lwd_single hn j y * Xn y (lwd_shift hn i) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [hstep y, Finset.sum_mul]
    _ = ∑ j, ∑ y, m j * lwd_single hn j y * Xn y (lwd_shift hn i) :=
          Finset.sum_comm
    _ = ∑ j, m j * Xn (lwd_shift hn j) (lwd_shift hn i) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [show (∑ y, m j * lwd_single hn j y * Xn y (lwd_shift hn i))
              = m j * ∑ y, lwd_single hn j y * Xn y (lwd_shift hn i) by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro y _
                ring]
          rw [show (∑ y, lwd_single hn j y * Xn y (lwd_shift hn i))
              = Xn (lwd_shift hn j) (lwd_shift hn i) by
                unfold lwd_single
                rw [Fintype.sum_eq_single (lwd_shift hn j)
                  (fun y hy => by rw [Pi.single_eq_of_ne hy, zero_mul])]
                rw [Pi.single_eq_same, one_mul]]
    _ = ∑ j, m j * Xb j i := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hX j i]

private theorem lwd_sRefl_extend {n b₀ : ℕ} (hn : b₀ ≤ n)
    {Xn : Matrix (Option (Fin n)) (Option (Fin n)) ℤ}
    {Xb : Matrix (Option (Fin b₀)) (Option (Fin b₀)) ℤ}
    (hX : ∀ i j, Xn (lwd_shift hn i) (lwd_shift hn j) = Xb i j)
    (j : Option (Fin b₀)) (m : Option (Fin b₀) → ℤ) :
    ggSRefl Xn (lwd_shift hn j) (lwd_extend hn m) = lwd_extend hn (ggSRefl Xb j m) := by
  rw [show ggSRefl Xn (lwd_shift hn j) (lwd_extend hn m)
      = lwd_extend hn m - (∑ y, Xn (lwd_shift hn j) y * lwd_extend hn m y) •
          lwd_single hn j from rfl]
  rw [lwd_dot_extend hn hX m j]
  rw [show ggSRefl Xb j m = m - (∑ i, Xb j i * m i) • Pi.single j (1:ℤ) from rfl]
  rw [lwd_extend_sub_smul, lwd_extend_single]

private theorem lwd_sReflR_extend {n b₀ : ℕ} (hn : b₀ ≤ n)
    {Xn : Matrix (Option (Fin n)) (Option (Fin n)) ℤ}
    {Xb : Matrix (Option (Fin b₀)) (Option (Fin b₀)) ℤ}
    (hX : ∀ i j, Xn (lwd_shift hn i) (lwd_shift hn j) = Xb i j)
    (j : Option (Fin b₀)) (m : Option (Fin b₀) → ℤ) :
    ggSReflR Xn (lwd_shift hn j) (lwd_extend hn m) = lwd_extend hn (ggSReflR Xb j m) := by
  rw [show ggSReflR Xn (lwd_shift hn j) (lwd_extend hn m)
      = lwd_extend hn m - (∑ y, lwd_extend hn m y * Xn y (lwd_shift hn j)) •
          lwd_single hn j from rfl]
  rw [lwd_dot_extendR hn hX m j]
  rw [show ggSReflR Xb j m = m - (∑ i, m i * Xb i j) • Pi.single j (1:ℤ) from rfl]
  rw [lwd_extend_sub_smul, lwd_extend_single]

theorem lwd_sWord_extend {n b₀ : ℕ} (hn : b₀ ≤ n)
    {Xn : Matrix (Option (Fin n)) (Option (Fin n)) ℤ}
    {Xb : Matrix (Option (Fin b₀)) (Option (Fin b₀)) ℤ}
    (hX : ∀ i j, Xn (lwd_shift hn i) (lwd_shift hn j) = Xb i j)
    (ψ : List (Option (Fin b₀))) (m : Option (Fin b₀) → ℤ) :
    ggSWord Xn (ψ.map (lwd_shift hn)) (lwd_extend hn m)
      = lwd_extend hn (ggSWord Xb ψ m) := by
  induction ψ generalizing m with
  | nil => rw [List.map_nil]; rfl
  | cons j ψ ih =>
    rw [List.map_cons, ggSWord, ggSWord, ih, lwd_sRefl_extend hn hX]

theorem lwd_sWordR_extend {n b₀ : ℕ} (hn : b₀ ≤ n)
    {Xn : Matrix (Option (Fin n)) (Option (Fin n)) ℤ}
    {Xb : Matrix (Option (Fin b₀)) (Option (Fin b₀)) ℤ}
    (hX : ∀ i j, Xn (lwd_shift hn i) (lwd_shift hn j) = Xb i j)
    (ψ : List (Option (Fin b₀))) (m : Option (Fin b₀) → ℤ) :
    ggSWordR Xn (ψ.map (lwd_shift hn)) (lwd_extend hn m)
      = lwd_extend hn (ggSWordR Xb ψ m) := by
  induction ψ generalizing m with
  | nil => rw [List.map_nil]; rfl
  | cons j ψ ih =>
    rw [List.map_cons, ggSWordR, ggSWordR, ih, lwd_sReflR_extend hn hX]

private theorem lwd_D_sub {n b₀ : ℕ} (hb : 3 ≤ b₀) (hn : b₀ ≤ n) {i j : Fin b₀} :
    CartanMatrix.D n ⟨n - b₀ + i, by omega⟩ ⟨n - b₀ + j, by omega⟩ =
      CartanMatrix.D b₀ i j := by
  have hi : (i : ℕ) < b₀ := i.isLt
  have hj : (j : ℕ) < b₀ := j.isLt
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem lwd_attach_sub {n b₀ : ℕ} (hb : 4 ≤ b₀) (hn : b₀ ≤ n)
    (kb : Fin b₀) {k : Fin n} (hk : k = ⟨n - b₀ + kb, by omega⟩) (i j : Option (Fin b₀)) :
    ggAttachCartan (CartanMatrix.D n) k (lwd_shift hn i) (lwd_shift hn j) =
      ggAttachCartan (CartanMatrix.D b₀) kb i j := by
  rcases i with _ | i <;> rcases j with _ | j
  · rfl
  · simp only [lwd_shift, ggAttachCartan_none_some]
    rw [hk]
    by_cases h : j = kb
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (by
        intro hh
        exact h (Fin.ext (by
          have h' : n - b₀ + (j : ℕ) = n - b₀ + (kb : ℕ) := congrArg Fin.val hh
          omega)))]
  · simp only [lwd_shift, ggAttachCartan_some_none]
    rw [hk]
    by_cases h : i = kb
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (by
        intro hh
        exact h (Fin.ext (by
          have h' : n - b₀ + (i : ℕ) = n - b₀ + (kb : ℕ) := congrArg Fin.val hh
          omega)))]
  · simp only [lwd_shift, ggAttachCartan_some_some]
    exact lwd_D_sub (by omega) hn

theorem lwd_extend_eq_zero_of_not_mem {n b₀ : ℕ} (hn : b₀ ≤ n)
    (m : Option (Fin b₀) → ℤ) {y : Option (Fin n)}
    (hy : y ∉ Set.range (lwd_shift hn)) : lwd_extend hn m y = 0 := by
  unfold lwd_extend lwd_single
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  rw [Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    if_neg (fun h => hy ⟨j, h.symm⟩), mul_zero]

theorem lwd_not_mem_shift {n b₀ : ℕ} (hn : b₀ ≤ n) {i : ℕ} (hi : i < n - b₀) :
    (some ⟨i, by omega⟩ : Option (Fin n)) ∉ Set.range (lwd_shift hn) := by
  rintro ⟨x, hx⟩
  rcases x with _ | x
  · simp only [lwd_shift] at hx
    exact absurd hx (by simp)
  · simp only [lwd_shift, Option.some.injEq] at hx
    have hix : i = n - b₀ + x := (congrArg Fin.val hx).symm
    have := x.isLt
    omega

private theorem lwd_latticeWitness_of_block {n b₀ : ℕ} (hb : 5 ≤ b₀) (hn : b₀ ≤ n)
    (kb k₀ : Fin b₀) (ψγb : List (Option (Fin b₀))) (gb gRb : Option (Fin b₀) → ℤ)
    (hgb : ggSWord (ggAttachCartan (CartanMatrix.D b₀) kb) ψγb (Pi.single (some k₀) 1) = gb)
    (hgRb : ggSWordR (ggAttachCartan (CartanMatrix.D b₀) kb) ψγb
      (Pi.single (some k₀) 1) = gRb)
    (hgRb_none : gRb none = 1)
    (hP1 : (∑ j, ggAttachCartan (CartanMatrix.D b₀) kb none j * gb j) = -2)
    (hP2 : (∑ j, gRb j * ggAttachCartan (CartanMatrix.D b₀) kb j none) = -2)
    (hblock0 : ∀ u ∈ ggDRootList b₀,
      12 % ggLWminors ((List.range b₀).map fun i =>
        if h : i < b₀ then - gb (some ⟨i, h⟩) else 0) u = 0)
    {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    {k : Fin n} (hk : k = ⟨n - b₀ + kb, by omega⟩) :
    GGLatticeWitness (ggAttachCartan (CartanMatrix.D n) k) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨by omega⟩
  let Xb : Matrix (Option (Fin b₀)) (Option (Fin b₀)) ℤ := ggAttachCartan (CartanMatrix.D b₀) kb
  let Xn : Matrix (Option (Fin n)) (Option (Fin n)) ℤ := ggAttachCartan (CartanMatrix.D n) k
  have hX : ∀ i j : Option (Fin b₀), Xn (lwd_shift hn i) (lwd_shift hn j) = Xb i j := by
    intro i j
    dsimp only [Xn, Xb]
    exact lwd_attach_sub (by omega) hn kb hk i j
  have hdiagn : ∀ j, Xn j j = 2 := by
    intro j
    rcases j with _ | j
    · simp [Xn, ggAttachCartan]
    · simp [Xn, ggAttachCartan, CartanMatrix.D]
  let ψγ : List (Option (Fin n)) := ψγb.map (lwd_shift hn)
  let kγ : Option (Fin n) := lwd_shift hn (some k₀)
  have hgn : ggSWord Xn ψγ (Pi.single kγ 1) = lwd_extend hn gb := by
    dsimp only [ψγ, kγ]
    change ggSWord Xn (List.map (lwd_shift hn) ψγb) (lwd_single hn (some k₀))
      = lwd_extend hn gb
    rw [← lwd_extend_single hn (some k₀), lwd_sWord_extend hn hX]
    dsimp only [Xb]
    rw [hgb]
  have hgRn : ggSWordR Xn ψγ (Pi.single kγ 1) = lwd_extend hn gRb := by
    dsimp only [ψγ, kγ]
    change ggSWordR Xn (List.map (lwd_shift hn) ψγb) (lwd_single hn (some k₀))
      = lwd_extend hn gRb
    rw [← lwd_extend_single hn (some k₀), lwd_sWordR_extend hn hX]
    dsimp only [Xb]
    rw [hgRb]
  have hP1n : (∑ j, ggSWord Xn ψγ (Pi.single kγ 1) j * Xn none j) = -2 := by
    rw [hgn]
    calc ∑ j, lwd_extend hn gb j * Xn none j
        = ∑ j, Xn none j * lwd_extend hn gb j := by
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = ∑ j, Xb none j * gb j := by
          simpa only [lwd_shift] using lwd_dot_extend hn hX gb none
      _ = -2 := by
          dsimp only [Xb]
          exact hP1
  have hP2n : (∑ i, ggSWordR Xn ψγ (Pi.single kγ 1) i * Xn i none) = -2 := by
    rw [hgRn]
    calc ∑ i, lwd_extend hn gRb i * Xn i none
        = ∑ j, gRb j * Xb j none := by
          simpa only [lwd_shift] using lwd_dot_extendR hn hX gRb none
      _ = -2 := by
          dsimp only [Xb]
          exact hP2
  let m : ℕ := ((4 : ZMod p)⁻¹).val
  have hm : ((m : ℤ) : ZMod p) = (4 : ZMod p)⁻¹ := by
    dsimp only [m]
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  let ψ : List (Option (Fin n)) := ggAffineWord ψγ kγ none m
  have hword := ggAffinePair_word Xn hdiagn none kγ ψγ hP1n hP2n m
  refine ⟨ψ, none, ?_, ?_⟩
  · rw [hword.2]
    have hge : lwd_extend hn gRb none = 1 := by
      rw [← show lwd_shift hn none = none from rfl, lwd_extend_shift, hgRb_none]
    have hnone : ((Pi.single none (1 : ℤ) : Option (Fin n) → ℤ) - (2 * (m : ℤ)) •
        ((Pi.single none (1 : ℤ) : Option (Fin n) → ℤ) +
          ggSWordR Xn ψγ (Pi.single kγ 1))) none = 1 - 4 * (m : ℤ) := by
      rw [hgRn]
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, Pi.single_eq_same, hge,
        smul_eq_mul]
      ring
    rw [hnone]
    have h4 : (4 : ZMod p) ≠ 0 := by
      intro h
      have hd : p ∣ 4 := (ZMod.natCast_eq_zero_iff 4 p).mp h
      have : p ≤ 4 := Nat.le_of_dvd (by norm_num) hd
      omega
    push_cast
    rw [show ((m : ZMod p)) = (4 : ZMod p)⁻¹ by exact_mod_cast hm]
    field_simp
    ring
  · intro v hv r heq
    obtain ⟨hv0, hrootd⟩ :=
      ggDRoot_of_mem_ggLCoroots (n := n) (le_trans hb hn) k (show v ∈ ggLCoroots Xn from hv)
    let wbig : Option (Fin n) → ℤ := Pi.single none 1 - lwd_extend hn gb
    let wℕ : ℕ → ℤ := fun i => if h : i < n then wbig (some ⟨i, h⟩) else 0
    have hw : ∀ i < n - b₀, wℕ i = 0 := by
      intro i hi
      dsimp only [wℕ]
      rw [dif_pos (by omega)]
      dsimp only [wbig]
      rw [Pi.sub_apply, Pi.single_eq_of_ne (by simp), zero_sub, neg_eq_zero]
      exact lwd_extend_eq_zero_of_not_mem hn gb (lwd_not_mem_shift hn hi)
    have htail : (List.range b₀).map (fun i => wℕ (n - b₀ + i))
        = (List.range b₀).map (fun i =>
            if h : i < b₀ then - gb (some ⟨i, h⟩) else 0) := by
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      dsimp only [wℕ]
      rw [dif_pos (by omega)]
      dsimp only [wbig]
      rw [Pi.sub_apply, Pi.single_eq_of_ne (by simp), zero_sub]
      rw [show (some ⟨n - b₀ + i, by omega⟩ : Option (Fin n)) =
        lwd_shift hn (some ⟨i, hi⟩) from rfl]
      rw [lwd_extend_shift]
      rw [dif_pos hi]
    have hblock : ∀ u ∈ ggDRootList b₀,
        12 % ggLWminors ((List.range b₀).map fun i => wℕ (n - b₀ + i)) u = 0 := by
      intro u hu
      rw [htail]
      exact hblock0 u hu
    refine ggD_nonprop (b₀ := b₀) hb hn (w := wℕ) hw hblock hp h5 hrootd
      (2 * (r : ZMod p)) ?_
    intro i hi
    dsimp only [wℕ]
    rw [dif_pos hi]
    dsimp only [wbig]
    have h2c : ((2 * ggSWord Xn ψ (Pi.single none 1) (some ⟨i, hi⟩) : ℤ) : ZMod p)
        = (wbig (some ⟨i, hi⟩) : ZMod p) := by
      rw [hword.1, hgn]
      dsimp only [wbig]
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, Pi.single_apply,
        Option.some_ne_none, if_false, smul_eq_mul]
      push_cast
      rw [show ((m : ZMod p)) = (4 : ZMod p)⁻¹ by exact_mod_cast hm]
      have h4 : (4 : ZMod p) ≠ 0 := by
        intro h
        have hd : p ∣ 4 := (ZMod.natCast_eq_zero_iff 4 p).mp h
        have : p ≤ 4 := Nat.le_of_dvd (by norm_num) hd
        omega
      field_simp
      ring_nf
    rw [← h2c]
    have hci := congrFun heq (some ⟨i, hi⟩)
    push_cast
    rw [hci, dif_pos hi]
    ring

@[expose] def lwd_psig5 : List (Option (Fin 5)) :=
  [some ⟨2, by decide⟩, some ⟨4, by decide⟩, some ⟨1, by decide⟩, some ⟨2, by decide⟩, none,
    some ⟨3, by decide⟩, some ⟨2, by decide⟩, some ⟨1, by decide⟩]

@[expose] def lwd_gb5 : Option (Fin 5) → ℤ
  | none => 1
  | some i => ![1, 2, 4, 1, 2] i

theorem lwd_gb5_eq :
    ggSWord (ggAttachCartan (CartanMatrix.D 5) ⟨2, by decide⟩) lwd_psig5
      (Pi.single (some ⟨0, by decide⟩) 1) = lwd_gb5 := by
  funext i
  rcases i with _ | i
  · decide +kernel
  · fin_cases i <;> decide +kernel

theorem lwd_gRb5_eq :
    ggSWordR (ggAttachCartan (CartanMatrix.D 5) ⟨2, by decide⟩) lwd_psig5
      (Pi.single (some ⟨0, by decide⟩) 1) = lwd_gb5 := by
  funext i
  rcases i with _ | i
  · decide +kernel
  · fin_cases i <;> decide +kernel

theorem lwd_gb5_none : lwd_gb5 none = 1 := rfl

theorem lwd_hP1_5 :
    (∑ j, ggAttachCartan (CartanMatrix.D 5) ⟨2, by decide⟩ none j * lwd_gb5 j) = -2 := by
  decide +kernel

theorem lwd_hP2_5 :
    (∑ j, lwd_gb5 j * ggAttachCartan (CartanMatrix.D 5) ⟨2, by decide⟩ j none) = -2 := by
  decide +kernel

private theorem lwd_hblock5_bool : (ggDRootList 5).all (fun u =>
    decide (12 % ggLWminors ((List.range 5).map fun i =>
      if h : i < 5 then - lwd_gb5 (some ⟨i, h⟩) else 0) u = 0)) = true := by
  decide +kernel

private theorem lwd_hblock5 : ∀ u ∈ ggDRootList 5,
    12 % ggLWminors ((List.range 5).map fun i =>
      if h : i < 5 then - lwd_gb5 (some ⟨i, h⟩) else 0) u = 0 := by
  intro u hu
  exact of_decide_eq_true ((List.all_eq_true.mp lwd_hblock5_bool) u hu)

theorem ggLatticeWitness_D_cell {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ}
    {c : Λ} {n : ℕ} (hn : 5 ≤ n) (e : Fin n ≃ Λ)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.D n i j) (hc : c = e ⟨n - 3, by omega⟩)
    {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : GGLatticeWitness (ggAttachCartan C c) p := by
  refine ggLatticeWitness_of_equiv e
    (X := ggAttachCartan (CartanMatrix.D n) ⟨n - 3, by omega⟩)
    (ggAttachCartan_map_equiv e hC hc) ?_
  refine lwd_latticeWitness_of_block (n := n) (b₀ := 5) (hb := by norm_num) (hn := hn)
    (kb := ⟨2, by decide⟩) (k₀ := ⟨0, by decide⟩) (ψγb := lwd_psig5)
    (gb := lwd_gb5) (gRb := lwd_gb5) (hgb := lwd_gb5_eq) (hgRb := lwd_gRb5_eq)
    (hgRb_none := lwd_gb5_none) (hP1 := lwd_hP1_5) (hP2 := lwd_hP2_5)
    (hblock0 := lwd_hblock5) (hp := hp) (h5 := h5) (k := ⟨n - 3, by omega⟩)
    (hk := Fin.ext (by simp only [Fin.val_mk]; omega))

@[expose] def lwd_psig8 : List (Option (Fin 8)) :=
  [some ⟨7, by decide⟩, some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨4, by decide⟩,
    some ⟨5, by decide⟩, some ⟨7, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩,
    some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨2, by decide⟩, some ⟨3, by decide⟩,
    some ⟨4, by decide⟩, some ⟨5, by decide⟩, some ⟨7, by decide⟩, none,
    some ⟨1, by decide⟩, some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩,
    some ⟨5, by decide⟩, some ⟨7, by decide⟩, some ⟨6, by decide⟩, some ⟨5, by decide⟩,
    some ⟨4, by decide⟩, some ⟨3, by decide⟩, some ⟨2, by decide⟩, some ⟨1, by decide⟩]

@[expose] def lwd_gb8 : Option (Fin 8) → ℤ
  | none => 1
  | some i => ![1, 2, 3, 4, 5, 6, 3, 4] i

theorem lwd_gb8_eq :
    ggSWord (ggAttachCartan (CartanMatrix.D 8) ⟨7, by decide⟩) lwd_psig8
      (Pi.single (some ⟨0, by decide⟩) 1) = lwd_gb8 := by
  funext i
  rcases i with _ | i
  · decide +kernel
  · fin_cases i <;> decide +kernel

theorem lwd_gRb8_eq :
    ggSWordR (ggAttachCartan (CartanMatrix.D 8) ⟨7, by decide⟩) lwd_psig8
      (Pi.single (some ⟨0, by decide⟩) 1) = lwd_gb8 := by
  funext i
  rcases i with _ | i
  · decide +kernel
  · fin_cases i <;> decide +kernel

theorem lwd_gb8_none : lwd_gb8 none = 1 := rfl

theorem lwd_hP1_8 :
    (∑ j, ggAttachCartan (CartanMatrix.D 8) ⟨7, by decide⟩ none j * lwd_gb8 j) = -2 := by
  decide +kernel

theorem lwd_hP2_8 :
    (∑ j, lwd_gb8 j * ggAttachCartan (CartanMatrix.D 8) ⟨7, by decide⟩ j none) = -2 := by
  decide +kernel

private theorem lwd_hblock8_bool : (ggDRootList 8).all (fun u =>
    decide (12 % ggLWminors ((List.range 8).map fun i =>
      if h : i < 8 then - lwd_gb8 (some ⟨i, h⟩) else 0) u = 0)) = true := by
  decide +kernel

private theorem lwd_hblock8 : ∀ u ∈ ggDRootList 8,
    12 % ggLWminors ((List.range 8).map fun i =>
      if h : i < 8 then - lwd_gb8 (some ⟨i, h⟩) else 0) u = 0 := by
  intro u hu
  exact of_decide_eq_true ((List.all_eq_true.mp lwd_hblock8_bool) u hu)
@[expose] def lwd_psig8a : List (Option (Fin 8)) :=
  [some ⟨6, by decide⟩, some ⟨5, by decide⟩, some ⟨7, by decide⟩, some ⟨4, by decide⟩,
    some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩,
    some ⟨5, by decide⟩, some ⟨7, by decide⟩, some ⟨2, by decide⟩, some ⟨3, by decide⟩,
    some ⟨4, by decide⟩, some ⟨5, by decide⟩, some ⟨6, by decide⟩, none,
    some ⟨1, by decide⟩, some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩,
    some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩, some ⟨5, by decide⟩,
    some ⟨4, by decide⟩, some ⟨3, by decide⟩, some ⟨2, by decide⟩, some ⟨1, by decide⟩]

@[expose] def lwd_gb8a : Option (Fin 8) → ℤ
  | none => 1
  | some i => ![1, 2, 3, 4, 5, 6, 4, 3] i

theorem lwd_gb8a_eq :
    ggSWord (ggAttachCartan (CartanMatrix.D 8) ⟨6, by decide⟩) lwd_psig8a
      (Pi.single (some ⟨0, by decide⟩) 1) = lwd_gb8a := by
  funext i
  rcases i with _ | i
  · decide +kernel
  · fin_cases i <;> decide +kernel

theorem lwd_gRb8a_eq :
    ggSWordR (ggAttachCartan (CartanMatrix.D 8) ⟨6, by decide⟩) lwd_psig8a
      (Pi.single (some ⟨0, by decide⟩) 1) = lwd_gb8a := by
  funext i
  rcases i with _ | i
  · decide +kernel
  · fin_cases i <;> decide +kernel

theorem lwd_gb8a_none : lwd_gb8a none = 1 := rfl

theorem lwd_hP1_8a :
    (∑ j, ggAttachCartan (CartanMatrix.D 8) ⟨6, by decide⟩ none j * lwd_gb8a j) = -2 := by
  decide +kernel

theorem lwd_hP2_8a :
    (∑ j, lwd_gb8a j * ggAttachCartan (CartanMatrix.D 8) ⟨6, by decide⟩ j none) = -2 := by
  decide +kernel

private theorem lwd_hblock8a_bool : (ggDRootList 8).all (fun u =>
    decide (12 % ggLWminors ((List.range 8).map fun i =>
      if h : i < 8 then - lwd_gb8a (some ⟨i, h⟩) else 0) u = 0)) = true := by
  decide +kernel

private theorem lwd_hblock8a : ∀ u ∈ ggDRootList 8,
    12 % ggLWminors ((List.range 8).map fun i =>
      if h : i < 8 then - lwd_gb8a (some ⟨i, h⟩) else 0) u = 0 := by
  intro u hu
  exact of_decide_eq_true ((List.all_eq_true.mp lwd_hblock8a_bool) u hu)

theorem ggLatticeWitness_D_cell_one {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ}
    {b : Λ} {n : ℕ} (hn : 9 ≤ n) (e : Fin n ≃ Λ)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.D n i j)
    (hb : b = e ⟨n - 2, by omega⟩ ∨ b = e ⟨n - 1, by omega⟩)
    {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : GGLatticeWitness (ggAttachCartan C b) p := by
  rcases hb with hb | hb
  · refine ggLatticeWitness_of_equiv e
      (X := ggAttachCartan (CartanMatrix.D n) ⟨n - 2, by omega⟩)
      (ggAttachCartan_map_equiv e hC hb) ?_
    refine lwd_latticeWitness_of_block (n := n) (b₀ := 8) (hb := by norm_num)
      (hn := by omega) (kb := ⟨6, by decide⟩) (k₀ := ⟨0, by decide⟩) (ψγb := lwd_psig8a)
      (gb := lwd_gb8a) (gRb := lwd_gb8a) (hgb := lwd_gb8a_eq) (hgRb := lwd_gRb8a_eq)
      (hgRb_none := lwd_gb8a_none) (hP1 := lwd_hP1_8a) (hP2 := lwd_hP2_8a)
      (hblock0 := lwd_hblock8a) (hp := hp) (h5 := h5) (k := ⟨n - 2, by omega⟩)
      (hk := Fin.ext (by simp only [Fin.val_mk]; omega))
  · refine ggLatticeWitness_of_equiv e
      (X := ggAttachCartan (CartanMatrix.D n) ⟨n - 1, by omega⟩)
      (ggAttachCartan_map_equiv e hC hb) ?_
    refine lwd_latticeWitness_of_block (n := n) (b₀ := 8) (hb := by norm_num)
      (hn := by omega) (kb := ⟨7, by decide⟩) (k₀ := ⟨0, by decide⟩) (ψγb := lwd_psig8)
      (gb := lwd_gb8) (gRb := lwd_gb8) (hgb := lwd_gb8_eq) (hgRb := lwd_gRb8_eq)
      (hgRb_none := lwd_gb8_none) (hP1 := lwd_hP1_8) (hP2 := lwd_hP2_8)
      (hblock0 := lwd_hblock8) (hp := hp) (h5 := h5) (k := ⟨n - 1, by omega⟩)
      (hk := Fin.ext (by simp only [Fin.val_mk]; omega))

end CFSG.StandardType
