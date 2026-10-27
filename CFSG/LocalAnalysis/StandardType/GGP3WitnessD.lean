module

public import CFSG.LocalAnalysis.StandardType.GGP3Witness
public import CFSG.LocalAnalysis.StandardType.GGDRootOrbit

public section

namespace CFSG.StandardType

private theorem p3d_getD_range_map (f : ℕ → ℤ) {m i : ℕ} (hi : i < m) :
    ((List.range m).map f).getD i 0 = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

private theorem p3d_eq_zero_of_zmod3 {z : ℤ} (hz : ((z : ℤ) : ZMod 3) = 0)
    (hle : |z| ≤ 2) : z = 0 := by
  have hdvd : (3 : ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z 3).mp hz
  by_contra hne
  have hdvd' : 3 ∣ z.natAbs := (Int.natCast_dvd).mp hdvd
  have hpos : 0 < z.natAbs := Int.natAbs_pos.mpr hne
  have hle2 : z.natAbs ≤ 2 := by
    have h1 : z ≤ 2 := (abs_le.mp hle).2
    have h2 : -2 ≤ z := (abs_le.mp hle).1
    rcases Int.eq_nat_or_neg z with ⟨k, hk | hk⟩
    · rw [hk]; simp only [Int.natAbs_natCast]; omega
    · rw [hk]; rw [Int.natAbs_neg, Int.natAbs_natCast]; omega
  have h3 : 3 ≤ z.natAbs := Nat.le_of_dvd hpos hdvd'
  omega

private def p3d_shift {n b₀ : ℕ} (hn : b₀ ≤ n) : Option (Fin b₀) → Option (Fin n)
  | none => none
  | some i => some ⟨n - b₀ + i, by have := i.isLt; omega⟩

private theorem p3d_shift_inj {n b₀ : ℕ} (hn : b₀ ≤ n) :
    Function.Injective (p3d_shift hn) := by
  intro x y h
  rcases x with _ | x <;> rcases y with _ | y
  · rfl
  · simp only [p3d_shift] at h
    exact absurd h (by simp)
  · simp only [p3d_shift] at h
    exact absurd h (by simp)
  · simp only [p3d_shift, Option.some.injEq] at h
    have hv : (n - b₀ + x : ℕ) = n - b₀ + y := congrArg Fin.val h
    have hx : (x : ℕ) = y := by omega
    exact congrArg some (Fin.ext hx)

private def p3d_single {n b₀ : ℕ} (hn : b₀ ≤ n) (j : Option (Fin b₀)) :
    Option (Fin n) → ℤ :=
  Pi.single (p3d_shift hn j) (1 : ℤ)

private def p3d_extend {n b₀ : ℕ} (hn : b₀ ≤ n) (m : Option (Fin b₀) → ℤ) :
    Option (Fin n) → ℤ :=
  ∑ j, m j • p3d_single hn j

private theorem p3d_extend_shift {n b₀ : ℕ} (hn : b₀ ≤ n) (m : Option (Fin b₀) → ℤ)
    (x : Option (Fin b₀)) : p3d_extend hn m (p3d_shift hn x) = m x := by
  unfold p3d_extend p3d_single
  rw [Finset.sum_apply, Fintype.sum_eq_single x]
  · rw [Pi.smul_apply, smul_eq_mul, Pi.single_apply, if_pos rfl, mul_one]
  · intro j hj
    rw [Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      if_neg (fun h => hj (p3d_shift_inj hn h).symm), mul_zero]

private theorem p3d_extend_single {n b₀ : ℕ} (hn : b₀ ≤ n) (x : Option (Fin b₀)) :
    p3d_extend hn (Pi.single x 1) = p3d_single hn x := by
  unfold p3d_extend p3d_single
  rw [Fintype.sum_eq_single x]
  · rw [Pi.single_eq_same, one_smul]
  · intro j hj
    rw [Pi.single_eq_of_ne hj, zero_smul]

private theorem p3d_extend_sub_smul {n b₀ : ℕ} (hn : b₀ ≤ n) (m m' : Option (Fin b₀) → ℤ)
    (r : ℤ) : p3d_extend hn (m - r • m') = p3d_extend hn m - r • p3d_extend hn m' := by
  unfold p3d_extend
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_smul, mul_smul]

private theorem p3d_dot_extend {n b₀ : ℕ} (hn : b₀ ≤ n)
    {Xn : Matrix (Option (Fin n)) (Option (Fin n)) ℤ}
    {Xb : Matrix (Option (Fin b₀)) (Option (Fin b₀)) ℤ}
    (hX : ∀ i j, Xn (p3d_shift hn i) (p3d_shift hn j) = Xb i j)
    (m : Option (Fin b₀) → ℤ) (i : Option (Fin b₀)) :
    (∑ y, Xn (p3d_shift hn i) y * p3d_extend hn m y) = ∑ j, Xb i j * m j := by
  have hstep : ∀ y, p3d_extend hn m y = ∑ j, m j * p3d_single hn j y := by
    intro y
    unfold p3d_extend
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [Pi.smul_apply, smul_eq_mul]
  calc ∑ y, Xn (p3d_shift hn i) y * p3d_extend hn m y
      = ∑ y, ∑ j, Xn (p3d_shift hn i) y * (m j * p3d_single hn j y) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [hstep y, Finset.mul_sum]
    _ = ∑ j, ∑ y, Xn (p3d_shift hn i) y * (m j * p3d_single hn j y) :=
          Finset.sum_comm
    _ = ∑ j, m j * Xn (p3d_shift hn i) (p3d_shift hn j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [show (∑ y, Xn (p3d_shift hn i) y * (m j * p3d_single hn j y))
              = m j * ∑ y, Xn (p3d_shift hn i) y * p3d_single hn j y by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro y _
                ring]
          rw [show (∑ y, Xn (p3d_shift hn i) y * p3d_single hn j y)
              = Xn (p3d_shift hn i) (p3d_shift hn j) by
                unfold p3d_single
                rw [Fintype.sum_eq_single (p3d_shift hn j)
                  (fun y hy => by rw [Pi.single_eq_of_ne hy, mul_zero])]
                rw [Pi.single_eq_same, mul_one]]
    _ = ∑ j, Xb i j * m j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hX i j]
          ring

private theorem p3d_dot_extendR {n b₀ : ℕ} (hn : b₀ ≤ n)
    {Xn : Matrix (Option (Fin n)) (Option (Fin n)) ℤ}
    {Xb : Matrix (Option (Fin b₀)) (Option (Fin b₀)) ℤ}
    (hX : ∀ i j, Xn (p3d_shift hn i) (p3d_shift hn j) = Xb i j)
    (m : Option (Fin b₀) → ℤ) (i : Option (Fin b₀)) :
    (∑ y, p3d_extend hn m y * Xn y (p3d_shift hn i)) = ∑ j, m j * Xb j i := by
  have hstep : ∀ y, p3d_extend hn m y = ∑ j, m j * p3d_single hn j y := by
    intro y
    unfold p3d_extend
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [Pi.smul_apply, smul_eq_mul]
  calc ∑ y, p3d_extend hn m y * Xn y (p3d_shift hn i)
      = ∑ y, ∑ j, m j * p3d_single hn j y * Xn y (p3d_shift hn i) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [hstep y, Finset.sum_mul]
    _ = ∑ j, ∑ y, m j * p3d_single hn j y * Xn y (p3d_shift hn i) :=
          Finset.sum_comm
    _ = ∑ j, m j * Xn (p3d_shift hn j) (p3d_shift hn i) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [show (∑ y, m j * p3d_single hn j y * Xn y (p3d_shift hn i))
              = m j * ∑ y, p3d_single hn j y * Xn y (p3d_shift hn i) by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro y _
                ring]
          rw [show (∑ y, p3d_single hn j y * Xn y (p3d_shift hn i))
              = Xn (p3d_shift hn j) (p3d_shift hn i) by
                unfold p3d_single
                rw [Fintype.sum_eq_single (p3d_shift hn j)
                  (fun y hy => by rw [Pi.single_eq_of_ne hy, zero_mul])]
                rw [Pi.single_eq_same, one_mul]]
    _ = ∑ j, m j * Xb j i := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hX j i]

private theorem p3d_sRefl_extend {n b₀ : ℕ} (hn : b₀ ≤ n)
    {Xn : Matrix (Option (Fin n)) (Option (Fin n)) ℤ}
    {Xb : Matrix (Option (Fin b₀)) (Option (Fin b₀)) ℤ}
    (hX : ∀ i j, Xn (p3d_shift hn i) (p3d_shift hn j) = Xb i j)
    (j : Option (Fin b₀)) (m : Option (Fin b₀) → ℤ) :
    ggSRefl Xn (p3d_shift hn j) (p3d_extend hn m) = p3d_extend hn (ggSRefl Xb j m) := by
  rw [show ggSRefl Xn (p3d_shift hn j) (p3d_extend hn m)
      = p3d_extend hn m - (∑ y, Xn (p3d_shift hn j) y * p3d_extend hn m y) •
          p3d_single hn j from rfl]
  rw [p3d_dot_extend hn hX m j]
  rw [show ggSRefl Xb j m = m - (∑ i, Xb j i * m i) • Pi.single j (1:ℤ) from rfl]
  rw [p3d_extend_sub_smul, p3d_extend_single]

private theorem p3d_sReflR_extend {n b₀ : ℕ} (hn : b₀ ≤ n)
    {Xn : Matrix (Option (Fin n)) (Option (Fin n)) ℤ}
    {Xb : Matrix (Option (Fin b₀)) (Option (Fin b₀)) ℤ}
    (hX : ∀ i j, Xn (p3d_shift hn i) (p3d_shift hn j) = Xb i j)
    (j : Option (Fin b₀)) (m : Option (Fin b₀) → ℤ) :
    ggSReflR Xn (p3d_shift hn j) (p3d_extend hn m) = p3d_extend hn (ggSReflR Xb j m) := by
  rw [show ggSReflR Xn (p3d_shift hn j) (p3d_extend hn m)
      = p3d_extend hn m - (∑ y, p3d_extend hn m y * Xn y (p3d_shift hn j)) •
          p3d_single hn j from rfl]
  rw [p3d_dot_extendR hn hX m j]
  rw [show ggSReflR Xb j m = m - (∑ i, m i * Xb i j) • Pi.single j (1:ℤ) from rfl]
  rw [p3d_extend_sub_smul, p3d_extend_single]

private theorem p3d_sWord_extend {n b₀ : ℕ} (hn : b₀ ≤ n)
    {Xn : Matrix (Option (Fin n)) (Option (Fin n)) ℤ}
    {Xb : Matrix (Option (Fin b₀)) (Option (Fin b₀)) ℤ}
    (hX : ∀ i j, Xn (p3d_shift hn i) (p3d_shift hn j) = Xb i j)
    (ψ : List (Option (Fin b₀))) (m : Option (Fin b₀) → ℤ) :
    ggSWord Xn (ψ.map (p3d_shift hn)) (p3d_extend hn m)
      = p3d_extend hn (ggSWord Xb ψ m) := by
  induction ψ generalizing m with
  | nil => rw [List.map_nil]; rfl
  | cons j ψ ih =>
    rw [List.map_cons, ggSWord, ggSWord, ih, p3d_sRefl_extend hn hX]

private theorem p3d_sWordR_extend {n b₀ : ℕ} (hn : b₀ ≤ n)
    {Xn : Matrix (Option (Fin n)) (Option (Fin n)) ℤ}
    {Xb : Matrix (Option (Fin b₀)) (Option (Fin b₀)) ℤ}
    (hX : ∀ i j, Xn (p3d_shift hn i) (p3d_shift hn j) = Xb i j)
    (ψ : List (Option (Fin b₀))) (m : Option (Fin b₀) → ℤ) :
    ggSWordR Xn (ψ.map (p3d_shift hn)) (p3d_extend hn m)
      = p3d_extend hn (ggSWordR Xb ψ m) := by
  induction ψ generalizing m with
  | nil => rw [List.map_nil]; rfl
  | cons j ψ ih =>
    rw [List.map_cons, ggSWordR, ggSWordR, ih, p3d_sReflR_extend hn hX]

private theorem p3d_D_sub {n b₀ : ℕ} (hb : 3 ≤ b₀) (hn : b₀ ≤ n) {i j : Fin b₀} :
    CartanMatrix.D n ⟨n - b₀ + i, by omega⟩ ⟨n - b₀ + j, by omega⟩ =
      CartanMatrix.D b₀ i j := by
  have hi : (i : ℕ) < b₀ := i.isLt
  have hj : (j : ℕ) < b₀ := j.isLt
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

private theorem p3d_attach_sub {n b₀ : ℕ} (hb : 4 ≤ b₀) (hn : b₀ ≤ n)
    (kb : Fin b₀) {k : Fin n} (hk : k = ⟨n - b₀ + kb, by omega⟩) (i j : Option (Fin b₀)) :
    ggAttachCartan (CartanMatrix.D n) k (p3d_shift hn i) (p3d_shift hn j) =
      ggAttachCartan (CartanMatrix.D b₀) kb i j := by
  rcases i with _ | i <;> rcases j with _ | j
  · rfl
  · simp only [p3d_shift, ggAttachCartan_none_some]
    rw [hk]
    by_cases h : j = kb
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (by
        intro hh
        exact h (Fin.ext (by
          have h' : n - b₀ + (j : ℕ) = n - b₀ + (kb : ℕ) := congrArg Fin.val hh
          omega)))]
  · simp only [p3d_shift, ggAttachCartan_some_none]
    rw [hk]
    by_cases h : i = kb
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (by
        intro hh
        exact h (Fin.ext (by
          have h' : n - b₀ + (i : ℕ) = n - b₀ + (kb : ℕ) := congrArg Fin.val hh
          omega)))]
  · simp only [p3d_shift, ggAttachCartan_some_some]
    exact p3d_D_sub (by omega) hn

private theorem p3d_extend_eq_zero_of_not_mem {n b₀ : ℕ} (hn : b₀ ≤ n)
    (m : Option (Fin b₀) → ℤ) {y : Option (Fin n)}
    (hy : y ∉ Set.range (p3d_shift hn)) : p3d_extend hn m y = 0 := by
  unfold p3d_extend p3d_single
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  rw [Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    if_neg (fun h => hy ⟨j, h.symm⟩), mul_zero]

private theorem p3d_not_mem_shift {n b₀ : ℕ} (hn : b₀ ≤ n) {i : ℕ} (hi : i < n - b₀) :
    (some ⟨i, by omega⟩ : Option (Fin n)) ∉ Set.range (p3d_shift hn) := by
  rintro ⟨x, hx⟩
  rcases x with _ | x
  · simp only [p3d_shift] at hx
    exact absurd hx (by simp)
  · simp only [p3d_shift, Option.some.injEq] at hx
    have hix : i = n - b₀ + x := (congrArg Fin.val hx).symm
    have := x.isLt
    omega


private theorem p3d_invTest3_of_block {n b₀ : ℕ} (hb : 5 ≤ b₀) (hn : b₀ ≤ n)
    (kb : Fin b₀) {k : Fin n} (hk : k = ⟨n - b₀ + kb, by omega⟩)
    (ψb : List (Option (Fin b₀))) (wb cb : Option (Fin b₀) → ℤ) (i₀ : Fin b₀)
    (hwb : ggSWord (ggAttachCartan (CartanMatrix.D b₀) kb) ψb (Pi.single none 1) = wb)
    (hcb : ggSWordR (ggAttachCartan (CartanMatrix.D b₀) kb) ψb (Pi.single none 1) = cb)
    (hc0 : ((cb none : ℤ) : ZMod 3) = 0)
    (hblock : ∀ u ∈ ggDRootList b₀,
      ¬ (∀ i : Fin b₀,
        ((((Pi.single (some i₀) (1 : ℤ) : Option (Fin b₀) → ℤ)
            - (∑ j, cb j * ggAttachCartan (CartanMatrix.D b₀) kb j (some i₀)) • wb) (some i)
           - u.getD i 0 : ℤ) : ZMod 3) = 0)) :
    GGInvTest3 (ggAttachCartan (CartanMatrix.D n) k) := by
  let Xb : Matrix (Option (Fin b₀)) (Option (Fin b₀)) ℤ := ggAttachCartan (CartanMatrix.D b₀) kb
  let Xn : Matrix (Option (Fin n)) (Option (Fin n)) ℤ := ggAttachCartan (CartanMatrix.D n) k
  have hX : ∀ i j : Option (Fin b₀), Xn (p3d_shift hn i) (p3d_shift hn j) = Xb i j := by
    intro i j
    dsimp only [Xn, Xb]
    exact p3d_attach_sub (by omega) hn kb hk i j
  let ψ : List (Option (Fin n)) := ψb.map (p3d_shift hn)
  let ρ : Option (Fin n) → ℤ := p3d_single hn (some i₀)
  have hwn : ggSWord Xn ψ (Pi.single none 1) = p3d_extend hn wb := by
    dsimp only [ψ]
    change ggSWord Xn (List.map (p3d_shift hn) ψb) (p3d_single hn none) = p3d_extend hn wb
    rw [← p3d_extend_single hn none, p3d_sWord_extend hn hX]
    dsimp only [Xb]
    rw [hwb]
  have hcn : ggSWordR Xn ψ (Pi.single none 1) = p3d_extend hn cb := by
    dsimp only [ψ]
    change ggSWordR Xn (List.map (p3d_shift hn) ψb) (p3d_single hn none) = p3d_extend hn cb
    rw [← p3d_extend_single hn none, p3d_sWordR_extend hn hX]
    dsimp only [Xb]
    rw [hcb]
  have hE : (∑ i', ggSWordR Xn ψ (Pi.single none 1) i' * ∑ j, Xn i' j * ρ j : ℤ)
      = ∑ j, cb j * ggAttachCartan (CartanMatrix.D b₀) kb j (some i₀) := by
    rw [hcn]
    have hρ : ∀ i', (∑ j, Xn i' j * ρ j) = Xn i' (p3d_shift hn (some i₀)) := by
      intro i'
      dsimp only [ρ, p3d_single]
      rw [Fintype.sum_eq_single (p3d_shift hn (some i₀))]
      · rw [Pi.single_eq_same, mul_one]
      · intro j hj
        rw [Pi.single_eq_of_ne hj, mul_zero]
    simp only [hρ]
    exact p3d_dot_extendR hn hX cb (some i₀)
  refine ⟨ψ, none, ρ, ?_, ?_, ?_⟩
  · refine ⟨[], ⟨n - b₀ + i₀, by omega⟩, ?_⟩
    show ρ = (Pi.single (some ⟨n - b₀ + i₀, by omega⟩) (1 : ℤ) : Option (Fin n) → ℤ)
    dsimp only [ρ, p3d_single, p3d_shift]
  · rw [hcn]
    rw [← show p3d_shift hn none = none from rfl, p3d_extend_shift]
    exact hc0
  · intro v hv hcon
    obtain ⟨_, hroot⟩ := ggDRoot_of_mem_ggLCoroots (le_trans hb hn) k hv
    let vl : ℕ → ℤ := fun i => if h : i < n then v (some ⟨i, h⟩) else 0
    have hroot' : GGDRoot n vl := hroot
    have hvl : ∀ i (h : i < n), vl i = v (some ⟨i, h⟩) := by
      intro i h
      dsimp only [vl]
      rw [dif_pos h]
    have hzero : ∀ i < n - b₀, vl i = 0 := by
      intro i hi
      have hcon_i := congrFun hcon (some ⟨i, by omega⟩)
      have hρ0 : ρ (some ⟨i, by omega⟩) = 0 := by
        dsimp only [ρ]
        rw [← p3d_extend_single hn (some i₀)]
        exact p3d_extend_eq_zero_of_not_mem hn _ (p3d_not_mem_shift hn hi)
      have hw0 : ggSWord (ggAttachCartan (CartanMatrix.D n) k) ψ (Pi.single none 1)
          (some ⟨i, by omega⟩) = 0 := by
        change ggSWord Xn ψ (Pi.single none 1) (some ⟨i, by omega⟩) = 0
        rw [hwn]
        exact p3d_extend_eq_zero_of_not_mem hn wb (p3d_not_mem_shift hn hi)
      simp only [hρ0, hw0, Int.cast_zero, mul_zero] at hcon_i
      have hvi : ((v (some ⟨i, by omega⟩) : ℤ) : ZMod 3) = 0 := hcon_i.symm
      have hle : |v (some ⟨i, by omega⟩)| ≤ 2 := by
        have h := ggDRoot_abs_le (le_trans hb hn) hroot' (i := i) (by omega)
        rwa [hvl i (by omega)] at h
      have hz := p3d_eq_zero_of_zmod3 hvi hle
      rwa [hvl i (by omega)]
    have htail : GGDRoot b₀ (fun i => vl (n - b₀ + i)) := by
      have h := ggDRoot_tail (n := n) (m := n - b₀) (by omega) hroot' hzero
      rwa [show n - (n - b₀) = b₀ by omega] at h
    have hmem : (List.range b₀).map (fun i => vl (n - b₀ + i)) ∈ ggDRootList b₀ :=
      ggDRoot_mem_ggDRootList (by omega) htail
    refine hblock _ hmem ?_
    intro i
    have hcon_i := congrFun hcon (p3d_shift hn (some i))
    have hρi : ρ (p3d_shift hn (some i))
        = ((Pi.single (some i₀) (1 : ℤ) : Option (Fin b₀) → ℤ) (some i)) := by
      dsimp only [ρ]
      rw [← p3d_extend_single hn (some i₀), p3d_extend_shift]
    have hwi : ggSWord Xn ψ (Pi.single none 1) (p3d_shift hn (some i)) = wb (some i) := by
      rw [hwn, p3d_extend_shift]
    have hvi : v (p3d_shift hn (some i))
        = ((List.range b₀).map fun k => vl (n - b₀ + k)).getD i 0 := by
      rw [p3d_getD_range_map (f := fun k => vl (n - b₀ + k)) i.isLt]
      simpa only [p3d_shift] using (hvl (n - b₀ + i) (by omega)).symm
    rw [hρi, hwi, hvi, hE] at hcon_i
    have hgoal : ((((Pi.single (some i₀) (1 : ℤ) : Option (Fin b₀) → ℤ)
            - (∑ j, cb j * ggAttachCartan (CartanMatrix.D b₀) kb j (some i₀)) • wb) (some i)
          - ((List.range b₀).map fun k => vl (n - b₀ + k)).getD i 0 : ℤ) : ZMod 3)
        = (((Pi.single (some i₀) (1 : ℤ) : Option (Fin b₀) → ℤ) (some i) : ℤ) : ZMod 3)
          - (((∑ j, cb j * ggAttachCartan (CartanMatrix.D b₀) kb j (some i₀) : ℤ)) : ZMod 3)
            * ((wb (some i) : ℤ) : ZMod 3)
          - ((((List.range b₀).map fun k => vl (n - b₀ + k)).getD i 0 : ℤ) : ZMod 3) := by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [hgoal]
    rw [← hcon_i]
    ring

private def p3d_psig5 : List (Option (Fin 5)) :=
  [some ⟨2, by decide⟩, some ⟨4, by decide⟩, some ⟨1, by decide⟩, some ⟨2, by decide⟩,
   none, some ⟨3, by decide⟩, some ⟨2, by decide⟩, some ⟨1, by decide⟩,
   some ⟨0, by decide⟩, some ⟨1, by decide⟩, some ⟨2, by decide⟩, some ⟨3, by decide⟩,
   none, some ⟨2, by decide⟩, some ⟨1, by decide⟩, some ⟨4, by decide⟩, some ⟨2, by decide⟩,
   none]

private def p3d_gb5 : Option (Fin 5) → ℤ
  | none => -3
  | some i => ![-2, -4, -8, -2, -4] i

private theorem p3d_gb5_eq :
    ggSWord (ggAttachCartan (CartanMatrix.D 5) ⟨2, by decide⟩) p3d_psig5
      (Pi.single none 1) = p3d_gb5 := by
  funext i
  rcases i with _ | i
  · decide +kernel
  · fin_cases i <;> decide +kernel

private theorem p3d_gRb5_eq :
    ggSWordR (ggAttachCartan (CartanMatrix.D 5) ⟨2, by decide⟩) p3d_psig5
      (Pi.single none 1) = p3d_gb5 := by
  funext i
  rcases i with _ | i
  · decide +kernel
  · fin_cases i <;> decide +kernel

private theorem p3d_gb5_none : ((p3d_gb5 none : ℤ) : ZMod 3) = 0 := by
  decide +kernel

private theorem p3d_hblock5_bool : (ggDRootList 5).all (fun u =>
    decide (¬ (∀ i : Fin 5,
      ((((Pi.single (some ⟨1, by decide⟩) (1 : ℤ) : Option (Fin 5) → ℤ)
          - (∑ j, p3d_gb5 j
              * ggAttachCartan (CartanMatrix.D 5) ⟨2, by decide⟩ j (some ⟨1, by decide⟩))
            • p3d_gb5) (some i)
         - u.getD i 0 : ℤ) : ZMod 3) = 0))) = true := by
  decide +kernel

private theorem p3d_hblock5 : ∀ u ∈ ggDRootList 5,
    ¬ (∀ i : Fin 5,
      ((((Pi.single (some ⟨1, by decide⟩) (1 : ℤ) : Option (Fin 5) → ℤ)
          - (∑ j, p3d_gb5 j
              * ggAttachCartan (CartanMatrix.D 5) ⟨2, by decide⟩ j (some ⟨1, by decide⟩))
            • p3d_gb5) (some i)
         - u.getD i 0 : ℤ) : ZMod 3) = 0) := by
  intro u hu
  exact of_decide_eq_true ((List.all_eq_true.mp p3d_hblock5_bool) u hu)

private def p3d_psig9 : List (Option (Fin 9)) :=
  [some ⟨8, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩, some ⟨5, by decide⟩,
   some ⟨6, by decide⟩, some ⟨8, by decide⟩, some ⟨4, by decide⟩, some ⟨5, by decide⟩,
   some ⟨6, by decide⟩, some ⟨7, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩,
   some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨8, by decide⟩, none, some ⟨2, by decide⟩,
   some ⟨3, by decide⟩, some ⟨4, by decide⟩, some ⟨5, by decide⟩, some ⟨6, by decide⟩,
   some ⟨8, by decide⟩, some ⟨7, by decide⟩, some ⟨6, by decide⟩, some ⟨5, by decide⟩,
   some ⟨4, by decide⟩, some ⟨3, by decide⟩, some ⟨2, by decide⟩, some ⟨1, by decide⟩,
   some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩, some ⟨5, by decide⟩,
   some ⟨6, by decide⟩, some ⟨7, by decide⟩, some ⟨8, by decide⟩, some ⟨6, by decide⟩,
   some ⟨5, by decide⟩, some ⟨4, by decide⟩, some ⟨3, by decide⟩, some ⟨2, by decide⟩, none,
   some ⟨8, by decide⟩, some ⟨6, by decide⟩, some ⟨5, by decide⟩, some ⟨4, by decide⟩,
   some ⟨3, by decide⟩, some ⟨7, by decide⟩, some ⟨6, by decide⟩, some ⟨5, by decide⟩,
   some ⟨4, by decide⟩, some ⟨8, by decide⟩, some ⟨6, by decide⟩, some ⟨5, by decide⟩,
   some ⟨7, by decide⟩, some ⟨6, by decide⟩, some ⟨8, by decide⟩, none]

private def p3d_psig9s : List (Option (Fin 9)) :=
  [some ⟨7, by decide⟩, some ⟨6, by decide⟩, some ⟨8, by decide⟩, some ⟨5, by decide⟩,
   some ⟨6, by decide⟩, some ⟨7, by decide⟩, some ⟨4, by decide⟩, some ⟨5, by decide⟩,
   some ⟨6, by decide⟩, some ⟨8, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩,
   some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩, none, some ⟨2, by decide⟩,
   some ⟨3, by decide⟩, some ⟨4, by decide⟩, some ⟨5, by decide⟩, some ⟨6, by decide⟩,
   some ⟨7, by decide⟩, some ⟨8, by decide⟩, some ⟨6, by decide⟩, some ⟨5, by decide⟩,
   some ⟨4, by decide⟩, some ⟨3, by decide⟩, some ⟨2, by decide⟩, some ⟨1, by decide⟩,
   some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩, some ⟨5, by decide⟩,
   some ⟨6, by decide⟩, some ⟨8, by decide⟩, some ⟨7, by decide⟩, some ⟨6, by decide⟩,
   some ⟨5, by decide⟩, some ⟨4, by decide⟩, some ⟨3, by decide⟩, some ⟨2, by decide⟩, none,
   some ⟨7, by decide⟩, some ⟨6, by decide⟩, some ⟨5, by decide⟩, some ⟨4, by decide⟩,
   some ⟨3, by decide⟩, some ⟨8, by decide⟩, some ⟨6, by decide⟩, some ⟨5, by decide⟩,
   some ⟨4, by decide⟩, some ⟨7, by decide⟩, some ⟨6, by decide⟩, some ⟨5, by decide⟩,
   some ⟨8, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩, none]

private def p3d_gb9 : Option (Fin 9) → ℤ
  | none => -3
  | some i => ![0, -2, -4, -6, -8, -10, -12, -6, -8] i

private def p3d_gb9s : Option (Fin 9) → ℤ
  | none => -3
  | some i => ![0, -2, -4, -6, -8, -10, -12, -8, -6] i

private theorem p3d_gb9_eq :
    ggSWord (ggAttachCartan (CartanMatrix.D 9) ⟨8, by decide⟩) p3d_psig9
      (Pi.single none 1) = p3d_gb9 := by
  funext i
  rcases i with _ | i
  · decide +kernel
  · fin_cases i <;> decide +kernel

private theorem p3d_gRb9_eq :
    ggSWordR (ggAttachCartan (CartanMatrix.D 9) ⟨8, by decide⟩) p3d_psig9
      (Pi.single none 1) = p3d_gb9 := by
  funext i
  rcases i with _ | i
  · decide +kernel
  · fin_cases i <;> decide +kernel

private theorem p3d_gb9s_eq :
    ggSWord (ggAttachCartan (CartanMatrix.D 9) ⟨7, by decide⟩) p3d_psig9s
      (Pi.single none 1) = p3d_gb9s := by
  funext i
  rcases i with _ | i
  · decide +kernel
  · fin_cases i <;> decide +kernel

private theorem p3d_gRb9s_eq :
    ggSWordR (ggAttachCartan (CartanMatrix.D 9) ⟨7, by decide⟩) p3d_psig9s
      (Pi.single none 1) = p3d_gb9s := by
  funext i
  rcases i with _ | i
  · decide +kernel
  · fin_cases i <;> decide +kernel

private theorem p3d_gb9_none : ((p3d_gb9 none : ℤ) : ZMod 3) = 0 := by
  decide +kernel

private theorem p3d_gb9s_none : ((p3d_gb9s none : ℤ) : ZMod 3) = 0 := by
  decide +kernel

private theorem p3d_hblock9_bool : (ggDRootList 9).all (fun u =>
    decide (¬ (∀ i : Fin 9,
      ((((Pi.single (some ⟨8, by decide⟩) (1 : ℤ) : Option (Fin 9) → ℤ)
          - (∑ j, p3d_gb9 j
              * ggAttachCartan (CartanMatrix.D 9) ⟨8, by decide⟩ j (some ⟨8, by decide⟩))
            • p3d_gb9) (some i)
         - u.getD i 0 : ℤ) : ZMod 3) = 0))) = true := by
  decide +kernel

private theorem p3d_hblock9 : ∀ u ∈ ggDRootList 9,
    ¬ (∀ i : Fin 9,
      ((((Pi.single (some ⟨8, by decide⟩) (1 : ℤ) : Option (Fin 9) → ℤ)
          - (∑ j, p3d_gb9 j
              * ggAttachCartan (CartanMatrix.D 9) ⟨8, by decide⟩ j (some ⟨8, by decide⟩))
            • p3d_gb9) (some i)
         - u.getD i 0 : ℤ) : ZMod 3) = 0) := by
  intro u hu
  exact of_decide_eq_true ((List.all_eq_true.mp p3d_hblock9_bool) u hu)

private theorem p3d_hblock9s_bool : (ggDRootList 9).all (fun u =>
    decide (¬ (∀ i : Fin 9,
      ((((Pi.single (some ⟨7, by decide⟩) (1 : ℤ) : Option (Fin 9) → ℤ)
          - (∑ j, p3d_gb9s j
              * ggAttachCartan (CartanMatrix.D 9) ⟨7, by decide⟩ j (some ⟨7, by decide⟩))
            • p3d_gb9s) (some i)
         - u.getD i 0 : ℤ) : ZMod 3) = 0))) = true := by
  decide +kernel

private theorem p3d_hblock9s : ∀ u ∈ ggDRootList 9,
    ¬ (∀ i : Fin 9,
      ((((Pi.single (some ⟨7, by decide⟩) (1 : ℤ) : Option (Fin 9) → ℤ)
          - (∑ j, p3d_gb9s j
              * ggAttachCartan (CartanMatrix.D 9) ⟨7, by decide⟩ j (some ⟨7, by decide⟩))
            • p3d_gb9s) (some i)
         - u.getD i 0 : ℤ) : ZMod 3) = 0) := by
  intro u hu
  exact of_decide_eq_true ((List.all_eq_true.mp p3d_hblock9s_bool) u hu)

theorem ggInvTest3_D_cell {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ}
    {c : Λ} {n : ℕ} (hn : 5 ≤ n) (e : Fin n ≃ Λ)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.D n i j) (hc : c = e ⟨n - 3, by omega⟩) :
    GGInvTest3 (ggAttachCartan C c) := by
  refine ggInvTest3_of_equiv e
    (X := ggAttachCartan (CartanMatrix.D n) ⟨n - 3, by omega⟩)
    (ggAttachCartan_map_equiv e hC hc) ?_
  refine p3d_invTest3_of_block (n := n) (b₀ := 5) (hb := by norm_num) (hn := hn)
    (kb := ⟨2, by decide⟩) (k := ⟨n - 3, by omega⟩)
    (hk := Fin.ext (by dsimp only; omega))
    (ψb := p3d_psig5) (wb := p3d_gb5) (cb := p3d_gb5) (i₀ := ⟨1, by decide⟩)
    (hwb := p3d_gb5_eq) (hcb := p3d_gRb5_eq) (hc0 := p3d_gb5_none)
    (hblock := p3d_hblock5)

theorem ggInvTest3_D_cell_one {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ}
    {b : Λ} {n : ℕ} (hn : 9 ≤ n) (e : Fin n ≃ Λ)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.D n i j)
    (hb : b = e ⟨n - 2, by omega⟩ ∨ b = e ⟨n - 1, by omega⟩) :
    GGInvTest3 (ggAttachCartan C b) := by
  rcases hb with hb | hb
  · refine ggInvTest3_of_equiv e
      (X := ggAttachCartan (CartanMatrix.D n) ⟨n - 2, by omega⟩)
      (ggAttachCartan_map_equiv e hC hb) ?_
    refine p3d_invTest3_of_block (n := n) (b₀ := 9) (hb := by norm_num) (hn := by omega)
      (kb := ⟨7, by decide⟩) (k := ⟨n - 2, by omega⟩)
      (hk := Fin.ext (by dsimp only; omega))
      (ψb := p3d_psig9s) (wb := p3d_gb9s) (cb := p3d_gb9s) (i₀ := ⟨7, by decide⟩)
      (hwb := p3d_gb9s_eq) (hcb := p3d_gRb9s_eq) (hc0 := p3d_gb9s_none)
      (hblock := p3d_hblock9s)
  · refine ggInvTest3_of_equiv e
      (X := ggAttachCartan (CartanMatrix.D n) ⟨n - 1, by omega⟩)
      (ggAttachCartan_map_equiv e hC hb) ?_
    refine p3d_invTest3_of_block (n := n) (b₀ := 9) (hb := by norm_num) (hn := by omega)
      (kb := ⟨8, by decide⟩) (k := ⟨n - 1, by omega⟩)
      (hk := Fin.ext (by dsimp only; omega))
      (ψb := p3d_psig9) (wb := p3d_gb9) (cb := p3d_gb9) (i₀ := ⟨8, by decide⟩)
      (hwb := p3d_gb9_eq) (hcb := p3d_gRb9_eq) (hc0 := p3d_gb9_none)
      (hblock := p3d_hblock9)

end CFSG.StandardType
