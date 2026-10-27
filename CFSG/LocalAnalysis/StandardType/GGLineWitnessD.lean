module

public import CFSG.LocalAnalysis.StandardType.GGLineWitnessData
public import CFSG.LocalAnalysis.StandardType.GGLatticeWitnessD

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def lwld_Ublock {b₀ : ℕ} (X : Matrix (Option (Fin b₀)) (Option (Fin b₀)) ℤ)
    (gb gRb : Option (Fin b₀) → ℤ) (jb : Fin b₀) : List ℤ :=
  (List.range b₀).map fun i =>
    if h : i < b₀ then
      4 * (if (⟨i, h⟩ : Fin b₀) = jb then 1 else 0) +
        (∑ i', ((Pi.single none 1 : Option (Fin b₀) → ℤ) - gRb) i' * X i' (some jb)) *
          gb (some ⟨i, h⟩)
    else 0

private def lwld_Ufun {n b₀ : ℕ} (hn : b₀ ≤ n)
    (X : Matrix (Option (Fin b₀)) (Option (Fin b₀)) ℤ) (gb gRb : Option (Fin b₀) → ℤ)
    (jb : Fin b₀) : ℕ → ℤ := fun i =>
  if h : i < n then
    4 * (if i = n - b₀ + jb then 1 else 0) -
      (∑ i', ((Pi.single none 1 : Option (Fin b₀) → ℤ) - gRb) i' * X i' (some jb)) *
        lwd_extend hn ((Pi.single none 1 : Option (Fin b₀) → ℤ) - gb) (some ⟨i, h⟩)
  else 0

private theorem lwld_Ufun_zero {n b₀ : ℕ} (hn : b₀ ≤ n)
    (X : Matrix (Option (Fin b₀)) (Option (Fin b₀)) ℤ) (gb gRb : Option (Fin b₀) → ℤ)
    (jb : Fin b₀) : ∀ i < n - b₀, lwld_Ufun hn X gb gRb jb i = 0 := by
  intro i hi
  dsimp only [lwld_Ufun]
  rw [dif_pos (by omega : i < n), if_neg (by omega : ¬ i = n - b₀ + jb),
    lwd_extend_eq_zero_of_not_mem hn _ (lwd_not_mem_shift hn hi)]
  ring

private theorem lwld_Ufun_tail {n b₀ : ℕ} (hn : b₀ ≤ n)
    (X : Matrix (Option (Fin b₀)) (Option (Fin b₀)) ℤ) (gb gRb : Option (Fin b₀) → ℤ)
    (jb : Fin b₀) :
    (List.range b₀).map (fun i => lwld_Ufun hn X gb gRb jb (n - b₀ + i)) =
      lwld_Ublock X gb gRb jb := by
  dsimp only [lwld_Ublock]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  dsimp only [lwld_Ufun]
  rw [dif_pos (by omega : n - b₀ + i < n), dif_pos hi]
  have hext : lwd_extend hn ((Pi.single none 1 : Option (Fin b₀) → ℤ) - gb)
      (some ⟨n - b₀ + i, by omega⟩) = - gb (some ⟨i, hi⟩) := by
    rw [show (some ⟨n - b₀ + i, by omega⟩ : Option (Fin n)) =
      lwd_shift hn (some ⟨i, hi⟩) from rfl]
    rw [lwd_extend_shift, Pi.sub_apply, Pi.single_eq_of_ne (by simp), zero_sub]
  rw [hext]
  by_cases h : (⟨i, hi⟩ : Fin b₀) = jb
  · have hc : (n - b₀ + i : ℕ) = n - b₀ + (jb : ℕ) := by
      have h' : (i : ℕ) = (jb : ℕ) := by simpa using Fin.ext_iff.mp h
      omega
    rw [if_pos hc, if_pos h]
    ring
  · have hc : ¬ ((n - b₀ + i : ℕ) = n - b₀ + (jb : ℕ)) := by
      intro hc'
      exact h (Fin.ext (show (i : ℕ) = (jb : ℕ) from by omega))
    rw [if_neg hc, if_neg h]
    ring

private theorem lwld_word_embed {n b₀ : ℕ} (hb : 5 ≤ b₀) (hn : b₀ ≤ n)
    (kb k₀ : Fin b₀) (ψγb : List (Option (Fin b₀))) (gb gRb : Option (Fin b₀) → ℤ)
    (hgb : ggSWord (ggAttachCartan (CartanMatrix.D b₀) kb) ψγb (Pi.single (some k₀) 1) = gb)
    (hgRb : ggSWordR (ggAttachCartan (CartanMatrix.D b₀) kb) ψγb
      (Pi.single (some k₀) 1) = gRb)
    (hP1 : (∑ j, ggAttachCartan (CartanMatrix.D b₀) kb none j * gb j) = -2)
    (hP2 : (∑ j, gRb j * ggAttachCartan (CartanMatrix.D b₀) kb j none) = -2)
    {k : Fin n} (hk : k = ⟨n - b₀ + kb, by omega⟩) (m : ℕ) :
    ggSWord (ggAttachCartan (CartanMatrix.D n) k)
        (ggAffineWord (ψγb.map (lwd_shift hn)) (lwd_shift hn (some k₀)) none m)
        (Pi.single none 1) =
      Pi.single none 1 - (2 * (m : ℤ)) • (Pi.single none 1 + lwd_extend hn gb) ∧
    ggSWordR (ggAttachCartan (CartanMatrix.D n) k)
        (ggAffineWord (ψγb.map (lwd_shift hn)) (lwd_shift hn (some k₀)) none m)
        (Pi.single none 1) =
      Pi.single none 1 - (2 * (m : ℤ)) • (Pi.single none 1 + lwd_extend hn gRb) := by
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
  have hword := ggAffinePair_word Xn hdiagn none kγ ψγ hP1n hP2n m
  refine ⟨?_, ?_⟩
  · rw [hword.1, hgn]
  · rw [hword.2, hgRn]

private theorem lwld_cast_identity {n b₀ : ℕ} (hn : b₀ ≤ n) {p : ℕ}
    {Xn : Matrix (Option (Fin n)) (Option (Fin n)) ℤ}
    {Xb : Matrix (Option (Fin b₀)) (Option (Fin b₀)) ℤ}
    (hX : ∀ i j, Xn (lwd_shift hn i) (lwd_shift hn j) = Xb i j)
    (gb gRb : Option (Fin b₀) → ℤ) (jb : Fin b₀) (m : ℕ)
    (hm : (4 : ZMod p) * (m : ZMod p) = 1) (w c : Option (Fin n) → ℤ)
    (hw : w = Pi.single none 1 - (2 * (m : ℤ)) • (Pi.single none 1 + lwd_extend hn gb))
    (hc : c = Pi.single none 1 - (2 * (m : ℤ)) • (Pi.single none 1 + lwd_extend hn gRb))
    {i : ℕ} (hi : i < n) :
    (4 : ZMod p) * (((lwd_single hn (some jb)) (some ⟨i, hi⟩) : ℤ) -
      ((∑ i', c i' * ∑ j, Xn i' j * lwd_single hn (some jb) j : ℤ) : ZMod p) *
        (w (some ⟨i, hi⟩) : ZMod p)) = (lwld_Ufun hn Xb gb gRb jb i : ZMod p) := by
  have hext1 : lwd_extend hn ((Pi.single none 1 : Option (Fin b₀) → ℤ) - gb)
      = Pi.single none 1 - lwd_extend hn gb := by
    rw [show ((Pi.single none 1 : Option (Fin b₀) → ℤ) - gb)
        = Pi.single none 1 - (1 : ℤ) • gb from by rw [one_smul]]
    rw [lwd_extend_sub_smul, lwd_extend_single, one_smul]
    rfl
  have hext2 : lwd_extend hn ((Pi.single none 1 : Option (Fin b₀) → ℤ) - gRb)
      = Pi.single none 1 - lwd_extend hn gRb := by
    rw [show ((Pi.single none 1 : Option (Fin b₀) → ℤ) - gRb)
        = Pi.single none 1 - (1 : ℤ) • gRb from by rw [one_smul]]
    rw [lwd_extend_sub_smul, lwd_extend_single, one_smul]
    rfl
  have h4m : (2 : ZMod p) * (2 * (m : ZMod p)) = 1 := by
    have h22 : (2 : ZMod p) * 2 = 4 := by norm_num
    rw [← mul_assoc, h22, hm]
  have hvec1 : ∀ y, (2 * (w y : ZMod p)) =
      (lwd_extend hn ((Pi.single none 1 : Option (Fin b₀) → ℤ) - gb) y : ZMod p) := by
    intro y
    rw [hw, hext1]
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    push_cast
    rw [mul_sub, ← mul_assoc, h4m, one_mul]
    ring
  have hvec2 : ∀ y, (2 * (c y : ZMod p)) =
      (lwd_extend hn ((Pi.single none 1 : Option (Fin b₀) → ℤ) - gRb) y : ZMod p) := by
    intro y
    rw [hc, hext2]
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    push_cast
    rw [mul_sub, ← mul_assoc, h4m, one_mul]
    ring
  have hρ : ∀ i', (∑ j, Xn i' j * lwd_single hn (some jb) j) =
      Xn i' (lwd_shift hn (some jb)) := by
    intro i'
    unfold lwd_single
    rw [Fintype.sum_eq_single (lwd_shift hn (some jb))]
    · rw [Pi.single_eq_same, mul_one]
    · intro j hj
      rw [Pi.single_eq_of_ne hj, mul_zero]
  have hsingle : ((lwd_single hn (some jb)) (some ⟨i, hi⟩) : ℤ) =
      if i = n - b₀ + (jb : ℕ) then 1 else 0 := by
    unfold lwd_single
    rw [Pi.single_apply]
    refine if_congr ?_ rfl rfl
    constructor
    · intro h
      have := congrArg Fin.val (Option.some.inj h)
      omega
    · intro h
      exact congrArg some (Fin.ext (by omega))
  have hsingleZ : ((lwd_single hn (some jb)) (some ⟨i, hi⟩) : ZMod p) =
      if i = n - b₀ + (jb : ℕ) then 1 else 0 := by
    rw [show ((lwd_single hn (some jb)) (some ⟨i, hi⟩) : ZMod p) =
        (((lwd_single hn (some jb)) (some ⟨i, hi⟩) : ℤ) : ZMod p) from rfl, hsingle]
    by_cases h : i = n - b₀ + (jb : ℕ)
    · rw [if_pos h, if_pos h]
      norm_num
    · rw [if_neg h, if_neg h]
      norm_num
  have hpair : (∑ i', c i' * ∑ j, Xn i' j * lwd_single hn (some jb) j : ℤ) =
      ∑ i', c i' * Xn i' (lwd_shift hn (some jb)) := by
    apply Finset.sum_congr rfl
    intro i' _
    rw [hρ i']
  have h2P : (2 : ZMod p) *
      ((∑ i', c i' * Xn i' (lwd_shift hn (some jb)) : ℤ) : ZMod p) =
      ((∑ y, lwd_extend hn ((Pi.single none 1 : Option (Fin b₀) → ℤ) - gRb) y *
        Xn y (lwd_shift hn (some jb)) : ℤ) : ZMod p) := by
    rw [Int.cast_sum, Int.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i' _
    push_cast
    rw [← hvec2 i']
    ring
  have hM : (∑ y, lwd_extend hn ((Pi.single none 1 : Option (Fin b₀) → ℤ) - gRb) y *
        Xn y (lwd_shift hn (some jb))) =
      ∑ i', ((Pi.single none 1 : Option (Fin b₀) → ℤ) - gRb) i' * Xb i' (some jb) :=
    lwd_dot_extendR hn hX ((Pi.single none 1 : Option (Fin b₀) → ℤ) - gRb) (some jb)
  have h2Pfull : (2 : ZMod p) *
      ((∑ i', c i' * ∑ j, Xn i' j * lwd_single hn (some jb) j : ℤ) : ZMod p) =
      ((∑ i', ((Pi.single none 1 : Option (Fin b₀) → ℤ) - gRb) i' *
        Xb i' (some jb) : ℤ) : ZMod p) := by
    rw [hpair, h2P, hM]
  have h4w : (2 : ZMod p) * (w (some ⟨i, hi⟩) : ZMod p) =
      (lwd_extend hn ((Pi.single none 1 : Option (Fin b₀) → ℤ) - gb)
        (some ⟨i, hi⟩) : ZMod p) :=
    hvec1 (some ⟨i, hi⟩)
  have h4Pw : (4 : ZMod p) *
      (((∑ i', c i' * ∑ j, Xn i' j * lwd_single hn (some jb) j : ℤ) : ZMod p) *
        (w (some ⟨i, hi⟩) : ZMod p)) =
      ((∑ i', ((Pi.single none 1 : Option (Fin b₀) → ℤ) - gRb) i' *
        Xb i' (some jb) : ℤ) : ZMod p) *
        (lwd_extend hn ((Pi.single none 1 : Option (Fin b₀) → ℤ) - gb)
          (some ⟨i, hi⟩) : ZMod p) := by
    calc (4 : ZMod p) *
          (((∑ i', c i' * ∑ j, Xn i' j * lwd_single hn (some jb) j : ℤ) : ZMod p) *
            (w (some ⟨i, hi⟩) : ZMod p))
        = ((2 : ZMod p) *
            ((∑ i', c i' * ∑ j, Xn i' j * lwd_single hn (some jb) j : ℤ) : ZMod p)) *
          ((2 : ZMod p) * (w (some ⟨i, hi⟩) : ZMod p)) := by ring
      _ = ((∑ i', ((Pi.single none 1 : Option (Fin b₀) → ℤ) - gRb) i' *
            Xb i' (some jb) : ℤ) : ZMod p) *
          (lwd_extend hn ((Pi.single none 1 : Option (Fin b₀) → ℤ) - gb)
            (some ⟨i, hi⟩) : ZMod p) := by rw [h2Pfull, h4w]
  rw [mul_sub, h4Pw, hsingleZ]
  unfold lwld_Ufun
  rw [dif_pos hi]
  push_cast
  ring

private theorem lwld_lineTest_of_block {n b₀ : ℕ} (hb : 5 ≤ b₀) (hn : b₀ ≤ n)
    (kb k₀ jb : Fin b₀) (ψγb : List (Option (Fin b₀))) (gb gRb : Option (Fin b₀) → ℤ)
    (hgb : ggSWord (ggAttachCartan (CartanMatrix.D b₀) kb) ψγb (Pi.single (some k₀) 1) = gb)
    (hgRb : ggSWordR (ggAttachCartan (CartanMatrix.D b₀) kb) ψγb
      (Pi.single (some k₀) 1) = gRb)
    (hgRb_none : gRb none = 1)
    (hP1 : (∑ j, ggAttachCartan (CartanMatrix.D b₀) kb none j * gb j) = -2)
    (hP2 : (∑ j, gRb j * ggAttachCartan (CartanMatrix.D b₀) kb j none) = -2)
    (hblock0 : ∀ u ∈ ggDRootList b₀,
      12 % ggLWminors (lwld_Ublock (ggAttachCartan (CartanMatrix.D b₀) kb) gb gRb jb) u = 0)
    {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    {k : Fin n} (hk : k = ⟨n - b₀ + kb, by omega⟩) :
    GGLineTest (ggAttachCartan (CartanMatrix.D n) k) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨by omega⟩
  let Xb : Matrix (Option (Fin b₀)) (Option (Fin b₀)) ℤ := ggAttachCartan (CartanMatrix.D b₀) kb
  let Xn : Matrix (Option (Fin n)) (Option (Fin n)) ℤ := ggAttachCartan (CartanMatrix.D n) k
  have hX : ∀ i j : Option (Fin b₀), Xn (lwd_shift hn i) (lwd_shift hn j) = Xb i j := by
    intro i j
    dsimp only [Xn, Xb]
    exact lwd_attach_sub (by omega) hn kb hk i j
  let m : ℕ := ((4 : ZMod p)⁻¹).val
  have hm4 : (4 : ZMod p) * (m : ZMod p) = 1 := by
    have h4 : (4 : ZMod p) ≠ 0 := by
      intro h
      have hd : p ∣ 4 := (ZMod.natCast_eq_zero_iff 4 p).mp h
      have : p ≤ 4 := Nat.le_of_dvd (by norm_num) hd
      omega
    dsimp only [m]
    rw [ZMod.natCast_zmod_val]
    exact mul_inv_cancel₀ h4
  let ψ : List (Option (Fin n)) :=
    ggAffineWord (ψγb.map (lwd_shift hn)) (lwd_shift hn (some k₀)) none m
  obtain ⟨hw1, hw2⟩ := lwld_word_embed (n := n) (b₀ := b₀) hb hn kb k₀ ψγb gb gRb
    hgb hgRb hP1 hP2 (k := k) hk m
  refine ⟨ψ, none, lwd_single hn (some jb), ?_, ?_, ?_⟩
  · refine ⟨[], ⟨n - b₀ + jb, by omega⟩, ?_⟩
    show lwd_single hn (some jb) =
      (Pi.single (some ⟨n - b₀ + jb, by omega⟩) (1 : ℤ) : Option (Fin n) → ℤ)
    dsimp only [lwd_single, lwd_shift]
  · rw [hw2]
    have hge : lwd_extend hn gRb none = 1 := by
      rw [← show lwd_shift hn none = none from rfl, lwd_extend_shift, hgRb_none]
    have hnone : ((Pi.single none (1 : ℤ) : Option (Fin n) → ℤ) - (2 * (m : ℤ)) •
        ((Pi.single none (1 : ℤ) : Option (Fin n) → ℤ) + lwd_extend hn gRb)) none
        = 1 - 4 * (m : ℤ) := by
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, Pi.single_eq_same, hge,
        smul_eq_mul]
      ring
    rw [hnone]
    push_cast
    rw [hm4]
    ring
  · intro v hv r heq
    obtain ⟨_, hrootd⟩ :=
      ggDRoot_of_mem_ggLCoroots (n := n) (le_trans hb hn) k (show v ∈ ggLCoroots Xn from hv)
    refine ggD_nonprop (b₀ := b₀) hb hn (w := lwld_Ufun hn Xb gb gRb jb)
      (lwld_Ufun_zero hn Xb gb gRb jb) ?_ hp h5 hrootd (4 * (r : ZMod p)) ?_
    · intro u hu
      rw [lwld_Ufun_tail]
      exact hblock0 u hu
    · intro i hi
      rw [← lwld_cast_identity hn hX gb gRb jb m hm4
        (ggSWord Xn ψ (Pi.single none 1)) (ggSWordR Xn ψ (Pi.single none 1)) hw1 hw2 hi]
      have hci := congrFun heq (some ⟨i, hi⟩)
      rw [hci]
      have hvli : (if h : i < n then (v (some ⟨i, h⟩) : ℤ) else 0) =
          (v (some ⟨i, hi⟩) : ℤ) := by
        rw [dif_pos hi]
      rw [hvli]
      ring

private theorem lwld_hblock5_bool : (ggDRootList 5).all (fun u =>
    decide (12 % ggLWminors (lwld_Ublock (ggAttachCartan (CartanMatrix.D 5) ⟨2, by decide⟩)
      lwd_gb5 lwd_gb5 ⟨1, by decide⟩) u = 0)) = true := by
  decide +kernel

private theorem lwld_hblock5 : ∀ u ∈ ggDRootList 5,
    12 % ggLWminors (lwld_Ublock (ggAttachCartan (CartanMatrix.D 5) ⟨2, by decide⟩)
      lwd_gb5 lwd_gb5 ⟨1, by decide⟩) u = 0 := by
  intro u hu
  exact of_decide_eq_true ((List.all_eq_true.mp lwld_hblock5_bool) u hu)

private theorem lwld_hblock8_bool : (ggDRootList 8).all (fun u =>
    decide (12 % ggLWminors (lwld_Ublock (ggAttachCartan (CartanMatrix.D 8) ⟨7, by decide⟩)
      lwd_gb8 lwd_gb8 ⟨7, by decide⟩) u = 0)) = true := by
  decide +kernel

private theorem lwld_hblock8 : ∀ u ∈ ggDRootList 8,
    12 % ggLWminors (lwld_Ublock (ggAttachCartan (CartanMatrix.D 8) ⟨7, by decide⟩)
      lwd_gb8 lwd_gb8 ⟨7, by decide⟩) u = 0 := by
  intro u hu
  exact of_decide_eq_true ((List.all_eq_true.mp lwld_hblock8_bool) u hu)

private theorem lwld_hblock8a_bool : (ggDRootList 8).all (fun u =>
    decide (12 % ggLWminors (lwld_Ublock (ggAttachCartan (CartanMatrix.D 8) ⟨6, by decide⟩)
      lwd_gb8a lwd_gb8a ⟨6, by decide⟩) u = 0)) = true := by
  decide +kernel

private theorem lwld_hblock8a : ∀ u ∈ ggDRootList 8,
    12 % ggLWminors (lwld_Ublock (ggAttachCartan (CartanMatrix.D 8) ⟨6, by decide⟩)
      lwd_gb8a lwd_gb8a ⟨6, by decide⟩) u = 0 := by
  intro u hu
  exact of_decide_eq_true ((List.all_eq_true.mp lwld_hblock8a_bool) u hu)

theorem ggLineTest_D_cell {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ}
    {c : Λ} {n : ℕ} (hn : 5 ≤ n) (e : Fin n ≃ Λ)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.D n i j) (hc : c = e ⟨n - 3, by omega⟩)
    {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : GGLineTest (ggAttachCartan C c) p := by
  refine ggLineTest_of_equiv e
    (X := ggAttachCartan (CartanMatrix.D n) ⟨n - 3, by omega⟩)
    (ggAttachCartan_map_equiv e hC hc) ?_
  exact lwld_lineTest_of_block (n := n) (b₀ := 5) (hb := by norm_num) (hn := hn)
    (kb := ⟨2, by decide⟩) (k₀ := ⟨0, by decide⟩) (jb := ⟨1, by decide⟩) (ψγb := lwd_psig5)
    (gb := lwd_gb5) (gRb := lwd_gb5) (hgb := lwd_gb5_eq) (hgRb := lwd_gRb5_eq)
    (hgRb_none := lwd_gb5_none) (hP1 := lwd_hP1_5) (hP2 := lwd_hP2_5)
    (hblock0 := lwld_hblock5) (hp := hp) (h5 := h5) (k := ⟨n - 3, by omega⟩)
    (hk := Fin.ext (by simp only [Fin.val_mk]; omega))

theorem ggLineTest_D_cell_one {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ}
    {b : Λ} {n : ℕ} (hn : 9 ≤ n) (e : Fin n ≃ Λ)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.D n i j)
    (hb : b = e ⟨n - 2, by omega⟩ ∨ b = e ⟨n - 1, by omega⟩)
    {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : GGLineTest (ggAttachCartan C b) p := by
  rcases hb with hb | hb
  · refine ggLineTest_of_equiv e
      (X := ggAttachCartan (CartanMatrix.D n) ⟨n - 2, by omega⟩)
      (ggAttachCartan_map_equiv e hC hb) ?_
    exact lwld_lineTest_of_block (n := n) (b₀ := 8) (hb := by norm_num)
      (hn := by omega) (kb := ⟨6, by decide⟩) (k₀ := ⟨0, by decide⟩) (jb := ⟨6, by decide⟩)
      (ψγb := lwd_psig8a) (gb := lwd_gb8a) (gRb := lwd_gb8a) (hgb := lwd_gb8a_eq)
      (hgRb := lwd_gRb8a_eq) (hgRb_none := lwd_gb8a_none) (hP1 := lwd_hP1_8a)
      (hP2 := lwd_hP2_8a) (hblock0 := lwld_hblock8a) (hp := hp) (h5 := h5)
      (k := ⟨n - 2, by omega⟩) (hk := Fin.ext (by simp only [Fin.val_mk]; omega))
  · refine ggLineTest_of_equiv e
      (X := ggAttachCartan (CartanMatrix.D n) ⟨n - 1, by omega⟩)
      (ggAttachCartan_map_equiv e hC hb) ?_
    exact lwld_lineTest_of_block (n := n) (b₀ := 8) (hb := by norm_num)
      (hn := by omega) (kb := ⟨7, by decide⟩) (k₀ := ⟨0, by decide⟩) (jb := ⟨7, by decide⟩)
      (ψγb := lwd_psig8) (gb := lwd_gb8) (gRb := lwd_gb8) (hgb := lwd_gb8_eq)
      (hgRb := lwd_gRb8_eq) (hgRb_none := lwd_gb8_none) (hP1 := lwd_hP1_8)
      (hP2 := lwd_hP2_8) (hblock0 := lwld_hblock8) (hp := hp) (h5 := h5)
      (k := ⟨n - 1, by omega⟩) (hk := Fin.ext (by simp only [Fin.val_mk]; omega))

end CFSG.StandardType
