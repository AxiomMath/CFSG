module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10DirectFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10DirectK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Norm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BetaKer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {T : Type} [CommGroup T] [Finite T]

private theorem s16c1610_mem_stabSub_of_map_eq {Y : Subgroup T} {g : MulAut T}
    (h : Y.map g.toMonoidHom = Y) : g ∈ stabSub Y := by
  rw [mem_stabSub]
  intro u
  constructor
  · intro hgu
    rw [← h] at hgu
    obtain ⟨u', hu', huu⟩ := Subgroup.mem_map.mp hgu
    rwa [g.injective huu] at hu'
  · intro hu
    rw [← h]
    exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩

theorem s16c1610_false_of_direct_three (hT : ∀ t : T, t ^ 2 = 1) {X A B : Subgroup (MulAut T)}
    (hA : IsElemAbelianOfRank 3 3 ↥A) (hAP : A ≤ pCoreOf 3 X)
    (hAn : ∀ m ∈ X, ∀ a ∈ A, m * a * m⁻¹ ∈ A)
    (hS : SymSumOfConj X (⊤ : Subgroup T) 3 (dParam 3)) (hBX : B ≤ X) (hB1 : B ≠ ⊥)
    (hB2 : IsElemAbelian2 B) {Ut : Subgroup T} (hUt : Ut ≠ ⊤) (hk : rkIdx Ut ≤ 1)
    (hA3 : ∀ b ∈ B, b ≠ 1 → fixV (Subgroup.zpowers b) ≤ Ut)
    (hA4 : ∀ b ∈ B, b ≠ 1 → ∀ w, w ∈ Ut ↔ w * (b w)⁻¹ ∈ fixV B)
    (hA5 : rkIdx (fixV B) = rk ↥B + rkIdx Ut) : False := by
  classical
  obtain ⟨ι, hιF, Y, hY⟩ := s16c1610_symSumFamily_of_symSumOfConj hS
  have hY2 : SymSumFamily X Y 3 2 := by
    simpa only [s16c1610_dParam_three] using hY
  have hcard : Fintype.card ι = 4 := by
    have h := hY.card
    omega
  obtain ⟨hpc_le, -, -, hAYpc⟩ :=
    s16c13beta_pcore_data (X := X) (p := 3) (ι := ι) (Y := Y) (by norm_num) (by norm_num)
      hY.inj hY.perm hY.surj (by omega)
  have hAX : A ≤ X := hAP.trans hpc_le
  have hAY : ∀ a ∈ A, ∀ s, (Y s).map a.toMonoidHom = Y s :=
    fun a ha s => hAYpc a (hAP ha) s
  have hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := hB2.1
  have hBsq : ∀ a ∈ B, a ^ 2 = 1 := hB2.2
  have hBperm : ∀ b ∈ B, ∀ i, ∃ j, (Y i).map b.toMonoidHom = Y j :=
    fun b hb i => hY.perm b (hBX hb) i
  have hnotall : ¬ ∀ i, Y i ≤ Ut := by
    intro hall
    exact hUt (eq_top_iff.mpr (by rw [← hY.sup]; exact iSup_le hall))
  obtain ⟨i, hi⟩ := not_forall.mp hnotall
  have hrki : rk ↥(Y i) = 2 := (hY.rank i).trans s16c1610_dParam_three
  have hYinf : Y i ⊓ Ut ≠ ⊥ :=
    s16c1610_inf_ne_bot_of_rkIdx_lt hT (by rw [hrki]; omega)
  obtain hUtbot | ⟨u, hu, hu1⟩ := Subgroup.bot_or_exists_ne_one (Y i ⊓ Ut)
  · exact absurd hUtbot hYinf
  have hN2 : ∀ b ∈ B ⊓ stabSub (Y i), b ^ 2 = 1 := fun b hb => hBsq b hb.1
  have hNY : B ⊓ stabSub (Y i) ≤ stabSub (Y i) := inf_le_right
  have hBcent : B ⊓ centSub (Y i) = ⊥ := s16c1610_inf_centSub_eq_bot hA3 hi
  have hNker : (B ⊓ stabSub (Y i)) ⊓ centSub (Y i) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxB : x ∈ B ⊓ centSub (Y i) := ⟨hx.1.1, hx.2⟩
    rwa [hBcent] at hxB
  have hcardN : Nat.card ↥(B ⊓ stabSub (Y i)) ≤ 2 :=
    s16c1610_card_le_two_of_rk_two hT hN2 hrki hNY hNker
  obtain ⟨Y', horbY⟩ :
      ∃ Y' : Subgroup T, ∀ b ∈ B, (Y i).map b.toMonoidHom = Y i ∨
        (Y i).map b.toMonoidHom = Y' := by
    by_cases h : ∃ b ∈ B, (Y i).map b.toMonoidHom ≠ Y i
    · obtain ⟨b0, hb0, hb0move⟩ := h
      obtain ⟨j, hj⟩ := hY.perm b0 (hBX hb0) i
      have hji : j ≠ i := by
        intro hji
        exact hb0move (by rw [hj, hji])
      have hb01 : b0 ≠ 1 := by
        intro hb01
        exact hb0move (by rw [hb01]; exact Subgroup.map_id (Y i))
      have hfix : u * b0 u ∈ fixV B := by
        have h1 : u * (b0 u)⁻¹ ∈ fixV B := (hA4 b0 hb0 hb01 u).mp hu.2
        have h2 : (b0 u)⁻¹ = b0 u := by
          rw [inv_eq_iff_mul_eq_one]
          simpa [pow_two] using hT (b0 u)
        rwa [h2] at h1
      exact ⟨Y j, s16c1610_orbit_pair hY.indep hBcomm hBperm (Ne.symm hji)
        hb0 hj hu.1 hu1 hfix⟩
    · refine ⟨Y i, fun b hb => Or.inl ?_⟩
      by_contra hne
      exact h ⟨b, hb, hne⟩
  have hcardB_le2N : Nat.card B ≤ 2 * Nat.card ↥(B ⊓ stabSub (Y i)) :=
    s16c1610_card_le_two_mul_stab horbY
  have hcardB_le4 : Nat.card B ≤ 4 := by
    calc Nat.card B ≤ 2 * Nat.card ↥(B ⊓ stabSub (Y i)) := hcardB_le2N
      _ ≤ 2 * 2 := Nat.mul_le_mul_left 2 hcardN
      _ = 4 := by norm_num
  have hBp : IsPGroup 2 ↥B := isPGroup_two_of_sq_eq_one fun b : ↥B =>
    Subtype.ext (by simpa using hBsq (b : MulAut T) b.2)
  have hcardBpow : Nat.card B = 2 ^ rk ↥B := card_eq_two_pow_of_isPGroup hBp
  have hBne1 : Nat.card B ≠ 1 := fun h => hB1 (Subgroup.card_eq_one.mp h)
  have hk_le : rk ↥B ≤ 2 := by
    have h : 2 ^ rk ↥B ≤ 2 ^ 2 := by
      rw [← hcardBpow]
      simpa using hcardB_le4
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h
  have hk_pos : 1 ≤ rk ↥B := by
    by_contra h
    have h0 : rk ↥B = 0 := by omega
    exact hB1 ((rk_eq_zero_iff_of_isPGroup hBp).mp h0)
  have hk_cases : rk ↥B = 1 ∨ rk ↥B = 2 := by omega
  have hcardB_cases : Nat.card B = 2 ∨ Nat.card B = 4 := by
    rcases hk_cases with hk1 | hk2
    · exact Or.inl (by rw [hcardBpow, hk1]; norm_num)
    · exact Or.inr (by rw [hcardBpow, hk2]; norm_num)
  rcases hcardB_cases with h2 | h4
  · exact hUt (s16c1610_ut_eq_top_of_card_le_two hT hB1 hB2 (by omega) hA4)
  · have hrkB : rk ↥B = 2 := by
      rcases hk_cases with hk1 | hk2
      · rw [hcardBpow, hk1] at h4
        norm_num at h4
      · exact hk2
    have hcardN2 : Nat.card ↥(B ⊓ stabSub (Y i)) = 2 := by
      have h : 4 ≤ 2 * Nat.card ↥(B ⊓ stabSub (Y i)) := by
        rw [← h4]
        exact hcardB_le2N
      omega
    have hBnotleN : ¬ B ≤ B ⊓ stabSub (Y i) := by
      intro hle
      have hEq : (B ⊓ stabSub (Y i)) = B := le_antisymm inf_le_left hle
      rw [hEq] at hcardN
      omega
    obtain ⟨b0, hb0, hb0N⟩ : ∃ b ∈ B, b ∉ B ⊓ stabSub (Y i) := by
      by_contra hcon
      exact hBnotleN fun b hb => by
        by_contra hbN
        exact hcon ⟨b, hb, hbN⟩
    have hb0move : (Y i).map b0.toMonoidHom ≠ Y i := fun hmap =>
      hb0N ⟨hb0, s16c1610_mem_stabSub_of_map_eq hmap⟩
    obtain ⟨j, hj⟩ := hY.perm b0 (hBX hb0) i
    have hY'eq : Y' = Y j := by
      rcases horbY b0 hb0 with h | h
      · exact absurd h hb0move
      · exact h.symm.trans hj
    have horb : ∀ b' ∈ B, (Y i).map b'.toMonoidHom = Y i ∨
        (Y i).map b'.toMonoidHom = Y j := by
      intro b' hb'
      rcases horbY b' hb' with h | h
      · exact Or.inl h
      · exact Or.inr (h.trans hY'eq)
    have hij : i ≠ j := by
      intro hij
      exact hb0move (by rw [hj, hij])
    have hb01 : b0 ≠ 1 := by
      intro hb01
      exact hb0N (by rw [hb01]; exact ⟨B.one_mem, (stabSub (Y i)).one_mem⟩)
    have hNne : (B ⊓ stabSub (Y i)) ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hcardN2
      norm_num at hcardN2
    obtain hNbot | ⟨c, hcN, hc1⟩ := Subgroup.bot_or_exists_ne_one (B ⊓ stabSub (Y i))
    · exact absurd hNbot hNne
    have hcB : c ∈ B := hcN.1
    have hcStab : c ∈ stabSub (Y i) := hcN.2
    have hcimap : (Y i).map c.toMonoidHom = Y i := map_eq_of_mem_stabSub hcStab
    have hi_ex : ∃ y ∈ Y i, c y ≠ y := by
      by_contra hcon
      apply hc1
      have hc_cent : c ∈ centSub (Y i) := by
        rw [mem_centSub]
        intro y hy
        by_contra hne
        exact hcon ⟨y, hy, hne⟩
      have hmem : c ∈ (B ⊓ stabSub (Y i)) ⊓ centSub (Y i) := ⟨hcN, hc_cent⟩
      rw [hNker] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hc2 : c ^ 2 = 1 := hBsq c hcB
    have hkUt1 : rkIdx Ut = 1 := by
      rcases Nat.eq_zero_or_pos (rkIdx Ut) with h0 | hpos
      · exfalso
        apply hUt
        refine eq_of_le_of_rk_le hT le_top ?_
        have h1 : rk ↥Ut + rkIdx Ut = rk T := rk_add_rkIdx Ut
        have h2 : rk (⊤ : Subgroup T) = rk T := rk_top
        omega
      · omega
    have hrkIdxFix : rkIdx (fixV B) = 3 := by
      rw [hA5]
      omega
    have hfixcomp : ∀ l, l ≠ i → l ≠ j → ∀ y ∈ Y l, ∀ b' ∈ B, b' y = y :=
      s16c1610_fix_complement_of_four hT hY2 hBX hB2 hij hb0 hcB horb hj hcimap hi_ex
        hrkIdxFix.le
    have hj_mem : j ∈ (Finset.univ : Finset ι).erase i :=
      Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
    have hi_mem : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
    have hcompl_card : (((Finset.univ : Finset ι).erase i).erase j).card = 2 := by
      rw [Finset.card_erase_of_mem hj_mem, Finset.card_erase_of_mem hi_mem,
        Finset.card_univ, hcard]
    obtain ⟨l, m, hlm, hset⟩ := Finset.card_eq_two.mp hcompl_card
    have hlmem : l ∈ ((Finset.univ : Finset ι).erase i).erase j := by
      rw [hset]
      exact Finset.mem_insert_self l {m}
    have hmmem : m ∈ ((Finset.univ : Finset ι).erase i).erase j := by
      rw [hset]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self m)
    have hli : l ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hlmem).2).1
    have hlj : l ≠ j := (Finset.mem_erase.mp hlmem).1
    have hmi : m ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hmmem).2).1
    have hmj : m ≠ j := (Finset.mem_erase.mp hmmem).1
    have hcl : ∀ y ∈ Y l, c y = y := fun y hy => hfixcomp l hli hlj y hy c hcB
    have hcm : ∀ y ∈ Y m, c y = y := fun y hy => hfixcomp m hmi hmj y hy c hcB
    have hcj_ex : ∃ y ∈ Y j, c y ≠ y := by
      obtain ⟨y, hy, hyne⟩ := hi_ex
      refine ⟨b0 y, ?_, ?_⟩
      · rw [← hj]
        exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
      · intro hcontra
        have hcomm : c (b0 y) = b0 (c y) := by
          have hh := congrArg (fun f : MulAut T => f y) (hBcomm c hcB b0 hb0)
          simpa [MulAut.coe_mul] using hh
        rw [hcomm] at hcontra
        exact hyne (b0.injective hcontra)
    have hcjmap : (Y j).map c.toMonoidHom = Y j := by
      have hcomm : c.toMonoidHom.comp b0.toMonoidHom = b0.toMonoidHom.comp c.toMonoidHom := by
        ext x
        have hh := congrArg (fun f : MulAut T => f x) (hBcomm c hcB b0 hb0)
        simpa [MulAut.coe_mul] using hh
      rw [← hj, Subgroup.map_map, hcomm, ← Subgroup.map_map, hcimap]
    have hcY : ∀ s, (Y s).map c.toMonoidHom = Y s := by
      intro s
      by_cases hsi : s = i
      · subst hsi
        exact hcimap
      by_cases hsj : s = j
      · subst hsj
        exact hcjmap
      · refine map_eq_of_mem_stabSub ?_
        rw [mem_stabSub]
        intro w
        constructor
        · intro hcw
          have hfix_cw : c (c w) = c w := hfixcomp s hsi hsj (c w) hcw c hcB
          have hcw_eq : c w = w := c.injective hfix_cw
          rw [← hcw_eq]
          exact hcw
        · intro hw
          rw [hfixcomp s hsi hsj w hw c hcB]
          exact hw
    exact s16c1610_false_of_involution_on_two hT hY2 hA hAX hAn hAY (hBX hcB) hc2 hcY
      hij (Ne.symm hli) (Ne.symm hmi) (Ne.symm hlj) (Ne.symm hmj) hlm hi_ex hcj_ex hcl hcm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
