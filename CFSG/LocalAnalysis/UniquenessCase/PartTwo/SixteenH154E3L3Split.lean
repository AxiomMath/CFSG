module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Fix
import CFSG.Adapters.StatedSLPerfect
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfGen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenSmallMod
import CFSG.Quasithin.Vol2.Ch3B513NC1Lin
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3CoverA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3FixLe
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JPBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

structure S16hL3Split (L : Subgroup (MulAut W)) (k : ℕ) where
  I : Fin k → Subgroup W
  J : Fin k → Subgroup W
  Z_le_I : ∀ i, commSub ⊤ L ⊓ fixV L ≤ I i
  I_ind : ∀ i, I i ⊓ ((commSub ⊤ L ⊓ fixV L) ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j) ≤
    commSub ⊤ L ⊓ fixV L
  I_nat : ∀ i, BinaryNaturalSL L (I i) (commSub ⊤ L ⊓ fixV L) 3 1
  J_le_I : ∀ i, J i ≤ I i
  J_inv : ∀ i, ∀ l ∈ L, ∀ x ∈ J i, l x ∈ J i
  J_comm : ∀ i, commSub (J i) L = J i
  J_sup_Z : ∀ i, J i ⊔ (commSub ⊤ L ⊓ fixV L) = I i
  J_nat : ∀ i, BinaryNaturalSL L (J i) (J i ⊓ fixV L) 3 1
  J_rk : ∀ i, rk ↥(J i) = 4
  J_fix_rk : ∀ i, rk ↥(J i ⊓ fixV L) = 1
  J_ind : ∀ i, J i ⊓ ⨆ (j : Fin k) (_ : j ≠ i), J j = ⊥
  J_iSup : (⨆ i, J i) = commSub ⊤ L

private theorem s16h_e3_l3_rk_le_of_card_le {Z : Subgroup W} {m : ℕ}
    (h : Nat.card ↥Z ≤ 2 ^ m) : rk ↥Z ≤ m := by
  change padicValNat 2 (Nat.card ↥Z) ≤ m
  calc padicValNat 2 (Nat.card ↥Z) ≤ Nat.log 2 (Nat.card ↥Z) := padicValNat_le_nat_log _
    _ ≤ Nat.log 2 (2 ^ m) := Nat.log_mono_right h
    _ = m := Nat.log_pow (by norm_num) m

theorem s16h_e3_l3_split_nonempty (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} {k : ℕ}
    (hL3 : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) k)
    (hd : rk ↥(commSub ⊤ L ⊓ fixV L) = k) : Nonempty (S16hL3Split L k) := by
  have hL3copy := hL3
  obtain ⟨hsl, I, hZI, hind, hsup, hnat⟩ := hL3
  obtain ⟨K, hKf, -, hKcard, ⟨e⟩⟩ := hsl
  letI := hKf
  haveI : Group.IsPerfect ↥(StatedSL 3 K) :=
    CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le (by norm_num) K
  have hperf : Group.IsPerfect ↥L :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hnatEx : ∀ i, ∃ (K' : Type) (_ : Field K') (_ : Finite K'), Nat.card K' = 2 ^ 1 ∧
      (FFModel.nat (StatedSL 3 K')).Realizes L (I i) (commSub ⊤ L ⊓ fixV L) := hnat
  choose K' hK'f hK'fin hK'card hreal using hnatEx
  let J : Fin k → Subgroup W := fun i => commSub (I i) L
  have htop : ∀ l ∈ L, ∀ y ∈ (⊤ : Subgroup W), l y ∈ (⊤ : Subgroup W) :=
    fun l _ y _ => Subgroup.mem_top (l y)
  have hUinv : ∀ l ∈ L, ∀ u ∈ commSub ⊤ L, l u ∈ commSub ⊤ L :=
    s16jp_commSub_stable (L := L) (Y := ⊤) htop
  have hUc : commSub (commSub ⊤ L) L = commSub ⊤ L :=
    s16jp_commSub_commSub hperf (Y := ⊤) htop
  have hIinv : ∀ i, ∀ l ∈ L, ∀ x ∈ I i, l x ∈ I i := by
    intro i
    letI := hK'f i
    letI := hK'fin i
    exact s16c1614_invariant_of_realizes (hreal i)
  have hJI : ∀ i, J i ≤ I i := fun i => commSub_le_of_invariant (hIinv i)
  have hJinv : ∀ i, ∀ l ∈ L, ∀ x ∈ J i, l x ∈ J i :=
    fun i => s16jp_commSub_stable (L := L) (Y := I i) (hIinv i)
  have hJJ : ∀ i, commSub (J i) L = J i :=
    fun i => s16jp_commSub_commSub hperf (hIinv i)
  have hJZ : ∀ i, J i ⊔ (commSub ⊤ L ⊓ fixV L) = I i := by
    intro i
    letI := hK'f i
    letI := hK'fin i
    exact s16fh_commSub_sup_nat (by norm_num) (hreal i)
  have hIleU : ∀ i, I i ≤ commSub ⊤ L := by
    intro i
    calc I i ≤ ⨆ i, I i := le_iSup (fun i => I i) i
      _ ≤ (commSub ⊤ L ⊓ fixV L) ⊔ ⨆ i, I i := le_sup_right
      _ = commSub ⊤ L := hsup
  have hJU : ∀ i, J i ≤ commSub ⊤ L := fun i => (hJI i).trans (hIleU i)
  have hZJ : ∀ i, (commSub ⊤ L ⊓ fixV L) ⊓ J i = J i ⊓ fixV L := by
    intro i
    rw [inf_assoc, inf_comm (fixV L) (J i), ← inf_assoc, inf_eq_right.mpr (hJU i)]
  have hJnat : ∀ i, BinaryNaturalSL L (J i) (J i ⊓ fixV L) 3 1 := by
    intro i
    letI := hK'f i
    letI := hK'fin i
    refine ⟨K' i, hK'f i, hK'fin i, hK'card i, ?_⟩
    rw [← hZJ i]
    exact s16jp_realizes_restrict_sub (hJI i) (hJinv i) (hJZ i) (hreal i)
  have hgen : ∀ y ∈ ⨆ i, I i, ∀ l ∈ L, l y * y⁻¹ ∈ ⨆ i, J i := by
    intro y hy
    refine Subgroup.iSup_induction (fun i => I i) hy
      (C := fun z => ∀ l ∈ L, l z * z⁻¹ ∈ ⨆ i, J i) ?_ ?_ ?_
    · intro i y hy l hl
      exact le_iSup (fun i => J i) i (Subgroup.subset_closure ⟨l, hl, y, hy, rfl⟩)
    · intro l hl
      simpa only [map_one, inv_one, one_mul] using Subgroup.one_mem (⨆ i, J i)
    · intro a b ha hb l hl
      rw [map_mul, mul_inv_rev]
      rw [show (l a * l b) * (b⁻¹ * a⁻¹) = (l a * a⁻¹) * (l b * b⁻¹) by ac_rfl]
      exact mul_mem (ha l hl) (hb l hl)
  have hUJ : commSub ⊤ L ≤ ⨆ i, J i := by
    rw [← hUc]
    change Subgroup.closure {c : W | ∃ x ∈ L, ∃ w ∈ commSub ⊤ L, x w * w⁻¹ = c} ≤
      ⨆ i, J i
    rw [Subgroup.closure_le]
    rintro c ⟨l, hl, x, hx, rfl⟩
    have hx' : x ∈ (commSub ⊤ L ⊓ fixV L) ⊔ ⨆ i, I i := by rw [hsup]; exact hx
    obtain ⟨z, hz, y, hy, hzy⟩ := Subgroup.mem_sup.mp hx'
    have hzL : l z = z := (mem_fixV.mp hz.2) l hl
    have hxy : l x * x⁻¹ = l y * y⁻¹ := by
      rw [← hzy, map_mul, mul_inv_rev, hzL]
      rw [show (z * l y) * (y⁻¹ * z⁻¹) = (z * z⁻¹) * (l y * y⁻¹) by ac_rfl]
      rw [mul_inv_cancel, one_mul]
    rw [hxy]
    exact hgen y hy l hl
  have hJU' : (⨆ i, J i) ≤ commSub ⊤ L := iSup_le fun i => hJU i
  have hUeq : commSub ⊤ L = ⨆ i, J i := le_antisymm hUJ hJU'
  have hJdim : ∀ i, rk ↥(J i) = rk ↥(J i ⊓ fixV L) + 3 := by
    intro i
    obtain ⟨K'', hK''f, hK''fin, hK''card, hres⟩ := hJnat i
    letI := hK''f
    letI := hK''fin
    have h := s16fh_rk_of_realizes_nat (d := 3) (a := 1) hK''card hres
    simpa using h
  have hJle4 : ∀ i, rk ↥(J i) ≤ 4 := by
    intro i
    have h1 := hJdim i
    have h2 := s16h_e3_l3_rk_inf_fixV_le_one hW hL3copy.1 (hJJ i) (hJnat i)
    omega
  have h4k : rk ↥(commSub ⊤ L) = 4 * k :=
    s16h_e3_l3_sum_rank_four L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) k hL3copy hd
  have hcardU : Nat.card ↥(commSub ⊤ L) ≤ ∏ i, Nat.card ↥(J i) := by
    rw [hUeq]
    exact CFSG.Quasithin.B513N.card_iSup_le_prod k J
  have hpow_le : 2 ^ (4 * k) ≤ 2 ^ ∑ i, rk ↥(J i) := by
    calc 2 ^ (4 * k) = 2 ^ rk ↥(commSub ⊤ L) := by rw [h4k]
      _ = Nat.card ↥(commSub ⊤ L) := (card_eq_two_pow hW (commSub ⊤ L)).symm
      _ ≤ ∏ i, Nat.card ↥(J i) := hcardU
      _ = ∏ i, 2 ^ rk ↥(J i) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          exact card_eq_two_pow hW (J i)
      _ = 2 ^ ∑ i, rk ↥(J i) :=
          Finset.prod_pow_eq_pow_sum Finset.univ (fun i => rk ↥(J i)) 2
  have hle_sum : 4 * k ≤ ∑ i, rk ↥(J i) :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow_le
  have hsum4 : (∑ i : Fin k, (4 : ℕ)) = 4 * k := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.mul_comm]
  have hsum_le : (∑ i, rk ↥(J i)) ≤ 4 * k := by
    calc (∑ i, rk ↥(J i)) ≤ ∑ i, (4 : ℕ) := Finset.sum_le_sum fun i _ => hJle4 i
      _ = 4 * k := hsum4
  have hsum_eq : (∑ i, rk ↥(J i)) = 4 * k := le_antisymm hsum_le hle_sum
  have hJrk : ∀ i, rk ↥(J i) = 4 := by
    intro i
    by_contra hne
    have hlt : rk ↥(J i) < 4 := lt_of_le_of_ne (hJle4 i) hne
    have hsum_lt : (∑ j, rk ↥(J j)) < ∑ j, (4 : ℕ) :=
      Finset.sum_lt_sum (fun j _ => hJle4 j) ⟨i, Finset.mem_univ i, hlt⟩
    rw [hsum_eq, hsum4] at hsum_lt
    exact lt_irrefl _ hsum_lt
  have hJfixrk : ∀ i, rk ↥(J i ⊓ fixV L) = 1 := by
    intro i
    have h1 := hJdim i
    have h2 := hJrk i
    omega
  have hJind : ∀ i, J i ⊓ ⨆ (j : Fin k) (_ : j ≠ i), J j = ⊥ := by
    intro i
    let J' : Subgroup W := ⨆ (j : Fin k) (_ : j ≠ i), J j
    have hUJ' : commSub ⊤ L = J i ⊔ J' := by
      rw [hUeq]
      apply le_antisymm
      · refine iSup_le fun j => ?_
        by_cases hji : j = i
        · subst hji
          exact le_sup_left
        · exact le_sup_of_le_right (le_iSup₂ (f := fun j (_ : j ≠ i) => J j) j hji)
      · apply sup_le
        · exact le_iSup (fun j => J j) i
        · refine iSup_le fun j => iSup_le fun hji => ?_
          exact le_iSup (fun j => J j) j
    have hcardJ' : Nat.card ↥J' ≤ 16 ^ (k - 1) := by
      let T : Fin k → Subgroup W := fun j => if j = i then ⊥ else J j
      have hJ'T : J' = ⨆ j, T j := by
        apply le_antisymm
        · refine iSup_le fun j => iSup_le fun hji => ?_
          have hTj : T j = J j := by simp [T, hji]
          rw [← hTj]
          exact le_iSup T j
        · refine iSup_le fun j => ?_
          by_cases hji : j = i
          · subst hji
            simp [T]
          · have hTj : T j = J j := by simp [T, hji]
            rw [hTj]
            exact le_iSup₂ (f := fun j (_ : j ≠ i) => J j) j hji
      have hcard1 : Nat.card ↥J' ≤ ∏ j, Nat.card ↥(T j) := by
        rw [hJ'T]
        exact CFSG.Quasithin.B513N.card_iSup_le_prod k T
      have hprod : ∏ j, Nat.card ↥(T j) = 16 ^ (k - 1) := by
        have hTi : Nat.card ↥(T i) = 1 := by
          have hbot : T i = ⊥ := by simp [T]
          rw [hbot, Subgroup.card_bot]
        rw [(Finset.prod_erase (s := Finset.univ) (f := fun j => Nat.card ↥(T j))
          (a := i) hTi).symm]
        calc ∏ j ∈ Finset.univ.erase i, Nat.card ↥(T j)
            = ∏ j ∈ Finset.univ.erase i, Nat.card ↥(J j) := by
              refine Finset.prod_congr rfl fun j hj => ?_
              have hji : j ≠ i := (Finset.mem_erase.mp hj).1
              have hTj : T j = J j := by simp [T, hji]
              rw [hTj]
          _ = ∏ j ∈ Finset.univ.erase i, (16 : ℕ) := by
              refine Finset.prod_congr rfl fun j _ => ?_
              rw [card_eq_two_pow hW (J j), hJrk j]
              norm_num
          _ = 16 ^ (k - 1) := by
              have h1 : (∏ j ∈ Finset.univ.erase i, (16 : ℕ)) =
                  16 ^ (Finset.univ.erase i).card := Finset.prod_const (16 : ℕ)
              rw [h1, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
                Fintype.card_fin]
      calc Nat.card ↥J' ≤ ∏ j, Nat.card ↥(T j) := hcard1
        _ = 16 ^ (k - 1) := hprod
    have hrkJ' : rk ↥J' ≤ 4 * (k - 1) := by
      apply s16h_e3_l3_rk_le_of_card_le
      calc Nat.card ↥J' ≤ 16 ^ (k - 1) := hcardJ'
        _ = 2 ^ (4 * (k - 1)) := by
            rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]
    have hsup_rank : rk ↥(commSub ⊤ L) + rk ↥(J i ⊓ J') = rk ↥(J i) + rk ↥J' := by
      have h := rk_sup_add_rk_inf (J i) J'
      rwa [← hUJ'] at h
    rw [h4k, hJrk i] at hsup_rank
    have hk_pos : 1 ≤ k := by
      have := i.isLt
      omega
    have hzero : rk ↥(J i ⊓ J') = 0 := by
      have hle : 4 + rk ↥J' ≤ 4 * k := by
        have := hrkJ'
        omega
      omega
    simpa only [J'] using (rk_eq_zero_iff hW).mp hzero
  exact ⟨{
    I := I
    J := J
    Z_le_I := hZI
    I_ind := hind
    I_nat := hnat
    J_le_I := hJI
    J_inv := hJinv
    J_comm := hJJ
    J_sup_Z := hJZ
    J_nat := hJnat
    J_rk := hJrk
    J_fix_rk := hJfixrk
    J_ind := hJind
    J_iSup := hUeq.symm }⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
