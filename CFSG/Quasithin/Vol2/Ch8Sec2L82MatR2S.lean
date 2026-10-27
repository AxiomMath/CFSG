module

public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatGen
public import CFSG.Quasithin.Background.HParabCode22

public section

namespace CFSG.Quasithin.H13.Mat

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Coc CFSG.Quasithin.H.Code22 CFSG.Quasithin.E3
  CFSG.Quasithin.H13

@[expose] def mb2B9 : List ℕ := [707, 369, 254, 68, 60, 19, 14, 3, 1]

@[expose] def mb2W8 : List ℕ := [513, 279, 149, 118, 49, 16, 13, 3]

@[expose] def mb2L2 : List ℕ := [16, 19, 152, 386, 336, 500, 435, 946]

theorem mb2B9_lt : ∀ a ∈ mb2B9, a < 2 ^ 10 := by decide +kernel

theorem mb2B9_nodup : (combos mb2B9).Nodup :=
  (nodup_of_nodupB _ 0 (by decide +kernel)).1

theorem mb2W8_lt : ∀ a ∈ mb2W8, a < 2 ^ 10 := by decide +kernel

theorem mb2W8_nodup : (combos mb2W8).Nodup :=
  (nodup_of_nodupB _ 0 (by decide +kernel)).1

theorem mb2L2_lt : ∀ a ∈ mb2L2, a < 2 ^ 10 := by decide +kernel

theorem mb2L2_nodup : (combos mb2L2).Nodup :=
  (nodup_of_nodupB _ 0 (by decide +kernel)).1

private theorem kcovB_r2s : ∀ l ∈ [149, 13, 282, 665, 227, 453, 945, 370],
    (∃ c ∈ [hbACols, hbBCols], ∃ j < 10, l = actM c (2 ^ j) ^^^ 2 ^ j) ∨
      l ∈ combos hbU0Basis := by
  decide +kernel

private theorem kW8a_r2s : ∀ j < 10, actM hbACols (2 ^ j) ^^^ 2 ^ j ∈ combos mb2W8 := by
  decide +kernel

private theorem kW8b_r2s : ∀ j < 10, actM hbBCols (2 ^ j) ^^^ 2 ^ j ∈ combos mb2W8 := by
  decide +kernel

private theorem kW8B_r2s : ∀ l ∈ mb2W8, l ∈ combos [149, 13, 282, 665, 227, 453, 945, 370] := by
  decide +kernel

private theorem kU0W8_r2s : ∀ u ∈ hbU0Basis, u ∈ combos mb2W8 := by decide +kernel

private theorem kW8B9_r2s : ∀ l ∈ mb2W8, l ∈ combos mb2B9 := by decide +kernel

private theorem kU0B9_r2s : ∀ u ∈ hbU0Basis, u ∈ combos mb2B9 := by decide +kernel

private theorem kaB9L2_r2s : ∀ b ∈ mb2B9, actM hbACols b ^^^ b ∈ combos mb2L2 := by
  decide +kernel

private theorem kbB9L2_r2s : ∀ b ∈ mb2B9, actM hbBCols b ^^^ b ∈ combos mb2L2 := by
  decide +kernel

private theorem kU0L2_r2s : ∀ u ∈ hbU0Basis, u ∈ combos mb2L2 := by decide +kernel

private theorem kL2B9_r2s : ∀ l ∈ mb2L2, l ∈ combos mb2B9 := by decide +kernel

private theorem kcovL2_r2s : ∀ l ∈ mb2L2, (∃ c ∈ [hbACols, hbBCols], ∃ b ∈ mb2B9,
    l = actM c b ^^^ b) ∨ l ∈ combos hbU0Basis := by
  decide +kernel

private theorem kQ16_r2s : ∀ t < 16, ∀ b ∈ mb2B9,
    actM (matOf 10 (actC10 (q16Arr t))) b ^^^ b ∈ combos hbU0Basis := by
  decide +kernel

private theorem mem_id_combos_r2s {c L L' : List ℕ}
    (hb : ∀ b ∈ L, actM c b ^^^ b ∈ combos L') :
    ∀ m ∈ combos L, actM c m ^^^ m ∈ combos L' := by
  intro m hm
  refine mem_of_combos (fun m => actM c m ^^^ m ∈ combos L') ?_ ?_ L hb m hm
  · show actM c 0 ^^^ 0 ∈ combos L'
    rw [Nat.xor_zero, (actM_xor c).map_zero]
    exact zero_mem_combos L'
  · intro a b ha hb'
    show actM c (a ^^^ b) ^^^ (a ^^^ b) ∈ combos L'
    have e : actM c (a ^^^ b) ^^^ (a ^^^ b) = (actM c a ^^^ a) ^^^ (actM c b ^^^ b) :=
      xorLin_actM_id c a b
    rw [e]
    exact xor_mem_combos L' ha hb'

private theorem mem_combos_sub_r2s {L L' : List ℕ} (h : ∀ a ∈ L, a ∈ combos L') :
    ∀ m ∈ combos L, m ∈ combos L' :=
  fun m hm => mem_of_combos (fun m => m ∈ combos L') (zero_mem_combos L')
    (fun a b ha hb => xor_mem_combos L' ha hb) L h m hm

private theorem maskSub_mono_r2s {n : ℕ} {L L' : List ℕ} (h : ∀ a ∈ L, a ∈ combos L') :
    maskSub n L ≤ maskSub n L' := by
  rintro _ ⟨m, hm, rfl⟩
  exact toW_mem_maskSub (mem_combos_sub_r2s h m hm)

private theorem rhoA_act_r2s :
    ActsBy (n := 10) (rhoC10 mog22 mog22_le_mog22plus ⟨hbA, hbA_mem⟩) hbACols := by
  have h := CFSG.Quasithin.H.Coc.actsBy_of_xorLin (n := 10) (xorLin_actC10 hbAArr)
    (fun m => rhoC10_toW mog22 mog22_le_mog22plus ⟨hbA, hbA_mem⟩ hasArr_hbA m)
  rw [hbCols_eq.1] at h
  exact h

private theorem rhoB_act_r2s :
    ActsBy (n := 10) (rhoC10 mog22 mog22_le_mog22plus ⟨hbB, hbB_mem⟩) hbBCols := by
  have h := CFSG.Quasithin.H.Coc.actsBy_of_xorLin (n := 10) (xorLin_actC10 hbBArr)
    (fun m => rhoC10_toW mog22 mog22_le_mog22plus ⟨hbB, hbB_mem⟩ hasArr_hbB m)
  rw [hbCols_eq.2.1] at h
  exact h

private theorem rhoA_mem_r2s :
    rhoC10 mog22 mog22_le_mog22plus ⟨hbA, hbA_mem⟩ ∈ imgC hbQ :=
  Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hbA_mem_Q)

private theorem rhoB_mem_r2s :
    rhoC10 mog22 mog22_le_mog22plus ⟨hbB, hbB_mem⟩ ∈ imgC hbQ :=
  Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hbB_mem_Q)

private theorem hbQ_rho_mem_r2s : ∀ τ ∈ hbQ, ∀ h : τ ∈ mog22,
    rhoC10 mog22 mog22_le_mog22plus ⟨τ, h⟩ ∈ Subgroup.closure
      ({rhoC10 mog22 mog22_le_mog22plus ⟨hbA, hbA_mem⟩,
        rhoC10 mog22 mog22_le_mog22plus ⟨hbB, hbB_mem⟩} : Set (MulAut W10)) := by
  intro τ hτ
  change τ ∈ Subgroup.closure ({hbA, hbB} : Set (Equiv.Perm (Fin 24))) at hτ
  induction hτ using Subgroup.closure_induction with
  | mem x hx =>
    intro h
    rcases hx with rfl | rfl
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  | one =>
    intro h
    have e : (⟨(1 : Equiv.Perm (Fin 24)), h⟩ : ↥mog22) = 1 := rfl
    rw [e, map_one]
    exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy =>
    intro h
    have hx' : x ∈ mog22 := hbQ_le hx
    have hy' : y ∈ mog22 := hbQ_le hy
    have e : (⟨x * y, h⟩ : ↥mog22) = ⟨x, hx'⟩ * ⟨y, hy'⟩ := Subtype.ext rfl
    rw [e, map_mul]
    exact Subgroup.mul_mem _ (ihx hx') (ihy hy')
  | inv x hx ihx =>
    intro h
    have hx' : x ∈ mog22 := hbQ_le hx
    have e : (⟨x⁻¹, h⟩ : ↥mog22) = (⟨x, hx'⟩ : ↥mog22)⁻¹ := Subtype.ext rfl
    rw [e, map_inv]
    exact Subgroup.inv_mem _ (ihx hx')

private theorem imgC_hbQ_eq_r2s : imgC hbQ = Subgroup.closure
    ({rhoC10 mog22 mog22_le_mog22plus ⟨hbA, hbA_mem⟩,
      rhoC10 mog22 mog22_le_mog22plus ⟨hbB, hbB_mem⟩} : Set (MulAut W10)) := by
  apply le_antisymm
  · rintro _ ⟨σ, hσ, rfl⟩
    exact hbQ_rho_mem_r2s _ (Subgroup.mem_subgroupOf.1 hσ) σ.2
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ (rfl | rfl)
    · exact rhoA_mem_r2s
    · exact rhoB_mem_r2s

private theorem hcovB_r2s : ∀ l ∈ [149, 13, 282, 665, 227, 453, 945, 370],
    (∃ g ∈ ({rhoC10 mog22 mog22_le_mog22plus ⟨hbA, hbA_mem⟩,
      rhoC10 mog22 mog22_le_mog22plus ⟨hbB, hbB_mem⟩} : Set (MulAut W10)), ∃ c, ActsBy g c ∧
      ∃ j < 10, l = actM c (2 ^ j) ^^^ 2 ^ j) ∨ l ∈ combos hbU0Basis := by
  intro l hl
  rcases kcovB_r2s l hl with ⟨c, hc, j, hj, hl'⟩ | hU
  · left
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨_, Set.mem_insert _ _, hbACols, rhoA_act_r2s, j, hj, hl'⟩
    · exact ⟨_, Set.mem_insert_of_mem _ rfl, hbBCols, rhoB_act_r2s, j, hj, hl'⟩
  · exact Or.inr hU

private theorem hcovL2_r2s : ∀ l ∈ mb2L2, (∃ g ∈ ({rhoC10 mog22 mog22_le_mog22plus ⟨hbA, hbA_mem⟩,
      rhoC10 mog22 mog22_le_mog22plus ⟨hbB, hbB_mem⟩} : Set (MulAut W10)), ∃ c, ActsBy g c ∧
      ∃ b ∈ mb2B9, l = actM c b ^^^ b) ∨ l ∈ combos hbU0Basis := by
  intro l hl
  rcases kcovL2_r2s l hl with ⟨c, hc, b, hb, hl'⟩ | hU
  · left
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨_, Set.mem_insert _ _, hbACols, rhoA_act_r2s, b, hb, hl'⟩
    · exact ⟨_, Set.mem_insert_of_mem _ rfl, hbBCols, rhoB_act_r2s, b, hb, hl'⟩
  · exact Or.inr hU

theorem std2_commP_sup : commV (imgC hbQ) ⊔ UC = maskSub 10 mb2W8 := by
  apply le_antisymm
  · refine sup_le ?_ (maskSub_mono_r2s (n := 10) kU0W8_r2s)
    rw [imgC_hbQ_eq_r2s]
    refine commV_closure_le_maskSub (n := 10) (L := mb2W8) ?_
    rintro _ (rfl | rfl)
    · exact ⟨hbACols, rhoA_act_r2s, kW8a_r2s⟩
    · exact ⟨hbBCols, rhoB_act_r2s, kW8b_r2s⟩
  · rw [imgC_hbQ_eq_r2s]
    exact le_trans (maskSub_mono_r2s (n := 10) kW8B_r2s)
      (maskSub_le_commV_sup (n := 10)
        (S := ({rhoC10 mog22 mog22_le_mog22plus ⟨hbA, hbA_mem⟩,
          rhoC10 mog22 mog22_le_mog22plus ⟨hbB, hbB_mem⟩} : Set (MulAut W10)))
        (L := [149, 13, 282, 665, 227, 453, 945, 370]) (Ub := hbU0Basis) hcovB_r2s)

theorem std2_W8_le_B9 : maskSub 10 mb2W8 ≤ maskSub 10 mb2B9 :=
  maskSub_mono_r2s kW8B9_r2s

theorem std2_commP_le_B9 : commV (imgC hbQ) ≤ maskSub 10 mb2B9 :=
  le_trans le_sup_left (le_trans (le_of_eq std2_commP_sup) std2_W8_le_B9)

private theorem UC_le_B9_r2s : UC ≤ maskSub 10 mb2B9 := maskSub_mono_r2s kU0B9_r2s

private theorem hB_clos_r2s : ∀ s ∈ Subgroup.closure
      ({rhoC10 mog22 mog22_le_mog22plus ⟨hbA, hbA_mem⟩,
        rhoC10 mog22 mog22_le_mog22plus ⟨hbB, hbB_mem⟩} : Set (MulAut W10)),
    ∀ w ∈ maskSub 10 mb2B9, s w ∈ maskSub 10 mb2B9 := by
  have h := invariant_of_commV_le_mat std2_commP_le_B9
  rw [imgC_hbQ_eq_r2s] at h
  exact h

private theorem hS_r2s : ∀ s ∈ ({rhoC10 mog22 mog22_le_mog22plus ⟨hbA, hbA_mem⟩,
      rhoC10 mog22 mog22_le_mog22plus ⟨hbB, hbB_mem⟩} : Set (MulAut W10)),
    ∀ w ∈ maskSub 10 mb2B9, s w * w⁻¹ ∈ maskSub 10 mb2L2 := by
  rintro _ (rfl | rfl) _ ⟨m, hm, rfl⟩
  · have e := comm_toW_mat rhoA_act_r2s m
    exact Eq.mpr (congrArg (· ∈ maskSub 10 mb2L2) e)
      (toW_mem_maskSub (mem_id_combos_r2s kaB9L2_r2s m hm))
  · have e := comm_toW_mat rhoB_act_r2s m
    exact Eq.mpr (congrArg (· ∈ maskSub 10 mb2L2) e)
      (toW_mem_maskSub (mem_id_combos_r2s kbB9L2_r2s m hm))

theorem std2_BPrime_eq
    (Xs : Subgroup (MulAut W10)) (hU : fixV Xs = UC) (h1 : commV Xs ≤ maskSub 10 mb2B9)
    (h2 : ¬ commV Xs ≤ maskSub 10 mb2W8) :
    s828BPrime (imgC mog22) Xs = maskSub 10 mb2B9 := by
  have hP : perfectCore (imgC mog22 ⊓ stabSub (fixV Xs)) = imgC hbQ :=
    (congrArg (fun U => perfectCore (imgC mog22 ⊓ stabSub U)) hU).trans perfectCore_stab_UC
  have e1 : s828BPrime (imgC mog22) Xs = commV Xs ⊔ commV (imgC hbQ) ⊔ UC :=
    congrArg₂ (· ⊔ ·) (congrArg₂ (· ⊔ ·) rfl (congrArg commV hP)) hU
  have hB9 : commV Xs ⊔ commV (imgC hbQ) ⊔ UC ≤ maskSub 10 mb2B9 :=
    sup_le (sup_le h1 std2_commP_le_B9) UC_le_B9_r2s
  have hW8 : maskSub 10 mb2W8 ≤ commV Xs ⊔ commV (imgC hbQ) ⊔ UC := by
    rw [← std2_commP_sup]
    exact sup_le
      ((le_sup_right : commV (imgC hbQ) ≤ commV Xs ⊔ commV (imgC hbQ)).trans le_sup_left)
      le_sup_right
  have hXB : commV Xs ≤ commV Xs ⊔ commV (imgC hbQ) ⊔ UC :=
    (le_sup_left : commV Xs ≤ commV Xs ⊔ commV (imgC hbQ)).trans le_sup_left
  have hnot : ¬ commV Xs ⊔ commV (imgC hbQ) ⊔ UC ≤ maskSub 10 mb2W8 :=
    fun h => h2 (hXB.trans h)
  have hc8 : Nat.card ↥(maskSub 10 mb2W8) = 2 ^ 8 :=
    (card_maskSub mb2W8_lt mb2W8_nodup).trans (by decide)
  have hc9 : Nat.card ↥(maskSub 10 mb2B9) = 2 ^ 9 :=
    (card_maskSub mb2B9_lt mb2B9_nodup).trans (by decide)
  have hdvd1 : Nat.card ↥(maskSub 10 mb2W8) ∣ Nat.card ↥(commV Xs ⊔ commV (imgC hbQ) ⊔ UC) :=
    Subgroup.card_dvd_of_le hW8
  have hdvd2 : Nat.card ↥(commV Xs ⊔ commV (imgC hbQ) ⊔ UC) ∣ 2 ^ 9 := by
    rw [← hc9]
    exact Subgroup.card_dvd_of_le hB9
  rw [hc8] at hdvd1
  obtain ⟨i, hi, hBi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd2
  have hle8 : 2 ^ 8 ≤ Nat.card ↥(commV Xs ⊔ commV (imgC hbQ) ⊔ UC) :=
    Nat.le_of_dvd Nat.card_pos hdvd1
  have h8i : 8 ≤ i := by
    have h' : 2 ^ 8 ≤ 2 ^ i := by
      rw [← hBi]
      exact hle8
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h'
  have hBeq : commV Xs ⊔ commV (imgC hbQ) ⊔ UC = maskSub 10 mb2B9 := by
    rcases (show i = 8 ∨ i = 9 by omega) with rfl | rfl
    · exfalso
      have hcard : Nat.card ↥(commV Xs ⊔ commV (imgC hbQ) ⊔ UC) ≤ Nat.card ↥(maskSub 10 mb2W8) :=
        le_of_eq (hBi.trans hc8.symm)
      have heq : maskSub 10 mb2W8 = commV Xs ⊔ commV (imgC hbQ) ⊔ UC :=
        Subgroup.eq_of_le_of_card_ge hW8 hcard
      exact hnot (le_of_eq heq.symm)
    · have hcard : Nat.card ↥(maskSub 10 mb2B9) ≤ Nat.card ↥(commV Xs ⊔ commV (imgC hbQ) ⊔ UC) :=
        le_of_eq (hc9.trans hBi.symm)
      exact Subgroup.eq_of_le_of_card_ge hB9 hcard
  exact e1.trans hBeq

theorem std2_mQuot : mQuot ⊤ (maskSub 10 mb2B9) = 1 :=
  (mQuot_top_maskSub mb2B9_lt mb2B9_nodup).trans (by decide)

theorem std2_MB1 : (s828CommSub (imgC hbQ) (maskSub 10 mb2B9) ⊔ UC).relIndex
    (maskSub 10 mb2B9) = 2 := by
  have hD : s828CommSub (imgC hbQ) (maskSub 10 mb2B9) ⊔ UC = maskSub 10 mb2L2 := by
    apply le_antisymm
    · refine sup_le ?_ (maskSub_mono_r2s (n := 10) kU0L2_r2s)
      rw [imgC_hbQ_eq_r2s]
      exact s828CommSub_closure_le _ _ _ hB_clos_r2s hS_r2s
    · rw [imgC_hbQ_eq_r2s]
      exact maskSub_le_commSub_sup (n := 10)
        (S := ({rhoC10 mog22 mog22_le_mog22plus ⟨hbA, hbA_mem⟩,
          rhoC10 mog22 mog22_le_mog22plus ⟨hbB, hbB_mem⟩} : Set (MulAut W10)))
        (L := mb2B9) (L2 := mb2L2) (Ub := hbU0Basis) hcovL2_r2s
  rw [hD]
  exact (relIndex_maskSub mb2L2_lt mb2L2_nodup mb2B9_lt mb2B9_nodup
    (maskSub_mono_r2s kL2B9_r2s)).trans (by decide)

theorem std2_trivK : ∀ x ∈ imgC Q16P, ∀ b ∈ maskSub 10 mb2B9, x b * b⁻¹ ∈ UC := by
  rintro _ ⟨σ, hσ, rfl⟩ _ ⟨m, hm, rfl⟩
  obtain ⟨t, ht⟩ := mem_Q16P.1 (Subgroup.mem_subgroupOf.1 hσ)
  have ha : HasArr (σ : Equiv.Perm (Fin 24)) (q16Arr t) := by
    rw [← ht]
    exact hasArr_q16P t
  have hA := CFSG.Quasithin.H.Coc.actsBy_of_xorLin (n := 10) (xorLin_actC10 (q16Arr t))
    (fun m => rhoC10_toW mog22 mog22_le_mog22plus σ ha m)
  have hc := comm_toW_mat hA m
  have hkey := mem_id_combos_r2s (kQ16_r2s (t : ℕ) t.2) m hm
  exact Eq.mpr (congrArg (· ∈ UC) hc) (toW_mem_maskSub hkey)

end CFSG.Quasithin.H13.Mat
