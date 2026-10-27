module

public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatGen
public import CFSG.Quasithin.Background.HLUCode24

public section

namespace CFSG.Quasithin.H13.Mat

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Coc CFSG.Quasithin.H.LU24 CFSG.Quasithin.E3
  CFSG.Quasithin.H13

@[expose] def mb3L10 : List ℕ := [948, 1572, 1355, 82, 1562, 568, 143, 671, 1894, 1477]

@[expose] def mb3L2 : List ℕ := [1987, 247, 924, 225, 1575, 1015, 1477, 848, 675, 302]

theorem mb3L10_lt : ∀ a ∈ mb3L10, a < 2 ^ 11 := by decide +kernel

theorem mb3L10_nodup : (combos mb3L10).Nodup :=
  (nodup_of_nodupB _ 0 (by decide +kernel)).1

theorem imgCd_P0_eq_r3s :
    imgCd sxP0 = Subgroup.closure ({rhoCd sxG1_mem, rhoCd sxG2_mem} : Set (MulAut W11)) := by
  have hS : ({sxG1, sxG2} : Set (Equiv.Perm (Fin 24))) ⊆ AutPerm := by
    rintro _ (rfl | rfl)
    · exact sxG1_mem
    · exact sxG2_mem
  refine le_antisymm (imgCd_closure_le hS ?_) ?_
  · rintro _ (rfl | rfl)
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ (rfl | rfl)
    · exact rhoCd_mem_imgCd sxG1_mem sxG1_mem_P0
    · exact rhoCd_mem_imgCd sxG2_mem sxG2_mem_P0

theorem commV_mono_r3s {X Y : Subgroup (MulAut W11)} (h : X ≤ Y) : commV X ≤ commV Y := by
  unfold commV
  exact Subgroup.closure_mono fun x ⟨y, hy, v, hyv⟩ => ⟨y, h hy, v, hyv⟩

theorem s828CommSub_mono_Y_r3s {Y Y' : Subgroup (MulAut W11)} (h : Y ≤ Y') (B : Subgroup W11) :
    s828CommSub Y B ≤ s828CommSub Y' B := by
  unfold s828CommSub
  exact Subgroup.closure_mono fun x ⟨y, hy, w, hw, hx⟩ => ⟨y, h hy, w, hw, hx⟩

theorem k1_r3s : ∀ j : ℕ, j < 11 → (actM sxG1C (2 ^ j) ^^^ 2 ^ j) ∈ combos mb3L10 := by
  decide +kernel

theorem k2_r3s : ∀ j : ℕ, j < 11 → (actM sxG2C (2 ^ j) ^^^ 2 ^ j) ∈ combos mb3L10 := by
  decide +kernel

theorem gens_r3s : ∀ g ∈ ({rhoCd sxG1_mem, rhoCd sxG2_mem} : Set (MulAut W11)),
    ∃ c, ActsBy g c ∧ ∀ j < 11, (actM c (2 ^ j) ^^^ 2 ^ j) ∈ combos mb3L10 := by
  rintro g (rfl | rfl)
  · exact ⟨sxG1C, actsBy_sxG1, k1_r3s⟩
  · exact ⟨sxG2C, actsBy_sxG2, k2_r3s⟩

theorem gen10_r3s : ∀ l ∈ mb3L10, (∃ j : ℕ, j < 11 ∧ l = actM sxG1C (2 ^ j) ^^^ 2 ^ j) ∨
    (∃ j : ℕ, j < 11 ∧ l = actM sxG2C (2 ^ j) ^^^ 2 ^ j) ∨ l ∈ combos uSBasis := by
  decide +kernel

theorem gen2_r3s : ∀ l ∈ mb3L2, (∃ b ∈ mb3L10, l = actM sxG1C b ^^^ b) ∨
    (∃ b ∈ mb3L10, l = actM sxG2C b ^^^ b) ∨ l ∈ combos uSBasis := by
  decide +kernel

theorem mb3L10_cover_r3s : ∀ l ∈ mb3L10, l ∈ combos mb3L2 := by decide +kernel

theorem uS_sub_r3s : ∀ u ∈ uSBasis, u ∈ combos mb3L10 := by decide +kernel

theorem trivK_r3s : ∀ i : ℕ, i < 6 → ∀ b ∈ mb3L10, (actM (ksC6 i) b ^^^ b) ∈ combos uSBasis := by
  decide +kernel

theorem gen10_S_r3s : ∀ l ∈ mb3L10, (∃ g ∈ ({rhoCd sxG1_mem, rhoCd sxG2_mem} : Set (MulAut W11)),
    ∃ c, ActsBy g c ∧ ∃ j : ℕ, j < 11 ∧ l = actM c (2 ^ j) ^^^ 2 ^ j) ∨ l ∈ combos uSBasis := by
  intro l hl
  rcases gen10_r3s l hl with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | hU
  · exact Or.inl ⟨rhoCd sxG1_mem, Set.mem_insert _ _, sxG1C, actsBy_sxG1, j, hj, rfl⟩
  · exact Or.inl ⟨rhoCd sxG2_mem, Set.mem_insert_of_mem _ rfl, sxG2C, actsBy_sxG2, j, hj, rfl⟩
  · exact Or.inr hU

theorem gen2_S_r3s : ∀ l ∈ mb3L2, (∃ g ∈ ({rhoCd sxG1_mem, rhoCd sxG2_mem} : Set (MulAut W11)),
    ∃ c, ActsBy g c ∧ ∃ b ∈ mb3L10, l = actM c b ^^^ b) ∨ l ∈ combos uSBasis := by
  intro l hl
  rcases gen2_r3s l hl with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩ | hU
  · exact Or.inl ⟨rhoCd sxG1_mem, Set.mem_insert _ _, sxG1C, actsBy_sxG1, b, hb, rfl⟩
  · exact Or.inl ⟨rhoCd sxG2_mem, Set.mem_insert_of_mem _ rfl, sxG2C, actsBy_sxG2, b, hb, rfl⟩
  · exact Or.inr hU

theorem US_le_mb_r3s : maskSub 11 uSBasis ≤ maskSub 11 mb3L10 := by
  rintro _ ⟨m, hm, rfl⟩
  exact toW_mem_maskSub (mem_of_combos (fun k => k ∈ combos mb3L10) (zero_mem_combos mb3L10)
    (fun a b ha hb => xor_mem_combos mb3L10 ha hb) uSBasis uS_sub_r3s m hm)

theorem std3_commV_sup : commV (imgCd sxP0) ⊔ US = maskSub 11 mb3L10 := by
  refine le_antisymm (sup_le ?_ US_le_mb_r3s) ?_
  · exact (commV_mono_r3s (le_of_eq imgCd_P0_eq_r3s)).trans
      (commV_closure_le_maskSub (n := 11) gens_r3s)
  · exact (maskSub_le_commV_sup (n := 11)
      (S := ({rhoCd sxG1_mem, rhoCd sxG2_mem} : Set (MulAut W11))) (L := mb3L10)
      (Ub := uSBasis) gen10_S_r3s).trans
      (sup_le_sup_right (commV_mono_r3s (le_of_eq imgCd_P0_eq_r3s.symm)) _)

theorem std3_mQuot : mQuot ⊤ (maskSub 11 mb3L10) = 1 :=
  (mQuot_top_maskSub mb3L10_lt mb3L10_nodup).trans (by decide)

theorem std3_MB1 : s828CommSub (imgCd sxP0) (maskSub 11 mb3L10) ⊔ US = maskSub 11 mb3L10 := by
  have hC : commV (imgCd sxP0) ≤ maskSub 11 mb3L10 :=
    (le_sup_left : commV (imgCd sxP0) ≤ commV (imgCd sxP0) ⊔ US).trans (le_of_eq std3_commV_sup)
  refine le_antisymm (sup_le ((s828CommSub_le_commV (imgCd sxP0) (maskSub 11 mb3L10)).trans hC)
    US_le_mb_r3s) ?_
  have h := maskSub_le_commSub_sup_of_cover (n := 11)
    (S := ({rhoCd sxG1_mem, rhoCd sxG2_mem} : Set (MulAut W11)))
    (L := mb3L10) (L2 := mb3L2) (Ub := uSBasis) gen2_S_r3s mb3L10_cover_r3s
  exact h.trans (sup_le_sup_right
    (s828CommSub_mono_Y_r3s (le_of_eq imgCd_P0_eq_r3s.symm) (maskSub 11 mb3L10)) _)

theorem std3_trivK : ∀ x ∈ imgCd sxKS, ∀ b ∈ maskSub 11 mb3L10, x b * b⁻¹ ∈ US := by
  have hSub : Set.range (fun i : Fin 6 => ks6P i) ⊆ AutPerm := by
    rintro _ ⟨i, rfl⟩
    exact ks6_autPerm i
  have hK : imgCd sxKS ≤
      Subgroup.closure (Set.range (fun i : Fin 6 => rhoCd (ks6_autPerm i))) := by
    refine imgCd_closure_le hSub ?_
    rintro _ ⟨i, rfl⟩
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hgen : ∀ g ∈ Set.range (fun i : Fin 6 => rhoCd (ks6_autPerm i)), ∃ c, ActsBy g c ∧
      ∀ b ∈ mb3L10, (actM c b ^^^ b) ∈ combos uSBasis := by
    rintro _ ⟨i, rfl⟩
    exact ⟨ksC6 i, actsBy_ks6 i.2, fun b hb => trivK_r3s i i.2 b hb⟩
  intro x hx b hb
  exact mem_trivOnAut.1 ((closure_le_trivOnAut US_le_mb_r3s hgen) (hK hx)) b hb

end CFSG.Quasithin.H13.Mat
