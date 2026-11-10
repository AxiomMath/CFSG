module

public import CFSG.Quasithin.Background.HParabL34
public import CFSG.Quasithin.Background.HMathieuO2Data

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin.H.L34Z CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H13.Ch9.Herm9 CFSG.Quasithin.E3

@[expose] def mbL8_mb : List ℕ := [33, 1, 8, 24, 65, 130, 2, 258]

theorem mbL8_mb_lt : ∀ a ∈ mbL8_mb, a < 2 ^ 9 := by decide +kernel

theorem mbL8_mb_nodup : (combos mbL8_mb).Nodup := by decide +kernel

theorem mbQ_basis_mem_mb : ∀ t < 16, ∀ j < 9,
    (actM (colsS1.getD (4 * t) []) (2 ^ j) ^^^ 2 ^ j) ∈ combos mbL8_mb := by
  decide +kernel

theorem mbP_basis_mem_mb : ∀ c ∈ [colsX2, colsY2], ∀ j < 9,
    (actM c (2 ^ j) ^^^ 2 ^ j) ∈ combos mbL8_mb := by
  decide +kernel

theorem mbP_inv_mem_mb : ∀ c ∈ [colsX2, colsY2, colsX2i, colsY2i], ∀ l ∈ mbL8_mb,
    actM c l ∈ combos mbL8_mb := by
  decide +kernel

theorem mbQ_mod_U0_mb : ∀ t < 16, ∀ l ∈ mbL8_mb,
    (actM (colsS1.getD (4 * t) []) l ^^^ l) ∈ combos [1, 2, 8, 16] := by
  decide +kernel

theorem mbU0_sub_mb : ∀ m ∈ combos [1, 2, 8, 16], m ∈ combos mbL8_mb := by
  decide +kernel

theorem xorLin_actM_id_mb (cs : List ℕ) : XorLin (fun m => actM cs m ^^^ m) := by
  intro a b
  show actM cs (a ^^^ b) ^^^ (a ^^^ b) = (actM cs a ^^^ a) ^^^ (actM cs b ^^^ b)
  rw [actM_xor cs a b]
  ac_rfl

theorem actM_id_mem_mb (c : List ℕ) (h : ∀ j < 9, (actM c (2 ^ j) ^^^ 2 ^ j) ∈ combos mbL8_mb)
    {m : ℕ} (hm : m < 512) : actM c m ^^^ m ∈ combos mbL8_mb := by
  have hm' : m < 2 ^ 9 := by norm_num; exact hm
  exact mem_combos_of_xorLin (f := fun m => actM c m ^^^ m) (xorLin_actM_id_mb c)
    (fun j hj => h j hj) m hm'

theorem actM_mem_combos_mb (c : List ℕ) (h : ∀ l ∈ mbL8_mb, actM c l ∈ combos mbL8_mb)
    {m : ℕ} (hm : m ∈ combos mbL8_mb) : actM c m ∈ combos mbL8_mb := by
  refine mem_of_combos (fun m => actM c m ∈ combos mbL8_mb) ?_ ?_ mbL8_mb h m hm
  · rw [(actM_xor c).map_zero]
    exact zero_mem_combos _
  · intro a b ha hb
    rw [actM_xor c a b]
    exact xor_mem_combos _ ha hb

theorem toW_inv_mb (a : ℕ) : (toW 9 a)⁻¹ = toW 9 a := by
  apply inv_eq_of_mul_eq_one_right
  have h := toW_xor 9 a a
  rw [Nat.xor_self, toW_zero] at h
  exact h.symm

theorem comm_mul_mb {V : Type} [CommGroup V] (x : MulAut V) (a b : V) :
    x (a * b) * (a * b)⁻¹ = (x a * a⁻¹) * (x b * b⁻¹) := by
  rw [map_mul, mul_inv]
  ac_rfl

theorem comm_one_mb {V : Type} [CommGroup V] (x : MulAut V) : x 1 * (1 : V)⁻¹ = 1 := by
  simp

theorem rho9_vG_toW_mb {t : ℕ} (ht : t < 16) {m : ℕ} (hm : m < 512) :
    rho9 (vG t) (toW 9 m) = toW 9 (actM (colsS1.getD (4 * t) []) m) :=
  rho9_toW_cols (vG t) (cols_vG ht) hm

theorem rho9_x2_toW_mb {m : ℕ} (hm : m < 512) : rho9 x2G (toW 9 m) = toW 9 (actM colsX2 m) :=
  rho9_toW_cols x2G cols_x2.1 hm

theorem rho9_y2_toW_mb {m : ℕ} (hm : m < 512) : rho9 y2G (toW 9 m) = toW 9 (actM colsY2 m) :=
  rho9_toW_cols y2G cols_x2.2.1 hm

theorem rho9_x2i_toW_mb {m : ℕ} (hm : m < 512) :
    (rho9 x2G)⁻¹ (toW 9 m) = toW 9 (actM colsX2i m) := by
  rw [← map_inv]
  exact rho9_toW_cols x2G⁻¹ cols_x2.2.2.1 hm

theorem rho9_y2i_toW_mb {m : ℕ} (hm : m < 512) :
    (rho9 y2G)⁻¹ (toW 9 m) = toW 9 (actM colsY2i m) := by
  rw [← map_inv]
  exact rho9_toW_cols y2G⁻¹ cols_x2.2.2.2 hm

theorem comm_vG_toW_mb {t : ℕ} (ht : t < 16) {m : ℕ} (hm : m < 512) :
    rho9 (vG t) (toW 9 m) * (toW 9 m)⁻¹ = toW 9 (actM (colsS1.getD (4 * t) []) m ^^^ m) := by
  rw [rho9_vG_toW_mb ht hm, toW_inv_mb]
  exact (toW_xor 9 _ _).symm

theorem comm_x2_toW_mb {m : ℕ} (hm : m < 512) :
    rho9 x2G (toW 9 m) * (toW 9 m)⁻¹ = toW 9 (actM colsX2 m ^^^ m) := by
  rw [rho9_x2_toW_mb hm, toW_inv_mb]
  exact (toW_xor 9 _ _).symm

theorem comm_y2_toW_mb {m : ℕ} (hm : m < 512) :
    rho9 y2G (toW 9 m) * (toW 9 m)⁻¹ = toW 9 (actM colsY2 m ^^^ m) := by
  rw [rho9_y2_toW_mb hm, toW_inv_mb]
  exact (toW_xor 9 _ _).symm

theorem mask_lt_512_mb {m : ℕ} (hm : m ∈ combos mbL8_mb) : m < 512 := by
  have h := combos_lt (n := 9) mbL8_mb_lt m hm
  norm_num at h
  exact h

theorem mask_lt_512_of_pow_mb {m : ℕ} (hm : m < 2 ^ 9) : m < 512 := by
  norm_num at hm
  exact hm

theorem commQ_le_mb : CFSG.Quasithin.commV QW9 ≤ maskSub 9 mbL8_mb := by
  unfold CFSG.Quasithin.commV
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨g, hg, v, rfl⟩
  obtain ⟨t, ht, rfl⟩ := mem_QW9.1 hg
  obtain ⟨m, hm, rfl⟩ := toW_surj 9 v
  have hm' := mask_lt_512_of_pow_mb hm
  exact mem_maskSub.2 ⟨_, actM_id_mem_mb _ (mbQ_basis_mem_mb t ht) hm', (comm_vG_toW_mb ht hm').symm⟩

theorem comm_closure_le_mb {V : Type} [CommGroup V] (S : Set (MulAut V)) (W : Subgroup V)
    (hS : ∀ s ∈ S, (∀ w ∈ W, s w ∈ W) ∧ (∀ w ∈ W, s⁻¹ w ∈ W))
    (hgen : ∀ s ∈ S, ∀ v : V, s v * v⁻¹ ∈ W) :
    CFSG.Quasithin.commV (Subgroup.closure S) ≤ W := by
  have key : ∀ g ∈ Subgroup.closure S, (∀ v : V, g v * v⁻¹ ∈ W) ∧ (∀ w ∈ W, g w ∈ W) ∧
      (∀ w ∈ W, g⁻¹ w ∈ W) := by
    intro g hg
    refine Subgroup.closure_induction (p := fun g _ => (∀ v : V, g v * v⁻¹ ∈ W) ∧
      (∀ w ∈ W, g w ∈ W) ∧ (∀ w ∈ W, g⁻¹ w ∈ W)) ?_ ?_ ?_ ?_ hg
    · intro x hx
      exact ⟨hgen x hx, (hS x hx).1, (hS x hx).2⟩
    · exact ⟨fun v => by simpa using W.one_mem, fun w hw => by simpa using hw,
        fun w hw => by simpa using hw⟩
    · intro x y _ _ hx hy
      refine ⟨fun v => ?_, fun w hw => hx.2.1 _ (hy.2.1 w hw), fun w hw => ?_⟩
      · have e : (x * y) v * v⁻¹ = x (y v * v⁻¹) * (x v * v⁻¹) := by
          rw [MulAut.mul_apply, map_mul, map_inv]
          group
        rw [e]
        exact W.mul_mem (hx.2.1 _ (hy.1 v)) (hx.1 v)
      · rw [mul_inv_rev, MulAut.mul_apply]
        exact hy.2.2 _ (hx.2.2 w hw)
    · intro x _ hx
      refine ⟨fun v => ?_, fun w hw => hx.2.2 w hw, fun w hw => ?_⟩
      · obtain ⟨u, rfl⟩ : ∃ u, v = x u := ⟨x⁻¹ v, by simp⟩
        have hu := W.inv_mem (hx.1 u)
        have e : x⁻¹ (x u) * (x u)⁻¹ = (x u * u⁻¹)⁻¹ := by
          rw [MulAut.inv_apply_self]
          group
        rw [e]
        exact hu
      · rw [inv_inv]
        exact hx.2.1 w hw
  unfold CFSG.Quasithin.commV
  rw [Subgroup.closure_le]
  rintro _ ⟨g, hg, v, rfl⟩
  exact (key g hg).1 v


theorem commP_le_mb : CFSG.Quasithin.commV P2 ≤ maskSub 9 mbL8_mb := by
  unfold P2
  refine comm_closure_le_mb _ _ ?_ ?_
  · rintro s (rfl | rfl)
    · refine ⟨fun w hw => ?_, fun w hw => ?_⟩
      · obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 hw
        exact mem_maskSub.2 ⟨actM colsX2 m, actM_mem_combos_mb colsX2
          (mbP_inv_mem_mb colsX2 (by simp)) hm, (rho9_x2_toW_mb (mask_lt_512_mb hm)).symm⟩
      · obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 hw
        exact mem_maskSub.2 ⟨actM colsX2i m, actM_mem_combos_mb colsX2i
          (mbP_inv_mem_mb colsX2i (by simp)) hm, (rho9_x2i_toW_mb (mask_lt_512_mb hm)).symm⟩
    · refine ⟨fun w hw => ?_, fun w hw => ?_⟩
      · obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 hw
        exact mem_maskSub.2 ⟨actM colsY2 m, actM_mem_combos_mb colsY2
          (mbP_inv_mem_mb colsY2 (by simp)) hm, (rho9_y2_toW_mb (mask_lt_512_mb hm)).symm⟩
      · obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 hw
        exact mem_maskSub.2 ⟨actM colsY2i m, actM_mem_combos_mb colsY2i
          (mbP_inv_mem_mb colsY2i (by simp)) hm, (rho9_y2i_toW_mb (mask_lt_512_mb hm)).symm⟩
  · rintro s (rfl | rfl) v
    · obtain ⟨m, hm, rfl⟩ := toW_surj 9 v
      have hm' := mask_lt_512_of_pow_mb hm
      exact mem_maskSub.2 ⟨_, actM_id_mem_mb colsX2 (mbP_basis_mem_mb colsX2 (by simp)) hm',
        (comm_x2_toW_mb hm').symm⟩
    · obtain ⟨m, hm, rfl⟩ := toW_surj 9 v
      have hm' := mask_lt_512_of_pow_mb hm
      exact mem_maskSub.2 ⟨_, actM_id_mem_mb colsY2 (mbP_basis_mem_mb colsY2 (by simp)) hm',
        (comm_y2_toW_mb hm').symm⟩

noncomputable abbrev BStd_mb : Subgroup W9 :=
  CFSG.Quasithin.commV QW9 ⊔ CFSG.Quasithin.commV P2 ⊔ U0

theorem U0_le_mb : U0 ≤ maskSub 9 mbL8_mb := by
  intro w hw
  obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 hw
  exact toW_mem_maskSub (mbU0_sub_mb m hm)

theorem BStd_le_mb : BStd_mb ≤ maskSub 9 mbL8_mb :=
  sup_le (sup_le commQ_le_mb commP_le_mb) U0_le_mb

theorem mbL8_mem_BStd_mb : ∀ l ∈ mbL8_mb, toW 9 l ∈ BStd_mb := by
  have hU : ∀ l ∈ ([1, 2, 8, 24] : List ℕ), toW 9 l ∈ BStd_mb := by
    intro l hl
    have hmem : toW 9 l ∈ U0 := toW_mem_maskSub (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl <;> decide)
    exact Subgroup.mem_sup_right hmem
  have hK : ∀ t m l : ℕ, t < 16 → m < 512 → actM (colsS1.getD (4 * t) []) m ^^^ m = l →
      toW 9 l ∈ BStd_mb := by
    intro t m l ht hm h
    have hc0 : rho9 (vG t) (toW 9 m) * (toW 9 m)⁻¹ ∈ CFSG.Quasithin.commV QW9 :=
      Subgroup.subset_closure ⟨rho9 (vG t), mem_QW9.2 ⟨t, ht, rfl⟩, toW 9 m, rfl⟩
    have e : toW 9 l = rho9 (vG t) (toW 9 m) * (toW 9 m)⁻¹ := by
      rw [← h]
      exact (comm_vG_toW_mb ht hm).symm
    have hc : toW 9 l ∈ CFSG.Quasithin.commV QW9 := e ▸ hc0
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hc)
  intro l hl
  simp only [mbL8_mb, List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hK 1 4 33 (by norm_num) (by norm_num) (by decide +kernel)
  · exact hU 1 (by simp)
  · exact hU 8 (by simp)
  · exact hU 24 (by simp)
  · exact hK 2 4 65 (by norm_num) (by norm_num) (by decide +kernel)
  · exact hK 4 4 130 (by norm_num) (by norm_num) (by decide +kernel)
  · exact hU 2 (by simp)
  · exact hK 8 4 258 (by norm_num) (by norm_num) (by decide +kernel)

theorem maskSub_le_BStd_mb : maskSub 9 mbL8_mb ≤ BStd_mb := by
  intro w hw
  obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 hw
  refine mem_of_combos (fun m => toW 9 m ∈ BStd_mb) ?_ ?_ mbL8_mb ?_ m hm
  · show toW 9 0 ∈ BStd_mb
    rw [toW_zero]
    exact BStd_mb.one_mem
  · intro a b ha hb
    show toW 9 (a ^^^ b) ∈ BStd_mb
    rw [toW_xor]
    exact BStd_mb.mul_mem ha hb
  · exact mbL8_mem_BStd_mb

theorem BStd_eq_mb : BStd_mb = maskSub 9 mbL8_mb :=
  le_antisymm BStd_le_mb maskSub_le_BStd_mb

theorem card_BStd_mb : Nat.card BStd_mb = 2 ^ 8 := by
  rw [BStd_eq_mb, card_maskSub mbL8_mb_lt mbL8_mb_nodup]
  rfl

theorem mbMB0_std_mb : mQuot ⊤ BStd_mb = 1 := by
  unfold mQuot
  rw [Subgroup.relIndex_top_right]
  have h := Subgroup.index_mul_card (H := BStd_mb)
  rw [card_BStd_mb, natCard_Wn] at h
  have h2 : BStd_mb.index = 2 := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 ^ 8 by positivity)
    rw [h]
    norm_num
  rw [h2]
  exact padicValNat_self

theorem mbMB3_std_mb : ∀ x ∈ QW9, ∀ b ∈ BStd_mb, x b * b⁻¹ ∈ U0 := by
  have key : ∀ m ∈ combos mbL8_mb, ∀ x ∈ QW9, x (toW 9 m) * (toW 9 m)⁻¹ ∈ U0 := by
    intro m hm
    refine mem_of_combos (fun m => ∀ x ∈ QW9, x (toW 9 m) * (toW 9 m)⁻¹ ∈ U0) ?_ ?_ mbL8_mb ?_ m hm
    · intro x _
      have h1 : x (toW 9 0) * (toW 9 0)⁻¹ = 1 := by
        rw [toW_zero]
        exact comm_one_mb x
      rw [h1]
      exact U0.one_mem
    · intro a b ha hb x hx
      have h := U0.mul_mem (ha x hx) (hb x hx)
      have e : x (toW 9 (a ^^^ b)) * (toW 9 (a ^^^ b))⁻¹ =
          (x (toW 9 a) * (toW 9 a)⁻¹) * (x (toW 9 b) * (toW 9 b)⁻¹) := by
        rw [toW_xor]
        exact comm_mul_mb x _ _
      rw [e]
      exact h
    · intro l hl x hx
      obtain ⟨t, ht, rfl⟩ := mem_QW9.1 hx
      have hl' : l < 512 := by
        have := mbL8_mb_lt l hl
        norm_num at this
        exact this
      exact mem_maskSub.2 ⟨_, mbQ_mod_U0_mb t ht l hl, (comm_vG_toW_mb ht hl').symm⟩
  intro x hx b hb
  rw [BStd_eq_mb] at hb
  obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 hb
  exact key m hm x hx

end CFSG.Quasithin.H13
