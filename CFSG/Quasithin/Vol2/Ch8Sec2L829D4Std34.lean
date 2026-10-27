module

public import CFSG.Quasithin.Background.HLUL34
public import CFSG.Quasithin.Vol2.Ch8Sec2L829D4Nf

public section

namespace CFSG.Quasithin.H13.L829N

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.L34Z CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H13.Ch9.Herm9 CFSG.Quasithin.H.L3W9
open scoped commutatorElement

def N0L_sd4 : List ℕ := [3, 26, 65, 16, 1, 440, 192, 160]

def REPS_sd4 : List ℕ := [32, 64, 96, 128, 160, 192, 224, 256, 288, 320, 352, 384, 416, 448, 480]

def wordsFor_sd4 (r : ℕ) : List (List ℕ) :=
  if r = 192 ∨ r = 352 ∨ r = 416 then [[], [1], [1, 0], [1, 1]] else [[], [0], [1], [0, 1]]

def wordAct_sd4 : List ℕ → ℕ → ℕ
  | [], m => m
  | a :: w, m => if a = 0 then wordAct_sd4 w (actM colsX2 m) else wordAct_sd4 w (actM colsY2 m)

def gensList_sd4 : List ℕ :=
  (List.range 9).flatMap (fun i => [actM colsX2 (2 ^ i) ^^^ 2 ^ i, actM colsY2 (2 ^ i) ^^^ 2 ^ i])

theorem c_nodup_sd4 : (combos N0L_sd4).Nodup := by decide +kernel

theorem c_U_sd4 : ∀ u ∈ combos U0Basis, u ∈ combos N0L_sd4 := by decide +kernel

theorem c_gen_sd4 : ∀ a ∈ N0L_sd4, a ∈ gensList_sd4 := by decide +kernel

theorem c_irr_sd4 : ∀ r ∈ REPS_sd4, ∀ b ∈ N0L_sd4,
    b ∈ combos (U0Basis ++ (wordsFor_sd4 r).map (fun w => wordAct_sd4 w r)) := by
  decide +kernel

theorem c_red_sd4 : ∀ m ∈ combos N0L_sd4, m ∉ combos U0Basis →
    ∃ r ∈ REPS_sd4, (m ^^^ r) ∈ combos U0Basis := by
  decide +kernel

theorem c_gen_mask_sd4 : ∀ m < 512,
    (actM colsX2 m ^^^ m) ∈ combos N0L_sd4 ∧ (actM colsY2 m ^^^ m) ∈ combos N0L_sd4 := by
  decide +kernel

theorem c_mem32_sd4 : (32 : ℕ) ∈ combos N0L_sd4 := by decide +kernel

theorem c_U0basis_sd4 : ∀ a ∈ U0Basis, a ∈ combos U0Basis := by decide +kernel

theorem c_invX_sd4 : ∀ k < 2 ^ 9, actM colsX2 (actM colsX2i k) = k := by decide +kernel

theorem c_invY_sd4 : ∀ k < 2 ^ 9, actM colsY2 (actM colsY2i k) = k := by decide +kernel

theorem c_nonab2_sd4 :
    (actM colsY2 (actM colsX2 (actM colsY2i (actM colsX2i 32)))) ^^^ 32 ∉ combos U0Basis := by
  decide +kernel

theorem c_nonab2_lt_sd4 :
    (actM colsY2 (actM colsX2 (actM colsY2i (actM colsX2i 32)))) ^^^ 32 < 2 ^ 9 := by
  decide +kernel

theorem c_mem512_sd4 : ∀ m < 2 ^ 9, m < 512 := fun m hm => by norm_num at hm ⊢; exact hm

theorem w_mul_inv_sd4 (x z : Wn 9) : (x * z)⁻¹ = x⁻¹ * z⁻¹ := mul_inv x z

theorem w_inv_mul_cancel_left_sd4 (x y : Wn 9) : x⁻¹ * (x * y) = y := inv_mul_cancel_left x y

theorem w_mul_inv_cancel_sd4 (x : Wn 9) : x * x⁻¹ = 1 := mul_inv_cancel x

theorem w_mul_comm_sd4 (x y : Wn 9) : x * y = y * x := mul_comm x y

theorem w_inv_inv_sd4 (x : Wn 9) : x⁻¹⁻¹ = x := inv_inv x

section Group

theorem hX_sd4 (m : ℕ) : rho9 x2G (toW 9 m) = toW 9 (actM colsX2 m) := actsBy_rho9_x2 m

theorem hY_sd4 (m : ℕ) : rho9 y2G (toW 9 m) = toW 9 (actM colsY2 m) := actsBy_rho9_y2 m

theorem toW9_inv_sd4 (m : ℕ) : (toW 9 m)⁻¹ = toW 9 m := by
  have h := toW_xor 9 m m
  rw [Nat.xor_self, toW_zero] at h
  exact inv_eq_of_mul_eq_one_right h.symm

theorem inv_action_sd4 {g : MulAut (Wn 9)} {c c' : List ℕ}
    (h : ∀ m, g (toW 9 m) = toW 9 (actM c m))
    (hc : ∀ m < 2 ^ 9, actM c (actM c' m) = m) (m : ℕ) (hm : m < 2 ^ 9) :
    g⁻¹ (toW 9 m) = toW 9 (actM c' m) := by
  have key : g (toW 9 (actM c' m)) = toW 9 m := by rw [h, hc m hm]
  rw [← key]
  show g.symm (g (toW 9 (actM c' m))) = _
  rw [MulEquiv.symm_apply_apply]

theorem hXi_sd4 (m : ℕ) (hm : m < 2 ^ 9) :
    (rho9 x2G)⁻¹ (toW 9 m) = toW 9 (actM colsX2i m) :=
  inv_action_sd4 hX_sd4 c_invX_sd4 m hm

theorem hYi_sd4 (m : ℕ) (hm : m < 2 ^ 9) :
    (rho9 y2G)⁻¹ (toW 9 m) = toW 9 (actM colsY2i m) :=
  inv_action_sd4 hY_sd4 c_invY_sd4 m hm

def Sst_sd4 : Subgroup (MulAut (Wn 9)) where
  carrier := {y | ∀ v : Wn 9, y v * v⁻¹ ∈ maskSub 9 N0L_sd4}
  mul_mem' := by
    intro a b ha hb v
    have h1 : b v * v⁻¹ ∈ maskSub 9 N0L_sd4 := hb v
    have h2 : a (b v) * (b v)⁻¹ ∈ maskSub 9 N0L_sd4 := ha (b v)
    have e : (a * b) v * v⁻¹ = a (b v) * (b v)⁻¹ * (b v * v⁻¹) := by
      rw [MulAut.mul_apply, mul_assoc]
      exact congrArg (fun z => a (b v) * z) (w_inv_mul_cancel_left_sd4 (b v) v⁻¹).symm
    rw [e]
    exact mul_mem h2 h1
  one_mem' := by
    intro v
    rw [MulAut.one_apply, w_mul_inv_cancel_sd4]
    exact one_mem _
  inv_mem' := by
    intro y hy v
    obtain ⟨w, rfl⟩ : ∃ w, v = y w := ⟨y⁻¹ v, by simp⟩
    have h : (y w * w⁻¹)⁻¹ ∈ maskSub 9 N0L_sd4 := inv_mem (hy w)
    have hw : y⁻¹ (y w) = w := by simp
    have e : y⁻¹ (y w) * (y w)⁻¹ = (y w * w⁻¹)⁻¹ := by
      rw [hw, w_mul_inv_sd4, w_inv_inv_sd4, w_mul_comm_sd4 w (y w)⁻¹]
    rw [e]
    exact h

theorem x_mem_Sst_sd4 : rho9 x2G ∈ Sst_sd4 := by
  intro v
  obtain ⟨m, hm, rfl⟩ := toW_surj 9 v
  rw [hX_sd4, toW9_inv_sd4, ← toW_xor]
  exact toW_mem_maskSub (c_gen_mask_sd4 m (c_mem512_sd4 m hm)).1

theorem y_mem_Sst_sd4 : rho9 y2G ∈ Sst_sd4 := by
  intro v
  obtain ⟨m, hm, rfl⟩ := toW_surj 9 v
  rw [hY_sd4, toW9_inv_sd4, ← toW_xor]
  exact toW_mem_maskSub (c_gen_mask_sd4 m (c_mem512_sd4 m hm)).2

theorem comm_le_M_sd4 : comm_sd4 P2 ≤ maskSub 9 N0L_sd4 := by
  unfold comm_sd4
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨y, hy, v, rfl⟩
  have hPS : P2 ≤ Sst_sd4 := by
    unfold P2
    refine (Subgroup.closure_le _).2 ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact x_mem_Sst_sd4
    · exact y_mem_Sst_sd4
  exact hPS hy v

theorem combos_mem_sub_sd4 {n : ℕ} (H : Subgroup (Wn n)) :
    ∀ (l : List ℕ), (∀ a ∈ l, toW n a ∈ H) → ∀ m ∈ combos l, toW n m ∈ H
  | [], _, m, hm => by
    simp only [combos, List.mem_singleton] at hm
    rw [hm, toW_zero]
    exact H.one_mem
  | a :: l, h, m, hm => by
    rw [combos, List.mem_append, List.mem_map] at hm
    rcases hm with hm | ⟨k, hk, rfl⟩
    · exact combos_mem_sub_sd4 H l (fun b hb => h b (List.mem_cons_of_mem a hb)) m hm
    · rw [toW_xor]
      exact H.mul_mem (combos_mem_sub_sd4 H l (fun b hb => h b (List.mem_cons_of_mem a hb)) k hk)
        (h a List.mem_cons_self)

theorem gen_mem_comm_sd4 (i : ℕ) : toW 9 (actM colsX2 (2 ^ i) ^^^ 2 ^ i) ∈ comm_sd4 P2 := by
  have h1 : rho9 x2G (toW 9 (2 ^ i)) * (toW 9 (2 ^ i))⁻¹ ∈ comm_sd4 P2 :=
    Subgroup.subset_closure ⟨rho9 x2G, Subgroup.subset_closure (Set.mem_insert _ _),
      toW 9 (2 ^ i), rfl⟩
  rwa [hX_sd4, toW9_inv_sd4, ← toW_xor] at h1

theorem genY_mem_comm_sd4 (i : ℕ) : toW 9 (actM colsY2 (2 ^ i) ^^^ 2 ^ i) ∈ comm_sd4 P2 := by
  have h1 : rho9 y2G (toW 9 (2 ^ i)) * (toW 9 (2 ^ i))⁻¹ ∈ comm_sd4 P2 :=
    Subgroup.subset_closure ⟨rho9 y2G, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl),
      toW 9 (2 ^ i), rfl⟩
  rwa [hY_sd4, toW9_inv_sd4, ← toW_xor] at h1

theorem gensList_comm_sd4 : ∀ g ∈ gensList_sd4, toW 9 g ∈ comm_sd4 P2 := by
  intro g hg
  unfold gensList_sd4 at hg
  rw [List.mem_flatMap] at hg
  obtain ⟨i, -, hg⟩ := hg
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl
  · exact gen_mem_comm_sd4 i
  · exact genY_mem_comm_sd4 i

theorem M_le_comm_sd4 : maskSub 9 N0L_sd4 ≤ comm_sd4 P2 := by
  rintro _ ⟨m, hm, rfl⟩
  exact combos_mem_sub_sd4 (comm_sd4 P2) N0L_sd4
    (fun a ha => gensList_comm_sd4 a (c_gen_sd4 a ha)) m hm

theorem comm_eq_M_sd4 : comm_sd4 P2 = maskSub 9 N0L_sd4 :=
  le_antisymm comm_le_M_sd4 M_le_comm_sd4

theorem U0_le_M_sd4 : U0 ≤ maskSub 9 N0L_sd4 := by
  rintro _ ⟨m, hm, rfl⟩
  exact toW_mem_maskSub (c_U_sd4 m hm)

theorem irr_sd4 (C : Subgroup (Wn 9)) (hUC : U0 ≤ C) (hCM : C ≤ maskSub 9 N0L_sd4)
    (hinv : ∀ p ∈ P2, ∀ c ∈ C, p c ∈ C) : C = U0 ∨ C = maskSub 9 N0L_sd4 := by
  by_cases hCU : C = U0
  · exact Or.inl hCU
  right
  have hlt : U0 < C := lt_of_le_of_ne hUC (Ne.symm hCU)
  obtain ⟨c, hcC, hcU⟩ := SetLike.exists_of_lt hlt
  obtain ⟨m, hm, rfl⟩ := hCM hcC
  have hmU : m ∉ combos U0Basis := fun h => hcU (toW_mem_maskSub h)
  obtain ⟨r, hr, hmr⟩ := c_red_sd4 m hm hmU
  have hrC : toW 9 r ∈ C := by
    have h1 : toW 9 (m ^^^ r) ∈ C := hUC (toW_mem_maskSub hmr)
    have h2 : toW 9 m * toW 9 (m ^^^ r) ∈ C := C.mul_mem hcC h1
    rw [← toW_xor, Nat.xor_xor_cancel_left] at h2
    exact h2
  have hXC : ∀ k, toW 9 k ∈ C → toW 9 (actM colsX2 k) ∈ C := by
    intro k hk
    rw [← hX_sd4]
    exact hinv _ (Subgroup.subset_closure (Set.mem_insert _ _)) _ hk
  have hYC : ∀ k, toW 9 k ∈ C → toW 9 (actM colsY2 k) ∈ C := by
    intro k hk
    rw [← hY_sd4]
    exact hinv _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) _ hk
  have hwordC : ∀ (w : List ℕ) (k : ℕ), toW 9 k ∈ C → toW 9 (wordAct_sd4 w k) ∈ C := by
    intro w
    induction w with
    | nil => intro k hk; exact hk
    | cons a w ih =>
      intro k hk
      by_cases ha : a = 0
      · subst ha
        simp only [wordAct_sd4, if_true]
        exact ih _ (hXC k hk)
      · simp only [wordAct_sd4, if_neg ha]
        exact ih _ (hYC k hk)
  have hgens : ∀ a ∈ U0Basis ++ (wordsFor_sd4 r).map (fun w => wordAct_sd4 w r),
      toW 9 a ∈ C := by
    intro a ha
    rw [List.mem_append, List.mem_map] at ha
    rcases ha with ha | ⟨w, -, rfl⟩
    · exact hUC (toW_mem_maskSub (c_U0basis_sd4 a ha))
    · exact hwordC w r hrC
  have hN : ∀ b ∈ N0L_sd4, toW 9 b ∈ C :=
    fun b hb => combos_mem_sub_sd4 C _ hgens b (c_irr_sd4 r hr b hb)
  apply le_antisymm hCM
  rintro _ ⟨m', hm', rfl⟩
  exact combos_mem_sub_sd4 C N0L_sd4 hN m' hm'

theorem nonab_sd4 : ∃ p ∈ P2, ∃ q ∈ P2, ∃ n ∈ maskSub 9 N0L_sd4,
    ((⁅p, q⁆ : MulAut (Wn 9))⁻¹ n) * n⁻¹ ∉ U0 := by
  refine ⟨rho9 x2G, Subgroup.subset_closure (Set.mem_insert _ _), rho9 y2G,
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl), toW 9 32,
    toW_mem_maskSub c_mem32_sd4, ?_⟩
  have e1 : (⁅rho9 x2G, rho9 y2G⁆ : MulAut (Wn 9))⁻¹ =
      rho9 y2G * rho9 x2G * (rho9 y2G)⁻¹ * (rho9 x2G)⁻¹ := by
    rw [commutatorElement_def]
    simp [mul_assoc]
  have h32 : (32 : ℕ) < 2 ^ 9 := by norm_num
  have hlt1 : ∀ m, actM colsX2i m < 2 ^ 9 := fun m => actM_lt (by decide) m
  have hlt2 : ∀ m, actM colsY2i m < 2 ^ 9 := fun m => actM_lt (by decide) m
  rw [e1]
  simp only [MulAut.mul_apply]
  rw [hXi_sd4 32 h32, hYi_sd4 _ (hlt1 32), hX_sd4, hY_sd4, toW9_inv_sd4, ← toW_xor]
  intro h
  obtain ⟨m, hm, hmk⟩ := h
  have hm_eq := toW_inj (combos_lt U0Basis_lt m hm) c_nonab2_lt_sd4 hmk
  exact c_nonab2_sd4 (hm_eq ▸ hm)

end Group

theorem D4NF_std34_sd4 : D4NF_sd4 img9 U0 := by
  have hP : D4P_sd4 img9 U0 = P2 := by
    unfold D4P_sd4
    exact perfectCore_stab_U0
  have hN : D4N_sd4 img9 U0 = maskSub 9 N0L_sd4 := by
    unfold D4N_sd4
    rw [hP, comm_eq_M_sd4]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hN]
    exact U0_le_M_sd4
  · have hcN : Nat.card ↥(D4N_sd4 img9 U0) = 2 ^ 8 := by
      rw [hN]
      exact card_maskSub (n := 9) (l := N0L_sd4) (by decide) c_nodup_sd4
    rw [hcN]
    show (2 : ℕ) ^ 8 = 16 * Nat.card ↥(U0 : Subgroup W9)
    rw [card_U0]
    norm_num
  · intro C hUC hCN hinv
    rw [hN] at hCN ⊢
    rw [hP] at hinv
    exact irr_sd4 C hUC hCN hinv
  · rw [hP, hN]
    exact nonab_sd4

end CFSG.Quasithin.H13.L829N
