module

public import CFSG.Quasithin.Background.HLUCode22
public import CFSG.Quasithin.Vol2.Ch8Sec2L829D4Nf

public section

namespace CFSG.Quasithin.H13.L829N

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Code22 CFSG.Quasithin.H.ModChk
open scoped commutatorElement

def cA22_sd4 : List ℕ := [148, 15, 145, 274, 649, 195, 389, 841, 921, 806]
def cB22_sd4 : List ℕ := [944, 368, 569, 246, 723, 755, 316, 589, 974, 882]
def cAi22_sd4 : List ℕ := [337, 280, 340, 287, 489, 599, 213, 188, 249, 226]
def cBi22_sd4 : List ℕ := [352, 928, 234, 549, 723, 48, 653, 812, 108, 418]

def N0L22_sd4 : List ℕ := [149, 945, 13, 370, 573, 282, 665, 227]

def REPS22_sd4 : List ℕ := [3, 13, 14, 33, 34, 44, 47, 68, 71, 73, 74, 101, 102, 104, 107]

def WORDS22_sd4 : List (ℕ × List (List ℕ)) :=
  [(3, [[], [0], [0, 1], [0, 1, 0]]), (13, [[], [0], [1], [0, 1]]), (14, [[], [0], [1], [1, 0]]),
    (33, [[], [0], [0, 1], [0, 1, 0]]), (34, [[], [0], [0, 1], [0, 1, 0]]),
    (44, [[], [0], [1], [1, 0]]), (47, [[], [0], [1], [0, 1]]), (68, [[], [0], [1], [1, 0]]),
    (71, [[], [0], [1], [0, 1]]), (73, [[], [0], [1], [1, 0]]), (74, [[], [0], [1], [1, 0]]),
    (101, [[], [0], [1], [1, 0]]), (102, [[], [0], [1], [0, 1]]), (104, [[], [0], [1], [0, 1]]),
    (107, [[], [0], [1], [0, 1]])]

def wordsFor22_sd4 (r : ℕ) : List (List ℕ) := (WORDS22_sd4.lookup r).getD []

def wordAct22_sd4 : List ℕ → ℕ → ℕ
  | [], m => m
  | a :: w, m => if a = 0 then wordAct22_sd4 w (actM cA22_sd4 m) else wordAct22_sd4 w (actM cB22_sd4 m)

def gensList22_sd4 : List ℕ :=
  (List.range 10).flatMap (fun i => [actM cA22_sd4 (2 ^ i) ^^^ 2 ^ i, actM cB22_sd4 (2 ^ i) ^^^ 2 ^ i])

theorem c_cols22_sd4 : matOf 10 (actC10 hbAArr) = cA22_sd4 ∧ matOf 10 (actC10 hbBArr) = cB22_sd4 ∧
    matOf 10 (actC10 hbAInv) = cAi22_sd4 ∧ matOf 10 (actC10 hbBInv) = cBi22_sd4 := by
  decide +kernel

theorem c_nodup22_sd4 : (combos N0L22_sd4).Nodup := by decide +kernel

theorem c_U22_sd4 : ∀ u ∈ combos hbU0Basis, u ∈ combos N0L22_sd4 := by decide +kernel

theorem c_U0basis22_sd4 : ∀ a ∈ hbU0Basis, a ∈ combos hbU0Basis := by decide +kernel

theorem c_gen22_sd4 : ∀ a ∈ N0L22_sd4, a ∈ gensList22_sd4 := by decide +kernel

theorem c_irr22_sd4 : ∀ r ∈ REPS22_sd4, ∀ b ∈ N0L22_sd4,
    b ∈ combos (hbU0Basis ++ (wordsFor22_sd4 r).map (fun w => wordAct22_sd4 w r)) := by
  decide +kernel

theorem c_red22_sd4 : ∀ m ∈ combos N0L22_sd4, m ∉ combos hbU0Basis →
    ∃ r ∈ REPS22_sd4, (m ^^^ r) ∈ combos hbU0Basis := by
  decide +kernel

theorem c_gen_mask22_sd4 : ∀ m < 2 ^ 10,
    (actM cA22_sd4 m ^^^ m) ∈ combos N0L22_sd4 ∧ (actM cB22_sd4 m ^^^ m) ∈ combos N0L22_sd4 := by
  decide +kernel

theorem c_invA22_sd4 : ∀ k < 2 ^ 10, actM cA22_sd4 (actM cAi22_sd4 k) = k := by decide +kernel

theorem c_invB22_sd4 : ∀ k < 2 ^ 10, actM cB22_sd4 (actM cBi22_sd4 k) = k := by decide +kernel

theorem c_mem3_22_sd4 : (3 : ℕ) ∈ combos N0L22_sd4 := by decide +kernel

theorem c_nonab22_sd4 :
    (actM cB22_sd4 (actM cA22_sd4 (actM cBi22_sd4 (actM cAi22_sd4 3)))) ^^^ 3 ∉ combos hbU0Basis := by
  decide +kernel

theorem c_nonab22_lt_sd4 :
    (actM cB22_sd4 (actM cA22_sd4 (actM cBi22_sd4 (actM cAi22_sd4 3)))) ^^^ 3 < 2 ^ 10 := by
  decide +kernel

theorem c_lt_cAi22_sd4 : ∀ c ∈ cAi22_sd4, c < 2 ^ 10 := by decide +kernel

theorem c_lt_cBi22_sd4 : ∀ c ∈ cBi22_sd4, c < 2 ^ 10 := by decide +kernel

theorem w10_mul_inv_22_sd4 (x z : Wn 10) : (x * z)⁻¹ = x⁻¹ * z⁻¹ := mul_inv x z

theorem w10_inv_mul_cancel_left_22_sd4 (x y : Wn 10) : x⁻¹ * (x * y) = y := inv_mul_cancel_left x y

theorem w10_mul_inv_cancel_22_sd4 (x : Wn 10) : x * x⁻¹ = 1 := mul_inv_cancel x

theorem w10_mul_comm_22_sd4 (x y : Wn 10) : x * y = y * x := mul_comm x y

theorem w10_inv_inv_22_sd4 (x : Wn 10) : x⁻¹⁻¹ = x := inv_inv x

theorem toW10_inv22_sd4 (m : ℕ) : (toW 10 m)⁻¹ = toW 10 m := by
  have h := toW_xor 10 m m
  rw [Nat.xor_self, toW_zero] at h
  exact inv_eq_of_mul_eq_one_right h.symm

section Group22

noncomputable def rhoA22_sd4 : MulAut (Wn 10) := rhoC10 mog22 mog22_le_mog22plus ⟨hbA, hbA_mem⟩

noncomputable def rhoB22_sd4 : MulAut (Wn 10) := rhoC10 mog22 mog22_le_mog22plus ⟨hbB, hbB_mem⟩

theorem rhoA22_act_sd4 (m : ℕ) : rhoA22_sd4 (toW 10 m) = toW 10 (actM cA22_sd4 m) := by
  have h : ∀ m, rhoA22_sd4 (toW 10 m) = toW 10 (actM (matOf 10 (actC10 hbAArr)) m) :=
    CFSG.Quasithin.H.Coc.actsBy_of_xorLin (n := 10) (xorLin_actC10 hbAArr)
      (fun m => rhoC10_toW mog22 mog22_le_mog22plus ⟨hbA, hbA_mem⟩ hasArr_hbA m)
  rw [c_cols22_sd4.1] at h
  exact h m

theorem rhoB22_act_sd4 (m : ℕ) : rhoB22_sd4 (toW 10 m) = toW 10 (actM cB22_sd4 m) := by
  have h : ∀ m, rhoB22_sd4 (toW 10 m) = toW 10 (actM (matOf 10 (actC10 hbBArr)) m) :=
    CFSG.Quasithin.H.Coc.actsBy_of_xorLin (n := 10) (xorLin_actC10 hbBArr)
      (fun m => rhoC10_toW mog22 mog22_le_mog22plus ⟨hbB, hbB_mem⟩ hasArr_hbB m)
  rw [c_cols22_sd4.2.1] at h
  exact h m

theorem inv_action22_sd4 {g : MulAut (Wn 10)} {c c' : List ℕ}
    (h : ∀ m, g (toW 10 m) = toW 10 (actM c m))
    (hc : ∀ m < 2 ^ 10, actM c (actM c' m) = m) (m : ℕ) (hm : m < 2 ^ 10) :
    g⁻¹ (toW 10 m) = toW 10 (actM c' m) := by
  have key : g (toW 10 (actM c' m)) = toW 10 m := by rw [h, hc m hm]
  rw [← key]
  show g.symm (g (toW 10 (actM c' m))) = _
  rw [MulEquiv.symm_apply_apply]

theorem rhoA22_inv_sd4 (m : ℕ) (hm : m < 2 ^ 10) :
    rhoA22_sd4⁻¹ (toW 10 m) = toW 10 (actM cAi22_sd4 m) :=
  inv_action22_sd4 rhoA22_act_sd4 c_invA22_sd4 m hm

theorem rhoB22_inv_sd4 (m : ℕ) (hm : m < 2 ^ 10) :
    rhoB22_sd4⁻¹ (toW 10 m) = toW 10 (actM cBi22_sd4 m) :=
  inv_action22_sd4 rhoB22_act_sd4 c_invB22_sd4 m hm

def Sst22_sd4 : Subgroup (MulAut (Wn 10)) where
  carrier := {y | ∀ v : Wn 10, y v * v⁻¹ ∈ maskSub 10 N0L22_sd4}
  mul_mem' := by
    intro a b ha hb v
    have h1 : b v * v⁻¹ ∈ maskSub 10 N0L22_sd4 := hb v
    have h2 : a (b v) * (b v)⁻¹ ∈ maskSub 10 N0L22_sd4 := ha (b v)
    have e : (a * b) v * v⁻¹ = a (b v) * (b v)⁻¹ * (b v * v⁻¹) := by
      rw [MulAut.mul_apply, mul_assoc]
      exact congrArg (fun z => a (b v) * z) (w10_inv_mul_cancel_left_22_sd4 (b v) v⁻¹).symm
    rw [e]
    exact mul_mem h2 h1
  one_mem' := by
    intro v
    rw [MulAut.one_apply, w10_mul_inv_cancel_22_sd4]
    exact one_mem _
  inv_mem' := by
    intro y hy v
    obtain ⟨w, rfl⟩ : ∃ w, v = y w := ⟨y⁻¹ v, by simp⟩
    have h : (y w * w⁻¹)⁻¹ ∈ maskSub 10 N0L22_sd4 := inv_mem (hy w)
    have hw : y⁻¹ (y w) = w := by simp
    have e : y⁻¹ (y w) * (y w)⁻¹ = (y w * w⁻¹)⁻¹ := by
      rw [hw, w10_mul_inv_22_sd4, w10_inv_inv_22_sd4, w10_mul_comm_22_sd4 w (y w)⁻¹]
    rw [e]
    exact h

theorem rhoA22_mem_Sst_sd4 : rhoA22_sd4 ∈ Sst22_sd4 := by
  intro v
  obtain ⟨m, hm, rfl⟩ := toW_surj 10 v
  rw [rhoA22_act_sd4, toW10_inv22_sd4, ← toW_xor]
  exact toW_mem_maskSub (c_gen_mask22_sd4 m hm).1

theorem rhoB22_mem_Sst_sd4 : rhoB22_sd4 ∈ Sst22_sd4 := by
  intro v
  obtain ⟨m, hm, rfl⟩ := toW_surj 10 v
  rw [rhoB22_act_sd4, toW10_inv22_sd4, ← toW_xor]
  exact toW_mem_maskSub (c_gen_mask22_sd4 m hm).2

theorem rhoA22_mem_P_sd4 : rhoA22_sd4 ∈ imgC hbQ :=
  Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hbA_mem_Q)

theorem rhoB22_mem_P_sd4 : rhoB22_sd4 ∈ imgC hbQ :=
  Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hbB_mem_Q)

theorem hbQ_rho_mem_Sst_sd4 : ∀ τ ∈ hbQ, ∀ h : τ ∈ mog22,
    rhoC10 mog22 mog22_le_mog22plus ⟨τ, h⟩ ∈ Sst22_sd4 := by
  intro τ hτ
  change τ ∈ Subgroup.closure {hbA, hbB} at hτ
  induction hτ using Subgroup.closure_induction with
  | mem x hx =>
    intro h
    rcases hx with rfl | rfl
    · exact rhoA22_mem_Sst_sd4
    · exact rhoB22_mem_Sst_sd4
  | one =>
    intro h
    have e : (⟨(1 : Equiv.Perm (Fin 24)), h⟩ : ↥mog22) = 1 := rfl
    rw [e, map_one]
    exact Sst22_sd4.one_mem
  | mul x y hx hy ihx ihy =>
    intro h
    have hx' : x ∈ mog22 := hbQ_le hx
    have hy' : y ∈ mog22 := hbQ_le hy
    have e : (⟨x * y, h⟩ : ↥mog22) = ⟨x, hx'⟩ * ⟨y, hy'⟩ := Subtype.ext rfl
    rw [e, map_mul]
    exact Sst22_sd4.mul_mem (ihx hx') (ihy hy')
  | inv x hx ihx =>
    intro h
    have hx' : x ∈ mog22 := hbQ_le hx
    have e : (⟨x⁻¹, h⟩ : ↥mog22) = (⟨x, hx'⟩ : ↥mog22)⁻¹ := Subtype.ext rfl
    rw [e, map_inv]
    exact Sst22_sd4.inv_mem (ihx hx')

theorem imgC_hbQ_le_Sst22_sd4 : imgC hbQ ≤ Sst22_sd4 := by
  unfold imgC
  refine Subgroup.map_le_iff_le_comap.2 ?_
  intro σ hσ
  exact hbQ_rho_mem_Sst_sd4 σ (Subgroup.mem_subgroupOf.mp hσ) σ.2

theorem comm_le_M22_sd4 : comm_sd4 (imgC hbQ) ≤ maskSub 10 N0L22_sd4 := by
  unfold comm_sd4
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨y, hy, v, rfl⟩
  exact imgC_hbQ_le_Sst22_sd4 hy v

theorem gen_mem_comm22_sd4 (i : ℕ) : toW 10 (actM cA22_sd4 (2 ^ i) ^^^ 2 ^ i) ∈ comm_sd4 (imgC hbQ) := by
  have h1 : rhoA22_sd4 (toW 10 (2 ^ i)) * (toW 10 (2 ^ i))⁻¹ ∈ comm_sd4 (imgC hbQ) :=
    Subgroup.subset_closure ⟨rhoA22_sd4, rhoA22_mem_P_sd4, toW 10 (2 ^ i), rfl⟩
  rwa [rhoA22_act_sd4, toW10_inv22_sd4, ← toW_xor] at h1

theorem genB_mem_comm22_sd4 (i : ℕ) : toW 10 (actM cB22_sd4 (2 ^ i) ^^^ 2 ^ i) ∈ comm_sd4 (imgC hbQ) := by
  have h1 : rhoB22_sd4 (toW 10 (2 ^ i)) * (toW 10 (2 ^ i))⁻¹ ∈ comm_sd4 (imgC hbQ) :=
    Subgroup.subset_closure ⟨rhoB22_sd4, rhoB22_mem_P_sd4, toW 10 (2 ^ i), rfl⟩
  rwa [rhoB22_act_sd4, toW10_inv22_sd4, ← toW_xor] at h1

theorem combos_mem_sub22_sd4 (H : Subgroup (Wn 10)) :
    ∀ (l : List ℕ), (∀ a ∈ l, toW 10 a ∈ H) → ∀ m ∈ combos l, toW 10 m ∈ H
  | [], _, m, hm => by
    simp only [combos, List.mem_singleton] at hm
    rw [hm, toW_zero]
    exact H.one_mem
  | a :: l, h, m, hm => by
    rw [combos, List.mem_append, List.mem_map] at hm
    rcases hm with hm | ⟨k, hk, rfl⟩
    · exact combos_mem_sub22_sd4 H l (fun b hb => h b (List.mem_cons_of_mem a hb)) m hm
    · rw [toW_xor]
      exact H.mul_mem (combos_mem_sub22_sd4 H l (fun b hb => h b (List.mem_cons_of_mem a hb)) k hk)
        (h a List.mem_cons_self)

theorem gensList_comm22_sd4 : ∀ g ∈ gensList22_sd4, toW 10 g ∈ comm_sd4 (imgC hbQ) := by
  intro g hg
  unfold gensList22_sd4 at hg
  rw [List.mem_flatMap] at hg
  obtain ⟨i, -, hg⟩ := hg
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl
  · exact gen_mem_comm22_sd4 i
  · exact genB_mem_comm22_sd4 i

theorem M_le_comm22_sd4 : maskSub 10 N0L22_sd4 ≤ comm_sd4 (imgC hbQ) := by
  rintro _ ⟨m, hm, rfl⟩
  exact combos_mem_sub22_sd4 (comm_sd4 (imgC hbQ)) N0L22_sd4
    (fun a ha => gensList_comm22_sd4 a (c_gen22_sd4 a ha)) m hm

theorem comm_eq22_sd4 : comm_sd4 (imgC hbQ) = maskSub 10 N0L22_sd4 :=
  le_antisymm comm_le_M22_sd4 M_le_comm22_sd4

theorem UC_le_M22_sd4 : UC ≤ maskSub 10 N0L22_sd4 := by
  rintro _ ⟨m, hm, rfl⟩
  exact toW_mem_maskSub (c_U22_sd4 m hm)

theorem irr22_sd4 (C : Subgroup (Wn 10)) (hUC : UC ≤ C) (hCM : C ≤ maskSub 10 N0L22_sd4)
    (hinv : ∀ p ∈ imgC hbQ, ∀ c ∈ C, p c ∈ C) : C = UC ∨ C = maskSub 10 N0L22_sd4 := by
  by_cases hCU : C = UC
  · exact Or.inl hCU
  right
  have hlt : UC < C := lt_of_le_of_ne hUC (Ne.symm hCU)
  obtain ⟨c, hcC, hcU⟩ := SetLike.exists_of_lt hlt
  obtain ⟨m, hm, rfl⟩ := hCM hcC
  have hmU : m ∉ combos hbU0Basis := fun h => hcU (toW_mem_maskSub h)
  obtain ⟨r, hr, hmr⟩ := c_red22_sd4 m hm hmU
  have hrC : toW 10 r ∈ C := by
    have h1 : toW 10 (m ^^^ r) ∈ C := hUC (toW_mem_maskSub hmr)
    have h2 : toW 10 m * toW 10 (m ^^^ r) ∈ C := C.mul_mem hcC h1
    rw [← toW_xor, Nat.xor_xor_cancel_left] at h2
    exact h2
  have hAC : ∀ k, toW 10 k ∈ C → toW 10 (actM cA22_sd4 k) ∈ C := by
    intro k hk
    rw [← rhoA22_act_sd4]
    exact hinv rhoA22_sd4 rhoA22_mem_P_sd4 _ hk
  have hBC : ∀ k, toW 10 k ∈ C → toW 10 (actM cB22_sd4 k) ∈ C := by
    intro k hk
    rw [← rhoB22_act_sd4]
    exact hinv rhoB22_sd4 rhoB22_mem_P_sd4 _ hk
  have hwordC : ∀ (w : List ℕ) (k : ℕ), toW 10 k ∈ C → toW 10 (wordAct22_sd4 w k) ∈ C := by
    intro w
    induction w with
    | nil => intro k hk; exact hk
    | cons a w ih =>
      intro k hk
      by_cases ha : a = 0
      · subst ha
        simp only [wordAct22_sd4, if_true]
        exact ih _ (hAC k hk)
      · simp only [wordAct22_sd4, if_neg ha]
        exact ih _ (hBC k hk)
  have hgens : ∀ a ∈ hbU0Basis ++ (wordsFor22_sd4 r).map (fun w => wordAct22_sd4 w r), toW 10 a ∈ C := by
    intro a ha
    rw [List.mem_append, List.mem_map] at ha
    rcases ha with ha | ⟨w, -, rfl⟩
    · exact hUC (toW_mem_maskSub (c_U0basis22_sd4 a ha))
    · exact hwordC w r hrC
  have hN : ∀ b ∈ N0L22_sd4, toW 10 b ∈ C :=
    fun b hb => combos_mem_sub22_sd4 C _ hgens b (c_irr22_sd4 r hr b hb)
  apply le_antisymm hCM
  rintro _ ⟨m', hm', rfl⟩
  exact combos_mem_sub22_sd4 C N0L22_sd4 hN m' hm'

theorem nonab22_sd4 : ∃ p ∈ imgC hbQ, ∃ q ∈ imgC hbQ, ∃ n ∈ maskSub 10 N0L22_sd4,
    ((⁅p, q⁆ : MulAut (Wn 10))⁻¹ n) * n⁻¹ ∉ UC := by
  refine ⟨rhoA22_sd4, rhoA22_mem_P_sd4, rhoB22_sd4, rhoB22_mem_P_sd4, toW 10 3,
    toW_mem_maskSub c_mem3_22_sd4, ?_⟩
  have e1 : (⁅rhoA22_sd4, rhoB22_sd4⁆ : MulAut (Wn 10))⁻¹ =
      rhoB22_sd4 * rhoA22_sd4 * (rhoB22_sd4)⁻¹ * (rhoA22_sd4)⁻¹ := by
    rw [commutatorElement_def]
    simp [mul_assoc]
  have h3 : (3 : ℕ) < 2 ^ 10 := by norm_num
  have hlt1 : ∀ m, actM cAi22_sd4 m < 2 ^ 10 := fun m => actM_lt c_lt_cAi22_sd4 m
  have hlt2 : ∀ m, actM cBi22_sd4 m < 2 ^ 10 := fun m => actM_lt c_lt_cBi22_sd4 m
  rw [e1]
  simp only [MulAut.mul_apply]
  rw [rhoA22_inv_sd4 3 h3, rhoB22_inv_sd4 _ (hlt1 3), rhoA22_act_sd4, rhoB22_act_sd4, toW10_inv22_sd4, ← toW_xor]
  intro h
  obtain ⟨m, hm, hmk⟩ := h
  have hm_eq := toW_inj (combos_lt hbU0Basis_lt m hm) c_nonab22_lt_sd4 hmk
  exact c_nonab22_sd4 (hm_eq ▸ hm)

end Group22

theorem D4NF_stdM22_sd4 :
    D4NF_sd4 (imgC mog22) UC := by
  have hP : D4P_sd4 (imgC mog22) UC = imgC hbQ := by
    unfold D4P_sd4
    exact perfectCore_stab_UC
  have hN : D4N_sd4 (imgC mog22) UC = maskSub 10 N0L22_sd4 := by
    unfold D4N_sd4
    rw [hP, comm_eq22_sd4]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hN]
    exact UC_le_M22_sd4
  · have hcN : Nat.card ↥(D4N_sd4 (imgC mog22) UC) = 2 ^ 8 := by
      rw [hN]
      exact card_maskSub (n := 10) (l := N0L22_sd4) (by decide) c_nodup22_sd4
    rw [hcN]
    show (2 : ℕ) ^ 8 = 16 * Nat.card ↥(UC : Subgroup (Wn 10))
    rw [card_UC]
    norm_num
  · intro C hUC hCN hinv
    rw [hN] at hCN ⊢
    rw [hP] at hinv
    exact irr22_sd4 C hUC hCN hinv
  · rw [hP, hN]
    exact nonab22_sd4

end CFSG.Quasithin.H13.L829N
