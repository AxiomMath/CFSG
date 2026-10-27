module

public import CFSG.RankThree.Native.LyFiveCheck
public import CFSG.RankThree.Native.LyFiveImages
public import CFSG.RankThree.Native.LyFiveCosets

public noncomputable section

namespace CFSG.RankThree.Native

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native Subgroup
open scoped commutatorElement

attribute [local irreducible] lyFiveParArr lyFiveGenArr lyFiveNextArr lyFiveQArr
open CFSG.Sporadic.He.Native (toMat toMat_mulM toMat_powM toMat_idM toMat_eq_of_beq mulM powM
  idM)

section Generic

variable {M N : Type*} [Monoid M] [Monoid N]

theorem fiveSlpStep_map (f : M →* N) (r : ℕ → M) (ins : FiveIns) :
    fiveSlpStep (f ∘ r) ins = f ∘ fiveSlpStep r ins := by
  cases ins with
  | mu i j k =>
    funext m
    simp only [fiveSlpStep, Function.comp_apply, Function.update_apply]
    split_ifs <;> simp [map_mul]
  | pwr e i k =>
    funext m
    simp only [fiveSlpStep, Function.comp_apply, Function.update_apply]
    split_ifs <;> simp [map_pow]

theorem fiveSlpRun_map (f : M →* N) (prog : List FiveIns) (r : ℕ → M) :
    fiveSlpRun prog (f ∘ r) = f ∘ fiveSlpRun prog r := by
  induction prog generalizing r with
  | nil => rfl
  | cons ins prog ih =>
    simp only [fiveSlpRun, List.foldl_cons] at ih ⊢
    rw [fiveSlpStep_map, ih]

theorem fiveInit_map (f : M →* N) (g₁ g₂ : M) : f ∘ fiveInit g₁ g₂ = fiveInit (f g₁) (f g₂) := by
  funext k
  simp only [Function.comp_apply, fiveInit]
  split_ifs <;> simp

@[expose] def fiveLift (A B : M) (k : ℕ) : M :=
  if _h : 0 < k ∧ lyFiveParArr[k]! < k then
    (if lyFiveGenArr[k]! = 1 then B else A) * fiveLift A B lyFiveParArr[k]!
  else 1
termination_by k

theorem fiveLift_eq (A B : M) (k : ℕ) (hk : 0 < k) (hp : lyFiveParArr[k]! < k) :
    fiveLift A B k = (if lyFiveGenArr[k]! = 1 then B else A) * fiveLift A B lyFiveParArr[k]! := by
  rw [fiveLift, dite_eq_left ⟨hk, hp⟩]

theorem fiveLift_zero (A B : M) : fiveLift A B 0 = 1 := by
  rw [fiveLift, dite_eq_right (by omega)]

theorem fiveLift_map (f : M →* N) (A B : M) (k : ℕ) :
    f (fiveLift A B k) = fiveLift (f A) (f B) k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases h : 0 < k ∧ lyFiveParArr[k]! < k
    · rw [fiveLift_eq A B k h.1 h.2, fiveLift_eq (f A) (f B) k h.1 h.2, map_mul, ih _ h.2]
      split_ifs <;> rfl
    · rw [fiveLift, dite_eq_right h, fiveLift, dite_eq_right h, map_one]

@[expose] def fiveWordM (a b ai bi : M) (w : List ℤ) : M :=
  (w.map fun z => if z = 1 then a else if z = 2 then b else if z = -1 then ai else bi).prod

theorem fiveWordM_map (f : M →* N) (a b ai bi : M) (w : List ℤ) :
    f (fiveWordM a b ai bi w) = fiveWordM (f a) (f b) (f ai) (f bi) w := by
  rw [fiveWordM, map_list_prod, List.map_map, fiveWordM]
  congr 1
  apply List.map_congr_left
  intro z _
  simp only [Function.comp_apply]
  split_ifs <;> rfl

theorem fiveWord_eq_fiveWordM {G : Type*} [Group G] (a b : G) (w : List ℤ) :
    fiveWord a b w = fiveWordM a b a⁻¹ b⁻¹ w := rfl

end Generic

@[expose] def lyMatHom : J →* Matrix (Fin 111) (Fin 111) (ZMod 5) :=
  (Units.coeHom _).comp J.subtype

theorem lyMatHom_apply (g : J) : lyMatHom g = mat g := rfl

theorem lyMatHom_injective : Function.Injective lyMatHom := mat_injective

structure FiveRegsRep (r : Array (Array (Array ℕ))) (R : ℕ → Matrix (Fin 111) (Fin 111) (ZMod 5)) :
    Prop where
  size : r.size = 65
  get : ∀ k < 65, toMat 5 111 r[k]! = R k

@[expose] def FiveIns.lt65 : FiveIns → Bool
  | .mu i j k => decide (i < 65) && decide (j < 65) && decide (k < 65)
  | .pwr _ i k => decide (i < 65) && decide (k < 65)

theorem lyFiveProg_lt65 : lyFiveProg.all FiveIns.lt65 = true := by decide +kernel

theorem getElem!_set!_of_lt {α : Type*} [Inhabited α] (r : Array α) (k j : ℕ) (v : α)
    (hj : j < r.size) : (r.set! k v)[j]! = if j = k then v else r[j]! := by
  rw [Array.set!_eq_setIfInBounds, getElem!_pos _ j (by rw [Array.size_setIfInBounds]; exact hj),
    Array.getElem_setIfInBounds hj, getElem!_pos r j hj]
  by_cases h : j = k
  · subst h; simp
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h]

theorem fiveStepArr_rep {r : Array (Array (Array ℕ))} {R : ℕ → Matrix (Fin 111) (Fin 111) (ZMod 5)}
    (hr : FiveRegsRep r R) (ins : FiveIns) (hins : ins.lt65 = true) :
    FiveRegsRep (fiveStepArr r ins) (fiveSlpStep R ins) := by
  cases ins with
  | mu i j k =>
    simp only [FiveIns.lt65, Bool.and_eq_true, decide_eq_true_eq] at hins
    obtain ⟨⟨hi, hj⟩, hk⟩ := hins
    refine ⟨by simp [fiveStepArr, hr.size], fun m hm => ?_⟩
    simp only [fiveStepArr, fiveSlpStep, Function.update_apply]
    rw [getElem!_set!_of_lt _ _ _ _ (by rw [hr.size]; exact hm)]
    split_ifs
    · rw [toMat_mulM, hr.get i hi, hr.get j hj]
    · exact hr.get m hm
  | pwr e i k =>
    simp only [FiveIns.lt65, Bool.and_eq_true, decide_eq_true_eq] at hins
    obtain ⟨hi, hk⟩ := hins
    refine ⟨by simp [fiveStepArr, hr.size], fun m hm => ?_⟩
    simp only [fiveStepArr, fiveSlpStep, Function.update_apply]
    rw [getElem!_set!_of_lt _ _ _ _ (by rw [hr.size]; exact hm)]
    split_ifs
    · rw [toMat_powM, hr.get i hi]
    · exact hr.get m hm

theorem fiveRunArr_rep (prog : List FiveIns) (hprog : prog.all FiveIns.lt65 = true)
    {r : Array (Array (Array ℕ))} {R : ℕ → Matrix (Fin 111) (Fin 111) (ZMod 5)}
    (hr : FiveRegsRep r R) : FiveRegsRep (fiveRunArr prog r) (fiveSlpRun prog R) := by
  induction prog generalizing r R with
  | nil => exact hr
  | cons ins prog ih =>
    rw [List.all_cons, Bool.and_eq_true] at hprog
    exact ih hprog.2 (fiveStepArr_rep hr ins hprog.1)

theorem fiveInitArr_rep : FiveRegsRep fiveInitArr (fiveInit mA mB) := by
  refine ⟨by simp [fiveInitArr], fun k hk => ?_⟩
  have hs : (Array.replicate 65 (idM 111)).size = 65 := by simp
  have hs' : ((Array.replicate 65 (idM 111)).set! 1 matA).size = 65 := by simp
  rw [fiveInitArr, getElem!_set!_of_lt _ _ _ _ (by rw [hs']; exact hk),
    getElem!_set!_of_lt _ _ _ _ (by rw [hs]; exact hk), fiveInit]
  by_cases h1 : k = 1
  · subst h1; simp [toMat_matA]
  · by_cases h2 : k = 2
    · subst h2; simp [toMat_matB]
    · rw [ite_eq_right h2, ite_eq_right h1, ite_eq_right h1, ite_eq_right h2,
        getElem!_pos _ k (by rw [hs]; exact hk), Array.getElem_replicate, toMat_idM]

theorem toMat_lyFiveRegsArr {k : ℕ} (hk : k < 65) :
    toMat 5 111 lyFiveRegsArr[k]! = fiveSlpRun lyFiveProg (fiveInit mA mB) k :=
  (fiveRunArr_rep lyFiveProg lyFiveProg_lt65 fiveInitArr_rep).get k hk

@[expose] def lyFiveAJ : J := fiveSlpRun lyFiveProg (fiveInit a b) 1

@[expose] def lyFiveBJ : J := fiveSlpRun lyFiveProg (fiveInit a b) 2

theorem lyMatHom_regs (k : ℕ) :
    lyMatHom (fiveSlpRun lyFiveProg (fiveInit a b) k) =
      fiveSlpRun lyFiveProg (fiveInit mA mB) k := by
  have h := congrFun (fiveSlpRun_map lyMatHom lyFiveProg (fiveInit a b)) k
  rw [fiveInit_map] at h
  exact h.symm

theorem lyMatHom_AJ : lyMatHom lyFiveAJ = toMat 5 111 lyFiveAArr := by
  rw [lyFiveAJ, lyMatHom_regs, lyFiveAArr, toMat_lyFiveRegsArr (by norm_num)]

theorem lyMatHom_BJ : lyMatHom lyFiveBJ = toMat 5 111 lyFiveBArr := by
  rw [lyFiveBJ, lyMatHom_regs, lyFiveBArr, toMat_lyFiveRegsArr (by norm_num)]

theorem ly_five_small_parts :
    lyFiveChkA25 = true ∧ lyFiveChkX = true ∧ lyFiveChkB8 = true ∧ lyFiveChkB4 = true ∧
      lyFiveChkBX = true ∧ (∀ i, lyFiveChkV i = true) ∧ (∀ i j, lyFiveChkComm i j = true) ∧
      ∀ i, lyFiveChkConj i = true := by
  have h := ly_five_small_check
  simp only [lyFiveSmallCheck, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem ly_five_tree_parts :
    lyFiveParArr.size = 2880 ∧ lyFiveGenArr.size = 2880 ∧ lyFiveNextArr.size = 5760 ∧
      lyFiveQArr.size = 5760 ∧
      (∀ k < 2880, k = 0 ∨ (lyFiveParArr[k]! < k ∧ lyFiveGenArr[k]! < 2)) ∧
      ∀ t < 5760, lyFiveNextArr[t]! < 2880 ∧ lyFiveQArr[t]! < 3125 := by
  have h := ly_five_tree_check
  simp only [lyFiveTreeCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem toMat_foldl_word (L : ℤ → Array (Array ℕ)) (w : List ℤ) (acc : Array (Array ℕ)) :
    toMat 5 111 (w.foldl (fun acc z => mulM 5 111 acc (L z)) acc) =
      toMat 5 111 acc * (w.map fun z => toMat 5 111 (L z)).prod := by
  induction w generalizing acc with
  | nil => simp
  | cons z w ih =>
    rw [List.foldl_cons, ih, toMat_mulM, List.map_cons, List.prod_cons, Matrix.mul_assoc]

theorem toMat_fiveWordArr (w : List ℤ) :
    toMat 5 111 (fiveWordArr w) = fiveWordM (toMat 5 111 lyFiveAArr) (toMat 5 111 lyFiveBArr)
      (toMat 5 111 lyFiveAArr ^ 24) (toMat 5 111 lyFiveBArr ^ 7) w := by
  rw [fiveWordArr, toMat_foldl_word, toMat_idM, Matrix.one_mul, fiveWordM]
  congr 1
  apply List.map_congr_left
  intro z _
  simp only [fiveLetterArr, lyFiveAiArr, lyFiveBiArr]
  split_ifs <;> simp [toMat_powM]

@[expose] def lyFiveXJ : J := lyFiveAJ ^ 5

@[expose] def lyFiveVJ (i : Fin 4) : J := fiveWord lyFiveAJ lyFiveBJ (lyFiveVWords i)

theorem lyFiveAJ_pow25 : lyFiveAJ ^ 25 = 1 := by
  apply lyMatHom_injective
  rw [map_pow, lyMatHom_AJ, map_one, ← toMat_powM, ← toMat_idM 5 111]
  exact toMat_eq_of_beq (show (powM 5 111 lyFiveAArr 25 == idM 111) = true from
    ly_five_small_parts.1)

theorem lyFiveBJ_pow8 : lyFiveBJ ^ 8 = 1 := by
  apply lyMatHom_injective
  rw [map_pow, lyMatHom_BJ, map_one, ← toMat_powM, ← toMat_idM 5 111]
  exact toMat_eq_of_beq (show (powM 5 111 lyFiveBArr 8 == idM 111) = true from
    ly_five_small_parts.2.2.1)

theorem lyFiveAJ_inv : lyFiveAJ⁻¹ = lyFiveAJ ^ 24 := by
  rw [inv_eq_iff_mul_eq_one, ← pow_succ', lyFiveAJ_pow25]

theorem lyFiveBJ_inv : lyFiveBJ⁻¹ = lyFiveBJ ^ 7 := by
  rw [inv_eq_iff_mul_eq_one, ← pow_succ', lyFiveBJ_pow8]

theorem lyMatHom_XJ : lyMatHom lyFiveXJ = toMat 5 111 lyFiveXArr := by
  rw [lyFiveXJ, map_pow, lyMatHom_AJ, lyFiveXArr, toMat_powM]

theorem lyFiveVArr_get (i : Fin 4) : lyFiveVArr[i.val]! = fiveWordArr (lyFiveVWords i) := by
  rw [lyFiveVArr, getElem!_pos _ i.val (by simp), Array.getElem_ofFn]

theorem lyMatHom_VJ (i : Fin 4) : lyMatHom (lyFiveVJ i) = toMat 5 111 lyFiveVArr[i.val]! := by
  rw [lyFiveVJ, fiveWord_eq_fiveWordM, lyFiveAJ_inv, lyFiveBJ_inv, fiveWordM_map, map_pow,
    map_pow, lyMatHom_AJ, lyMatHom_BJ, lyFiveVArr_get, toMat_fiveWordArr]

theorem lyMatHom_nf (c : ZMod 5) (e : Fin 4 → ZMod 5) :
    lyMatHom (fiveNF lyFiveXJ lyFiveVJ c e) =
      toMat 5 111 (fiveNFDirect c.val fun j => (e j).val) := by
  have h0 : ((0 : Fin 4) : ℕ) = 0 := rfl
  have h1 : ((1 : Fin 4) : ℕ) = 1 := rfl
  have h2 : ((2 : Fin 4) : ℕ) = 2 := rfl
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [fiveNF, fiveNFDirect]
  simp only [map_mul, map_pow, lyMatHom_VJ, lyMatHom_XJ, toMat_mulM, toMat_powM, h0, h1, h2, h3]

theorem getElem!_ofFn_lt {α : Type*} [Inhabited α] {n : ℕ} (f : Fin n → α) {i : ℕ} (hi : i < n) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem toMat_lyFiveVPow (i : ℕ) {k : ℕ} (hk : k < 5) :
    toMat 5 111 (lyFiveVPow i)[k]! = toMat 5 111 lyFiveVArr[i]! ^ k := by
  rw [lyFiveVPow, getElem!_ofFn_lt _ hk, toMat_powM]

theorem toMat_lyFiveXPow {c : ℕ} (hc : c < 5) :
    toMat 5 111 lyFiveXPow[c]! = toMat 5 111 lyFiveXArr ^ c := by
  rw [lyFiveXPow, getElem!_ofFn_lt _ hc, toMat_powM]

theorem toMat_lyFiveNFArr {q : ℕ} (hq : q < 3125) :
    toMat 5 111 (lyFiveNFArr q) = toMat 5 111 (fiveNFDirect (fiveDigits q).1.val
      fun j => ((fiveDigits q).2 j).val) := by
  have hv : ∀ n : ℕ, ((n % 5 : ℕ) : ZMod 5).val = n % 5 := fun n => by
    rw [ZMod.val_natCast, Nat.mod_mod]
  simp only [lyFiveNFArr, fiveNFDirect, fiveDigits, hv, toMat_mulM, toMat_powM]
  rw [toMat_lyFiveXPow (Nat.mod_lt _ (by norm_num)), lyFiveP3210,
    getElem!_ofFn_lt _ (by omega), toMat_mulM, lyFiveP321, getElem!_ofFn_lt _ (by omega),
    toMat_mulM, lyFiveP32, getElem!_ofFn_lt _ (by omega), toMat_mulM, lyFiveP3, lyFiveVPow0,
    lyFiveVPow1, lyFiveVPow2,
    toMat_lyFiveVPow _ (by omega), toMat_lyFiveVPow _ (Nat.mod_lt _ (by norm_num)),
    toMat_lyFiveVPow _ (Nat.mod_lt _ (by norm_num)),
    toMat_lyFiveVPow _ (Nat.mod_lt _ (by norm_num))]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, zero_add, pow_one, Nat.div_div_eq_div_mul]
  have e3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [e3]
  congr 5
  norm_num [Nat.mod_eq_of_lt (show q / 625 < 5 by omega)]

theorem fold_push_spec {α : Type*} [Inhabited α] (g : ℕ → Array α → α) :
    ∀ n, (Nat.fold n (fun k _ acc => acc.push (g k acc)) #[]).size = n ∧
      ∀ k < n, (Nat.fold n (fun k _ acc => acc.push (g k acc)) #[])[k]! =
        g k (Nat.fold k (fun k _ acc => acc.push (g k acc)) #[]) := by
  intro n
  induction n with
  | zero => exact ⟨by simp, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ n ih =>
    rw [Nat.fold_succ]
    refine ⟨by rw [Array.size_push, ih.1], fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · rw [getElem!_pos _ k (by rw [Array.size_push, ih.1]; omega), Array.getElem_push_lt
        (by rw [ih.1]; exact hk), ← getElem!_pos _ k (by rw [ih.1]; exact hk), ih.2 k hk]
    · rw [getElem!_pos _ k (by rw [Array.size_push, ih.1]; omega), Array.getElem_push,
        dite_eq_right (by rw [ih.1]; omega)]

theorem fold_push_prefix {α : Type*} [Inhabited α] (g : ℕ → Array α → α) {m n : ℕ}
    (hmn : m ≤ n) {j : ℕ} (hj : j < m) :
    (Nat.fold n (fun k _ acc => acc.push (g k acc)) #[])[j]! =
      (Nat.fold m (fun k _ acc => acc.push (g k acc)) #[])[j]! := by
  rw [(fold_push_spec g n).2 j (by omega), (fold_push_spec g m).2 j hj]

theorem toMat_lyFiveTArr : ∀ k < 2880,
    toMat 5 111 lyFiveTArr[k]! = fiveLift (toMat 5 111 lyFiveAArr) (toMat 5 111 lyFiveBArr) k := by
  have htree := ly_five_tree_parts.2.2.2.2.1
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rw [lyFiveTArr, (fold_push_spec lyFiveTStep 2880).2 k hk]
    rcases htree k hk with rfl | ⟨hp, -⟩
    · rw [lyFiveTStep, ite_eq_left rfl, toMat_idM, fiveLift_zero]
    · rw [lyFiveTStep, ite_eq_right (by omega), toMat_mulM, fiveLift_eq _ _ k (by omega) hp,
        ← fold_push_prefix lyFiveTStep (le_of_lt hk) hp, ← lyFiveTArr, ih _ hp (hp.trans hk)]
      split_ifs <;> rfl

theorem lyFiveXJ_pow5 : lyFiveXJ ^ 5 = 1 := by
  rw [lyFiveXJ, ← pow_mul]
  exact lyFiveAJ_pow25

theorem lyFiveXJ_ne_one : lyFiveXJ ≠ 1 := by
  intro h
  apply toMat_ne_one_of_lyNeId (X := lyFiveXArr) ly_five_small_parts.2.1
  rw [← lyMatHom_XJ, h, map_one]

theorem lyFiveVJ_pow5 (i : Fin 4) : lyFiveVJ i ^ 5 = 1 := by
  have h := Bool.and_eq_true_iff.1 (ly_five_small_parts.2.2.2.2.2.1 i)
  apply lyMatHom_injective
  rw [map_pow, lyMatHom_VJ, map_one, ← toMat_powM, ← toMat_idM 5 111]
  exact toMat_eq_of_beq h.1

theorem lyFiveXJ_comm_VJ (i : Fin 4) : lyFiveXJ * lyFiveVJ i = lyFiveVJ i * lyFiveXJ := by
  have h := Bool.and_eq_true_iff.1 (ly_five_small_parts.2.2.2.2.2.1 i)
  apply lyMatHom_injective
  rw [map_mul, map_mul, lyMatHom_VJ, lyMatHom_XJ, ← toMat_mulM, ← toMat_mulM]
  exact toMat_eq_of_beq h.2

theorem lyFiveVJ_inv (i : Fin 4) : (lyFiveVJ i)⁻¹ = lyFiveVJ i ^ 4 := by
  rw [inv_eq_iff_mul_eq_one, ← pow_succ', lyFiveVJ_pow5]

theorem lyFiveVJ_comm (i j : Fin 4) :
    ⁅lyFiveVJ i, lyFiveVJ j⁆ = lyFiveXJ ^ (lyFiveOmega i j).val := by
  rw [commutatorElement_def, lyFiveVJ_inv, lyFiveVJ_inv]
  apply lyMatHom_injective
  rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, lyMatHom_VJ, lyMatHom_VJ, lyMatHom_XJ,
    ← toMat_powM, ← toMat_powM, ← toMat_powM, ← toMat_mulM, ← toMat_mulM, ← toMat_mulM]
  exact toMat_eq_of_beq (ly_five_small_parts.2.2.2.2.2.2.1 i j)

@[expose] def lyFiveOmegaMat : Matrix (Fin 4) (Fin 4) (ZMod 5) := Matrix.of lyFiveOmega

@[expose] def lyFiveOmegaInv : Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  !![0, 0, 3, 2; 0, 0, 2, 2; 2, 3, 0, 3; 3, 3, 2, 0]

theorem lyFiveOmega_mul_inv : lyFiveOmegaMat * lyFiveOmegaInv = 1 := by decide +kernel

theorem lyFiveOmega_nondeg (e : Fin 4 → ZMod 5) (h : ∀ j, ∑ i, e i * lyFiveOmega i j = 0) :
    e = 0 := by
  have h1 : Matrix.vecMul e lyFiveOmegaMat = 0 := funext fun j => h j
  calc e = Matrix.vecMul e (lyFiveOmegaMat * lyFiveOmegaInv) := by
        rw [lyFiveOmega_mul_inv, Matrix.vecMul_one]
    _ = Matrix.vecMul (Matrix.vecMul e lyFiveOmegaMat) lyFiveOmegaInv := by
        rw [Matrix.vecMul_vecMul]
    _ = 0 := by rw [h1, Matrix.zero_vecMul]

theorem lyFiveBJ_pow4_ne : lyFiveBJ ^ 4 ≠ 1 := by
  intro h
  apply toMat_ne_one_of_lyNeId (X := powM 5 111 lyFiveBArr 4) ly_five_small_parts.2.2.2.1
  rw [toMat_powM, ← lyMatHom_BJ, ← map_pow, h, map_one]

theorem lyFiveBJ_XJ : lyFiveBJ * lyFiveXJ = lyFiveXJ ^ 2 * lyFiveBJ := by
  apply lyMatHom_injective
  rw [map_mul, map_mul, map_pow, lyMatHom_BJ, lyMatHom_XJ, ← toMat_powM, ← toMat_mulM,
    ← toMat_mulM]
  exact toMat_eq_of_beq ly_five_small_parts.2.2.2.2.1

theorem lyFiveAJ_conj (i : Fin 4) :
    lyFiveAJ * lyFiveVJ i =
      fiveNF lyFiveXJ lyFiveVJ (lyFiveAlpha i) (fun j => lyFiveAbar j i) * lyFiveAJ := by
  have h := Bool.and_eq_true_iff.1 (ly_five_small_parts.2.2.2.2.2.2.2 i)
  apply lyMatHom_injective
  rw [map_mul, map_mul, lyMatHom_AJ, lyMatHom_VJ, lyMatHom_nf, ← toMat_mulM, ← toMat_mulM]
  exact toMat_eq_of_beq h.1

theorem lyFiveBJ_conj (i : Fin 4) :
    lyFiveBJ * lyFiveVJ i =
      fiveNF lyFiveXJ lyFiveVJ (lyFiveBeta i) (fun j => lyFiveBbar j i) * lyFiveBJ := by
  have h := Bool.and_eq_true_iff.1 (ly_five_small_parts.2.2.2.2.2.2.2 i)
  apply lyMatHom_injective
  rw [map_mul, map_mul, lyMatHom_BJ, lyMatHom_VJ, lyMatHom_nf, ← toMat_mulM, ← toMat_mulM]
  exact toMat_eq_of_beq h.2

theorem fiveWord_mem {G : Type*} [Group G] (a b : G) (w : List ℤ) :
    fiveWord a b w ∈ closure ({a, b} : Set G) := by
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨z, -, rfl⟩ := List.mem_map.1 hg
  have ha : a ∈ closure ({a, b} : Set G) := subset_closure (Set.mem_insert _ _)
  have hb : b ∈ closure ({a, b} : Set G) := subset_closure (Set.mem_insert_of_mem _ rfl)
  split_ifs
  · exact ha
  · exact hb
  · exact inv_mem ha
  · exact inv_mem hb

theorem lyFiveQRelJ : FiveQRel lyFiveXJ lyFiveVJ lyFiveOmega where
  x5 := lyFiveXJ_pow5
  x1 := lyFiveXJ_ne_one
  v5 := lyFiveVJ_pow5
  xv := lyFiveXJ_comm_VJ
  comm := lyFiveVJ_comm
  nondeg := lyFiveOmega_nondeg

theorem lyFiveMRelJ : FiveMRel lyFiveXJ lyFiveVJ lyFiveOmega lyFiveAJ lyFiveBJ lyFiveAbar
    lyFiveBbar lyFiveAlpha lyFiveBeta where
  q := lyFiveQRelJ
  a25 := lyFiveAJ_pow25
  ax := rfl
  b8 := lyFiveBJ_pow8
  b4 := lyFiveBJ_pow4_ne
  bx := lyFiveBJ_XJ
  av := lyFiveAJ_conj
  bv := lyFiveBJ_conj
  vM := fun _ => fiveWord_mem _ _ _

theorem fiveMat4_fiveArr4 (M : Matrix (Fin 4) (Fin 4) (ZMod 5)) : fiveMat4 (fiveArr4 M) = M := by
  ext i j
  simp only [fiveMat4, fiveArr4, Matrix.of_apply]
  rw [getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]
  congr 1 <;> apply Fin.ext <;> simp
  omega

theorem fiveMul4_eq (X Y : Array (ZMod 5)) :
    fiveMul4 X Y = fiveArr4 (fiveMat4 X * fiveMat4 Y) := by
  simp only [fiveMul4, fiveArr4, fiveMat4, Matrix.mul_apply, Matrix.of_apply]

theorem fiveMat4_fiveMul4 (X Y : Array (ZMod 5)) :
    fiveMat4 (fiveMul4 X Y) = fiveMat4 X * fiveMat4 Y := by
  rw [fiveMul4_eq, fiveMat4_fiveArr4]

theorem lyFiveTbStep_eq (k : ℕ) (acc : Array (Array (ZMod 5))) :
    ∃ M, lyFiveTbStep k acc = fiveArr4 M := by
  unfold lyFiveTbStep
  by_cases h : k = 0
  · rw [ite_eq_left h]
    exact ⟨1, rfl⟩
  · rw [ite_eq_right h]
    exact ⟨_, fiveMul4_eq _ _⟩

theorem lyFiveTbArr_size : lyFiveTbArr.size = 2880 := (fold_push_spec lyFiveTbStep 2880).1

theorem lyFiveTbArr_fix {k : ℕ} (hk : k < 2880) :
    fiveArr4 (fiveMat4 lyFiveTbArr[k]!) = lyFiveTbArr[k]! := by
  rw [lyFiveTbArr, (fold_push_spec lyFiveTbStep 2880).2 k hk]
  obtain ⟨M, hM⟩ :=
    lyFiveTbStep_eq k (Nat.fold k (fun k _ acc => acc.push (lyFiveTbStep k acc)) #[])
  rw [hM, fiveMat4_fiveArr4]

@[expose] def lyFivePar (k : ℕ) : ℕ := lyFiveParArr[k]!

@[expose] def lyFiveGen (k : ℕ) : Bool := decide (lyFiveGenArr[k]! = 1)

@[expose] def lyFiveTb (k : ℕ) : Matrix (Fin 4) (Fin 4) (ZMod 5) := fiveMat4 lyFiveTbArr[k]!

@[expose] def lyFiveNext (k : ℕ) (s : Bool) : ℕ := lyFiveNextArr[2 * k + s.toNat]!

@[expose] def lyFiveQc (k : ℕ) (s : Bool) : ZMod 5 × (Fin 4 → ZMod 5) :=
  fiveDigits lyFiveQArr[2 * k + s.toNat]!

theorem lyFiveTb_zero : lyFiveTb 0 = 1 := by
  rw [lyFiveTb, lyFiveTbArr, (fold_push_spec lyFiveTbStep 2880).2 0 (by norm_num), lyFiveTbStep,
    ite_eq_left rfl, fiveMat4_fiveArr4]

theorem lyFiveTb_succ {k : ℕ} (hk0 : 0 < k) (hk : k < 2880) (hp : lyFiveParArr[k]! < k) :
    lyFiveTb k = (if lyFiveGen k then lyFiveBbar else lyFiveAbar) * lyFiveTb (lyFivePar k) := by
  rw [lyFiveTb, lyFiveTb, lyFiveGen, lyFivePar, lyFiveTbArr,
    (fold_push_spec lyFiveTbStep 2880).2 k hk, lyFiveTbStep,
    ite_eq_right (by omega), fiveMat4_fiveMul4, fiveMat4_fiveArr4,
    fold_push_prefix lyFiveTbStep (le_of_lt hk) hp]
  simp only [decide_eq_true_eq]

theorem lyFiveTb_inj {k l : ℕ} (hk : k < 2880) (hl : l < 2880) (h : lyFiveTb k = lyFiveTb l) :
    k = l := by
  have h2 : lyFiveTbArr[k]! = lyFiveTbArr[l]! := by
    rw [← lyFiveTbArr_fix hk, ← lyFiveTbArr_fix hl]
    exact congrArg fiveArr4 h
  have hs := lyFiveTbArr_size
  rw [getElem!_pos _ k (by omega), getElem!_pos _ l (by omega), ← Array.getElem_toList,
    ← Array.getElem_toList] at h2
  exact (List.Nodup.getElem_inj_iff ly_five_tb_nodup).1 h2

theorem ly_five_rels_parts : ∀ k < 2880, lyFiveRelOK k 0 = true ∧ lyFiveRelOK k 1 = true := by
  have h := ly_five_rels_check
  simp only [lyFiveRelsCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
  exact h

theorem fiveDigits_zero : fiveDigits 0 = (0, 0) := by decide +kernel

theorem fiveNF_digits_zero {G : Type*} [Group G] (x : G) (v : Fin 4 → G) :
    fiveNF x v (fiveDigits 0).1 (fiveDigits 0).2 = 1 := by
  rw [fiveDigits_zero]
  exact FiveQRel.nf_zero

theorem lyFiveRelJ (k s : ℕ) (hk : k < 2880) (hs : s < 2) (hrel : lyFiveRelOK k s = true) :
    (if s = 1 then lyFiveBJ else lyFiveAJ) * fiveLift lyFiveAJ lyFiveBJ k =
      fiveLift lyFiveAJ lyFiveBJ lyFiveNextArr[2 * k + s]! *
        fiveNF lyFiveXJ lyFiveVJ (fiveDigits lyFiveQArr[2 * k + s]!).1
          (fiveDigits lyFiveQArr[2 * k + s]!).2 := by
  have htl : 2 * k + s < 5760 := by omega
  obtain ⟨hnext, hq⟩ := ly_five_tree_parts.2.2.2.2.2 _ htl
  unfold lyFiveRelOK at hrel
  rw [Bool.or_eq_true] at hrel
  rcases hrel with htree | hmat
  · simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at htree
    obtain ⟨⟨⟨hpar, hgen⟩, hne⟩, hq0⟩ := htree
    have hpos : 0 < lyFiveNextArr[2 * k + s]! := Nat.pos_of_ne_zero hne
    rcases ly_five_tree_parts.2.2.2.2.1 _ hnext with h0 | ⟨hp, -⟩
    · exact absurd h0 hne
    rw [fiveLift_eq _ _ _ hpos hp, hpar, hgen, hq0, fiveNF_digits_zero, mul_one]
  · apply lyMatHom_injective
    rw [map_mul, map_mul, apply_ite lyMatHom, fiveLift_map, fiveLift_map, lyMatHom_nf,
      lyMatHom_AJ, lyMatHom_BJ, ← toMat_lyFiveTArr k hk, ← toMat_lyFiveTArr _ hnext,
      ← toMat_lyFiveNFArr hq, ← apply_ite (toMat 5 111), ← toMat_mulM, ← toMat_mulM]
    exact toMat_eq_of_beq hmat

theorem lyFiveRelOK_bool (k : ℕ) (s : Bool) (hk : k < 2880) : lyFiveRelOK k s.toNat = true := by
  cases s
  · rw [Bool.toNat_false]
    exact (ly_five_rels_parts k hk).1
  · rw [Bool.toNat_true]
    exact (ly_five_rels_parts k hk).2

theorem lyFiveRelJ_bool (k : ℕ) (s : Bool) (hk : k < 2880) :
    (if s then lyFiveBJ else lyFiveAJ) * fiveLift lyFiveAJ lyFiveBJ k =
      fiveLift lyFiveAJ lyFiveBJ (lyFiveNext k s) *
        fiveNF lyFiveXJ lyFiveVJ (lyFiveQc k s).1 (lyFiveQc k s).2 := by
  have h := lyFiveRelJ k s.toNat hk (Bool.toNat_lt s) (lyFiveRelOK_bool k s hk)
  have hs : (if s.toNat = 1 then lyFiveBJ else lyFiveAJ) = if s then lyFiveBJ else lyFiveAJ := by
    cases s
    · rw [Bool.toNat_false, ite_eq_right (by decide), ite_eq_right (by decide)]
    · rw [Bool.toNat_true, ite_eq_left rfl, ite_eq_left rfl]
  rw [hs] at h
  rw [lyFiveNext, lyFiveQc]
  exact h

@[expose] def fiveMulEq {G : Type*} [Group G] (u w y z : G) : Prop := u * w = y * z

theorem fiveMulEq_J {u w y z : J} (h : u * w = y * z) : fiveMulEq u w y z := h

theorem lyFiveCertJ : CosetCert lyFiveXJ lyFiveVJ lyFiveAJ lyFiveBJ lyFiveAbar lyFiveBbar 2880
    lyFivePar lyFiveGen (fiveLift lyFiveAJ lyFiveBJ) lyFiveTb lyFiveNext lyFiveQc where
  pos := by norm_num
  par_lt := fun k hk0 hk => by
    rcases ly_five_tree_parts.2.2.2.2.1 k hk with h | ⟨hp, -⟩
    · omega
    · rw [lyFivePar]
      exact hp
  t_zero := fiveLift_zero _ _
  t_succ := fun k hk0 hk => by
    rcases ly_five_tree_parts.2.2.2.2.1 k hk with h | ⟨hp, -⟩
    · omega
    · rw [lyFiveGen, lyFivePar, fiveLift_eq _ _ k hk0 hp]
      simp only [decide_eq_true_eq]
  tb_zero := lyFiveTb_zero
  tb_succ := fun k hk0 hk => by
    rcases ly_five_tree_parts.2.2.2.2.1 k hk with h | ⟨hp, -⟩
    · omega
    · exact lyFiveTb_succ hk0 hk hp
  tb_inj := fun k l hk hl h => lyFiveTb_inj hk hl h
  next_lt := fun k s hk => by
    rw [lyFiveNext]
    exact (ly_five_tree_parts.2.2.2.2.2 (2 * k + s.toNat) (by have := Bool.toNat_lt s; omega)).1
  rel := fun k s hk => fiveMulEq_J (lyFiveRelJ_bool k s hk)

end CFSG.RankThree.Native
