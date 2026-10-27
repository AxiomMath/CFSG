module

public import CFSG.Quasithin.Vol2.KGFactE64Core
public import CFSG.LocalAnalysis.QuasithinUnique.SteinbergCHBinaryLinearParabolic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatO2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsL52Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import Certificates.Certificate7150
public import CFSG.Quasithin.Vol2.KGFactRankInputs

public section

namespace CFSG.Quasithin.H13.KGE64

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.KGInsp CFSG.Quasithin.H13.KGRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

@[expose] def ofB (b : Bool) : ZMod 2 := if b then 1 else 0

theorem ofB_xor (a b : Bool) : ofB (a ^^ b) = ofB a + ofB b := by
  cases a <;> cases b <;> decide

theorem ofB_and (a b : Bool) : ofB (a && b) = ofB a * ofB b := by
  cases a <;> cases b <;> decide

theorem ofB_injective : Function.Injective ofB := by
  intro a b
  cases a <;> cases b <;> decide

theorem ite_eq_self (x : ZMod 2) : (if x = 1 then (1 : ZMod 2) else 0) = x := by
  revert x
  decide

@[expose] def toM (A : List Bool) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  Matrix.of fun i j => ofB (m5 A i j)

theorem m5_map (f : ℕ → Bool) (i j : Fin 5) :
    m5 ((List.range 25).map f) i j = f (5 * i + j) := by
  have h : 5 * (i : ℕ) + j < 25 := by omega
  unfold m5
  simp [List.getD_eq_getElem?_getD, h]

theorem toM_mMul (A B : List Bool) : toM (mMul A B) = toM A * toM B := by
  ext i j
  have h1 : (5 * (i : ℕ) + j) / 5 = i := by omega
  have h2 : (5 * (i : ℕ) + j) % 5 = j := by omega
  simp only [toM, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_five, mMul, m5_map, h1, h2,
    ofB_xor, ofB_and]
  rfl

theorem toM_mId : toM mId = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem toM_mPow (A : List Bool) (k : ℕ) : toM (mPow A k) = toM A ^ k := by
  induction k with
  | zero => exact toM_mId
  | succ k ih => rw [mPow, toM_mMul, ih, pow_succ']

theorem mEq_iff (A B : List Bool) : mEq A B = true ↔ toM A = toM B := by
  unfold mEq
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · intro h
    ext i j
    simp only [toM, Matrix.of_apply]
    rw [h i i.2 j j.2]
  · intro h i hi j hj
    have := congrFun (congrFun h ⟨i, hi⟩) ⟨j, hj⟩
    simp only [toM, Matrix.of_apply] at this
    exact ofB_injective this

theorem ofB_eq_zero {b : Bool} : ofB b = 0 ↔ b = false := by
  cases b <;> decide

theorem ofB_eq_one {b : Bool} : ofB b = 1 ↔ b = true := by
  cases b <;> decide

theorem isUT_iff (A : List Bool) :
    isUT A = true ↔ (∀ i j : Fin 5, j < i → toM A i j = 0) ∧ ∀ i : Fin 5, toM A i i = 1 := by
  unfold isUT
  simp only [List.all_eq_true, List.mem_range, toM, Matrix.of_apply, ofB_eq_zero, ofB_eq_one]
  constructor
  · intro h
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · have := h i i.2 j j.2
      have hji' : (j : ℕ) < i := hji
      simpa [hji'] using this
    · have := h i i.2 i i.2
      simpa using this
  · rintro ⟨hl, hd⟩ i hi j hj
    by_cases hji : j < i
    · simpa [hji] using hl ⟨i, hi⟩ ⟨j, hj⟩ hji
    · by_cases hij : j = i
      · subst hij
        simpa using hd ⟨j, hj⟩
      · simp [hji, hij]

theorem mem_bools : ∀ l : List Bool, l ∈ bools l.length
  | [] => by simp [bools]
  | b :: l => by
    simp only [List.length_cons, bools, List.mem_flatMap]
    exact ⟨l, mem_bools l, by cases b <;> simp⟩

@[expose] def codeOf (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) : List Bool :=
  [decide (M 0 1 = 1), decide (M 0 2 = 1), decide (M 0 3 = 1), decide (M 0 4 = 1),
    decide (M 1 2 = 1), decide (M 1 3 = 1), decide (M 1 4 = 1), decide (M 2 3 = 1),
    decide (M 2 4 = 1), decide (M 3 4 = 1)]

theorem exists_code {u : SpecialLinearGroup (Fin 5) (ZMod 2)}
    (hu : u ∈ unitriangular 5 (ZMod 2)) :
    ∃ l ∈ bools 10, toM (ofCode l) = (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) := by
  obtain ⟨hl, hd⟩ := mem_unitriangular.mp hu
  refine ⟨codeOf u, mem_bools _, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toM, ofCode, m5_map, codeOf, codeIdx, hd, ofB, ite_eq_self,
      hl _ _ (show (0 : Fin 5) < 1 by decide), hl _ _ (show (0 : Fin 5) < 2 by decide),
      hl _ _ (show (0 : Fin 5) < 3 by decide), hl _ _ (show (0 : Fin 5) < 4 by decide),
      hl _ _ (show (1 : Fin 5) < 2 by decide), hl _ _ (show (1 : Fin 5) < 3 by decide),
      hl _ _ (show (1 : Fin 5) < 4 by decide), hl _ _ (show (2 : Fin 5) < 3 by decide),
      hl _ _ (show (2 : Fin 5) < 4 by decide), hl _ _ (show (3 : Fin 5) < 4 by decide)]

theorem eq_one_of_pow_seven {I : Set ℕ} (hI : ∀ j, 1 ≤ j → j ≤ 3 → j ∈ I ∨ j + 1 ∈ I)
    {g : SpecialLinearGroup (Fin 5) (ZMod 2)} (hg : g ∈ flagStabilizer 5 (ZMod 2) I)
    (h7 : g ^ 7 = 1) : g = 1 := by
  have hU : g ∈ unitriangular 5 (ZMod 2) := by
    refine Vol2Native.A312L.mem_unitriangular_of_blocks hg ?_
    intro a m h ha hb hc
    have hm : m ≤ 2 := by
      by_contra hm
      push Not at hm
      rcases hI (a + 1) (by omega) (by omega) with h1 | h1
      · exact hc _ h1 ⟨by omega, by omega⟩
      · exact hc _ h1 ⟨by omega, by omega⟩
    have hL : Vol2Native.A312L.BlockLeft (flagStabilizer 5 (ZMod 2) I) a m := by
      rcases ha with rfl | ha
      · exact Vol2Native.A312L.blockLeft_zero _ m
      · exact Vol2Native.A312L.blockLeft_of_stabilizer fun g hg => mem_flagStabilizer.mp hg a ha
    have hR : Vol2Native.A312L.BlockRight (flagStabilizer 5 (ZMod 2) I) a m := by
      rcases hb with hb | hb
      · exact Vol2Native.A312L.blockRight_top _ hb
      · exact Vol2Native.A312L.blockRight_of_stabilizer fun g hg =>
          mem_flagStabilizer.mp hg (a + m) hb
    have hφ : Vol2Native.A312L.blkMon (flagStabilizer 5 (ZMod 2) I) a m h hL hR ⟨g, hg⟩ ^ 7 =
        1 := by
      rw [← map_pow]
      have : (⟨g, hg⟩ : flagStabilizer 5 (ZMod 2) I) ^ 7 = 1 := Subtype.ext h7
      rw [this, map_one]
    have hφ' : Vol2Native.A312L.blkAt a m h (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
        Vol2Native.A312L.blkMon (flagStabilizer 5 (ZMod 2) I) a m h hL hR ⟨g, hg⟩ := rfl
    rw [hφ']
    generalize Vol2Native.A312L.blkMon (flagStabilizer 5 (ZMod 2) I) a m h hL hR ⟨g, hg⟩ = M
      at hφ ⊢
    interval_cases m
    · exact Subsingleton.elim _ _
    · revert M
      decide +kernel
    · revert M
      decide +kernel
  have hcardU : Nat.card (unitriangular 5 (ZMod 2)) = 2 ^ 10 := by
    rw [card_unitriangular, Nat.card_zmod]
  have h1 : (⟨g, hU⟩ : unitriangular 5 (ZMod 2)) ^ 2 ^ 10 = 1 := by
    rw [← hcardU]
    exact pow_card_eq_one'
  have h2 : g ^ 2 ^ 10 = 1 := congrArg Subtype.val h1
  have h3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h7) (orderOf_dvd_of_pow_eq_one h2)
  norm_num at h3
  exact h3

theorem exists_reflections {N : Subgroup (SpecialLinearGroup (Fin 5) (ZMod 2))}
    (hU : unitriangular 5 (ZMod 2) ≤ N) {y : SpecialLinearGroup (Fin 5) (ZMod 2)} (hy : y ∈ N)
    (hord : orderOf y = 7) :
    ∃ j, (j = 1 ∨ j = 2 ∨ j = 3) ∧ ∃ (h1 : 1 ≤ j) (h2 : j + 1 < 5),
      reflection 5 (ZMod 2) j h1 (by omega) ∈ N ∧ reflection 5 (ZMod 2) (j + 1) (by omega) h2 ∈ N
      := by
  by_contra hcon
  push Not at hcon
  have hI : ∀ j, 1 ≤ j → j ≤ 3 → j ∈ borelOvergroupCuts N ∨ j + 1 ∈ borelOvergroupCuts N := by
    intro j hj1 hj3
    by_contra h
    push Not at h
    exact hcon j (by omega) hj1 (by omega)
      (SteinbergCH.reflection_mem_of_not_mem_borelOvergroupCuts hj1 (by omega) h.1)
      (SteinbergCH.reflection_mem_of_not_mem_borelOvergroupCuts (by omega) (by omega) h.2)
  have hle := Setup.X7a.le_flagStabilizer_borelOvergroupCuts N hU
  have hy1 := eq_one_of_pow_seven hI (hle hy) (by rw [← hord]; exact pow_orderOf_eq_one y)
  rw [hy1, orderOf_one] at hord
  norm_num at hord

theorem yElt_lt {j : ℕ} (h2 : j + 1 < 5) : (⟨j - 1, by omega⟩ : Fin 5) < ⟨j + 1, h2⟩ :=
  Fin.lt_def.mpr (by simp only; omega)

@[expose] def yElt (j : ℕ) (h1 : 1 ≤ j) (h2 : j + 1 < 5) : SpecialLinearGroup (Fin 5) (ZMod 2) :=
  reflection 5 (ZMod 2) j h1 (by omega) * reflection 5 (ZMod 2) (j + 1) (by omega) h2 *
    SpecialLinearGroup.transvection (yElt_lt h2).ne (1 : ZMod 2)

theorem coe_yElt1 :
    (yElt 1 (by norm_num) (by norm_num) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = toM (l52Y 1) := by
  decide +kernel

theorem coe_yElt2 :
    (yElt 2 (by norm_num) (by norm_num) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = toM (l52Y 2) := by
  decide +kernel

theorem coe_yElt3 :
    (yElt 3 (by norm_num) (by norm_num) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = toM (l52Y 3) := by
  decide +kernel

theorem coe_yElt {j : ℕ} (hj : j = 1 ∨ j = 2 ∨ j = 3) (h1 : 1 ≤ j) (h2 : j + 1 < 5) :
    (yElt j h1 h2 : Matrix (Fin 5) (Fin 5) (ZMod 2)) = toM (l52Y j) := by
  rcases hj with rfl | rfl | rfl
  · exact coe_yElt1
  · exact coe_yElt2
  · exact coe_yElt3

theorem yElt_mem {N : Subgroup (SpecialLinearGroup (Fin 5) (ZMod 2))}
    (hU : unitriangular 5 (ZMod 2) ≤ N) {j : ℕ} (h1 : 1 ≤ j) (h2 : j + 1 < 5)
    (hr1 : reflection 5 (ZMod 2) j h1 (by omega) ∈ N)
    (hr2 : reflection 5 (ZMod 2) (j + 1) (by omega) h2 ∈ N) : yElt j h1 h2 ∈ N :=
  N.mul_mem (N.mul_mem hr1 hr2) (hU (transvection_mem_unitriangular (yElt_lt h2) 1))

theorem toM_powers (y : SpecialLinearGroup (Fin 5) (ZMod 2)) {Y : List Bool}
    (hy : (y : Matrix (Fin 5) (Fin 5) (ZMod 2)) = toM Y) (k : ℕ) {i : ℕ} (hi : i < 8) :
    toM (((List.range 8).map (mPow (mPow Y k))).getD i []) =
      (((y ^ k) ^ i : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range,
    toM_mPow, toM_mPow, ← hy, Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_pow]

theorem toM_cj5 (y : SpecialLinearGroup (Fin 5) (ZMod 2)) {Y : List Bool}
    (hy : (y : Matrix (Fin 5) (Fin 5) (ZMod 2)) = toM Y) (hy7 : y ^ 7 = 1) (k : ℕ)
    {a : SpecialLinearGroup (Fin 5) (ZMod 2)} {A : List Bool}
    (ha : (a : Matrix (Fin 5) (Fin 5) (ZMod 2)) = toM A) {i : ℕ} (hi : i ≤ 7) :
    toM (cj5 ((List.range 8).map (mPow (mPow Y k))) A i) =
      ((conjP (y ^ k) a i : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) := by
  have hyk : (y ^ k) ^ 7 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hy7, one_pow]
  unfold cj5
  rw [toM_mMul, toM_mMul, toM_powers y hy k (by omega), toM_powers y hy k (by omega), ← ha]
  unfold conjP
  have hinv : ((y ^ k) ^ i)⁻¹ = (y ^ k) ^ (7 - i) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_add, show i + (7 - i) = 7 by omega, hyk]
  rw [hinv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]

theorem coe_eq_one_iff (g : SpecialLinearGroup (Fin 5) (ZMod 2)) :
    (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 ↔ g = 1 :=
  ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩

theorem l52_sound (hc : l52Check = true) {j : ℕ} (hj : j = 1 ∨ j = 2 ∨ j = 3)
    {y : SpecialLinearGroup (Fin 5) (ZMod 2)}
    (hy : (y : Matrix (Fin 5) (Fin 5) (ZMod 2)) = toM (l52Y j)) :
    y ^ 7 = 1 ∧ ∀ k, 1 ≤ k → k ≤ 6 → ∀ a b : SpecialLinearGroup (Fin 5) (ZMod 2),
      (∀ i ≤ 6, conjP (y ^ k) a i ∈ unitriangular 5 (ZMod 2)) →
      (∀ i ≤ 6, conjP (y ^ k) b i ∈ unitriangular 5 (ZMod 2)) → ¬ Bad (y ^ k) a b := by
  have hcj : mEq (mPow (l52Y j) 7) mId = true ∧ l52CheckY (l52Y j) = true := by
    unfold l52Check at hc
    simp only [List.all_eq_true, List.mem_cons, List.not_mem_nil, or_false, Bool.and_eq_true]
      at hc
    exact hc j (by omega)
  have hy7 : y ^ 7 = 1 := by
    rw [← coe_eq_one_iff, Matrix.SpecialLinearGroup.coe_pow, hy, ← toM_mPow, ← toM_mId]
    exact (mEq_iff _ _).mp hcj.1
  refine ⟨hy7, fun k hk1 hk6 a b ha hb hbad => ?_⟩
  obtain ⟨hane, hbne, haa, hbb, hfa, hfb, hcomm⟩ := hbad
  have hck := hcj.2
  unfold l52CheckY at hck
  rw [List.all_eq_true] at hck
  have hk := hck k (List.mem_range'.mpr ⟨k - 1, by omega, by omega⟩)
  dsimp only at hk
  rw [List.all_eq_true] at hk
  have ha0 : a ∈ unitriangular 5 (ZMod 2) := by simpa [conjP] using ha 0 (by norm_num)
  have hb0 : b ∈ unitriangular 5 (ZMod 2) := by simpa [conjP] using hb 0 (by norm_num)
  obtain ⟨la, hla, hla'⟩ := exists_code ha0
  obtain ⟨lb, hlb, hlb'⟩ := exists_code hb0
  have hcjA := fun i (hi : i ≤ 7) => toM_cj5 y hy hy7 k hla'.symm hi
  have hcjB := fun i (hi : i ≤ 7) => toM_cj5 y hy hy7 k hlb'.symm hi
  have hUT : ∀ x : SpecialLinearGroup (Fin 5) (ZMod 2), x ∈ unitriangular 5 (ZMod 2) →
      ∀ X : List Bool, toM X = (x : Matrix (Fin 5) (Fin 5) (ZMod 2)) → isUT X = true :=
    fun x hx X hX => (isUT_iff X).mpr (by rw [hX]; exact mem_unitriangular.mp hx)
  have hcand : ∀ (c : SpecialLinearGroup (Fin 5) (ZMod 2)) (lc : List Bool), lc ∈ bools 10 →
      (∀ i ≤ 6, conjP (y ^ k) c i ∈ unitriangular 5 (ZMod 2)) →
      toM (ofCode lc) = (c : Matrix (Fin 5) (Fin 5) (ZMod 2)) →
        ofCode lc ∈ ((bools 10).map ofCode).filter fun u =>
          (List.range' 1 6).all fun i => isUT (cj5 ((List.range 8).map (mPow (mPow (l52Y j) k)))
            u i) := by
    intro c lc hlc0 hc' hlc
    refine List.mem_filter.mpr ⟨List.mem_map.mpr ⟨lc, hlc0, rfl⟩, ?_⟩
    rw [List.all_eq_true]
    intro i hi
    obtain ⟨i', hi', rfl⟩ := List.mem_range'.mp hi
    exact hUT _ (hc' _ (by omega)) _ (toM_cj5 y hy hy7 k hlc.symm (by omega))
  have hA : condA5 ((List.range 8).map (mPow (mPow (l52Y j) k))) (ofCode la) = true := by
    unfold condA5
    simp only [Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Bool.eq_false_iff]
      intro h
      rw [mEq_iff, toM_mId, hla', coe_eq_one_iff] at h
      exact hane h
    · rw [mEq_iff, toM_mMul, toM_mId, hla', ← Matrix.SpecialLinearGroup.coe_mul, coe_eq_one_iff]
      exact haa
    · rw [mEq_iff, toM_mMul, toM_mMul, hcjA 3 (by norm_num), hcjA 1 (by norm_num), toM_mId, hla',
        ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, coe_eq_one_iff]
      exact hfa
  have hB : condB5 ((List.range 8).map (mPow (mPow (l52Y j) k))) (ofCode lb) = true := by
    unfold condB5
    simp only [Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Bool.eq_false_iff]
      intro h
      rw [mEq_iff, toM_mId, hlb', coe_eq_one_iff] at h
      exact hbne h
    · rw [mEq_iff, toM_mMul, toM_mId, hlb', ← Matrix.SpecialLinearGroup.coe_mul, coe_eq_one_iff]
      exact hbb
    · rw [mEq_iff, toM_mMul, toM_mMul, hcjB 3 (by norm_num), hcjB 2 (by norm_num), toM_mId, hlb',
        ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, coe_eq_one_iff]
      exact hfb
  have hC : commAll5 ((List.range 8).map (mPow (mPow (l52Y j) k))) (ofCode la) (ofCode lb) =
      true := by
    unfold commAll5
    simp only [List.all_eq_true, List.mem_range]
    intro i hi i' hi'
    rw [mEq_iff, toM_mMul, toM_mMul, hcjA i (by omega), hcjB i' (by omega),
      ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul]
    rw [hcomm i hi i' hi']
  have h1 := hk (ofCode la) (List.mem_filter.mpr ⟨hcand a la hla ha hla', hA⟩)
  rw [List.all_eq_true] at h1
  have h2 := h1 (ofCode lb) (List.mem_filter.mpr ⟨hcand b lb hlb hb hlb', hB⟩)
  rw [hC] at h2
  exact Bool.noConfusion h2

theorem l52Y_ne_one {j : ℕ} (hj : j = 1 ∨ j = 2 ∨ j = 3) : toM (l52Y j) ≠ 1 := by
  rcases hj with rfl | rfl | rfl <;> decide +kernel

theorem nonempty_mulEquiv_sl52 {X : Type} [Group X] [Finite X]
    (hX : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 5 2 1) :
    Nonempty (X ≃* SpecialLinearGroup (Fin 5) (ZMod 2)) := by
  obtain ⟨-, F, _, _, hF, ⟨e₀⟩⟩ := hX
  have hF2 : Nat.card F = 2 := by rw [hF, pow_one]
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF' : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card, hF2]
  have : CharP F 2 :=
    finite_field_prime_power_characteristic Nat.prime_two (k := 1) le_rfl (by rw [hF2, pow_one])
  let ψ : SpecialLinearGroup (Fin 5) F ≃* projectiveSL 5 F := Vol2Native.A312L.slEquivProj hF2 5
  let φ : X ≃* SpecialLinearGroup (Fin 5) F :=
    (e₀.trans (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 5 F).symm).trans ψ.symm
  exact ⟨φ.trans (Vol2Native.L239.L52.slEquivOfRingEquiv (ZMod.ringEquiv F hF').symm 5)⟩

theorem card_sl52 : Nat.card (SpecialLinearGroup (Fin 5) (ZMod 2)) = 9999360 := by
  rw [Matrix.card_SL_field]
  simp [Fin.prod_univ_five]

theorem not_heInspCfg_l52 {X : Type} [Group X] [Finite X]
    (hX : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 5 2 1) : ¬ HeInspCfg X 3 := by
  intro hcfg
  obtain ⟨e⟩ := nonempty_mulEquiv_sl52 hX
  have : IsSimpleGroup (SpecialLinearGroup (Fin 5) (ZMod 2)) :=
    Vol2Native.A312L.sl_isSimple_of_card_two (Nat.card_zmod 2) (by norm_num)
  have : IsSimpleGroup X := MulEquiv.isSimpleGroup e
  have hcardX : Nat.card X = 9999360 := by rw [Nat.card_congr e.toEquiv, card_sl52]
  have hD := (badData_of_cfg (by rw [hcardX]; norm_num) hcfg).map e
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (n := 5) (by norm_num)
  have hU : IsSylowTwoOf (unitriangular 5 (ZMod 2)) ⊤ := hP₀ ▸ isSylowTwoOf_top_of_sylow P₀
  obtain ⟨N, y, a, b, hUN, -, hy, hord, ha, hb, hbad⟩ := hD.conj hU
  obtain ⟨j, hj, h1, h2, hr1, hr2⟩ := exists_reflections hUN hy hord
  have hy₀N : yElt j h1 h2 ∈ N := yElt_mem hUN h1 h2 hr1 hr2
  obtain ⟨hy₀7, hsound⟩ := l52_sound Certificates.certificate7150 hj (coe_yElt hj h1 h2)
  have hy₀1 : yElt j h1 h2 ≠ 1 := fun h => l52Y_ne_one hj (by rw [← coe_yElt hj h1 h2, h]; rfl)
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hord₀ : orderOf (yElt j h1 h2) = 7 := orderOf_eq_prime hy₀7 hy₀1
  have h49 : ¬ 49 ∣ Nat.card N := fun h => by
    have h' := h.trans (Subgroup.card_subgroup_dvd_card N)
    rw [card_sl52] at h'
    norm_num at h'
  obtain ⟨g, hg, k, hk1, hk6, rfl⟩ := exists_conj_pow h49 hy hy₀N hord hord₀
  set φ : SpecialLinearGroup (Fin 5) (ZMod 2) →* SpecialLinearGroup (Fin 5) (ZMod 2) :=
    (MulAut.conj g⁻¹).toMonoidHom with hφ
  have hbad' := hbad.map (φ := φ) (MulAut.conj g⁻¹).injective
  have hφy : φ (g * yElt j h1 h2 ^ k * g⁻¹) = yElt j h1 h2 ^ k := by simp [hφ, mul_assoc]
  rw [hφy] at hbad'
  obtain ⟨hU2, hUi⟩ := K1.isSylowTwoOf_top_iff.mp hU
  have hUodd : ¬ 2 ∣ ((unitriangular 5 (ZMod 2)).subgroupOf N).index := fun h2 =>
    hUi (h2.trans (Subgroup.relIndex_dvd_index_of_le hUN))
  have hconjU : ∀ z ∈ pCoreOf 2 N, ∀ i ≤ 6,
      conjP (yElt j h1 h2 ^ k) (φ z) i ∈ unitriangular 5 (ZMod 2) := by
    intro z hz i _
    have hz' : φ z ∈ pCoreOf 2 N := by
      have := conj_mem_pCoreOf (N.inv_mem hg) hz
      simpa [hφ] using this
    have hw : ((yElt j h1 h2 ^ k) ^ i)⁻¹ ∈ N := N.inv_mem (N.pow_mem (N.pow_mem hy₀N k) i)
    have := ((Ch1.SporLat.mem_pCoreOf_iff hUN hU2 hUodd _).mp hz').2 _ hw
    simpa [conjP] using this
  exact hsound k hk1 hk6 (φ a) (φ b) (hconjU a ha) (hconjU b hb) hbad'

end CFSG.Quasithin.H13.KGE64
