module

public import CFSG.Sporadic.Co1Patterson.TwistNativeBasis
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeBridgeBase
public import CFSG.Sporadic.Co1Patterson.NativeSetting

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson.TwistNative

open Subgroup CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.LargeExtraspecial
open CFSG.Blueprint (NativeSporadic.Co1)
open CFSG.EvenSmallLie.OmegaEight (vecK ind)

theorem card_zmod_two : Nat.card (ZMod 2) = 2 := by simp

@[expose] noncomputable def bv (c : ℕ) : Fin 8 → ZMod 2 := plusCoords.symm (vecK (ZMod 2) c)

theorem cidx_finSumFinEquiv_symm (i : Fin 8) :
    CFSG.EvenSmallLie.OmegaEight.cidx (finSumFinEquiv.symm i) = i := by
  fin_cases i <;> rfl

theorem bv_apply (c : ℕ) (i : Fin 8) : bv c i = ind (ZMod 2) (c.testBit i) := by
  simp only [bv, plusCoords, LinearEquiv.funCongrLeft_symm, LinearEquiv.funCongrLeft_apply,
    LinearMap.funLeft_apply, vecK, cidx_finSumFinEquiv_symm]

theorem plusCoords_bv (c : ℕ) : plusCoords (bv c) = vecK (ZMod 2) c := by
  rw [bv, LinearEquiv.apply_symm_apply]

theorem bv_xor (a b : ℕ) : bv (a ^^^ b) = bv a + bv b := by
  rw [bv, CFSG.EvenSmallLie.OmegaEight.vecK_xor card_zmod_two, map_add]
  rfl

theorem bv_zero : bv 0 = 0 := by
  rw [bv, CFSG.EvenSmallLie.OmegaEight.vecK_zero, map_zero]

theorem q₀_bv (c : ℕ) : q₀ (bv c) = ind (ZMod 2) (CFSG.EvenSmallLie.OmegaEight.qNat c) := by
  rw [← quadPlus_plusCoords, plusCoords_bv, CFSG.EvenSmallLie.OmegaEight.quadPlus_vecK
    card_zmod_two]

theorem exists_bv (v : Fin 8 → ZMod 2) : ∃ c < 256, bv c = v := by
  obtain ⟨c, hc, hv⟩ := CFSG.EvenSmallLie.OmegaEight.exists_vecK card_zmod_two (plusCoords v)
  exact ⟨c, hc, by rw [bv, hv, LinearEquiv.symm_apply_apply]⟩

theorem ind_eq_zero_iff (b : Bool) : ind (ZMod 2) b = 0 ↔ b = false := by
  cases b <;> simp [ind]

theorem ind_eq_one_iff (b : Bool) : ind (ZMod 2) b = 1 ↔ b = true := by
  cases b <;> simp [ind]

theorem zmod_two_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem bv_eq_sum (c : ℕ) : bv c = ∑ k : Fin 8, ind (ZMod 2) (c.testBit k) • Pi.single k 1 := by
  funext i
  rw [bv_apply, Finset.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [Ne.symm hk]
  · simp

theorem foldl_range_if_add {V : Type*} [AddCommMonoid V] (p : ℕ → Bool) (F : ℕ → V) (n : ℕ)
    (a : V) : (List.range n).foldl (fun acc i => if p i then acc + F i else acc) a =
      a + ∑ i ∈ Finset.range n, (if p i then F i else 0) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]
    simp only [List.foldl_cons, List.foldl_nil]
    by_cases hp : p n
    · rw [ite_eq_left hp, ite_eq_left hp, add_assoc]
    · simp [hp]

theorem bv_foldl_xor (p : ℕ → Bool) (F : ℕ → ℕ) (n a : ℕ) :
    bv ((List.range n).foldl (fun acc i => if p i then acc ^^^ F i else acc) a) =
      (List.range n).foldl (fun acc i => if p i then acc + bv (F i) else acc) (bv a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    by_cases hp : p n
    · rw [ite_eq_left hp, ite_eq_left hp, bv_xor, ih]
    · rw [ite_eq_right hp, ite_eq_right hp, ih]

theorem bv_colsApply (m : List ℕ) (v : ℕ) :
    bv (colsApply m v) = ∑ k : Fin 8, ind (ZMod 2) (v.testBit k) • bv (m.getD k 0) := by
  rw [colsApply, bv_foldl_xor, bv_zero, foldl_range_if_add, zero_add,
    ← Fin.sum_univ_eq_sum_range (fun i => if v.testBit i then bv (m.getD i 0) else 0)]
  refine Finset.sum_congr rfl fun k _ => ?_
  cases v.testBit k <;> simp [ind]

theorem bv_two_pow {k : ℕ} (hk : k < 8) : bv (2 ^ k) = Pi.single ⟨k, hk⟩ 1 := by
  funext i
  rw [bv_apply, Nat.testBit_two_pow, Pi.single_apply]
  by_cases h : k = i
  · subst h
    simp [ind]
  · have h' : i ≠ ⟨k, hk⟩ := fun e => h (by rw [e])
    simp [ind, h, h']

theorem apply_bv_of_cols (f : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) (m : List ℕ)
    (hf : ∀ k, k < 8 → f (bv (2 ^ k)) = bv (m.getD k 0)) (v : ℕ) :
    f (bv v) = bv (colsApply m v) := by
  rw [bv_colsApply, bv_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, ← hf k k.2, bv_two_pow k.2]

theorem linearMap_ext_bv {f g : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)}
    (h : ∀ k, k < 8 → f (bv (2 ^ k)) = g (bv (2 ^ k))) : f = g := by
  refine LinearMap.pi_ext' fun k => LinearMap.ext_ring ?_
  have := h k k.2
  rw [bv_two_pow k.2] at this
  simpa using this

theorem foldl_range_single {G : Type*} [Group G] (p : ℕ → Bool) (x : ℕ → G) {k n : ℕ}
    (hk : k < n) (hp : ∀ i, p i = true ↔ i = k) :
    (List.range n).foldl (fun b i => if p i then b * x i else b) 1 = x k := by
  have key : ∀ m, (List.range m).foldl (fun b i => if p i then b * x i else b) 1 =
      if k < m then x k else 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil]
      by_cases hm : m = k
      · subst hm
        rw [ite_eq_left ((hp m).2 rfl), ite_eq_right (lt_irrefl m),
          ite_eq_left (Nat.lt_succ_self m), one_mul]
      · rw [ite_eq_right fun h => hm ((hp m).1 h)]
        by_cases hkm : k < m
        · rw [ite_eq_left hkm, ite_eq_left (Nat.lt_succ_of_lt hkm)]
        · rw [ite_eq_right hkm, ite_eq_right (by omega)]
  rw [key, ite_eq_left hk]

theorem testBit_two_pow_iff (k i : ℕ) : (2 ^ k).testBit i = true ↔ i = k := by
  rw [Nat.testBit_two_pow]
  constructor
  · intro h
    exact (of_decide_eq_true h).symm
  · rintro rfl
    exact decide_eq_true rfl

theorem yprodG_two_pow {k : ℕ} (hk : k < 8) : yprodG (2 ^ k) = yG k := by
  unfold yprodG
  exact foldl_range_single (fun i => (2 ^ k).testBit i) yG hk (testBit_two_pow_iff k)

theorem testBit_mod_256 (c : ℕ) {i : ℕ} (hi : i < 8) : (c % 256).testBit i = c.testBit i := by
  rw [show (256 : ℕ) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow]
  simp [hi]

theorem yprodG_mod (c : ℕ) : yprodG (c % 256) = yprodG c := by
  unfold yprodG
  refine List.foldl_ext _ _ _ fun b i hi => ?_
  rw [testBit_mod_256 c (List.mem_range.1 hi)]

theorem bv_mod (c : ℕ) : bv (c % 256) = bv c := by
  funext i
  rw [bv_apply, bv_apply, testBit_mod_256 c i.2]

theorem bool_eq_not_iff {a b : Bool} (h : a = !b) : a = true ↔ b = false := by
  cases a <;> cases b <;> simp_all

theorem yFormOK_parts : ∀ c < 256,
    ((Native.mul (yprodRow c) (yprodRow c) == Native.one) =
      !CFSG.EvenSmallLie.OmegaEight.qNat c) ∧
    ∀ i < 8, ((Native.mul (yprodRow c) (yRow ((i + 4) % 8)) ==
      Native.mul (yRow ((i + 4) % 8)) (yprodRow c)) = !c.testBit i) := by
  have h := tw_yForm_check
  simp only [yFormOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  exact h

section Embed

@[expose] noncomputable def toH (g : GL24) (hg : g ∈ GA ⊓ centralizer {aG}) :
    centralizer ({aNC} : Set NativeSporadic.Co1) :=
  ⟨co1MatEquiv.symm ⟨g, (mem_inf.1 hg).1⟩, mem_centralizer_aNC_iff.2 (by
    rw [nativeEmb_apply, MulEquiv.apply_symm_apply]
    exact (mem_inf.1 hg).2)⟩

theorem centEmb_toH (g : GL24) (hg : g ∈ GA ⊓ centralizer {aG}) : centEmb (toH g hg) = g := by
  rw [centEmb_apply]
  change ((co1MatEquiv (co1MatEquiv.symm ⟨g, (mem_inf.1 hg).1⟩) : GA) : GL24) = g
  rw [MulEquiv.apply_symm_apply]

theorem yG_mem_cent (i : ℕ) : yG i ∈ GA ⊓ centralizer {aG} := twoAQ_le (yG_mem_twoAQ i)

theorem yprodG_mem_cent (c : ℕ) : yprodG c ∈ GA ⊓ centralizer {aG} :=
  twoAQ_le (yprodG_mem_twoAQ c)

@[expose] noncomputable def yH (i : ℕ) : centralizer ({aNC} : Set NativeSporadic.Co1) :=
  toH (yG i) (yG_mem_cent i)

@[expose] noncomputable def yprodH (c : ℕ) : centralizer ({aNC} : Set NativeSporadic.Co1) :=
  toH (yprodG c) (yprodG_mem_cent c)

theorem centEmb_yH (i : ℕ) : centEmb (yH i) = yG i := centEmb_toH _ _

theorem centEmb_yprodH (c : ℕ) : centEmb (yprodH c) = yprodG c := centEmb_toH _ _

theorem yprodH_two_pow {k : ℕ} (hk : k < 8) : yprodH (2 ^ k) = yH k :=
  centEmb_injective (by rw [centEmb_yprodH, centEmb_yH, yprodG_two_pow hk])

theorem yprodH_mod (c : ℕ) : yprodH (c % 256) = yprodH c :=
  centEmb_injective (by rw [centEmb_yprodH, centEmb_yprodH, yprodG_mod])

theorem centEmb_zM :
    centEmb nativeSetting.zM = aG := nativeEmb_aNC

theorem yprodG_sq_eq_one_iff {c : ℕ} (hc : c < 256) :
    yprodG c * yprodG c = 1 ↔ CFSG.EvenSmallLie.OmegaEight.qNat c = false := by
  rw [← bool_eq_not_iff (yFormOK_parts c hc).1,
    rows_beq_iff ((rep_yprodG c).mul (rep_yprodG c)) MRep.one
      (valid_mul (dagOK_parts.2.2.2.1 c hc) (dagOK_parts.2.2.2.1 c hc)) validRows_one]

theorem yprodG_comm_iff {c i : ℕ} (hc : c < 256) (hi : i < 8) :
    yprodG c * yG ((i + 4) % 8) = yG ((i + 4) % 8) * yprodG c ↔ c.testBit i = false := by
  have hv := dagOK_parts.2.2.1 ((i + 4) % 8) (Nat.mod_lt _ (by norm_num))
  rw [← bool_eq_not_iff ((yFormOK_parts c hc).2 i hi),
    rows_beq_iff ((rep_yprodG c).mul (rep_yG _)) ((rep_yG _).mul (rep_yprodG c))
      (valid_mul (dagOK_parts.2.2.2.1 c hc) hv) (valid_mul hv (dagOK_parts.2.2.2.1 c hc))]

end Embed

end CFSG.Sporadic.Co1Patterson.TwistNative
