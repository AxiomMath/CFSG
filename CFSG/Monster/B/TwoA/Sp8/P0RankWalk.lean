module

public import Certificates.Data.CFSGNative.MonsterB.P0Rank
public import Mathlib.Data.Finset.Max
public import Batteries.Data.Nat.Bitwise.Lemmas

public section

namespace CFSG.Monster.B.TwoA.Sp8.P0Rank

open MonsterB.P0Rank

@[expose] def XorClosed (S : Finset ℕ) : Prop := 0 ∈ S ∧ ∀ a ∈ S, ∀ b ∈ S, a ^^^ b ∈ S

private lemma two_pow_le_xor_of_lt {x v top : ℕ} (hx : x < 2 ^ top) (hv : 2 ^ top ≤ v) :
    2 ^ top ≤ v ^^^ x := by
  have hp : 0 < 2 ^ top := Nat.pow_pos (by decide)
  have hx0 : x / 2 ^ top = 0 := Nat.div_eq_of_lt hx
  have hd : (v ^^^ x) / 2 ^ top = v / 2 ^ top := by
    rw [Nat.xor_div_two_pow, hx0, Nat.xor_zero]
  have hvpos : 0 < v / 2 ^ top := Nat.div_pos hv hp
  by_contra h
  rw [Nat.div_eq_of_lt (Nat.lt_of_not_le h)] at hd
  omega

private lemma xor_lt_two_pow_dyadic {x y b : ℕ} (hx : 2 ^ b ≤ x) (hx' : x < 2 ^ (b + 1))
    (hy : 2 ^ b ≤ y) (hy' : y < 2 ^ (b + 1)) : x ^^^ y < 2 ^ b := by
  have hlt : x ^^^ y < 2 ^ (b + 1) := Nat.xor_lt_two_pow hx' hy'
  have hbit : (x ^^^ y).testBit b = false := by
    rw [Nat.testBit_xor, Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hx hx',
      Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hy hy']
    rfl
  by_contra h
  have hge : 2 ^ b ≤ x ^^^ y := Nat.le_of_not_lt h
  have htrue := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hge hlt
  rw [hbit] at htrue
  exact Bool.false_ne_true htrue

theorem swalk_sound {α : Type} {cands : α → List ℕ} {upd : α → ℕ → α}
    {visit : List ℕ → α → Bool} {S : Finset ℕ} (hS : XorClosed S)
    (I : List ℕ → ℕ → α → Prop)
    (hcand : ∀ node top a, I node top a → (∀ x, x ∈ node ↔ x ∈ S ∧ x < 2 ^ top) →
      ∀ v ∈ S, 2 ^ top ≤ v → v ∈ cands a)
    (hupd : ∀ node top a v, I node top a → (∀ x, x ∈ node ↔ x ∈ S ∧ x < 2 ^ top) →
      v ∈ S → 2 ^ top ≤ v → (∀ w ∈ S, 2 ^ top ≤ w → v ≤ w) →
      I (node ++ node.map (v ^^^ ·)) (Nat.log2 v + 1) (upd a v))
    {fuel : ℕ} {node : List ℕ} {top : ℕ} {a : α}
    (h : swalk cands upd visit fuel node top a = true) (hI : I node top a)
    (hnode : ∀ x, x ∈ node ↔ x ∈ S ∧ x < 2 ^ top) :
    ∃ node' top' a', (∀ x, x ∈ node' ↔ x ∈ S) ∧ I node' top' a' ∧ visit node' a' = true := by
  induction fuel generalizing node top a with
  | zero => simp [swalk] at h
  | succ fuel ih =>
    simp only [swalk, Bool.and_eq_true] at h
    obtain ⟨hvisit, hall⟩ := h
    by_cases hsome : ∃ v, v ∈ S ∧ 2 ^ top ≤ v
    · obtain ⟨v0, hv0S, hv0t⟩ := hsome
      let T : Finset ℕ := S.filter fun w => 2 ^ top ≤ w
      have hT : T.Nonempty := ⟨v0, Finset.mem_filter.mpr ⟨hv0S, hv0t⟩⟩
      let v : ℕ := T.min' hT
      have hvT : v ∈ T := Finset.min'_mem T hT
      have hvS : v ∈ S := (Finset.mem_filter.mp hvT).1
      have hvt : 2 ^ top ≤ v := (Finset.mem_filter.mp hvT).2
      have hmin : ∀ w ∈ S, 2 ^ top ≤ w → v ≤ w := fun w hwS hwt =>
        Finset.min'_le T w (Finset.mem_filter.mpr ⟨hwS, hwt⟩)
      have hv0 : v ≠ 0 := by
        have hp : 0 < v := lt_of_lt_of_le (Nat.pow_pos (by decide : 0 < 2)) hvt
        omega
      have htoplog : top ≤ Nat.log2 v := (Nat.le_log2 hv0).mpr hvt
      have hlogle : 2 ^ Nat.log2 v ≤ v := Nat.log2_self_le hv0
      have hloglt : v < 2 ^ (Nat.log2 v + 1) := Nat.lt_log2_self
      have hvpow : ∀ z, z < 2 ^ top → z < 2 ^ (Nat.log2 v + 1) := fun z hz =>
        lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
      have hvc : v ∈ cands a := hcand node top a hI hnode v hvS hvt
      have hnodeall : node.all (fun x => v ≤ v ^^^ x) = true := by
        rw [List.all_eq_true]
        intro x hx
        obtain ⟨hxS, hxlt⟩ := (hnode x).mp hx
        exact decide_eq_true (hmin (v ^^^ x) (hS.2 v hvS x hxS) (two_pow_le_xor_of_lt hxlt hvt))
      have hguard : decide (2 ^ top ≤ v) = true ∧
          (node.all fun x => decide (v ≤ v ^^^ x)) = true :=
        ⟨decide_eq_true hvt, hnodeall⟩
      have hall' := List.all_eq_true.mp hall
      have hf : swalk cands upd visit fuel (node ++ node.map (v ^^^ ·)) (Nat.log2 v + 1)
          (upd a v) = true := by
        have hv := hall' v hvc
        rwa [if_pos hguard] at hv
      have hchild : ∀ x, x ∈ node ++ node.map (v ^^^ ·) ↔
          x ∈ S ∧ x < 2 ^ (Nat.log2 v + 1) := by
        intro x
        rw [List.mem_append, List.mem_map]
        constructor
        · rintro (hx | ⟨y, hy, rfl⟩)
          · obtain ⟨hxS, hxlt⟩ := (hnode x).mp hx
            exact ⟨hxS, hvpow x hxlt⟩
          · obtain ⟨hyS, hylt⟩ := (hnode y).mp hy
            exact ⟨hS.2 v hvS y hyS, Nat.xor_lt_two_pow hloglt (hvpow y hylt)⟩
        · rintro ⟨hxS, hxlt⟩
          by_cases hxt : x < 2 ^ top
          · exact Or.inl ((hnode x).mpr ⟨hxS, hxt⟩)
          · have hxt' : 2 ^ top ≤ x := Nat.le_of_not_lt hxt
            have hvx : v ≤ x := hmin x hxS hxt'
            have hwxS : x ^^^ v ∈ S := hS.2 x hxS v hvS
            have hwxlt : x ^^^ v < 2 ^ Nat.log2 v :=
              xor_lt_two_pow_dyadic (x := x) (y := v) (le_trans hlogle hvx) hxlt hlogle hloglt
            have hwxtop : x ^^^ v < 2 ^ top := by
              by_contra hcon
              have hge : 2 ^ top ≤ x ^^^ v := Nat.le_of_not_lt hcon
              have hle : v ≤ x ^^^ v := hmin (x ^^^ v) hwxS hge
              omega
            exact Or.inr ⟨x ^^^ v, (hnode (x ^^^ v)).mpr ⟨hwxS, hwxtop⟩,
              by rw [Nat.xor_comm v (x ^^^ v), Nat.xor_xor_cancel_right]⟩
      exact ih hf (hupd node top a v hI hnode hvS hvt hmin) hchild
    · refine ⟨node, top, a, ?_, hI, hvisit⟩
      intro x
      rw [hnode x]
      exact ⟨fun hx => hx.1, fun hx =>
        ⟨hx, Nat.lt_of_not_le fun hle => hsome ⟨x, hx, hle⟩⟩⟩

private lemma testBit_foldl_maskOf (l : List ℕ) (m x : ℕ) :
    (l.foldl (fun m x => m ||| 2 ^ x) m).testBit x = (m.testBit x || decide (x ∈ l)) := by
  induction l generalizing m with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih (m ||| 2 ^ a), Nat.testBit_or, Nat.testBit_two_pow]
    have hmem : decide (x ∈ a :: l) = (decide (x = a) || decide (x ∈ l)) := by
      rw [decide_eq_decide.mpr List.mem_cons, Bool.decide_or]
    have hdec : decide (a = x) = decide (x = a) := decide_eq_decide.mpr eq_comm
    rw [hmem, hdec, Bool.or_assoc]

theorem testBit_maskOf (l : List ℕ) (x : ℕ) : (maskOf l).testBit x = decide (x ∈ l) := by
  have := testBit_foldl_maskOf l 0 x
  simpa [maskOf] using this

theorem ycover_sound {yl : List (List ℕ)} (h : ycover yl = true) {C : Finset ℕ}
    (hC : XorClosed C) (hC32 : ∀ z ∈ C, z < 2 ^ 5) : ∃ e ∈ yl, ∀ z, z ∈ e ↔ z ∈ C := by
  unfold ycover at h
  have hcand : ∀ (node : List ℕ) (top : ℕ) (a : Unit), True →
      (∀ x, x ∈ node ↔ x ∈ C ∧ x < 2 ^ top) →
      ∀ v ∈ C, 2 ^ top ≤ v → v ∈ List.range 32 := by
    intro node top a _ _ v hvC _
    rw [List.mem_range]
    simpa using hC32 v hvC
  have hnode : ∀ x, x ∈ [0] ↔ x ∈ C ∧ x < 2 ^ 0 := by
    intro x
    rw [List.mem_singleton, pow_zero, Nat.lt_one_iff]
    constructor
    · rintro rfl
      exact ⟨hC.1, rfl⟩
    · rintro ⟨-, rfl⟩
      rfl
  obtain ⟨node', top', a', hnode', _, hvisit⟩ :=
    swalk_sound (cands := fun _ : Unit => List.range 32) (upd := fun _ _ => ()) hC
      (fun _ _ _ => True) hcand (fun _ _ _ _ _ _ _ _ _ => trivial) h trivial hnode
  have hvisit' : (yl.any fun e => maskOf e == maskOf node') = true := by
    simpa using hvisit
  obtain ⟨e, he, hbeq⟩ := List.any_eq_true.mp hvisit'
  have hEq : maskOf e = maskOf node' := beq_iff_eq.mp hbeq
  refine ⟨e, he, ?_⟩
  intro z
  have hz : z ∈ e ↔ z ∈ node' := by
    have h1 := congrArg (fun m : ℕ => m.testBit z) hEq
    rw [testBit_maskOf, testBit_maskOf] at h1
    exact decide_eq_decide.mp h1
  rw [hz, hnode' z]

theorem eq_of_card_lt_two_mul {W M : Finset ℕ} (hW : XorClosed W) (hM : XorClosed M)
    (hWM : W ⊆ M) (hc : M.card < 2 * W.card) : W = M := by
  by_contra hne
  obtain ⟨m, hmM, hmW⟩ :=
    Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hWM, hne⟩)
  let f : ℕ → ℕ := fun w => m ^^^ w
  have hf_inj : Function.Injective f := Nat.xor_right_injective (x := m)
  have hsub : W ∪ W.image f ⊆ M := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxW | hxI
    · exact hWM hxW
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hxI
      exact hM.2 m hmM w (hWM hw)
  have hdisj : Disjoint W (W.image f) := by
    rw [Finset.disjoint_left]
    rintro w hwW hwI
    obtain ⟨w', hw', hwx⟩ := Finset.mem_image.mp hwI
    apply hmW
    have hm : m = w ^^^ w' := by
      rw [← hwx, Nat.xor_xor_cancel_right]
    rw [hm]
    exact hW.2 w hwW w' hw'
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective W hf_inj] at hcard
  omega

end CFSG.Monster.B.TwoA.Sp8.P0Rank
