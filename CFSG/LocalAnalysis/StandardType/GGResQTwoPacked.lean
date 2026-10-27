module

public import CFSG.LocalAnalysis.StandardType.GGResQTwoWordCache
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellData

public section

namespace CFSG.StandardType.GGResQTwoPacked

open CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def pkAnd (a b : Bool) : Bool := Bool.rec false b a
@[expose] noncomputable def pkOr (a b : Bool) : Bool := Bool.rec b true a
@[expose] noncomputable def pkNot (a : Bool) : Bool := Bool.rec true false a

@[expose] noncomputable def pkAllL {α : Type} (P : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ acc => pkAnd (P a) acc) l

@[expose] noncomputable def pkAnyL {α : Type} (P : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ acc => pkOr (P a) acc) l

@[expose] def pkLane (x i : ℕ) : ℕ := Nat.mod (Nat.div x (Nat.pow 4 i)) 4

@[expose] def pkSet (x j y : ℕ) : ℕ :=
  Nat.add (Nat.mod x (Nat.pow 4 j))
    (Nat.mul (Nat.add y (Nat.mul 4 (Nat.div x (Nat.pow 4 (Nat.succ j))))) (Nat.pow 4 j))

@[expose] def pkUnit (k : ℕ) : ℕ := pkSet 0 k 1

@[expose] noncomputable def pkNeg (n x : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) x
    (fun l acc => pkSet acc l (Nat.mod (Nat.sub 3 (pkLane acc l)) 3)) n

@[expose] noncomputable def pkSumN (f : ℕ → ℕ) (k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun l acc => Nat.add acc (f l)) k

@[expose] noncomputable def pkDotR (tab n j x : ℕ) : ℕ :=
  pkSumN (fun l => Nat.mul (pkLane tab (Nat.add (Nat.mul j n) l)) (pkLane x l)) n

@[expose] noncomputable def pkDotC (tab n j c : ℕ) : ℕ :=
  pkSumN (fun o => Nat.mul (pkLane c o) (pkLane tab (Nat.add (Nat.mul o n) j))) n

@[expose] noncomputable def pkRefl (tab n j x : ℕ) : ℕ :=
  pkSet x j (Nat.mod (Nat.add (pkLane x j) (Nat.mul 2 (pkDotR tab n j x))) 3)

@[expose] noncomputable def pkDRefl (tab n j c : ℕ) : ℕ :=
  pkSet c j (Nat.mod (Nat.add (pkLane c j) (Nat.mul 2 (pkDotC tab n j c))) 3)

@[expose] noncomputable def pkWordH {N : ℕ} (tab n : ℕ) (ws : List (Fin N)) (x : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) x (fun j _ acc => pkRefl tab n j.val acc) ws

@[expose] noncomputable def pkWordC {N : ℕ} (tab n : ℕ) (ws : List (Fin N)) (c : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) c (fun j _ acc => pkDRefl tab n j.val acc) ws

@[expose] noncomputable def pkDelta (l m : ℕ) : ℕ := Bool.rec 0 1 (Nat.beq l m)

@[expose] noncomputable def pkRowSum (f : ℕ → ℕ → ℕ) (n l a : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) a
    (fun m acc => Nat.add acc (Nat.mul (f l m) (Nat.pow 4 (Nat.add (Nat.mul n l) m)))) n

@[expose] noncomputable def pkDSum (f : ℕ → ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun l acc => pkRowSum f n l acc) n

@[expose] noncomputable def pkBlk (tab n c h : ℕ) : ℕ :=
  pkDSum (fun l m => Nat.mod (Nat.add (pkDelta l m)
    (Nat.mul 2 (Nat.mul (pkDotC tab n l c) (pkLane h m)))) 3) n

@[expose] noncomputable def pkBlkM (n : ℕ) (M : List (List (ZMod 3))) : ℕ :=
  pkDSum (fun l m => ((M.getD l []).getD m 0).val) n

@[expose] noncomputable def pkEntry {N : ℕ} (tab n : ℕ) (side : List (Fin N))
    (r : Fin N × List (Fin N)) (d : ℕ × ℕ × ℕ) : Bool :=
  pkAnd (pkAnyL (fun s => Nat.beq s.val r.1.val) side)
    (pkAnd (pkAllL (fun i => pkAnyL (fun s => Nat.beq s.val i.val) side) r.2)
      (pkAnd (Nat.beq (pkWordC tab n r.2 (pkUnit r.1.val)) d.1)
        (pkAnd (Nat.beq (pkWordH tab n r.2 (pkUnit r.1.val)) d.2.1)
          (Nat.beq (pkBlk tab n d.1 d.2.1) d.2.2))))

@[expose] noncomputable def pkWalk {N : ℕ} (tab n : ℕ) (side : List (Fin N)) :
    List (Fin N × List (Fin N)) → List (ℕ × ℕ × ℕ) → Bool :=
  fun R => List.rec (motive := fun _ => List (ℕ × ℕ × ℕ) → Bool)
    (fun D => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) D)
    (fun r _ ih D => List.rec (motive := fun _ => Bool) false
      (fun d D' _ => pkAnd (pkEntry tab n side r d) (ih D')) D) R

@[expose] noncomputable def pkMemPM (n c h : ℕ) (D : List (ℕ × ℕ × ℕ)) : Bool :=
  pkAnyL (fun d => pkOr (pkAnd (Nat.beq d.1 c) (Nat.beq d.2.1 h))
    (pkAnd (Nat.beq d.1 (pkNeg n c)) (Nat.beq d.2.1 (pkNeg n h)))) D

@[expose] noncomputable def pkSharedOK {N : ℕ} (tab n : ℕ) (side : List (Fin N))
    (R : List (Fin N × List (Fin N))) (D : List (ℕ × ℕ × ℕ)) : Bool :=
  pkAnd (pkAllL (fun s => Nat.blt s.val n) side)
    (pkAnd (pkWalk tab n side R D)
      (pkAnd (pkAllL (fun j => pkMemPM n (pkUnit j.val) (pkUnit j.val) D) side)
        (pkAllL (fun j => pkAllL (fun d =>
          pkMemPM n (pkDRefl tab n j.val d.1) (pkRefl tab n j.val d.2.1) D) D) side)))

@[expose] noncomputable def pkStrict (x : ℕ) (k : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun m _ => k (Nat.succ m)) x

@[expose] noncomputable def pkNotMem (x : ℕ) (D : List (ℕ × ℕ × ℕ)) : Bool :=
  pkStrict x fun y => pkAllL (fun d => pkNot (Nat.beq y d.2.2)) D

theorem pkAnd_sound {a b : Bool} (h : pkAnd a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [pkAnd]

theorem pkAllL_sound {α : Type} {P : α → Bool} :
    ∀ {l : List α}, pkAllL P l = true → ∀ a ∈ l, P a = true
  | [], _, a, ha => absurd ha (List.not_mem_nil)
  | b :: l, h, a, ha => by
    obtain ⟨h1, h2⟩ := pkAnd_sound (a := P b) (b := pkAllL P l) h
    rcases List.mem_cons.mp ha with rfl | ha
    · exact h1
    · exact pkAllL_sound h2 a ha

theorem pkAnyL_sound {α : Type} {P : α → Bool} :
    ∀ {l : List α}, pkAnyL P l = true → ∃ a ∈ l, P a = true
  | [], h => by cases h
  | b :: l, h => by
    change pkOr (P b) (pkAnyL P l) = true at h
    cases hb : P b
    · rw [hb] at h
      obtain ⟨a, ha, hPa⟩ := pkAnyL_sound (P := P) h
      exact ⟨a, List.mem_cons_of_mem _ ha, hPa⟩
    · exact ⟨b, List.mem_cons_self, hb⟩

theorem pkWalk_sound {N : ℕ} {tab n : ℕ} {side : List (Fin N)} :
    ∀ (R : List (Fin N × List (Fin N))) (D : List (ℕ × ℕ × ℕ)), pkWalk tab n side R D = true →
      List.Forall₂ (fun r d => pkEntry tab n side r d = true) R D
  | [], [], _ => List.Forall₂.nil
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | r :: R, d :: D, h => by
    obtain ⟨h1, h2⟩ := pkAnd_sound (a := pkEntry tab n side r d) (b := pkWalk tab n side R D) h
    exact List.Forall₂.cons h1 (pkWalk_sound R D h2)

theorem pk_forall₂_left {α β : Type} {P : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ P l₁ l₂ → ∀ a ∈ l₁, ∃ b ∈ l₂, P a b
  | _, _, List.Forall₂.nil, a, ha => absurd ha List.not_mem_nil
  | _, _, List.Forall₂.cons (a := x) (b := y) hxy h, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨y, List.mem_cons_self, hxy⟩
    · obtain ⟨b, hb, hab⟩ := pk_forall₂_left h a ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

theorem pk_forall₂_right {α β : Type} {P : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ P l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, P a b
  | _, _, List.Forall₂.nil, b, hb => absurd hb List.not_mem_nil
  | _, _, List.Forall₂.cons (a := x) (b := y) hxy h, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨x, List.mem_cons_self, hxy⟩
    · obtain ⟨a, ha, hab⟩ := pk_forall₂_right h b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hab⟩

theorem pk_beq {a b : ℕ} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem pkLane_eq (x i : ℕ) : pkLane x i = x / 4 ^ i % 4 := rfl

theorem pkSet_eq (x j y : ℕ) :
    pkSet x j y = x % 4 ^ j + (y + 4 * (x / 4 ^ (j + 1))) * 4 ^ j := rfl

theorem pkLane_lt (x i : ℕ) : pkLane x i < 4 := Nat.mod_lt _ (by norm_num)

private theorem pk_div_mod_lt {r w j l : ℕ} (hl : l < j) :
    (r + w * 4 ^ j) / 4 ^ l % 4 = r / 4 ^ l % 4 := by
  obtain ⟨d, rfl⟩ : ∃ d, j = l + 1 + d := ⟨j - l - 1, by omega⟩
  have e : w * 4 ^ (l + 1 + d) = (4 * (w * 4 ^ d)) * 4 ^ l := by ring
  rw [e, Nat.add_mul_div_right _ _ (by positivity), Nat.add_mul_mod_self_left]

private theorem pk_div_eq {r w j : ℕ} (hr : r < 4 ^ j) : (r + w * 4 ^ j) / 4 ^ j = w := by
  rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hr, zero_add]

private theorem pk_div_gt {r w j l : ℕ} (hr : r < 4 ^ j) (hl : j < l) :
    (r + w * 4 ^ j) / 4 ^ l = w / 4 ^ (l - j) := by
  have e : 4 ^ l = 4 ^ j * 4 ^ (l - j) := by rw [← pow_add, Nat.add_sub_cancel' hl.le]
  rw [e, ← Nat.div_div_eq_div_mul, pk_div_eq hr]

theorem pkLane_pkSet (x j y l : ℕ) (hy : y < 4) :
    pkLane (pkSet x j y) l = if l = j then y else pkLane x l := by
  have hP : 0 < 4 ^ j := by positivity
  have hr : x % 4 ^ j < 4 ^ j := Nat.mod_lt _ hP
  have hx : x = x % 4 ^ j + x / 4 ^ j * 4 ^ j := (Nat.mod_add_div' x (4 ^ j)).symm
  have hq : x / 4 ^ (j + 1) = x / 4 ^ j / 4 := by rw [Nat.div_div_eq_div_mul, pow_succ]
  rw [pkLane_eq, pkLane_eq, pkSet_eq]
  rcases lt_trichotomy l j with h | rfl | h
  · rw [if_neg h.ne, pk_div_mod_lt h]
    conv_rhs => rw [hx]
    rw [pk_div_mod_lt h]
  · rw [if_pos rfl, pk_div_eq hr, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy]
  · rw [if_neg h.ne']
    have e4 : 4 ^ (l - j) = 4 * 4 ^ (l - j - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega)]
    have e1 : (x % 4 ^ j + (y + 4 * (x / 4 ^ (j + 1))) * 4 ^ j) / 4 ^ l =
        x / 4 ^ j / 4 / 4 ^ (l - j - 1) := by
      rw [pk_div_gt hr h, hq, e4, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by norm_num),
        Nat.div_eq_of_lt hy, zero_add]
    have e2 : x / 4 ^ l = x / 4 ^ j / 4 / 4 ^ (l - j - 1) := by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← pow_succ', ← pow_add,
        show j + (l - j - 1 + 1) = l by omega]
    rw [e1, e2]

theorem pkLane_zero (i : ℕ) : pkLane 0 i = 0 := by simp [pkLane_eq]

theorem pkLane_pkNeg (x l : ℕ) :
    ∀ n, pkLane (pkNeg n x) l = if l < n then (3 - pkLane x l) % 3 else pkLane x l
  | 0 => by
    rw [if_neg (Nat.not_lt_zero l)]
    rfl
  | n + 1 => by
    have ih := pkLane_pkNeg x l n
    have hn := pkLane_pkNeg x n n
    rw [if_neg (lt_irrefl n)] at hn
    change pkLane (pkSet (pkNeg n x) n ((3 - pkLane (pkNeg n x) n) % 3)) l = _
    rw [pkLane_pkSet _ _ _ _ (by omega)]
    rcases eq_or_ne l n with rfl | h
    · rw [if_pos rfl, hn, if_pos (Nat.lt_succ_self _)]
    · rw [if_neg h, ih]
      by_cases h' : l < n
      · rw [if_pos h', if_pos (by omega)]
      · rw [if_neg h', if_neg (by omega)]

theorem pkSumN_eq (f : ℕ → ℕ) : ∀ k, pkSumN f k = ∑ i ∈ Finset.range k, f i
  | 0 => rfl
  | k + 1 => by
    rw [Finset.sum_range_succ, ← pkSumN_eq f k]
    rfl

theorem pkDotR_eq (tab n j x : ℕ) :
    pkDotR tab n j x = ∑ l ∈ Finset.range n, pkLane tab (j * n + l) * pkLane x l :=
  pkSumN_eq _ n

theorem pkDotC_eq (tab n j c : ℕ) :
    pkDotC tab n j c = ∑ o ∈ Finset.range n, pkLane c o * pkLane tab (o * n + j) :=
  pkSumN_eq _ n

theorem pkRefl_eq (tab n j x : ℕ) :
    pkRefl tab n j x = pkSet x j ((pkLane x j + 2 * pkDotR tab n j x) % 3) := rfl

theorem pkDRefl_eq (tab n j c : ℕ) :
    pkDRefl tab n j c = pkSet c j ((pkLane c j + 2 * pkDotC tab n j c) % 3) := rfl

theorem pkDelta_eq (l m : ℕ) : pkDelta l m = if l = m then 1 else 0 := by
  unfold pkDelta
  cases hb : Nat.beq l m
  · rw [if_neg (Nat.ne_of_beq_eq_false hb)]
  · rw [if_pos (Nat.eq_of_beq_eq_true hb)]

abbrev PkRep (n : ℕ) {L : ℕ} (x : ℕ) (z : Vector (ZMod 3) L) : Prop :=
  ∀ l : Fin L, z.get l = if l.val < n then ((pkLane x l.val : ℕ) : ZMod 3) else 0

abbrev PkTab (n tab : ℕ) (T : Fin (n + 1) → Vector (ZMod 3) (n + 2)) : Prop :=
  ∀ (j : Fin (n + 1)) (l : Fin (n + 2)), j.val < n → l.val < n →
    (T j).get l = ((pkLane tab (j.val * n + l.val) : ℕ) : ZMod 3)

private theorem pk_two : (2 : ZMod 3) = -1 := by decide

private theorem pk_cast_three_sub {a : ℕ} (ha : a < 4) :
    (((3 - a) % 3 : ℕ) : ZMod 3) = -((a : ℕ) : ZMod 3) := by
  interval_cases a <;> decide

private theorem pk_sum_fin_ite {L n : ℕ} (hn : n ≤ L) (g : ℕ → ZMod 3) :
    (∑ l : Fin L, if l.val < n then g l.val else 0) = ∑ i ∈ Finset.range n, g i := by
  have h1 := Fin.sum_univ_eq_sum_range (fun i => if i < n then g i else 0) L
  rw [h1, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨by omega, h⟩

theorem pk_ggFDot {n tab : ℕ} {T : Fin (n + 1) → Vector (ZMod 3) (n + 2)} (hT : PkTab n tab T)
    {j : Fin (n + 1)} (hj : j.val < n) {x : ℕ} {z : Vector (ZMod 3) (n + 2)}
    (hz : PkRep n x z) : ggFDot (T j) z = ((pkDotR tab n j.val x : ℕ) : ZMod 3) := by
  rw [pkDotR_eq, Nat.cast_sum, ← pk_sum_fin_ite (L := n + 1 + 1) (by omega)]
  unfold ggFDot
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hz l]
  split_ifs with hl
  · rw [hT j l hj hl, Nat.cast_mul]
  · simp

theorem pk_ggFDualAt {n tab : ℕ} {T : Fin (n + 1) → Vector (ZMod 3) (n + 2)} (hT : PkTab n tab T)
    {j : Fin (n + 1)} (hj : j.val < n) {c : ℕ} {w : Vector (ZMod 3) (n + 1)}
    (hw : PkRep n c w) : ggFDualAt T w j = ((pkDotC tab n j.val c : ℕ) : ZMod 3) := by
  rw [pkDotC_eq, Nat.cast_sum, ← pk_sum_fin_ite (L := n + 1) (by omega)]
  unfold ggFDualAt
  refine Finset.sum_congr rfl fun o _ => ?_
  have hj' : (j.castSucc : Fin (n + 2)).val < n := by rw [Fin.coe_castSucc]; exact hj
  rw [hw o]
  split_ifs with ho
  · rw [hT o j.castSucc ho hj', Fin.coe_castSucc, Nat.cast_mul]
  · simp

theorem pkRep_refl {n tab : ℕ} {T : Fin (n + 1) → Vector (ZMod 3) (n + 2)} (hT : PkTab n tab T)
    {j : Fin (n + 1)} (hj : j.val < n) {x : ℕ} {z : Vector (ZMod 3) (n + 2)}
    (hz : PkRep n x z) : PkRep n (pkRefl tab n j.val x) (ggFRefl T j z) := by
  intro l
  have hd := pk_ggFDot hT hj hz
  have hlt : (pkLane x j.val + 2 * pkDotR tab n j.val x) % 3 < 4 := by omega
  rw [ggFRefl, Vector.get_ofFn, pkRefl_eq, pkLane_pkSet _ _ _ _ hlt]
  by_cases hl : l = j.castSucc
  · have hv : l.val = j.val := by rw [hl, Fin.coe_castSucc]
    have hln : l.val < n := by omega
    have hzl : z.get l = ((pkLane x l.val : ℕ) : ZMod 3) := (hz l).trans (if_pos hln)
    rw [if_pos hl, if_pos hv, if_pos hln, hzl, hd, ZMod.natCast_mod, hv]
    push_cast
    rw [pk_two]
    ring
  · have hv : l.val ≠ j.val := fun h => hl (Fin.ext (by rw [h, Fin.coe_castSucc]))
    rw [if_neg hl, if_neg hv, hz l]

theorem pkRep_drefl {n tab : ℕ} {T : Fin (n + 1) → Vector (ZMod 3) (n + 2)} (hT : PkTab n tab T)
    {j : Fin (n + 1)} (hj : j.val < n) {c : ℕ} {w : Vector (ZMod 3) (n + 1)}
    (hw : PkRep n c w) : PkRep n (pkDRefl tab n j.val c) (ggFDRefl T j w) := by
  intro o
  have hd := pk_ggFDualAt hT hj hw
  have hlt : (pkLane c j.val + 2 * pkDotC tab n j.val c) % 3 < 4 := by omega
  rw [ggFDRefl, Vector.get_ofFn, pkDRefl_eq, pkLane_pkSet _ _ _ _ hlt]
  by_cases ho : o = j
  · have hv : o.val = j.val := by rw [ho]
    have hon : o.val < n := by omega
    have hwo : w.get o = ((pkLane c o.val : ℕ) : ZMod 3) := (hw o).trans (if_pos hon)
    rw [if_pos ho, if_pos hv, if_pos hon, hwo, hd, ZMod.natCast_mod, hv]
    push_cast
    rw [pk_two]
    ring
  · have hv : o.val ≠ j.val := fun h => ho (Fin.ext h)
    rw [if_neg ho, if_neg hv, hw o]

theorem pkRep_unitH {n : ℕ} (k : Fin (n + 1)) (hk : k.val < n) :
    PkRep n (pkUnit k.val) (ggFUnit (R := ZMod 3) (N := n + 1) k.castSucc) := by
  intro l
  rw [ggFUnit, Vector.get_ofFn, pkUnit, pkLane_pkSet _ _ _ _ (by norm_num)]
  by_cases hl : l = k.castSucc
  · have hv : l.val = k.val := by rw [hl, Fin.coe_castSucc]
    have hln : l.val < n := by omega
    rw [if_pos hl, if_pos hv, if_pos hln]
    simp
  · have hv : l.val ≠ k.val := fun h => hl (Fin.ext (by rw [h, Fin.coe_castSucc]))
    rw [if_neg hl, if_neg hv, pkLane_zero]
    simp

theorem pkRep_unitC {n : ℕ} (k : Fin (n + 1)) (hk : k.val < n) :
    PkRep n (pkUnit k.val) (ggFDUnit (R := ZMod 3) (N := n + 1) k) := by
  intro o
  rw [ggFDUnit, Vector.get_ofFn, pkUnit, pkLane_pkSet _ _ _ _ (by norm_num)]
  by_cases ho : o = k
  · have hv : o.val = k.val := by rw [ho]
    have hon : o.val < n := by omega
    rw [if_pos ho, if_pos hv, if_pos hon]
    simp
  · have hv : o.val ≠ k.val := fun h => ho (Fin.ext h)
    rw [if_neg ho, if_neg hv, pkLane_zero]
    simp

theorem pkRep_ggFH {n tab : ℕ} {T : Fin (n + 1) → Vector (ZMod 3) (n + 2)} (hT : PkTab n tab T)
    (k : Fin (n + 1)) (hk : k.val < n) :
    ∀ ws : List (Fin (n + 1)), (∀ j ∈ ws, j.val < n) →
      PkRep n (pkWordH tab n ws (pkUnit k.val)) (ggFH T (k, ws))
  | [], _ => pkRep_unitH k hk
  | j :: ws, h => by
    rw [ggFH_cons]
    exact pkRep_refl hT (h j List.mem_cons_self)
      (pkRep_ggFH hT k hk ws fun i hi => h i (List.mem_cons_of_mem _ hi))

theorem pkRep_ggFC {n tab : ℕ} {T : Fin (n + 1) → Vector (ZMod 3) (n + 2)} (hT : PkTab n tab T)
    (k : Fin (n + 1)) (hk : k.val < n) :
    ∀ ws : List (Fin (n + 1)), (∀ j ∈ ws, j.val < n) →
      PkRep n (pkWordC tab n ws (pkUnit k.val)) (ggFC T (k, ws))
  | [], _ => pkRep_unitC k hk
  | j :: ws, h => by
    rw [ggFC_cons]
    exact pkRep_drefl hT (h j List.mem_cons_self)
      (pkRep_ggFC hT k hk ws fun i hi => h i (List.mem_cons_of_mem _ hi))

theorem pkRep_neg {n L x : ℕ} {z z' : Vector (ZMod 3) L} (hz : PkRep n x z)
    (hz' : PkRep n (pkNeg n x) z') (l : Fin L) : z'.get l = -z.get l := by
  rw [hz l, hz' l]
  split_ifs with hl
  · rw [pkLane_pkNeg, if_pos hl, pk_cast_three_sub (pkLane_lt x l.val)]
  · simp

theorem pk_refMat_eq {n : ℕ} {T : Fin (n + 1) → Vector (ZMod 3) (n + 2)}
    {t t' : Fin (n + 1) × List (Fin (n + 1))} {c h c' h' : ℕ}
    (hc : PkRep n c (ggFC T t)) (hh : PkRep n h (ggFH T t))
    (hc' : PkRep n c' (ggFC T t')) (hh' : PkRep n h' (ggFH T t'))
    (hm : (c' = c ∧ h' = h) ∨ (c' = pkNeg n c ∧ h' = pkNeg n h)) :
    ggFRefMat T t' = ggFRefMat T t := by
  apply ggFRefMat_eq_of_raw_factors
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    exact ⟨fun m => by rw [hh' m.castSucc, hh m.castSucc], fun o => by rw [hc' o, hc o]⟩
  · right
    exact ⟨fun m => pkRep_neg hh hh' m.castSucc, fun o => pkRep_neg hc hc' o⟩

private theorem pkRec_congr {F G : ℕ → ℕ → ℕ} (a : ℕ) :
    ∀ k, (∀ m < k, ∀ acc, F m acc = G m acc) →
      Nat.rec (motive := fun _ => ℕ) a F k = Nat.rec (motive := fun _ => ℕ) a G k
  | 0, _ => rfl
  | k + 1, h => by
    change F k (Nat.rec (motive := fun _ => ℕ) a F k) = G k (Nat.rec (motive := fun _ => ℕ) a G k)
    rw [pkRec_congr a k fun m hm => h m (by omega), h k (by omega)]

theorem pkDSum_congr {f g : ℕ → ℕ → ℕ} {n : ℕ}
    (hfg : ∀ l m, l < n → m < n → f l m = g l m) : pkDSum f n = pkDSum g n :=
  pkRec_congr 0 n fun l hl acc =>
    pkRec_congr acc n fun m hm acc2 => by simp only [hfg l m hl hm]

private theorem pk_getD_finRange {α : Type} {N : ℕ} (f : Fin N → α) (d : α) {l : ℕ}
    (hl : l < N) : ((List.finRange N).map f).getD l d = f ⟨l, hl⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hl)]
  simp

theorem pkBlkM_refMat {n tab : ℕ} {T : Fin (n + 1) → Vector (ZMod 3) (n + 2)}
    (hT : PkTab n tab T) {t : Fin (n + 1) × List (Fin (n + 1))} {c h : ℕ}
    (hc : PkRep n c (ggFC T t)) (hh : PkRep n h (ggFH T t)) :
    pkBlkM n (ggFRefMat T t) = pkBlk tab n c h := by
  apply pkDSum_congr
  intro l m hl hm
  have hl' : l < n + 1 := by omega
  have hm' : m < n + 1 := by omega
  have hD := pk_ggFDualAt hT (j := ⟨l, hl'⟩) hl hc
  have hH : (ggFH T t).get (⟨m, hm'⟩ : Fin (n + 1)).castSucc = ((pkLane h m : ℕ) : ZMod 3) :=
    (hh _).trans (if_pos hm)
  have hif : (if (⟨l, hl'⟩ : Fin (n + 1)) = ⟨m, hm'⟩ then (1 : ZMod 3) else 0) =
      ((pkDelta l m : ℕ) : ZMod 3) := by
    rw [pkDelta_eq]
    by_cases hlm : l = m
    · subst hlm
      simp
    · rw [if_neg (fun e => hlm (Fin.mk.inj e)), if_neg hlm]
      simp
  have e : ((ggFRefMat T t).getD l []).getD m 0 =
      ((pkDelta l m + 2 * (pkDotC tab n l c * pkLane h m) : ℕ) : ZMod 3) := by
    simp only [ggFRefMat_eq_map, pk_getD_finRange _ _ hl', pk_getD_finRange _ _ hm']
    rw [hif, hD, hH]
    push_cast
    rw [pk_two]
    ring
  beta_reduce
  rw [e, ZMod.val_natCast]
  rfl

theorem pkShared_sound {n tab : ℕ} {side : List (Fin (n + 1))}
    {R : List (Fin (n + 1) × List (Fin (n + 1)))} {D : List (ℕ × ℕ × ℕ)}
    (hchk : pkSharedOK tab n side R D = true)
    {T : Fin (n + 1) → Vector (ZMod 3) (n + 2)} (hT : PkTab n tab T)
    (h2 : ∀ k, (T k).get k.castSucc = 2) (hx : ∀ k, (T k).get (Fin.last (n + 1)) = 0) :
    GGResQTwoListOK T side R ∧ ∀ r ∈ R, ∃ d ∈ D, pkBlkM n (ggFRefMat T r) = d.2.2 := by
  obtain ⟨hs, h1⟩ := pkAnd_sound hchk
  obtain ⟨hw, h1⟩ := pkAnd_sound h1
  obtain ⟨hseed, hcl⟩ := pkAnd_sound h1
  have hsl : ∀ s ∈ side, s.val < n := fun s hs' => Nat.le_of_ble_eq_true (pkAllL_sound hs s hs')
  have hin : ∀ i : Fin (n + 1),
      pkAnyL (fun s : Fin (n + 1) => Nat.beq s.val i.val) side = true → i ∈ side := by
    intro i hi
    obtain ⟨s, hs', he⟩ := pkAnyL_sound hi
    rw [← Fin.ext (pk_beq he)]
    exact hs'
  have hF := pkWalk_sound R D hw
  have hkey : ∀ r d, pkEntry tab n side r d = true →
      PkRep n d.1 (ggFC T r) ∧ PkRep n d.2.1 (ggFH T r) ∧
        (r.1 ∈ side ∧ ∀ i ∈ r.2, i ∈ side) ∧ pkBlk tab n d.1 d.2.1 = d.2.2 := by
    rintro ⟨k, ws⟩ d he
    obtain ⟨e1, he⟩ := pkAnd_sound he
    obtain ⟨e2, he⟩ := pkAnd_sound he
    obtain ⟨e3, he⟩ := pkAnd_sound he
    obtain ⟨e4, e5⟩ := pkAnd_sound he
    have hk : k ∈ side := hin k e1
    have hws : ∀ i ∈ ws, i ∈ side := fun i hi => hin i (pkAllL_sound e2 i hi)
    have hlt : ∀ i ∈ ws, i.val < n := fun i hi => hsl i (hws i hi)
    refine ⟨?_, ?_, ⟨hk, hws⟩, pk_beq e5⟩
    · rw [← pk_beq e3]
      exact pkRep_ggFC hT k (hsl k hk) ws hlt
    · rw [← pk_beq e4]
      exact pkRep_ggFH hT k (hsl k hk) ws hlt
  have hD : ∀ d ∈ D, ∃ r ∈ R, PkRep n d.1 (ggFC T r) ∧ PkRep n d.2.1 (ggFH T r) := by
    intro d hd
    obtain ⟨r, hr, he⟩ := pk_forall₂_right hF d hd
    exact ⟨r, hr, (hkey r d he).1, (hkey r d he).2.1⟩
  have hmem : ∀ t : Fin (n + 1) × List (Fin (n + 1)), ∀ c h : ℕ,
      PkRep n c (ggFC T t) → PkRep n h (ggFH T t) → pkMemPM n c h D = true →
      ∃ r ∈ R, ggFMat T (ggConjWord r) = ggFRefMat T t := by
    intro t c h hc hh hm
    obtain ⟨d, hd, hm⟩ := pkAnyL_sound hm
    beta_reduce at hm
    obtain ⟨r, hr, hc', hh'⟩ := hD d hd
    refine ⟨r, hr, ?_⟩
    rw [ggFMat_conjWord_eq_ggFRefMat h2 hx r]
    apply pk_refMat_eq hc hh hc' hh'
    cases ha : pkAnd (Nat.beq d.1 c) (Nat.beq d.2.1 h)
    · rw [ha] at hm
      obtain ⟨f1, f2⟩ := pkAnd_sound hm
      exact Or.inr ⟨pk_beq f1, pk_beq f2⟩
    · obtain ⟨f1, f2⟩ := pkAnd_sound ha
      exact Or.inl ⟨pk_beq f1, pk_beq f2⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro j hj
    obtain ⟨r, hr, he⟩ := hmem (j, []) _ _ (pkRep_ggFC hT j (hsl j hj) [] (by simp))
      (pkRep_ggFH hT j (hsl j hj) [] (by simp)) (pkAllL_sound hseed j hj)
    refine ⟨r, hr, ?_⟩
    rw [he]
    exact (ggFMat_conjWord_eq_ggFRefMat h2 hx (j, [])).symm
  · intro j hj r hr
    obtain ⟨d, hd, he⟩ := pk_forall₂_left hF r hr
    obtain ⟨hc, hh, ⟨hk, hws⟩, -⟩ := hkey r d he
    obtain ⟨k, ws⟩ := r
    have hjn : j.val < n := hsl j hj
    have hc2 : PkRep n (pkDRefl tab n j.val d.1) (ggFC T (k, j :: ws)) := by
      rw [ggFC_cons]
      exact pkRep_drefl hT hjn hc
    have hh2 : PkRep n (pkRefl tab n j.val d.2.1) (ggFH T (k, j :: ws)) := by
      rw [ggFH_cons]
      exact pkRep_refl hT hjn hh
    obtain ⟨r', hr', he'⟩ := hmem (k, j :: ws) _ _ hc2 hh2 (pkAllL_sound (pkAllL_sound hcl j hj) d hd)
    refine ⟨r', hr', ?_⟩
    rw [he', ggConjWord_cons (k, ws) j]
    exact (ggFMat_conjWord_eq_ggFRefMat h2 hx (k, j :: ws)).symm
  · intro r hr
    obtain ⟨d, -, he⟩ := pk_forall₂_left hF r hr
    exact (hkey r d he).2.2.1
  · intro r hr
    obtain ⟨d, hd, he⟩ := pk_forall₂_left hF r hr
    obtain ⟨hc, hh, -, hb⟩ := hkey r d he
    exact ⟨d, hd, by rw [pkBlkM_refMat hT hc hh, hb]⟩

theorem GGResQTwoNormOKK_of_pk {n : ℕ} {T : Fin (n + 1) → Vector (ZMod 3) (n + 2)}
    {side : List (Fin (n + 1))} {R : List (Fin (n + 1) × List (Fin (n + 1)))}
    {x₀ : List ℕ} {τ : List (Fin (n + 1))} {k : Fin (n + 1)} {D : List (ℕ × ℕ × ℕ)}
    (h2 : ∀ k, (T k).get k.castSucc = 2) (hx : ∀ k, (T k).get (Fin.last (n + 1)) = 0)
    (hS : (∀ k, (T k).get k.castSucc = 2) → (∀ k, (T k).get (Fin.last (n + 1)) = 0) →
      GGResQTwoListOK T side R ∧ ∀ r ∈ R, ∃ d ∈ D, pkBlkM n (ggFRefMat T r) = d.2.2)
    (hk : k ∈ side)
    (hrest : ggResQTwoVecNeZero (p := 3) (n := n) x₀ ∧ x₀.getD (n + 1) 0 = 0 ∧
      (∀ i ∈ side, ggFDot (T i) (ggFVec x₀) = 0) ∧
      ggResQTwoVecEqV (ggFWord T τ (ggFVec x₀)) (ggFVec x₀))
    (hnot : pkNotMem (pkBlkM n (ggFRefMat T (k, τ))) D = true) :
    GGResQTwoNormOKK T side R x₀ τ k := by
  obtain ⟨hL, hB⟩ := hS h2 hx
  refine ⟨hk, hL, hrest.1, hrest.2.1, hrest.2.2.1, hrest.2.2.2, ?_⟩
  intro r hr heq
  rw [ggFMat_conjWord_eq_ggFRefMat h2 hx, ggFMat_conjWord_eq_ggFRefMat h2 hx] at heq
  obtain ⟨d, hd, hb⟩ := hB r hr
  have hs : ∀ (x : ℕ) (k : ℕ → Bool), pkStrict x k = k x := by
    intro x k
    cases x <;> rfl
  rw [pkNotMem, hs] at hnot
  have hn := pkAllL_sound hnot d hd
  beta_reduce at hn
  rw [heq, hb, Nat.beq_refl] at hn
  exact Bool.false_ne_true hn

theorem pkTab_std {n tab : ℕ} {C : Matrix (Fin n) (Fin n) ℤ}
    (hC : ∀ a b : Fin n, ((C a b : ℤ) : ZMod 3) = ((pkLane tab (a.val * n + b.val) : ℕ) : ZMod 3))
    (ib ic : Fin n) (e₁ e₂ : ℤ) (u v : ZMod 3) :
    PkTab n tab (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) := by
  intro j l hj hl
  simp only [ggStdTableI, Vector.get_ofFn]
  unfold ggStdEntryI
  rw [dif_pos hj, dif_pos hl]
  exact hC ⟨j.val, hj⟩ ⟨l.val, hl⟩

end CFSG.StandardType.GGResQTwoPacked
