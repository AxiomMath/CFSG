module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Root
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6A5Std
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Common.ListGroup

public noncomputable section

namespace CFSG.StandardType.TableCRes.FrameK

open CFSG.KC.ListGroup (grp)

@[expose] def addK (a b : List ℤ) : List ℤ := List.zipWith (· + ·) a b

@[expose] def negK (a : List ℤ) : List ℤ := a.map fun x => -x

@[expose] def a2K (a b : List ℤ) : List (List ℤ) :=
  [a, b, addK a b, negK a, negK b, negK (addK a b)]

@[expose] def compK (X : List (List ℤ)) : List (List ℤ) :=
  e6RootList.filter fun g => X.all fun m => e6ip g m == 0

@[expose] def tab12K : List (ℤ × ℤ) :=
  [(2, -1), (-1, 2), (1, 1), (-2, 1), (1, -2), (-1, -1), (1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1),
    (1, -1)]

@[expose] def rootTabK : List (ℤ × ℤ) := [(2, -1), (-1, 2), (1, 1), (-2, 1), (1, -2), (-1, -1)]

@[expose] def wtTabK : List (ℤ × ℤ) := [(1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1)]

@[expose] def smulK (k : ℤ) (a : List ℤ) : List ℤ := a.map fun x => k * x

@[expose] def comb5K (c : List ℤ) (d₀ d₁ d₂ d₃ d₄ : List ℤ) : List ℤ :=
  match c with
  | [c0, c1, c2, c3, c4] =>
    addK (addK (addK (addK (smulK c0 d₀) (smulK c1 d₁)) (smulK c2 d₂)) (smulK c3 d₃))
      (smulK c4 d₄)
  | _ => []

@[expose] def chainK (d₀ d₁ d₂ d₃ d₄ : List ℤ) : List (List ℤ) :=
  std30.map fun c => comb5K c d₀ d₁ d₂ d₃ d₄

@[expose] def lineK (c₁ d₁ c₂ d₂ c₃ d₃ : List ℤ) (u₀ : ℤ × ℤ) : List (List ℤ) :=
  e6RootList.filter fun g =>
    !(decide (g ∈ a2K c₁ d₁ ++ a2K c₂ d₂)) &&
      (decide ((e6ip g c₃, e6ip g d₃) = u₀) || decide ((e6ip g c₃, e6ip g d₃) = (-u₀.1, -u₀.2)))

@[expose] def A5LastK (c₁ d₁ c₂ d₂ c₃ d₃ : List ℤ) (u₀ : ℤ × ℤ) (δ₀ δ₁ δ₂ δ₃ δ₄ : List ℤ) : Prop :=
  (∀ g ∈ a2K c₁ d₁ ++ a2K c₂ d₂ ++ lineK c₁ d₁ c₂ d₂ c₃ d₃ u₀,
    g ∈ chainK δ₀ δ₁ δ₂ δ₃ δ₄) ∧
  (∀ g ∈ chainK δ₀ δ₁ δ₂ δ₃ δ₄, g ∈ a2K c₁ d₁ ++ a2K c₂ d₂ ++ lineK c₁ d₁ c₂ d₂ c₃ d₃ u₀)

@[expose] def A5L4K (c₁ d₁ c₂ d₂ c₃ d₃ : List ℤ) (u₀ : ℤ × ℤ) (δ₀ δ₁ δ₂ δ₃ : List ℤ) : Prop :=
  ∃ δ₄ ∈ a2K c₂ d₂, e6ip δ₃ δ₄ = -1 ∧ e6ip δ₂ δ₄ = 0 ∧ e6ip δ₁ δ₄ = 0 ∧ e6ip δ₀ δ₄ = 0 ∧
    A5LastK c₁ d₁ c₂ d₂ c₃ d₃ u₀ δ₀ δ₁ δ₂ δ₃ δ₄

@[expose] def A5L3K (c₁ d₁ c₂ d₂ c₃ d₃ : List ℤ) (u₀ : ℤ × ℤ) (δ₀ δ₁ δ₂ : List ℤ) : Prop :=
  ∃ δ₃ ∈ a2K c₂ d₂, e6ip δ₂ δ₃ = -1 ∧ e6ip δ₁ δ₃ = 0 ∧ e6ip δ₀ δ₃ = 0 ∧
    A5L4K c₁ d₁ c₂ d₂ c₃ d₃ u₀ δ₀ δ₁ δ₂ δ₃

@[expose] def A5L2K (c₁ d₁ c₂ d₂ c₃ d₃ : List ℤ) (u₀ : ℤ × ℤ) (δ₀ δ₁ : List ℤ) : Prop :=
  ∃ δ₂ ∈ lineK c₁ d₁ c₂ d₂ c₃ d₃ u₀, e6ip δ₁ δ₂ = -1 ∧ e6ip δ₀ δ₂ = 0 ∧
    A5L3K c₁ d₁ c₂ d₂ c₃ d₃ u₀ δ₀ δ₁ δ₂

@[expose] def tcA5K (c₁ d₁ c₂ d₂ c₃ d₃ : List ℤ) (u₀ : ℤ × ℤ) : Prop :=
  ∃ δ₀ ∈ a2K c₁ d₁, ∃ δ₁ ∈ a2K c₁ d₁, e6ip δ₀ δ₁ = -1 ∧ A5L2K c₁ d₁ c₂ d₂ c₃ d₃ u₀ δ₀ δ₁

@[expose] def wtRepK : List (ℤ × ℤ) := [(1, 0), (0, 1), (1, -1)]

abbrev FrameK (c₁ d₁ c₂ d₂ c₃ d₃ : List ℤ) : Prop :=
  e6ip c₃ d₃ = -1 ∧
  (∀ g ∈ e6RootList, (g ∈ a2K c₁ d₁ ++ a2K c₂ d₂ ↔ (e6ip g c₃ = 0 ∧ e6ip g d₃ = 0))) ∧
  (∀ g ∈ e6RootList, g ∉ a2K c₁ d₁ ++ a2K c₂ d₂ → (e6ip g c₃, e6ip g d₃) ∈ tab12K) ∧
  (∀ g ∈ e6RootList, g ∉ a2K c₁ d₁ ++ a2K c₂ d₂ → (e6ip g c₃, e6ip g d₃) ∈ rootTabK →
    ∀ m ∈ a2K c₁ d₁ ++ a2K c₂ d₂, e6ip g m = 0) ∧
  (∀ g ∈ e6RootList, g ∉ a2K c₁ d₁ ++ a2K c₂ d₂ → (e6ip g c₃, e6ip g d₃) ∈ wtTabK →
    (∃ m ∈ a2K c₁ d₁, e6ip g m ≠ 0) ∧ (∃ m ∈ a2K c₂ d₂, e6ip g m ≠ 0)) ∧
  (∀ u₀ ∈ wtRepK, tcA5K c₁ d₁ c₂ d₂ c₃ d₃ u₀)

#kc_repo #kc_decls CFSG.StandardType.TableCRes.FrameK "CFSG/LocalAnalysis/StandardType/data/gg6tcwp4e6_frame.txt" 34199 17889985473398783467

@[expose] noncomputable def coverData : List (List ℕ) := grp 20 covF

@[expose] noncomputable def framesData1 : List (List (List ℕ)) := grp 2 (grp 17 frF1)

@[expose] noncomputable def framesData2 : List (List (List ℕ)) := grp 2 (grp 17 frF2)

@[expose] noncomputable def framesData3 : List (List (List ℕ)) := grp 2 (grp 17 frF3)

@[expose] noncomputable def framesData4 : List (List (List ℕ)) := grp 2 (grp 17 frF4)

@[expose] def walkIdx {α : Type} (f : ℕ → α → Bool) (L : List α) : ℕ → Bool :=
  @List.rec α (fun _ => ℕ → Bool) (fun _ => true) (fun a _ ih k => f k a && ih (Nat.succ k)) L

theorem walkIdx_cons {α : Type} (f : ℕ → α → Bool) (a : α) (L : List α) (k : ℕ) :
    walkIdx f (a :: L) k = (f k a && walkIdx f L (k + 1)) := rfl

theorem walkIdx_sound {α : Type} (f : ℕ → α → Bool) :
    ∀ (L : List α) (k : ℕ), walkIdx f L k = true →
      ∀ (i : ℕ) (hi : i < L.length), f (k + i) L[i] = true
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | a :: L, k, h, i, hi => by
    rw [walkIdx_cons, Bool.and_eq_true] at h
    cases i with
    | zero => exact h.1
    | succ i =>
      have hi' : i < L.length := by simpa using hi
      have h2 := walkIdx_sound f L (k + 1) h.2 i hi'
      have e : k + (i + 1) = k + 1 + i := by omega
      rw [List.getElem_cons_succ, e]
      exact h2

@[expose] def allLt (n : ℕ) (f : ℕ → Bool) : Bool :=
  @Nat.rec (fun _ => Bool) true (fun k acc => f k && acc) n

theorem allLt_sound {f : ℕ → Bool} : ∀ {n : ℕ}, allLt n f = true → ∀ k < n, f k = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | n + 1, h, k, hk => by
    have h' : (f n && allLt n f) = true := h
    rw [Bool.and_eq_true] at h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact allLt_sound h'.2 k hk
    · exact h'.1

@[expose] def memL (k : ℕ) (L : List ℕ) : Bool :=
  @List.rec ℕ (fun _ => Bool) false (fun a _ ih => Nat.beq a k || ih) L

theorem memL_iff {k : ℕ} : ∀ {L : List ℕ}, memL k L = true ↔ k ∈ L
  | [] => ⟨fun h => absurd h Bool.false_ne_true, fun h => by simp at h⟩
  | a :: L => by
    have e : memL k (a :: L) = (Nat.beq a k || memL k L) := rfl
    rw [e, Bool.or_eq_true, Nat.beq_eq, memL_iff, List.mem_cons]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h

theorem memL_eq {k : ℕ} {L : List ℕ} : memL k L = decide (k ∈ L) := by
  rw [Bool.eq_iff_iff, memL_iff, decide_eq_true_iff]

@[expose] def maskOf (L : List ℕ) : ℕ :=
  @List.rec ℕ (fun _ => ℕ) 0 (fun a _ ih => Nat.lor ih (Nat.shiftLeft 1 a)) L

@[expose] def bitB (M k : ℕ) : Bool := Nat.blt 0 (Nat.land M (Nat.shiftLeft 1 k))

theorem bitB_eq (M k : ℕ) : bitB M k = M.testBit k := by
  have e : Nat.land M (Nat.shiftLeft 1 k) = (M.testBit k).toNat * 2 ^ k := by
    rw [← Nat.and_two_pow, ← Nat.one_shiftLeft]
    rfl
  rw [bitB, e, Bool.eq_iff_iff, Nat.blt_eq]
  cases M.testBit k <;> simp [Nat.two_pow_pos]

theorem testBit_maskOf {k : ℕ} : ∀ {L : List ℕ}, (maskOf L).testBit k = decide (k ∈ L)
  | [] => by
    change (0 : ℕ).testBit k = _
    simp
  | a :: L => by
    have e : maskOf (a :: L) = (maskOf L ||| 1 <<< a) := rfl
    rw [e, Nat.testBit_or, testBit_maskOf, Nat.one_shiftLeft, Nat.testBit_two_pow]
    simp [List.mem_cons, eq_comm, or_comm, Bool.or_comm]

theorem bitB_maskOf (L : List ℕ) (k : ℕ) : bitB (maskOf L) k = memL k L := by
  rw [bitB_eq, testBit_maskOf, memL_eq]

@[expose] def allL {α : Type} (p : α → Bool) (L : List α) : Bool :=
  @List.rec α (fun _ => Bool) true (fun a _ ih => p a && ih) L

theorem allL_iff {α : Type} {p : α → Bool} : ∀ {L : List α}, allL p L = true ↔ ∀ a ∈ L, p a = true
  | [] => ⟨fun _ a h => by simp at h, fun _ => rfl⟩
  | a :: L => by
    have e : allL p (a :: L) = (p a && allL p L) := rfl
    rw [e, Bool.and_eq_true, allL_iff, List.forall_mem_cons]

@[expose] def anyL {α : Type} (p : α → Bool) (L : List α) : Bool :=
  @List.rec α (fun _ => Bool) false (fun a _ ih => p a || ih) L

theorem anyL_iff {α : Type} {p : α → Bool} : ∀ {L : List α}, anyL p L = true ↔ ∃ a ∈ L, p a = true
  | [] => ⟨fun h => absurd h Bool.false_ne_true, fun h => by simp at h⟩
  | a :: L => by
    have e : anyL p (a :: L) = (p a || anyL p L) := rfl
    rw [e, Bool.or_eq_true, anyL_iff]
    constructor
    · rintro (h | ⟨b, hb, h⟩)
      · exact ⟨a, List.mem_cons.2 (Or.inl rfl), h⟩
      · exact ⟨b, List.mem_cons.2 (Or.inr hb), h⟩
    · rintro ⟨b, hb, h⟩
      rcases List.mem_cons.1 hb with rfl | hb
      · exact Or.inl h
      · exact Or.inr ⟨b, hb, h⟩

@[expose] noncomputable def ipN (i j : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight ipD (Nat.mul 3 (Nat.add (Nat.mul 72 i) j))) 7

@[expose] noncomputable def negN (i : ℕ) : ℕ := Nat.land (Nat.shiftRight negD (Nat.mul 7 i)) 127

@[expose] noncomputable def addN (i j : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight addD (Nat.mul 7 (Nat.add (Nat.mul 72 i) j))) 127

@[expose] def ipZ (i j : ℕ) : ℤ := (ipN i j : ℤ) - 2

@[expose] def rt (i : ℕ) : List ℤ := e6RootList[i]!

theorem ipN_lt (i j : ℕ) : ipN i j < 8 := by
  unfold ipN
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem len72 : e6RootList.length = 72 := by decide

theorem rt_eq_get {i : ℕ} (h : i < e6RootList.length) : rt i = e6RootList[i] := by
  rw [rt, getElem!_pos e6RootList i h]

theorem lt_len {i : ℕ} (h : i < 72) : i < e6RootList.length := lt_of_lt_of_eq h len72.symm

theorem mem_iff_rt {g : List ℤ} : g ∈ e6RootList ↔ ∃ k < 72, rt k = g := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, lt_of_lt_of_eq hk len72, rt_eq_get hk⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, lt_len hk, (rt_eq_get (lt_len hk)).symm⟩

theorem rt_mem {k : ℕ} (hk : k < 72) : rt k ∈ e6RootList := mem_iff_rt.2 ⟨k, hk, rfl⟩

@[expose] def ipCheck : Bool :=
  walkIdx (fun i a => walkIdx (fun j b => e6ip a b == ipZ i j) e6RootList 0) e6RootList 0

theorem ipCheck_eq : ipCheck = true := by decide +kernel

theorem ip_rt {i j : ℕ} (hi : i < 72) (hj : j < 72) : e6ip (rt i) (rt j) = ipZ i j := by
  have h1 := walkIdx_sound _ _ 0 ipCheck_eq i (lt_len hi)
  simp only [Nat.zero_add] at h1
  have h2 := walkIdx_sound _ _ 0 h1 j (lt_len hj)
  simp only [Nat.zero_add, beq_iff_eq] at h2
  rw [rt_eq_get (lt_len hi), rt_eq_get (lt_len hj)]
  exact h2

theorem ip_val {i j v : ℕ} (hi : i < 72) (hj : j < 72) (h : ipN i j = v) :
    e6ip (rt i) (rt j) = (v : ℤ) - 2 := by
  rw [ip_rt hi hj, ipZ, h]

theorem ip_m1 {i j : ℕ} (hi : i < 72) (hj : j < 72) (h : ipN i j = 1) :
    e6ip (rt i) (rt j) = -1 := by
  rw [ip_val hi hj h]
  norm_num

theorem ip_0 {i j : ℕ} (hi : i < 72) (hj : j < 72) (h : ipN i j = 2) :
    e6ip (rt i) (rt j) = 0 := by
  rw [ip_val hi hj h]
  norm_num

theorem ipN_of_0 {i j : ℕ} (hi : i < 72) (hj : j < 72) (h : e6ip (rt i) (rt j) = 0) :
    ipN i j = 2 := by
  rw [ip_rt hi hj, ipZ] at h
  omega

@[expose] def injCheck : Bool :=
  allLt 72 fun a => allLt 72 fun b => Nat.beq (ipN a b) 4 == Nat.beq a b

theorem injCheck_eq : injCheck = true := by decide +kernel

theorem rt_inj {a b : ℕ} (ha : a < 72) (hb : b < 72) (h : rt a = rt b) : a = b := by
  have h1 : (Nat.beq (ipN a b) 4 == Nat.beq a b) = true :=
    allLt_sound (allLt_sound injCheck_eq a ha) b hb
  have h2 : (Nat.beq (ipN a a) 4 == Nat.beq a a) = true :=
    allLt_sound (allLt_sound injCheck_eq a ha) a ha
  rw [beq_iff_eq] at h1 h2
  rw [Nat.beq_refl] at h2
  have e : ipZ a b = ipZ a a := by rw [← ip_rt ha hb, ← ip_rt ha ha, h]
  have e2 : ipN a b = ipN a a := by
    unfold ipZ at e
    omega
  rw [e2, h2] at h1
  exact Nat.eq_of_beq_eq_true h1.symm

theorem mem_map_rt {L : List ℕ} (hL : ∀ m ∈ L, m < 72) {k : ℕ} (hk : k < 72) :
    rt k ∈ L.map rt ↔ k ∈ L := by
  constructor
  · intro h
    obtain ⟨m, hm, he⟩ := List.mem_map.1 h
    rw [← rt_inj (hL m hm) hk he]
    exact hm
  · intro h
    exact List.mem_map.2 ⟨k, h, rfl⟩

@[expose] def negCheck : Bool :=
  walkIdx (fun i a => Nat.blt (negN i) 72 && (negK a == rt (negN i))) e6RootList 0

theorem negCheck_eq : negCheck = true := by decide +kernel

theorem neg_rt {i : ℕ} (hi : i < 72) : negN i < 72 ∧ negK (rt i) = rt (negN i) := by
  have h1 := walkIdx_sound _ _ 0 negCheck_eq i (lt_len hi)
  simp only [Nat.zero_add, Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at h1
  rw [rt_eq_get (lt_len hi)]
  exact h1

@[expose] def addCheck : Bool :=
  walkIdx (fun i a => walkIdx (fun j b => !(Nat.beq (ipN i j) 1) ||
    (Nat.blt (addN i j) 72 && (addK a b == rt (addN i j)))) e6RootList 0) e6RootList 0

theorem addCheck_eq : addCheck = true := by decide +kernel

theorem add_rt {i j : ℕ} (hi : i < 72) (hj : j < 72) (h : ipN i j = 1) :
    addN i j < 72 ∧ addK (rt i) (rt j) = rt (addN i j) := by
  have h1 := walkIdx_sound _ _ 0 addCheck_eq i (lt_len hi)
  simp only [Nat.zero_add] at h1
  have h2 := walkIdx_sound _ _ 0 h1 j (lt_len hj)
  simp only [Nat.zero_add, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, Nat.blt_eq,
    beq_iff_eq] at h2
  rw [rt_eq_get (lt_len hi), rt_eq_get (lt_len hj)]
  rcases h2 with h2 | h2
  · rw [h] at h2
    exact absurd h2 (by decide)
  · exact h2

theorem rt_len {i : ℕ} (hi : i < 72) : (rt i).length = 6 := by
  have h : ∀ g ∈ e6RootList, g.length = 6 := by decide +kernel
  exact h _ (rt_mem hi)

@[expose] def a2I (i j : ℕ) : List ℕ := [i, j, addN i j, negN i, negN j, negN (addN i j)]

@[expose] def baseOK (i j : ℕ) : Bool := Nat.blt i 72 && Nat.blt j 72 && Nat.beq (ipN i j) 1

theorem a2_rt {i j : ℕ} (h : baseOK i j = true) :
    a2K (rt i) (rt j) = (a2I i j).map rt ∧ ∀ m ∈ a2I i j, m < 72 := by
  simp only [baseOK, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨hi, hj⟩, hij⟩ := h
  obtain ⟨hs, hsum⟩ := add_rt hi hj hij
  obtain ⟨hni, hneg_i⟩ := neg_rt hi
  obtain ⟨hnj, hneg_j⟩ := neg_rt hj
  obtain ⟨hns, hneg_s⟩ := neg_rt hs
  refine ⟨?_, ?_⟩
  · simp only [a2K, a2I, List.map_cons, List.map_nil, hsum, hneg_i, hneg_j, hneg_s]
  · intro m hm
    simp only [a2I, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

@[expose] def z6 : List ℤ := [0, 0, 0, 0, 0, 0]

theorem len6 {x : List ℤ} (h : x.length = 6) : ∃ a b c d e f, x = [a, b, c, d, e, f] := by
  rcases x with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, x⟩⟩⟩⟩⟩⟩⟩
  all_goals try simp at h
  all_goals try omega
  exact ⟨a, b, c, d, e, f, rfl⟩

theorem smulK_one (x : List ℤ) : smulK 1 x = x := by simp [smulK]

theorem smulK_neg_one (x : List ℤ) : smulK (-1) x = negK x := by simp [smulK, negK]

theorem smulK_zero {x : List ℤ} (h : x.length = 6) : smulK 0 x = z6 := by
  obtain ⟨a, b, c, d, e, f, rfl⟩ := len6 h
  simp [smulK, z6]

theorem addK_z6 {x : List ℤ} (h : x.length = 6) : addK x z6 = x := by
  obtain ⟨a, b, c, d, e, f, rfl⟩ := len6 h
  simp [addK, z6]

theorem z6_addK {x : List ℤ} (h : x.length = 6) : addK z6 x = x := by
  obtain ⟨a, b, c, d, e, f, rfl⟩ := len6 h
  simp [addK, z6]

theorem addK_negK {x y : List ℤ} (hx : x.length = 6) (hy : y.length = 6) :
    addK (negK x) (negK y) = negK (addK x y) := by
  obtain ⟨a, b, c, d, e, f, rfl⟩ := len6 hx
  obtain ⟨a', b', c', d', e', f', rfl⟩ := len6 hy
  simp only [addK, negK, List.map_cons, List.map_nil, List.zipWith_cons_cons, List.zipWith_nil_left,
    neg_add]

theorem len_z6 : z6.length = 6 := rfl

theorem z6_z6 : addK z6 z6 = z6 := by simp [addK, z6]

theorem len_addK' (x y : List ℤ) : (addK x y).length = min x.length y.length := by
  simp [addK]

theorem len_negK' (x : List ℤ) : (negK x).length = x.length := by simp [negK]

theorem std30_eq : std30 = [[1, 0, 0, 0, 0], [1, 1, 0, 0, 0], [1, 1, 1, 0, 0], [1, 1, 1, 1, 0],
    [1, 1, 1, 1, 1], [0, 1, 0, 0, 0], [0, 1, 1, 0, 0], [0, 1, 1, 1, 0], [0, 1, 1, 1, 1],
    [0, 0, 1, 0, 0], [0, 0, 1, 1, 0], [0, 0, 1, 1, 1], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1],
    [0, 0, 0, 0, 1],
    [-1, 0, 0, 0, 0], [-1, -1, 0, 0, 0], [-1, -1, -1, 0, 0], [-1, -1, -1, -1, 0],
    [-1, -1, -1, -1, -1], [0, -1, 0, 0, 0], [0, -1, -1, 0, 0], [0, -1, -1, -1, 0],
    [0, -1, -1, -1, -1], [0, 0, -1, 0, 0], [0, 0, -1, -1, 0], [0, 0, -1, -1, -1],
    [0, 0, 0, -1, 0], [0, 0, 0, -1, -1], [0, 0, 0, 0, -1]] := by
  decide +kernel

@[expose] def chainP (d₀ d₁ d₂ d₃ d₄ : List ℤ) : List (List ℤ) :=
  [d₀, addK d₀ d₁, addK (addK d₀ d₁) d₂, addK (addK (addK d₀ d₁) d₂) d₃,
    addK (addK (addK (addK d₀ d₁) d₂) d₃) d₄, d₁, addK d₁ d₂, addK (addK d₁ d₂) d₃,
    addK (addK (addK d₁ d₂) d₃) d₄, d₂, addK d₂ d₃, addK (addK d₂ d₃) d₄, d₃, addK d₃ d₄, d₄]

theorem chain_eq {d₀ d₁ d₂ d₃ d₄ : List ℤ} (h₀ : d₀.length = 6) (h₁ : d₁.length = 6)
    (h₂ : d₂.length = 6) (h₃ : d₃.length = 6) (h₄ : d₄.length = 6) :
    chainK d₀ d₁ d₂ d₃ d₄ = chainP d₀ d₁ d₂ d₃ d₄ ++ (chainP d₀ d₁ d₂ d₃ d₄).map negK := by
  simp only [chainK, std30_eq, List.map_cons, List.map_nil, comb5K, smulK_one, smulK_neg_one,
    smulK_zero h₀, smulK_zero h₁, smulK_zero h₂, smulK_zero h₃, smulK_zero h₄, chainP,
    List.cons_append, List.nil_append]
  simp only [z6_z6, addK_z6, z6_addK, addK_negK, len_addK', len_negK', len_z6, h₀, h₁, h₂, h₃,
    h₄, min_self]

@[expose] def chainPos (e₀ e₁ e₂ e₃ e₄ : ℕ) : List ℕ :=
  [e₀, addN e₀ e₁, addN (addN e₀ e₁) e₂, addN (addN (addN e₀ e₁) e₂) e₃,
    addN (addN (addN (addN e₀ e₁) e₂) e₃) e₄, e₁, addN e₁ e₂, addN (addN e₁ e₂) e₃,
    addN (addN (addN e₁ e₂) e₃) e₄, e₂, addN e₂ e₃, addN (addN e₂ e₃) e₄, e₃, addN e₃ e₄, e₄]

@[expose] def chainIdx (e₀ e₁ e₂ e₃ e₄ : ℕ) : List ℕ :=
  chainPos e₀ e₁ e₂ e₃ e₄ ++ (chainPos e₀ e₁ e₂ e₃ e₄).map negN

@[expose] def chainOK (e₀ e₁ e₂ e₃ e₄ : ℕ) : Bool :=
  Nat.beq (ipN e₀ e₁) 1 && Nat.beq (ipN (addN e₀ e₁) e₂) 1 &&
  Nat.beq (ipN (addN (addN e₀ e₁) e₂) e₃) 1 &&
  Nat.beq (ipN (addN (addN (addN e₀ e₁) e₂) e₃) e₄) 1 &&
  Nat.beq (ipN e₁ e₂) 1 && Nat.beq (ipN (addN e₁ e₂) e₃) 1 &&
  Nat.beq (ipN (addN (addN e₁ e₂) e₃) e₄) 1 &&
  Nat.beq (ipN e₂ e₃) 1 && Nat.beq (ipN (addN e₂ e₃) e₄) 1 && Nat.beq (ipN e₃ e₄) 1

theorem chain_rt {e₀ e₁ e₂ e₃ e₄ : ℕ} (h₀ : e₀ < 72) (h₁ : e₁ < 72) (h₂ : e₂ < 72)
    (h₃ : e₃ < 72) (h₄ : e₄ < 72) (h : chainOK e₀ e₁ e₂ e₃ e₄ = true) :
    chainK (rt e₀) (rt e₁) (rt e₂) (rt e₃) (rt e₄) = (chainIdx e₀ e₁ e₂ e₃ e₄).map rt ∧
      ∀ m ∈ chainIdx e₀ e₁ e₂ e₃ e₄, m < 72 := by
  simp only [chainOK, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨i01, i02⟩, i03⟩, i04⟩, i12⟩, i13⟩, i14⟩, i23⟩, i24⟩, i34⟩ := h
  obtain ⟨l02, s02⟩ := add_rt h₀ h₁ i01
  obtain ⟨l03, s03⟩ := add_rt l02 h₂ i02
  obtain ⟨l04, s04⟩ := add_rt l03 h₃ i03
  obtain ⟨l05, s05⟩ := add_rt l04 h₄ i04
  obtain ⟨l13, s13⟩ := add_rt h₁ h₂ i12
  obtain ⟨l14, s14⟩ := add_rt l13 h₃ i13
  obtain ⟨l15, s15⟩ := add_rt l14 h₄ i14
  obtain ⟨l24, s24⟩ := add_rt h₂ h₃ i23
  obtain ⟨l25, s25⟩ := add_rt l24 h₄ i24
  obtain ⟨l35, s35⟩ := add_rt h₃ h₄ i34
  have hP : ∀ m ∈ chainPos e₀ e₁ e₂ e₃ e₄, m < 72 := by
    intro m hm
    simp only [chainPos, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> assumption
  have hPm : chainP (rt e₀) (rt e₁) (rt e₂) (rt e₃) (rt e₄) = (chainPos e₀ e₁ e₂ e₃ e₄).map rt := by
    simp only [chainP, chainPos, List.map_cons, List.map_nil]
    rw [s02, s03, s04, s05, s13, s14, s15, s24, s25, s35]
  refine ⟨?_, ?_⟩
  · rw [chain_eq (rt_len h₀) (rt_len h₁) (rt_len h₂) (rt_len h₃) (rt_len h₄), hPm, chainIdx,
      List.map_append, List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro m hm
    exact (neg_rt (hP m hm)).2
  · intro m hm
    rcases List.mem_append.1 hm with hm | hm
    · exact hP m hm
    · obtain ⟨m', hm', rfl⟩ := List.mem_map.1 hm
      exact (neg_rt (hP m' hm')).1

@[expose] def codesR : List ℕ := [33, 12, 27, 3, 24, 9]

@[expose] def codesW : List ℕ := [26, 19, 11, 10, 17, 25]

theorem codes_spec' : ∀ x ∈ List.range 8, ∀ y ∈ List.range 8,
    ((((x : ℤ) - 2, (y : ℤ) - 2) ∈ tab12K ↔ x * 8 + y ∈ codesR ++ codesW) ∧
     (((x : ℤ) - 2, (y : ℤ) - 2) ∈ rootTabK ↔ x * 8 + y ∈ codesR) ∧
     (((x : ℤ) - 2, (y : ℤ) - 2) ∈ wtTabK ↔ x * 8 + y ∈ codesW)) := by
  decide +kernel

theorem codes_spec (x : ℕ) (hx : x < 8) (y : ℕ) (hy : y < 8) :
    ((((x : ℤ) - 2, (y : ℤ) - 2) ∈ tab12K ↔ x * 8 + y ∈ codesR ++ codesW) ∧
     (((x : ℤ) - 2, (y : ℤ) - 2) ∈ rootTabK ↔ x * 8 + y ∈ codesR) ∧
     (((x : ℤ) - 2, (y : ℤ) - 2) ∈ wtTabK ↔ x * 8 + y ∈ codesW)) :=
  codes_spec' x (List.mem_range.2 hx) y (List.mem_range.2 hy)

@[expose] def frG (MX : ℕ) (X X₁ X₂ : List ℕ) (k a b : ℕ) : Bool :=
  bif bitB MX k then Nat.beq a 2 && Nat.beq b 2
  else !(Nat.beq a 2 && Nat.beq b 2) && memL (a * 8 + b) (codesR ++ codesW) &&
    (!memL (a * 8 + b) codesR || allL (fun m => Nat.beq (ipN k m) 2) X) &&
    (!memL (a * 8 + b) codesW ||
      (anyL (fun m => !Nat.beq (ipN k m) 2) X₁ && anyL (fun m => !Nat.beq (ipN k m) 2) X₂))

theorem nbeq_false {a b : ℕ} : Nat.beq a b = false ↔ ¬a = b := by
  rw [← Bool.not_eq_true, Nat.beq_eq]

theorem frG_sound {MX : ℕ} {X X₁ X₂ : List ℕ} {k a b : ℕ} (hM : ∀ k, bitB MX k = memL k X)
    (h : frG MX X X₁ X₂ k a b = true) :
    (k ∈ X ↔ (a = 2 ∧ b = 2)) ∧
    (k ∉ X → a * 8 + b ∈ codesR ++ codesW ∧ (a * 8 + b ∈ codesR → ∀ m ∈ X, ipN k m = 2) ∧
      (a * 8 + b ∈ codesW → (∃ m ∈ X₁, ipN k m ≠ 2) ∧ (∃ m ∈ X₂, ipN k m ≠ 2))) := by
  cases hm : memL k X with
  | true =>
    rw [frG, hM, hm, cond_true] at h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h
    have hk := memL_iff.1 hm
    exact ⟨⟨fun _ => h, fun _ => hk⟩, fun hn => absurd hk hn⟩
  | false =>
    rw [frG, hM, hm, cond_false] at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', Nat.beq_eq, memL_eq,
      decide_eq_true_eq, decide_eq_false_iff_not, allL_iff, anyL_iff, Bool.not_and,
      nbeq_false] at h
    have hk : k ∉ X := by
      intro hk
      rw [memL_iff.2 hk] at hm
      exact absurd hm (by decide)
    obtain ⟨⟨⟨hab, hc⟩, hR⟩, hW⟩ := h
    refine ⟨⟨fun h' => absurd h' hk, fun ⟨ha, hb⟩ => ?_⟩, fun _ => ⟨hc, fun hr => ?_, fun hw => ?_⟩⟩
    · rcases hab with ha' | hb'
      · exact absurd ha ha'
      · exact absurd hb hb'
    · rcases hR with hR | hR
      · exact absurd hr hR
      · exact hR
    · rcases hW with hW | hW
      · exact absurd hw hW
      · exact hW

@[expose] def frameJ (X₁ X₂ : List ℕ) (MX c d : ℕ) : Bool :=
  Nat.blt c 72 && Nat.blt d 72 && allL (fun m => Nat.beq (ipN c m) 2) (X₁ ++ X₂) &&
  allL (fun m => Nat.beq (ipN d m) 2) (X₁ ++ X₂) && Nat.beq (ipN c d) 1 &&
  allLt 72 (fun k => frG MX (X₁ ++ X₂) X₁ X₂ k (ipN k c) (ipN k d))

@[expose] def frameI (X₁ X₂ : List ℕ) (c d : ℕ) : Bool := frameJ X₁ X₂ (maskOf (X₁ ++ X₂)) c d

theorem mem_compK {X : List ℕ} {c : ℕ} (hX : ∀ m ∈ X, m < 72) (hc : c < 72)
    (h : ∀ m ∈ X, ipN c m = 2) : rt c ∈ compK (X.map rt) := by
  refine List.mem_filter.2 ⟨rt_mem hc, ?_⟩
  rw [List.all_eq_true]
  intro m hm
  obtain ⟨m', hm', rfl⟩ := List.mem_map.1 hm
  rw [beq_iff_eq]
  exact ip_0 hc (hX m' hm') (h m' hm')

theorem frameI_sound {X₁ X₂ : List ℕ} {c d : ℕ} (hX₁ : ∀ m ∈ X₁, m < 72)
    (hX₂ : ∀ m ∈ X₂, m < 72) (h : frameI X₁ X₂ c d = true) :
    c < 72 ∧ d < 72 ∧ rt c ∈ compK (X₁.map rt ++ X₂.map rt) ∧
    rt d ∈ compK (X₁.map rt ++ X₂.map rt) ∧
    e6ip (rt c) (rt d) = -1 ∧
    (∀ g ∈ e6RootList, (g ∈ X₁.map rt ++ X₂.map rt ↔ (e6ip g (rt c) = 0 ∧ e6ip g (rt d) = 0))) ∧
    (∀ g ∈ e6RootList, g ∉ X₁.map rt ++ X₂.map rt → (e6ip g (rt c), e6ip g (rt d)) ∈ tab12K) ∧
    (∀ g ∈ e6RootList, g ∉ X₁.map rt ++ X₂.map rt → (e6ip g (rt c), e6ip g (rt d)) ∈ rootTabK →
      ∀ m ∈ X₁.map rt ++ X₂.map rt, e6ip g m = 0) ∧
    (∀ g ∈ e6RootList, g ∉ X₁.map rt ++ X₂.map rt → (e6ip g (rt c), e6ip g (rt d)) ∈ wtTabK →
      (∃ m ∈ X₁.map rt, e6ip g m ≠ 0) ∧ (∃ m ∈ X₂.map rt, e6ip g m ≠ 0)) := by
  simp only [frameI, frameJ, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, allL_iff] at h
  obtain ⟨⟨⟨⟨⟨hc, hd⟩, hcX⟩, hdX⟩, hcd⟩, hk⟩ := h
  have hX : ∀ m ∈ X₁ ++ X₂, m < 72 := by
    intro m hm
    rcases List.mem_append.1 hm with hm | hm
    · exact hX₁ m hm
    · exact hX₂ m hm
  rw [← List.map_append]
  refine ⟨hc, hd, mem_compK hX hc hcX, mem_compK hX hd hdX, ip_m1 hc hd hcd, ?_, ?_, ?_, ?_⟩
  all_goals
    intro g hg
    obtain ⟨k, hk72, rfl⟩ := mem_iff_rt.1 hg
    have hf := frG_sound (bitB_maskOf _) (allLt_sound hk k hk72)
    rw [mem_map_rt hX hk72, ip_rt hk72 hc, ip_rt hk72 hd, ipZ, ipZ]
    have hspec := codes_spec _ (ipN_lt k c) _ (ipN_lt k d)
  · rw [hf.1]
    constructor
    · rintro ⟨h1, h2⟩
      constructor <;> omega
    · rintro ⟨h1, h2⟩
      constructor <;> omega
  · intro hn
    exact hspec.1.2 (hf.2 hn).1
  · intro hn hr m hm
    obtain ⟨m', hm', rfl⟩ := List.mem_map.1 hm
    exact ip_0 hk72 (hX m' hm') ((hf.2 hn).2.1 (hspec.2.1.1 hr) m' hm')
  · intro hn hw
    obtain ⟨⟨m₁, hm₁, h₁⟩, ⟨m₂, hm₂, h₂⟩⟩ := (hf.2 hn).2.2 (hspec.2.2.1 hw)
    refine ⟨⟨rt m₁, List.mem_map.2 ⟨m₁, hm₁, rfl⟩, ?_⟩, ⟨rt m₂, List.mem_map.2 ⟨m₂, hm₂, rfl⟩, ?_⟩⟩
    · rw [ip_rt hk72 (hX₁ m₁ hm₁), ipZ]
      omega
    · rw [ip_rt hk72 (hX₂ m₂ hm₂), ipZ]
      omega

@[expose] def lineI (X : List ℕ) (c d ua ub k : ℕ) : Bool :=
  !memL k X && ((Nat.beq (ipN k c) ua && Nat.beq (ipN k d) ub) ||
    (Nat.beq (ipN k c) (4 - ua) && Nat.beq (ipN k d) (4 - ub)))

theorem lineI_eq {X : List ℕ} (hX : ∀ m ∈ X, m < 72) {c d ua ub k : ℕ} (hc : c < 72)
    (hd : d < 72) (hua : ua ≤ 4) (hub : ub ≤ 4) (hk : k < 72) :
    (!(decide (rt k ∈ X.map rt)) &&
      (decide ((e6ip (rt k) (rt c), e6ip (rt k) (rt d)) = ((ua : ℤ) - 2, (ub : ℤ) - 2)) ||
        decide ((e6ip (rt k) (rt c), e6ip (rt k) (rt d)) =
          (-((ua : ℤ) - 2, (ub : ℤ) - 2).1, -((ua : ℤ) - 2, (ub : ℤ) - 2).2)))) =
      lineI X c d ua ub k := by
  rw [lineI, memL_eq, ip_rt hk hc, ip_rt hk hd, ipZ, ipZ]
  have e1 : ∀ x u : ℕ, ((x : ℤ) - 2 = (u : ℤ) - 2) ↔ x = u := fun x u => by omega
  have e2 : ∀ x u : ℕ, u ≤ 4 → (((x : ℤ) - 2 = -((u : ℤ) - 2)) ↔ x = 4 - u) := fun x u hu => by
    omega
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq, Prod.mk.injEq, mem_map_rt hX hk, e1, e2 _ _ hua, e2 _ _ hub, Nat.beq_eq]

theorem mem_lineK {X₁ X₂ : List ℕ} (hX : ∀ m ∈ X₁ ++ X₂, m < 72) {c d ua ub : ℕ} (hc : c < 72)
    (hd : d < 72) (hua : ua ≤ 4) (hub : ub ≤ 4) {c₁ d₁ c₂ d₂ : List ℤ}
    (hA : a2K c₁ d₁ ++ a2K c₂ d₂ = (X₁ ++ X₂).map rt) {g : List ℤ} :
    g ∈ lineK c₁ d₁ c₂ d₂ (rt c) (rt d) ((ua : ℤ) - 2, (ub : ℤ) - 2) ↔
      ∃ k < 72, rt k = g ∧ lineI (X₁ ++ X₂) c d ua ub k = true := by
  rw [lineK, List.mem_filter, hA]
  constructor
  · rintro ⟨hg, hp⟩
    obtain ⟨k, hk, rfl⟩ := mem_iff_rt.1 hg
    refine ⟨k, hk, rfl, ?_⟩
    rw [← lineI_eq hX hc hd hua hub hk]
    exact hp
  · rintro ⟨k, hk, rfl, hl⟩
    refine ⟨rt_mem hk, ?_⟩
    rw [← lineI_eq hX hc hd hua hub hk] at hl
    exact hl

@[expose] def lineJ (MX c d ua ub k : ℕ) : Bool :=
  !bitB MX k && ((Nat.beq (ipN k c) ua && Nat.beq (ipN k d) ub) ||
    (Nat.beq (ipN k c) (4 - ua) && Nat.beq (ipN k d) (4 - ub)))

theorem lineJ_maskOf (X : List ℕ) (c d ua ub k : ℕ) :
    lineJ (maskOf X) c d ua ub k = lineI X c d ua ub k := by
  rw [lineJ, lineI, bitB_maskOf]

@[expose] def a5J (X₁ X₂ : List ℕ) (MX MC c d ua ub e₀ e₁ e₂ e₃ e₄ : ℕ) : Bool :=
  memL e₀ X₁ && memL e₁ X₁ && Nat.beq (ipN e₀ e₁) 1 &&
  Nat.blt e₂ 72 && lineJ MX c d ua ub e₂ && Nat.beq (ipN e₁ e₂) 1 &&
  Nat.beq (ipN e₀ e₂) 2 &&
  memL e₃ X₂ && Nat.beq (ipN e₂ e₃) 1 && Nat.beq (ipN e₁ e₃) 2 && Nat.beq (ipN e₀ e₃) 2 &&
  memL e₄ X₂ && Nat.beq (ipN e₃ e₄) 1 && Nat.beq (ipN e₂ e₄) 2 && Nat.beq (ipN e₁ e₄) 2 &&
  Nat.beq (ipN e₀ e₄) 2 && chainOK e₀ e₁ e₂ e₃ e₄ &&
  allLt 72 (fun k => (bitB MX k || lineJ MX c d ua ub k) == bitB MC k)

@[expose] def a5I (X₁ X₂ : List ℕ) (c d ua ub e₀ e₁ e₂ e₃ e₄ : ℕ) : Bool :=
  a5J X₁ X₂ (maskOf (X₁ ++ X₂)) (maskOf (chainIdx e₀ e₁ e₂ e₃ e₄)) c d ua ub e₀ e₁ e₂ e₃ e₄

theorem a5I_sound {X₁ X₂ : List ℕ} {c d ua ub e₀ e₁ e₂ e₃ e₄ : ℕ} {c₁ d₁ c₂ d₂ : List ℤ}
    (hX₁ : ∀ m ∈ X₁, m < 72) (hX₂ : ∀ m ∈ X₂, m < 72) (hc : c < 72) (hd : d < 72)
    (hua : ua ≤ 4) (hub : ub ≤ 4) (hA₁ : a2K c₁ d₁ = X₁.map rt) (hA₂ : a2K c₂ d₂ = X₂.map rt)
    (h : a5I X₁ X₂ c d ua ub e₀ e₁ e₂ e₃ e₄ = true) :
    tcA5K c₁ d₁ c₂ d₂ (rt c) (rt d) ((ua : ℤ) - 2, (ub : ℤ) - 2) := by
  have hX : ∀ m ∈ X₁ ++ X₂, m < 72 := by
    intro m hm
    rcases List.mem_append.1 hm with hm | hm
    · exact hX₁ m hm
    · exact hX₂ m hm
  have hA : a2K c₁ d₁ ++ a2K c₂ d₂ = (X₁ ++ X₂).map rt := by rw [hA₁, hA₂, List.map_append]
  simp only [a5I, a5J, lineJ_maskOf, bitB_maskOf, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨m0, m1⟩, i01⟩, l2⟩, hl⟩, i12⟩, i02⟩, m3⟩, i23⟩, i13⟩, i03⟩, m4⟩, i34⟩,
    i24⟩, i14⟩, i04⟩, hch⟩, hcov⟩ := h
  have b0 := hX₁ _ (memL_iff.1 m0)
  have b1 := hX₁ _ (memL_iff.1 m1)
  have b3 := hX₂ _ (memL_iff.1 m3)
  have b4 := hX₂ _ (memL_iff.1 m4)
  obtain ⟨hC, hCX⟩ := chain_rt b0 b1 l2 b3 b4 hch
  have hcv : ∀ k < 72, ((memL k (X₁ ++ X₂) || lineI (X₁ ++ X₂) c d ua ub k) ==
      memL k (chainIdx e₀ e₁ e₂ e₃ e₄)) = true := fun k hk => allLt_sound hcov k hk
  have hm₁ : ∀ e, memL e X₁ = true → rt e ∈ a2K c₁ d₁ := fun e he => by
    rw [hA₁]
    exact List.mem_map.2 ⟨e, memL_iff.1 he, rfl⟩
  have hm₂ : ∀ e, memL e X₂ = true → rt e ∈ a2K c₂ d₂ := fun e he => by
    rw [hA₂]
    exact List.mem_map.2 ⟨e, memL_iff.1 he, rfl⟩
  unfold tcA5K A5L2K A5L3K A5L4K A5LastK
  refine ⟨rt e₀, hm₁ e₀ m0, rt e₁, hm₁ e₁ m1, ip_m1 b0 b1 i01,
    rt e₂, (mem_lineK hX hc hd hua hub hA).2 ⟨e₂, l2, rfl, hl⟩, ip_m1 b1 l2 i12, ip_0 b0 l2 i02,
    rt e₃, hm₂ e₃ m3, ip_m1 l2 b3 i23, ip_0 b1 b3 i13, ip_0 b0 b3 i03,
    rt e₄, hm₂ e₄ m4, ip_m1 b3 b4 i34, ip_0 l2 b4 i24, ip_0 b1 b4 i14, ip_0 b0 b4 i04, ?_, ?_⟩
  · intro g hg
    rw [hC]
    have key : ∃ k < 72, rt k = g ∧ (memL k (X₁ ++ X₂) || lineI (X₁ ++ X₂) c d ua ub k) = true := by
      rcases List.mem_append.1 hg with hg | hg
      · rw [hA] at hg
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hg
        exact ⟨k, hX k hk, rfl, by rw [memL_iff.2 hk, Bool.true_or]⟩
      · obtain ⟨k, hk, rfl, hl⟩ := (mem_lineK hX hc hd hua hub hA).1 hg
        exact ⟨k, hk, rfl, by rw [hl, Bool.or_true]⟩
    obtain ⟨k, hk, rfl, hkey⟩ := key
    have e := hcv k hk
    rw [hkey, beq_iff_eq] at e
    exact List.mem_map.2 ⟨k, memL_iff.1 e.symm, rfl⟩
  · intro g hg
    rw [hC] at hg
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hg
    have e := hcv k (hCX k hk)
    rw [memL_iff.2 hk, beq_iff_eq, Bool.or_eq_true] at e
    rcases e with e | e
    · refine List.mem_append.2 (Or.inl ?_)
      rw [hA]
      exact List.mem_map.2 ⟨k, memL_iff.1 e, rfl⟩
    · exact List.mem_append.2 (Or.inr ((mem_lineK hX hc hd hua hub hA).2 ⟨k, hCX k hk, rfl, e⟩))

@[expose] def recI (p₁ p₂ : ℕ × ℕ) : List ℕ → Bool
  | c :: d :: a0 :: a1 :: a2 :: a3 :: a4 :: b0 :: b1 :: b2 :: b3 :: b4 :: f0 :: f1 :: f2 :: f3 :: f4
      :: _ =>
    frameI (a2I p₁.1 p₁.2) (a2I p₂.1 p₂.2) c d &&
      a5I (a2I p₁.1 p₁.2) (a2I p₂.1 p₂.2) c d 3 2 a0 a1 a2 a3 a4 &&
      a5I (a2I p₁.1 p₁.2) (a2I p₂.1 p₂.2) c d 2 3 b0 b1 b2 b3 b4 &&
      a5I (a2I p₁.1 p₁.2) (a2I p₂.1 p₂.2) c d 3 1 f0 f1 f2 f3 f4
  | _ => false

theorem wtRepK_eq : wtRepK = [(((3 : ℕ) : ℤ) - 2, ((2 : ℕ) : ℤ) - 2),
    (((2 : ℕ) : ℤ) - 2, ((3 : ℕ) : ℤ) - 2), (((3 : ℕ) : ℤ) - 2, ((1 : ℕ) : ℤ) - 2)] := by
  decide +kernel

theorem recI_sound {p₁ p₂ : ℕ × ℕ} {w : List ℕ} (hb₁ : baseOK p₁.1 p₁.2 = true)
    (hb₂ : baseOK p₂.1 p₂.2 = true) (h : recI p₁ p₂ w = true) :
    ∃ c₃ ∈ compK (a2K (rt p₁.1) (rt p₁.2) ++ a2K (rt p₂.1) (rt p₂.2)),
      ∃ d₃ ∈ compK (a2K (rt p₁.1) (rt p₁.2) ++ a2K (rt p₂.1) (rt p₂.2)),
      FrameK (rt p₁.1) (rt p₁.2) (rt p₂.1) (rt p₂.2) c₃ d₃ := by
  obtain ⟨hA₁, hX₁⟩ := a2_rt hb₁
  obtain ⟨hA₂, hX₂⟩ := a2_rt hb₂
  unfold recI at h
  split at h
  · simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨hf, ha⟩, hb⟩, he⟩ := h
    obtain ⟨hc, hd, hcc, hdc, h1, h2, h3, h4, h5⟩ := frameI_sound hX₁ hX₂ hf
    unfold FrameK
    rw [hA₁, hA₂]
    refine ⟨_, hcc, _, hdc, h1, h2, h3, h4, h5, ?_⟩
    rw [wtRepK_eq]
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl
    · exact a5I_sound hX₁ hX₂ hc hd (by decide) (by decide) hA₁ hA₂ ha
    · exact a5I_sound hX₁ hX₂ hc hd (by decide) (by decide) hA₁ hA₂ hb
    · exact a5I_sound hX₁ hX₂ hc hd (by decide) (by decide) hA₁ hA₂ he
  · exact absurd h (by decide)

@[expose] def walkB {α β : Type} (f : α → Bool) (g : α → β → Bool) : List α → List β → Bool
  | [], _ => true
  | a :: as, ws => bif f a then
      (match ws with
        | [] => false
        | w :: ws' => g a w && walkB f g as ws')
    else walkB f g as ws

theorem walkB_sound {α β : Type} (f : α → Bool) (g : α → β → Bool) :
    ∀ (L : List α) (W : List β), walkB f g L W = true → ∀ a ∈ L, f a = true → ∃ w, g a w = true
  | [], _, _, a, ha, _ => absurd ha List.not_mem_nil
  | a :: as, ws, h, x, hx, hf => by
    cases hfa : f a
    · simp only [walkB, hfa, cond_false] at h
      rcases List.mem_cons.1 hx with rfl | hx
      · rw [hfa] at hf
        exact absurd hf (by decide)
      · exact walkB_sound f g as ws h x hx hf
    · cases ws with
      | nil => simp [walkB, hfa] at h
      | cons w ws' =>
        simp only [walkB, hfa, cond_true, Bool.and_eq_true] at h
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨w, h.1⟩
        · exact walkB_sound f g as ws' h.2 x hx hf

@[expose] def orthI (p₁ p₂ : ℕ × ℕ) : Bool :=
  Nat.beq (ipN p₁.1 p₂.1) 2 && Nat.beq (ipN p₁.1 p₂.2) 2 && Nat.beq (ipN p₁.2 p₂.1) 2 &&
    Nat.beq (ipN p₁.2 p₂.2) 2

@[expose] def sliceI (S B : List (ℕ × ℕ)) (W : List (List (List ℕ))) : Bool :=
  allL (fun p => baseOK p.1 p.2) B &&
    walkB (fun _ => true) (fun p₁ ws => baseOK p₁.1 p₁.2 && walkB (orthI p₁) (recI p₁) B ws) S W

theorem frames_of (S B : List (ℕ × ℕ)) (W : List (List (List ℕ))) (h : sliceI S B W = true) :
    ∀ p₁ ∈ S.map (fun ij => (e6RootList[ij.1]!, e6RootList[ij.2]!)),
    ∀ p₂ ∈ B.map (fun ij => (e6RootList[ij.1]!, e6RootList[ij.2]!)),
      (e6ip p₁.1 p₂.1 = 0 ∧ e6ip p₁.1 p₂.2 = 0 ∧ e6ip p₁.2 p₂.1 = 0 ∧ e6ip p₁.2 p₂.2 = 0) →
      ∃ c₃ ∈ compK (a2K p₁.1 p₁.2 ++ a2K p₂.1 p₂.2),
        ∃ d₃ ∈ compK (a2K p₁.1 p₁.2 ++ a2K p₂.1 p₂.2),
        FrameK p₁.1 p₁.2 p₂.1 p₂.2 c₃ d₃ := by
  intro p₁ hp₁ p₂ hp₂ ho
  obtain ⟨q₁, hq₁, rfl⟩ := List.mem_map.1 hp₁
  obtain ⟨q₂, hq₂, rfl⟩ := List.mem_map.1 hp₂
  rw [sliceI, Bool.and_eq_true, allL_iff] at h
  have hb₂ := h.1 q₂ hq₂
  obtain ⟨ws, hws⟩ := walkB_sound _ _ S W h.2 q₁ hq₁ rfl
  simp only [Bool.and_eq_true] at hws
  have hb₁ := hws.1
  have hb₁' := hb₁
  have hb₂' := hb₂
  simp only [baseOK, Bool.and_eq_true, Nat.blt_eq] at hb₁' hb₂'
  have ho' : orthI q₁ q₂ = true := by
    obtain ⟨h1, h2, h3, h4⟩ := ho
    simp only [orthI, Bool.and_eq_true, Nat.beq_eq]
    exact ⟨⟨⟨ipN_of_0 hb₁'.1.1 hb₂'.1.1 h1, ipN_of_0 hb₁'.1.1 hb₂'.1.2 h2⟩,
      ipN_of_0 hb₁'.1.2 hb₂'.1.1 h3⟩, ipN_of_0 hb₁'.1.2 hb₂'.1.2 h4⟩
  obtain ⟨w, hw⟩ := walkB_sound _ _ B ws hws.2 q₂ hq₂ ho'
  exact recI_sound hb₁ hb₂ hw

@[expose] def coverJ (B : List (ℕ × ℕ)) (i j k : ℕ) : Bool :=
  match B[k]? with
  | some p => Nat.blt p.1 72 && Nat.blt p.2 72 && memL p.1 (a2I i j) && memL p.2 (a2I i j)
  | none => false

@[expose] def coverI (B : List (ℕ × ℕ)) (W : List (List ℕ)) : Bool :=
  walkB (fun _ => true)
    (fun i ks => walkB (fun j => Nat.beq (ipN i j) 1) (coverJ B i) (List.range 72) ks)
    (List.range 72) W

theorem cover_of (B : List (ℕ × ℕ)) (W : List (List ℕ)) (h : coverI B W = true) :
    ∀ a ∈ e6RootList, ∀ b ∈ e6RootList, e6ip a b = -1 →
      ∃ p ∈ B.map (fun ij => (e6RootList[ij.1]!, e6RootList[ij.2]!)),
        p.1 ∈ a2K a b ∧ p.2 ∈ a2K a b := by
  intro a ha b hb hab
  obtain ⟨i, hi, rfl⟩ := mem_iff_rt.1 ha
  obtain ⟨j, hj, rfl⟩ := mem_iff_rt.1 hb
  have hij : ipN i j = 1 := by
    rw [ip_rt hi hj, ipZ] at hab
    omega
  obtain ⟨ks, hks⟩ := walkB_sound _ _ _ W h i (List.mem_range.2 hi) rfl
  obtain ⟨k, hk⟩ := walkB_sound _ _ _ ks hks j (List.mem_range.2 hj)
    (by simp only [hij, Nat.beq_refl])
  have hb' : baseOK i j = true := by
    simp only [baseOK, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq]
    exact ⟨⟨hi, hj⟩, hij⟩
  obtain ⟨hA, hX⟩ := a2_rt hb'
  unfold coverJ at hk
  cases hp : B[k]? with
  | none =>
    rw [hp] at hk
    simp at hk
  | some p =>
    rw [hp] at hk
    simp only [Bool.and_eq_true, Nat.blt_eq, memL_iff] at hk
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hk
    refine ⟨(rt p.1, rt p.2), List.mem_map.2 ⟨p, List.mem_of_getElem? hp, rfl⟩, ?_, ?_⟩
    · rw [hA]
      exact List.mem_map.2 ⟨p.1, h3, rfl⟩
    · rw [hA]
      exact List.mem_map.2 ⟨p.2, h4, rfl⟩

end CFSG.StandardType.TableCRes.FrameK

end
