module

public import Certificates.Data.CFSGNative.YGroups.DCE.OmegaBig
public import CFSG.YGroups.DCE.PermBSpec
public import CFSG.YGroups.DCE.OmegaSpec
public import Batteries.Data.ByteArray
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.YGroups.DCE

open CFSG.Monster.B.Co2 Pointwise

namespace BigOmega

@[expose] def rowFinset (n : ℕ) (O : BigOmega) (p : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun x => ∃ k < O.m, (O.row p)[k]! = (x : ℕ)

theorem mem_rowFinset {n : ℕ} {O : BigOmega} {p : ℕ} {x : Fin n} :
    x ∈ rowFinset n O p ↔ ∃ k < O.m, (O.row p)[k]! = (x : ℕ) := by
  simp only [rowFinset, Finset.mem_filter, Finset.mem_univ, true_and]

theorem rowAux_zero (O : BigOmega) (q : ℕ) : O.rowAux 0 q = O.X0 := rfl

theorem rowAux_succ (O : BigOmega) (f q : ℕ) :
    O.rowAux (f + 1) q =
      if q = 0 then O.X0 else (O.rowAux f (O.parAt q)).map fun x => bget (O.tg[O.labAt q]!) x :=
  rfl

theorem size_rowAux (O : BigOmega) : ∀ f q, (O.rowAux f q).size = O.X0.size
  | 0, _ => rfl
  | f + 1, q => by
    rw [rowAux_succ]
    split_ifs
    · rfl
    · rw [Array.size_map]
      exact size_rowAux O f _

theorem size_row (O : BigOmega) (p : ℕ) : (O.row p).size = O.X0.size := size_rowAux O p p

theorem rowAux_eq_of_le (O : BigOmega) (hv : ∀ q < O.N, q ≠ 0 → O.parAt q < q) :
    ∀ q, q < O.N → ∀ f f', q ≤ f → q ≤ f' → O.rowAux f q = O.rowAux f' q := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq f f' hf hf'
    rcases Nat.eq_zero_or_pos q with rfl | hq0
    · cases f <;> cases f' <;> simp only [rowAux_zero, rowAux_succ, ↓reduceIte]
    · obtain ⟨f, rfl⟩ : ∃ f₀, f = f₀ + 1 := ⟨f - 1, by omega⟩
      obtain ⟨f', rfl⟩ : ∃ f₀, f' = f₀ + 1 := ⟨f' - 1, by omega⟩
      have hp := hv q hq (by omega)
      have hq0' : q ≠ 0 := by omega
      rw [rowAux_succ, rowAux_succ]
      simp only [hq0', ↓reduceIte]
      rw [ih (O.parAt q) hp (lt_trans hp hq) f f' (by omega) (by omega)]

theorem row_zero (O : BigOmega) : O.row 0 = O.X0 := rfl

theorem row_succ (O : BigOmega) (hv : ∀ q < O.N, q ≠ 0 → O.parAt q < q) {p : ℕ} (hp : p < O.N)
    (hp0 : p ≠ 0) :
    O.row p = (O.row (O.parAt p)).map fun x => bget (O.tg[O.labAt p]!) x := by
  have hpar := hv p hp hp0
  obtain ⟨f, rfl⟩ : ∃ f, p = f + 1 := ⟨p - 1, by omega⟩
  show O.rowAux (f + 1) (f + 1) = _
  rw [rowAux_succ]
  simp only [hp0, ↓reduceIte]
  rw [rowAux_eq_of_le O hv (O.parAt (f + 1)) (lt_trans hpar hp) f (O.parAt (f + 1)) (by omega)
    le_rfl]
  rfl

theorem getElem!_map_of_lt {a : Array ℕ} {f : ℕ → ℕ} {k : ℕ} (hk : k < a.size) :
    (a.map f)[k]! = f a[k]! := by
  rw [getElem!_pos (a.map f) k (by simpa using hk), Array.getElem_map, getElem!_pos a k hk]

theorem row_entry (O : BigOmega) (hv : ∀ q < O.N, q ≠ 0 → O.parAt q < q) {p : ℕ} (hp : p < O.N)
    (hp0 : p ≠ 0) {k : ℕ} (hk : k < O.X0.size) :
    (O.row p)[k]! = bget (O.tg[O.labAt p]!) (O.row (O.parAt p))[k]! := by
  rw [row_succ O hv hp hp0, getElem!_map_of_lt (by rw [size_row]; exact hk)]

theorem row_zero_entry (O : BigOmega) {k : ℕ} : (O.row 0)[k]! = O.X0[k]! := rfl

theorem rowHash_eq_sum {n : ℕ} {O : BigOmega} {p : ℕ} (hlt : ∀ k < O.m, (O.row p)[k]! < n)
    (hinj : ∀ k₁ < O.m, ∀ k₂ < O.m, (O.row p)[k₁]! = (O.row p)[k₂]! → k₁ = k₂) :
    O.rowHash p = ∑ x ∈ rowFinset n O p, O.R[(x : ℕ)]! := by
  show sumMod O.m (fun k => O.R[(O.row p)[k]!]!) = _
  rw [sumMod_eq_sum_range]
  exact sum_range_eq_sum_finset (fun k => (O.row p)[k]!) (fun y => O.R[y]!) hlt hinj

theorem imgHash_eq_sum {n : ℕ} {O : BigOmega} {σ : ByteArray} {p : ℕ}
    (hlt : ∀ k < O.m, bget σ (O.row p)[k]! < n)
    (hinj : ∀ k₁ < O.m, ∀ k₂ < O.m,
      bget σ (O.row p)[k₁]! = bget σ (O.row p)[k₂]! → k₁ = k₂) :
    O.imgHash σ p = ∑ x ∈ Finset.univ.filter
      (fun x : Fin n => ∃ k < O.m, bget σ (O.row p)[k]! = (x : ℕ)), O.R[(x : ℕ)]! := by
  show sumMod O.m (fun k => O.R[bget σ (O.row p)[k]!]!) = _
  rw [sumMod_eq_sum_range]
  exact sum_range_eq_sum_finset (fun k => bget σ (O.row p)[k]!) (fun y => O.R[y]!) hlt hinj

theorem imgFinset_eq_smul {n : ℕ} {O : BigOmega} {Γ : Subgroup (Equiv.Perm (Fin n))}
    {σ : ByteArray} {e : Γ} (hσ : RepB n σ (e : Equiv.Perm (Fin n))) {p : ℕ}
    (hlt : ∀ k < O.m, (O.row p)[k]! < n) :
    Finset.univ.filter (fun x : Fin n => ∃ k < O.m, bget σ (O.row p)[k]! = (x : ℕ)) =
      e • rowFinset n O p := by
  ext x
  rw [Finset.mem_filter, Finset.mem_smul_finset]
  constructor
  · rintro ⟨-, k, hk, hkx⟩
    refine ⟨⟨(O.row p)[k]!, hlt k hk⟩, mem_rowFinset.2 ⟨k, hk, rfl⟩, ?_⟩
    apply Fin.ext
    exact ((hσ.apply (hlt k hk)).symm).trans hkx
  · rintro ⟨c, hc, hcx⟩
    obtain ⟨k, hk, hkc⟩ := mem_rowFinset.1 hc
    refine ⟨Finset.mem_univ _, k, hk, ?_⟩
    rw [hkc, hσ.2 c]
    exact congrArg Fin.val hcx

structure TreeFacts (O : BigOmega) : Prop where
  m_eq : O.m = O.X0.size
  X0_lt : ∀ a < O.X0.size, O.X0[a]! < O.n
  tg_lt : ∀ l < O.tg.size, ∀ x < O.n, bget O.tg[l]! x < O.n
  tree : ∀ p < O.N, p ≠ 0 → O.parAt p < p ∧ O.labAt p < O.tg.size

theorem row_lt_n {O : BigOmega} (F : TreeFacts O) : ∀ p < O.N, ∀ k < O.m, (O.row p)[k]! < O.n := by
  have hv : ∀ q < O.N, q ≠ 0 → O.parAt q < q := fun q hq hq0 => (F.tree q hq hq0).1
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp k hk
    by_cases hp0 : p = 0
    · subst hp0
      rw [row_zero_entry]
      exact F.X0_lt k (F.m_eq ▸ hk)
    · obtain ⟨hpar, hlab⟩ := F.tree p hp hp0
      rw [row_entry O hv hp hp0 (F.m_eq ▸ hk)]
      exact F.tg_lt _ hlab _ (ih (O.parAt p) hpar (lt_trans hpar hp) k hk)

end BigOmega

theorem u32Entry_eq (b : ByteArray) (x : ℕ) :
    u32Entry b x = b[4 * x]!.toNat + 256 * b[4 * x + 1]!.toNat + 65536 * b[4 * x + 2]!.toNat +
      16777216 * b[4 * x + 3]!.toNat := by
  unfold u32Entry
  simp only [get!_eq_getElem!]

theorem getElem!_push4_lt (b : ByteArray) (a₀ a₁ a₂ a₃ : UInt8) {i : ℕ} (hi : i < b.size) :
    ((((b.push a₀).push a₁).push a₂).push a₃)[i]! = b[i]! := by
  rw [ByteArray.getElem!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
    ByteArray.getElem!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
    ByteArray.getElem!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
    ByteArray.getElem!_push_lt _ _ _ hi]

theorem size_push32 (b : ByteArray) (v : ℕ) : (push32 b v).size = b.size + 4 := by
  simp only [push32, ByteArray.size_push]

theorem u32Entry_push32_of_lt (b : ByteArray) (v : ℕ) {x : ℕ} (hx : 4 * x + 4 ≤ b.size) :
    u32Entry (push32 b v) x = u32Entry b x := by
  rw [u32Entry_eq, u32Entry_eq, push32, getElem!_push4_lt _ _ _ _ _ (by omega),
    getElem!_push4_lt _ _ _ _ _ (by omega), getElem!_push4_lt _ _ _ _ _ (by omega),
    getElem!_push4_lt _ _ _ _ _ (by omega)]

theorem u32Entry_push32_of_eq (b : ByteArray) (v : ℕ) {x : ℕ} (hx : b.size = 4 * x) :
    u32Entry (push32 b v) x = v % 2 ^ 32 := by
  rw [u32Entry_eq, push32]
  have h0 : ((((b.push (byteOf v 0)).push (byteOf v 1)).push (byteOf v 2)).push
      (byteOf v 3))[4 * x]! = byteOf v 0 := by
    rw [ByteArray.getElem!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.getElem!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.getElem!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega), ← hx]
    exact ByteArray.getElem!_push_eq b _
  have h1 : ((((b.push (byteOf v 0)).push (byteOf v 1)).push (byteOf v 2)).push
      (byteOf v 3))[4 * x + 1]! = byteOf v 1 := by
    rw [ByteArray.getElem!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.getElem!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega)]
    have := ByteArray.getElem!_push_eq (b.push (byteOf v 0)) (byteOf v 1)
    rwa [ByteArray.size_push, hx] at this
  have h2 : ((((b.push (byteOf v 0)).push (byteOf v 1)).push (byteOf v 2)).push
      (byteOf v 3))[4 * x + 2]! = byteOf v 2 := by
    rw [ByteArray.getElem!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega)]
    have := ByteArray.getElem!_push_eq ((b.push (byteOf v 0)).push (byteOf v 1)) (byteOf v 2)
    rwa [ByteArray.size_push, ByteArray.size_push, hx] at this
  have h3 : ((((b.push (byteOf v 0)).push (byteOf v 1)).push (byteOf v 2)).push
      (byteOf v 3))[4 * x + 3]! = byteOf v 3 := by
    have := ByteArray.getElem!_push_eq (((b.push (byteOf v 0)).push (byteOf v 1)).push
      (byteOf v 2)) (byteOf v 3)
    rwa [ByteArray.size_push, ByteArray.size_push, ByteArray.size_push, hx] at this
  rw [h0, h1, h2, h3]
  simp only [byteOf, UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  norm_num
  omega

theorem getElem!_append_left (a b : ByteArray) {i : ℕ} (hi : i < a.size) :
    (a ++ b)[i]! = a[i]! := by
  have h : i < (a ++ b).size := by rw [ByteArray.size_append]; omega
  rw [getElem!_pos (a ++ b) i h, getElem!_pos a i hi]
  exact ByteArray.getElem_append_left hi

theorem getElem!_append_right (a b : ByteArray) {i : ℕ} (hi : a.size ≤ i)
    (hi' : i < a.size + b.size) : (a ++ b)[i]! = b[i - a.size]! := by
  have h : i < (a ++ b).size := by rw [ByteArray.size_append]; exact hi'
  rw [getElem!_pos (a ++ b) i h, getElem!_pos b (i - a.size) (by omega)]
  exact ByteArray.getElem_append_right hi

theorem u32Entry_append_left (a b : ByteArray) {x : ℕ} (hx : 4 * x + 4 ≤ a.size) :
    u32Entry (a ++ b) x = u32Entry a x := by
  rw [u32Entry_eq, u32Entry_eq, getElem!_append_left _ _ (by omega),
    getElem!_append_left _ _ (by omega), getElem!_append_left _ _ (by omega),
    getElem!_append_left _ _ (by omega)]

theorem u32Entry_append_right (a b : ByteArray) {x lo : ℕ} (ha : a.size = 4 * lo)
    (hlo : lo ≤ x) (hx : 4 * (x - lo) + 4 ≤ b.size) :
    u32Entry (a ++ b) x = u32Entry b (x - lo) := by
  rw [u32Entry_eq, u32Entry_eq, getElem!_append_right _ _ (by omega) (by omega),
    getElem!_append_right _ _ (by omega) (by omega),
    getElem!_append_right _ _ (by omega) (by omega),
    getElem!_append_right _ _ (by omega) (by omega)]
  have e0 : 4 * x - a.size = 4 * (x - lo) := by omega
  have e1 : 4 * x + 1 - a.size = 4 * (x - lo) + 1 := by omega
  have e2 : 4 * x + 2 - a.size = 4 * (x - lo) + 2 := by omega
  have e3 : 4 * x + 3 - a.size = 4 * (x - lo) + 3 := by omega
  rw [e0, e1, e2, e3]

theorem u32fill_spec (f : ℕ → ℕ) : ∀ (k x : ℕ) (b : ByteArray) (c : ℕ), b.size = 4 * c →
    (u32fill f k x b).size = 4 * (c + k) ∧ (∀ y < c, u32Entry (u32fill f k x b) y = u32Entry b y) ∧
      ∀ j < k, u32Entry (u32fill f k x b) (c + j) = f (x + j) % 2 ^ 32 := by
  intro k
  induction k with
  | zero =>
    intro x b c hb
    exact ⟨by simpa [u32fill] using hb, fun y _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro x b c hb
    have hb' : (push32 b (f x)).size = 4 * (c + 1) := by rw [size_push32, hb]; omega
    obtain ⟨hs, hold, hnew⟩ := ih (x + 1) (push32 b (f x)) (c + 1) hb'
    have e : u32fill f (k + 1) x b = u32fill f k (x + 1) (push32 b (f x)) := rfl
    rw [e]
    have hc : u32Entry (u32fill f k (x + 1) (push32 b (f x))) c = f x % 2 ^ 32 := by
      rw [hold c (by omega), u32Entry_push32_of_eq _ _ hb]
    refine ⟨by rw [hs]; omega, fun y hy => ?_, fun j hj => ?_⟩
    · rw [hold y (by omega), u32Entry_push32_of_lt _ _ (by omega)]
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simpa using hc
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        have := hnew j' (by omega)
        rw [show c + (j' + 1) = c + 1 + j' by omega, this]
        congr 2
        omega

theorem u32chunk_spec (f : ℕ → ℕ) (lo hi : ℕ) :
    (u32chunk f lo hi).size = 4 * (hi - lo) ∧
      ∀ i < hi - lo, u32Entry (u32chunk f lo hi) i = f (lo + i) % 2 ^ 32 := by
  have e : u32chunk f lo hi =
      u32fill f (hi - lo) lo (ByteArray.emptyWithCapacity (4 * (hi - lo))) := rfl
  obtain ⟨hs, -, hg⟩ := u32fill_spec f (hi - lo) lo (ByteArray.emptyWithCapacity (4 * (hi - lo)))
    0 rfl
  rw [e]
  exact ⟨by simpa using hs, fun i hi' => by simpa using hg i hi'⟩

theorem u32prefix_spec (N sz : ℕ) (ch : ℕ → ℕ → ByteArray) (F : ℕ → ℕ)
    (hch : ∀ lo hi, lo ≤ hi → (ch lo hi).size = 4 * (hi - lo) ∧
      ∀ i < hi - lo, u32Entry (ch lo hi) i = F (lo + i)) (t : ℕ) :
    ((List.range t).foldl (fun acc s => acc ++ ch (min N (s * sz)) (min N ((s + 1) * sz)))
      (ByteArray.emptyWithCapacity (4 * N))).size = 4 * min N (t * sz) ∧
    ∀ x < min N (t * sz), u32Entry ((List.range t).foldl (fun acc s =>
      acc ++ ch (min N (s * sz)) (min N ((s + 1) * sz))) (ByteArray.emptyWithCapacity (4 * N))) x
        = F x := by
  induction t with
  | zero =>
    refine ⟨?_, fun x hx => absurd hx ?_⟩
    · simp only [List.range_zero, List.foldl_nil, zero_mul, zero_le, inf_of_le_right, mul_zero]
      rfl
    · simp only [zero_mul, zero_le, inf_of_le_right, not_lt_zero, not_false_eq_true]
  | succ t ih =>
    obtain ⟨hs, hg⟩ := ih
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hle : min N (t * sz) ≤ min N ((t + 1) * sz) := by
      have : t * sz ≤ (t + 1) * sz := Nat.mul_le_mul_right _ (Nat.le_succ t)
      omega
    obtain ⟨hcs, hcg⟩ := hch (min N (t * sz)) (min N ((t + 1) * sz)) hle
    refine ⟨by rw [ByteArray.size_append, hs, hcs]; omega, fun x hx => ?_⟩
    by_cases hxl : x < min N (t * sz)
    · rw [u32Entry_append_left _ _ (by omega), hg x hxl]
    · rw [u32Entry_append_right _ _ hs (by omega) (by omega), hcg _ (by omega)]
      congr 1
      omega

namespace BigOmega

theorem foldl_add_eq_sum (f : ℕ → ℕ) (a : Array ℕ) :
    a.foldl (fun s x => s + f x) 0 = ∑ k ∈ Finset.range a.size, f a[k]! := by
  rw [← Array.foldl_toList]
  have key : ∀ (l : List ℕ) (c : ℕ), l.foldl (fun s x => s + f x) c =
      c + ∑ k ∈ Finset.range l.length, f (l.getD k 0) := by
    intro l
    induction l with
    | nil =>
      intro c
      simp only [List.foldl_nil, List.length_nil, Finset.range_zero, Finset.sum_empty, add_zero]
    | cons x l ih =>
      intro c
      rw [List.foldl_cons, ih, List.length_cons, Finset.sum_range_succ' _ l.length]
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      omega
  rw [key, Nat.zero_add, Array.length_toList]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [getElem!_pos a k (Finset.mem_range.1 hk), List.getD_eq_getElem?_getD,
    Array.getElem?_toList, Array.getElem?_eq_getElem (Finset.mem_range.1 hk)]
  rfl

theorem getElem!_map_lt {α β : Type} [Inhabited α] [Inhabited β] {a : Array α} {f : α → β}
    {k : ℕ} (hk : k < a.size) : (a.map f)[k]! = f a[k]! := by
  rw [getElem!_pos (a.map f) k (by simpa using hk), Array.getElem_map, getElem!_pos a k hk]

theorem getElem!_range_lt {n i : ℕ} (hi : i < n) : (Array.range n)[i]! = i := by
  rw [getElem!_pos (Array.range n) i (by simpa using hi)]
  exact Array.getElem_range _

theorem rowVia_eq {O : BigOmega} (hv : ∀ q < O.N, q ≠ 0 → O.parAt q < q) {P : Array (Array ℕ)}
    {ps pos : Array ℕ} {i q : ℕ} (hP : ∀ j < ps.size, P[j]! = O.row ps[j]!) :
    O.rowVia P ps pos i q = O.row q := by
  unfold rowVia
  split_ifs with hc
  · obtain ⟨hq, hq0, hpos, hps⟩ := hc
    rw [hP _ hpos, hps]
    exact (row_succ O hv hq hq0).symm
  · rfl

theorem rowsFor_spec {O : BigOmega} (hv : ∀ q < O.N, q ≠ 0 → O.parAt q < q) :
    ∀ (f : ℕ) (qs : Array ℕ) (i : ℕ), i < qs.size → (O.rowsFor f qs)[i]! = O.row qs[i]! := by
  intro f
  induction f with
  | zero =>
    intro qs i hi
    show (qs.map O.row)[i]! = _
    rw [getElem!_map_lt hi]
  | succ f ih =>
    intro qs i hi
    unfold rowsFor
    split_ifs with hsmall
    · rw [getElem!_map_lt hi]
    · dsimp only
      generalize hrp : runs (qs.map O.parAt) = rp
      rw [getElem!_map_lt (by simpa using hi), getElem!_range_lt hi]
      exact rowVia_eq hv (ih rp.1)

theorem hashVia_eq {O : BigOmega} (F : TreeFacts O) {σ : ByteArray} {P : Array (Array ℕ)}
    {ps pos : Array ℕ} {i p : ℕ} (hP : ∀ j < ps.size, P[j]! = O.row ps[j]!) (hp : p < O.N)
    (hp0 : p ≠ 0) (hpos : pos[i]! < ps.size) (hps : ps[pos[i]!]! = O.parAt p) :
    O.hashVia (O.actTabs σ) P pos i p = O.imgHash σ p := by
  have hv : ∀ q < O.N, q ≠ 0 → O.parAt q < q := fun q hq hq0 => (F.tree q hq hq0).1
  obtain ⟨hpar, hlab⟩ := F.tree p hp hp0
  have hrow : P[pos[i]!]! = O.row (O.parAt p) := by rw [hP _ hpos, hps]
  unfold hashVia
  dsimp only
  rw [hrow, foldl_add_eq_sum]
  show _ = sumMod O.m (fun k => O.R[bget σ (O.row p)[k]!]!)
  rw [sumMod_eq_sum_range, size_row, ← F.m_eq]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < O.X0.size := F.m_eq ▸ Finset.mem_range.1 hk
  rw [row_entry O hv hp hp0 hk']
  have hxlt : (O.row (O.parAt p))[k]! < O.n :=
    row_lt_n F _ (lt_trans hpar hp) k (F.m_eq ▸ hk')
  unfold actTabs
  rw [getElem!_map_lt hlab, getElem!_map_lt (by simpa using hxlt), getElem!_range_lt hxlt]

theorem actVia_eq {O : BigOmega} {σ : ByteArray} {ps pos : Array ℕ} {i p h : ℕ}
    (hh : (p < O.N ∧ p ≠ 0 ∧ pos[i]! < ps.size ∧ ps[pos[i]!]! = O.parAt p) →
      h = O.imgHash σ p) : O.actVia σ ps pos i p h = O.act σ p := by
  unfold actVia
  split_ifs with hc
  · rw [hh hc]
    rfl
  · rfl

theorem actChunk_spec {O : BigOmega} (F : TreeFacts O) (σ : ByteArray) (a b : ℕ) :
    (O.actChunk (O.actTabs σ) σ a b).size = 4 * (b - a) ∧
      ∀ i < b - a, u32Entry (O.actChunk (O.actTabs σ) σ a b) i = O.act σ (a + i) % 2 ^ 32 := by
  have hv : ∀ q < O.N, q ≠ 0 → O.parAt q < q := fun q hq hq0 => (F.tree q hq hq0).1
  unfold actChunk
  dsimp only
  generalize hrp : runs ((Array.range (b - a)).map fun i => O.parAt (a + i)) = rp
  generalize hord : O.byLabel a (b - a) = ord
  have hP : ∀ j < rp.1.size, (O.rowsFor 64 rp.1)[j]! = O.row rp.1[j]! := rowsFor_spec hv 64 rp.1
  obtain ⟨hs, hg⟩ := u32chunk_spec (fun p => O.actVia σ rp.1 rp.2 (p - a) p
    (if ord.2[p - a]! < ord.1.size ∧ ord.1[ord.2[p - a]!]! = p - a then
      (ord.1.map fun i =>
        O.hashVia (O.actTabs σ) (O.rowsFor 64 rp.1) rp.2 i (a + i))[ord.2[p - a]!]!
     else O.hashVia (O.actTabs σ) (O.rowsFor 64 rp.1) rp.2 (p - a) p)) a b
  refine ⟨hs, fun i hi => ?_⟩
  rw [hg i hi]
  congr 1
  refine actVia_eq fun ⟨hp, hp0, hpos, hps⟩ => ?_
  have hsub : a + i - a = i := by omega
  rw [hsub]
  rw [hsub] at hpos hps
  have hh := hashVia_eq (σ := σ) F hP hp hp0 hpos hps
  rw [← hh]
  split_ifs with hc
  · obtain ⟨hj, hji⟩ := hc
    rw [getElem!_map_lt hj, hji]
  · rfl

theorem actAll_spec_mod {O : BigOmega} (F : TreeFacts O) (σ : ByteArray) {chunk : ℕ}
    (hc : 0 < chunk) {p : ℕ} (hp : p < O.N) :
    u32Entry (O.actAll σ chunk) p = O.act σ p % 2 ^ 32 := by
  have e : O.actAll σ chunk = (List.range (O.N / chunk + 1)).foldl (fun acc t =>
      acc ++ O.actChunk (O.actTabs σ) σ (min O.N (t * chunk)) (min O.N ((t + 1) * chunk)))
      (ByteArray.emptyWithCapacity (4 * O.N)) := by
    unfold actAll
    simp only [List.foldl_map]
    rfl
  rw [e]
  have hN : O.N ≤ (O.N / chunk + 1) * chunk := by
    have h1 := Nat.div_add_mod O.N chunk
    have h2 := Nat.mod_lt O.N hc
    rw [Nat.mul_comm] at h1
    rw [Nat.add_mul, Nat.one_mul]
    omega
  exact (u32prefix_spec O.N chunk (fun lo hi => O.actChunk (O.actTabs σ) σ lo hi)
    (fun x => O.act σ x % 2 ^ 32) (fun lo hi _ => by
      obtain ⟨hs, hg⟩ := actChunk_spec F σ lo hi
      exact ⟨hs, fun i hi' => hg i hi'⟩) (O.N / chunk + 1)).2 p
    (by rw [Nat.min_eq_left hN]; exact hp)

theorem tabGo_lt (tab : ByteArray) (key : UInt64) (mask : USize) :
    ∀ fuel s, tabGo tab key mask fuel s < 2 ^ 32 := by
  intro fuel
  induction fuel with
  | zero =>
    intro s
    show 0 < 2 ^ 32
    norm_num
  | succ f ih =>
    intro s
    unfold tabGo
    dsimp only
    split_ifs
    · norm_num
    · have := UInt32.toNat_lt_size (tabU32 tab (12 * s + 8))
      simpa [UInt32.size] using this
    · exact ih _

theorem find_lt {O : BigOmega} (hN : O.N < 4294967296) (h : ℕ) : O.find h < 2 ^ 32 := by
  unfold find
  dsimp only
  split_ifs
  · omega
  · have : tabGet O.tab O.bits h < 2 ^ 32 := tabGo_lt _ _ _ _ _
    omega

structure BigFacts (O : BigOmega) (letters : Array ByteArray) (fix : List ℕ) : Prop
    extends TreeFacts O where
  N_lt : O.N < 4294967296
  n_le : O.n ≤ 65536
  X0_inj : ∀ a < O.X0.size, ∀ b < O.X0.size, O.X0[a]! = O.X0[b]! → a = b
  fix_lt : ∀ l ∈ fix, l < letters.size
  fix_maps : ∀ l ∈ fix, ∀ a < O.X0.size,
    O.X0.contains (bget letters[l]! O.X0[a]!) = true
  find_spec : ∀ p < O.N, O.find (O.rowHash p) = p

theorem bigFacts {O : BigOmega} {letters : Array ByteArray} {fix : List ℕ}
    (h : bigOK O letters fix = true) : BigFacts O letters fix := by
  unfold bigOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, -⟩, h3⟩, h4⟩, -⟩, -⟩, -⟩, -⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  have T : TreeFacts O := by
    refine ⟨beq_iff_eq.1 h1, ?_, ?_, ?_⟩
    · intro a ha
      have := allLt_spec h10 ha
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1
    · intro l hl x hx
      have := Array.all_eq_true.1 h9 l hl
      simp only [Bool.and_eq_true] at this
      have h2 := allLt_spec this.2 hx
      simp only [decide_eq_true_eq] at h2
      rw [getElem!_pos O.tg l hl]
      exact h2
    · intro p hp hp0
      have := allLt_spec h12 hp
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at this
      rcases this with h0 | ⟨hpar, hlab⟩
      · exact absurd h0 hp0
      · exact ⟨hpar, hlab⟩
  refine ⟨T, of_decide_eq_true h3, of_decide_eq_true h4, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    have := allLt_spec h10 ha
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    have h2' := allLt_spec this.2 hb
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h2'
    rcases h2' with h2' | h2'
    · exact h2'
    · exact absurd hab h2'
  · intro l hl
    have := List.all_eq_true.1 h11 l hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  · intro l hl a ha
    have := List.all_eq_true.1 h11 l hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact allLt_spec this.2 ha
  · intro p hp
    unfold findOK at h13
    dsimp only at h13
    have hscan : u32Entry (O.actAll (bid O.n)) p = p := beq_iff_eq.1 (allLt_spec h13 hp)
    rw [actAll_spec_mod T (bid O.n) (by norm_num) hp] at hscan
    have hid : ∀ x < O.n, bget (bid O.n) x = x := fun x hx =>
      bget_bofFn (n := O.n) (f := fun x => x) hx (by have := of_decide_eq_true h4; omega)
    have himg : O.imgHash (bid O.n) p = O.rowHash p := by
      show sumMod O.m (fun k => O.R[bget (bid O.n) (O.row p)[k]!]!) =
        sumMod O.m (fun k => O.R[(O.row p)[k]!]!)
      rw [sumMod_eq_sum_range, sumMod_eq_sum_range]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hid _ (row_lt_n T p hp k (Finset.mem_range.1 hk))]
    unfold act at hscan
    rw [himg, Nat.mod_eq_of_lt (find_lt (of_decide_eq_true h3) _)] at hscan
    exact hscan

theorem parAt_lt_of_bigOK {O : BigOmega} {letters : Array ByteArray} {fix : List ℕ}
    (h : bigOK O letters fix = true) {p : ℕ} (hp : p < O.N) (hp0 : p ≠ 0) : O.parAt p < p :=
  ((bigFacts h).tree p hp hp0).1

theorem row_succ_of_bigOK {O : BigOmega} {letters : Array ByteArray} {fix : List ℕ}
    (h : bigOK O letters fix = true) {p : ℕ} (hp : p < O.N) (hp0 : p ≠ 0) :
    O.row p = (O.row (O.parAt p)).map fun x => bget (O.tg[O.labAt p]!) x :=
  row_succ O (fun _ hq hq0 => parAt_lt_of_bigOK h hq hq0) hp hp0

theorem fix_lt_of_bigOK {O : BigOmega} {letters : Array ByteArray} {fix : List ℕ}
    (h : bigOK O letters fix = true) {l : ℕ} (hl : l ∈ fix) : l < letters.size :=
  (bigFacts h).fix_lt l hl

theorem rowFinset_zero {n : ℕ} {O : BigOmega} {letters : Array ByteArray} {fix : List ℕ}
    (h : bigOK O letters fix = true) : rowFinset n O 0 = listFinset n O.X0 := by
  have F := bigFacts h
  ext x
  rw [mem_rowFinset, mem_listFinset]
  constructor
  · rintro ⟨k, hk, hkx⟩
    exact ⟨k, F.m_eq ▸ hk, by rw [← row_zero_entry]; exact hkx⟩
  · rintro ⟨k, hk, hkx⟩
    exact ⟨k, F.m_eq ▸ hk, by rw [row_zero_entry]; exact hkx⟩

theorem act_tree {O : BigOmega} {letters : Array ByteArray} {fix : List ℕ}
    (h : bigOK O letters fix = true) {p : ℕ} (hp : p < O.N) (hp0 : p ≠ 0) :
    O.act (O.tg[O.labAt p]!) (O.parAt p) = p := by
  have F := bigFacts h
  have hv : ∀ q < O.N, q ≠ 0 → O.parAt q < q := fun q hq hq0 => (F.tree q hq hq0).1
  have himg : O.imgHash (O.tg[O.labAt p]!) (O.parAt p) = O.rowHash p := by
    show sumMod O.m (fun k => O.R[bget (O.tg[O.labAt p]!) (O.row (O.parAt p))[k]!]!) =
      sumMod O.m (fun k => O.R[(O.row p)[k]!]!)
    rw [sumMod_eq_sum_range, sumMod_eq_sum_range]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [row_entry O hv hp hp0 (F.m_eq ▸ Finset.mem_range.1 hk)]
  unfold act
  rw [himg]
  exact F.find_spec p hp

section Rows

variable {n : ℕ} {O : BigOmega} {letters : Array ByteArray} {fix : List ℕ}
  (Γ : Subgroup (Equiv.Perm (Fin n))) (g : ℕ → Equiv.Perm (Fin n))
  (hg : ∀ l < O.tg.size, g l ∈ Γ ∧ RepB n O.tg[l]! (g l))
  (h : bigOK O letters fix = true) (hn : O.n = n)

include hg h hn

omit hn in
theorem rowFinset_succ_of_lt {p : ℕ} (hp : p < O.N) (hp0 : p ≠ 0)
    (hp_lt : ∀ k < O.m, (O.row (O.parAt p))[k]! < n) :
    rowFinset n O p = (⟨g (O.labAt p), (hg _ ((bigFacts h).tree p hp hp0).2).1⟩ : Γ) •
      rowFinset n O (O.parAt p) := by
  have F := bigFacts h
  have hv : ∀ q < O.N, q ≠ 0 → O.parAt q < q := fun q hq hq0 => (F.tree q hq hq0).1
  obtain ⟨hgl, hrep⟩ := hg (O.labAt p) (F.tree p hp hp0).2
  have hent : ∀ (k : ℕ) (hk : k < O.m), (O.row p)[k]! =
      (((g (O.labAt p)) ⟨(O.row (O.parAt p))[k]!, hp_lt k hk⟩ : Fin n) : ℕ) := by
    intro k hk
    rw [row_entry O hv hp hp0 (F.m_eq ▸ hk)]
    exact hrep.apply (hp_lt k hk)
  have hsm : ∀ c : Fin n, ((⟨g (O.labAt p), hgl⟩ : Γ) • c) = (g (O.labAt p)) c := fun c => rfl
  ext x
  rw [Finset.mem_smul_finset, mem_rowFinset]
  constructor
  · rintro ⟨k, hk, hkx⟩
    refine ⟨⟨(O.row (O.parAt p))[k]!, hp_lt k hk⟩, mem_rowFinset.2 ⟨k, hk, rfl⟩, ?_⟩
    apply Fin.ext
    rw [hsm]
    exact (hent k hk).symm.trans hkx
  · rintro ⟨c, hc, hcx⟩
    obtain ⟨k, hk, hkc⟩ := mem_rowFinset.1 hc
    refine ⟨k, hk, ?_⟩
    rw [hent k hk]
    have hc' : (⟨(O.row (O.parAt p))[k]!, hp_lt k hk⟩ : Fin n) = c := Fin.ext hkc
    rw [hc', ← hsm c, hcx]

theorem row_good : ∀ p < O.N, (∀ k < O.m, (O.row p)[k]! < n) ∧
    (∀ k₁ < O.m, ∀ k₂ < O.m, (O.row p)[k₁]! = (O.row p)[k₂]! → k₁ = k₂) ∧
    rowFinset n O p ∈ MulAction.orbit Γ (listFinset n O.X0) := by
  have F := bigFacts h
  have hv : ∀ q < O.N, q ≠ 0 → O.parAt q < q := fun q hq hq0 => (F.tree q hq hq0).1
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp
    by_cases hp0 : p = 0
    · subst hp0
      refine ⟨?_, ?_, ?_⟩
      · intro k hk
        rw [row_zero_entry]
        have := F.X0_lt k (F.m_eq ▸ hk)
        omega
      · intro k₁ hk₁ k₂ hk₂ he
        rw [row_zero_entry, row_zero_entry] at he
        exact F.X0_inj k₁ (F.m_eq ▸ hk₁) k₂ (F.m_eq ▸ hk₂) he
      · rw [rowFinset_zero h]
        exact MulAction.mem_orbit_self _
    · obtain ⟨hpar, hlab⟩ := F.tree p hp hp0
      obtain ⟨hp_lt, hp_inj, hp_orb⟩ := ih (O.parAt p) hpar (lt_trans hpar hp)
      obtain ⟨hgl, hrep⟩ := hg (O.labAt p) hlab
      have hent : ∀ (k : ℕ) (hk : k < O.m), (O.row p)[k]! =
          (((g (O.labAt p)) ⟨(O.row (O.parAt p))[k]!, hp_lt k hk⟩ : Fin n) : ℕ) := by
        intro k hk
        rw [row_entry O hv hp hp0 (F.m_eq ▸ hk)]
        exact hrep.apply (hp_lt k hk)
      have hrowEq := rowFinset_succ_of_lt Γ g hg h hp hp0 hp_lt
      refine ⟨fun k hk => ?_, fun k₁ hk₁ k₂ hk₂ he => ?_, ?_⟩
      · rw [hent k hk]
        exact Fin.is_lt _
      · rw [hent k₁ hk₁, hent k₂ hk₂] at he
        have h1 := (g (O.labAt p)).injective (Fin.ext he)
        exact hp_inj k₁ hk₁ k₂ hk₂ (congrArg Fin.val h1)
      · obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.1 hp_orb
        refine ⟨⟨g (O.labAt p), hgl⟩ * a, ?_⟩
        show ((⟨g (O.labAt p), hgl⟩ * a : Γ)) • listFinset n O.X0 = rowFinset n O p
        rw [mul_smul, ha, hrowEq]

theorem rowFinset_mem_orbit :
    ∀ p < O.N, rowFinset n O p ∈ MulAction.orbit Γ (listFinset n O.X0) :=
  fun p hp => (row_good Γ g hg h hn p hp).2.2

theorem rowFinset_succ {p : ℕ} (hp : p < O.N) (hp0 : p ≠ 0) :
    rowFinset n O p = (⟨g (O.labAt p), (hg _ ((bigFacts h).tree p hp hp0).2).1⟩ : Γ) •
      rowFinset n O (O.parAt p) :=
  rowFinset_succ_of_lt Γ g hg h hp hp0
    (row_good Γ g hg h hn _ (lt_trans ((bigFacts h).tree p hp hp0).1 hp)).1

theorem rowFinset_injOn :
    ∀ p < O.N, ∀ q < O.N, rowFinset n O p = rowFinset n O q → p = q := by
  intro p hp q hq hpq
  have F := bigFacts h
  obtain ⟨hp1, hp2, -⟩ := row_good Γ g hg h hn p hp
  obtain ⟨hq1, hq2, -⟩ := row_good Γ g hg h hn q hq
  have e1 : O.rowHash p = O.rowHash q := by
    rw [rowHash_eq_sum hp1 hp2, rowHash_eq_sum hq1 hq2, hpq]
  have h1 := F.find_spec p hp
  rw [e1, F.find_spec q hq] at h1
  exact h1.symm

theorem rows_card : ((Finset.range O.N).image (rowFinset n O)).card = O.N := by
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  exact rowFinset_injOn Γ g hg h hn a (Finset.mem_range.1 ha) b (Finset.mem_range.1 hb) hab

theorem rows_subset_orbit :
    (↑((Finset.range O.N).image (rowFinset n O)) : Set (Finset (Fin n))) ⊆
      MulAction.orbit Γ (listFinset n O.X0) := by
  intro s hs
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hs)
  exact rowFinset_mem_orbit Γ g hg h hn j (Finset.mem_range.1 hj)

theorem card_orbit_ge : O.N ≤ (MulAction.orbit Γ (listFinset n O.X0)).ncard := by
  have h1 := Set.ncard_le_ncard (rows_subset_orbit Γ g hg h hn) (Set.toFinite _)
  rwa [Set.ncard_coe_finset, rows_card Γ g hg h hn] at h1

theorem act_spec (hcard : (MulAction.orbit Γ (listFinset n O.X0)).ncard ≤ O.N)
    {σ : ByteArray} {e : Γ} (hσ : RepB n σ (e : Equiv.Perm (Fin n))) {p : ℕ} (hp : p < O.N) :
    O.act σ p < O.N ∧ rowFinset n O (O.act σ p) = e • rowFinset n O p := by
  have F := bigFacts h
  have hT : (↑((Finset.range O.N).image (rowFinset n O)) : Set (Finset (Fin n))) =
      MulAction.orbit Γ (listFinset n O.X0) :=
    Set.eq_of_subset_of_ncard_le (rows_subset_orbit Γ g hg h hn)
      (by rw [Set.ncard_coe_finset, rows_card Γ g hg h hn]; exact hcard) (Set.toFinite _)
  obtain ⟨hp1, hp2, hporb⟩ := row_good Γ g hg h hn p hp
  have hmem : e • rowFinset n O p ∈ MulAction.orbit Γ (listFinset n O.X0) := by
    obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.1 hporb
    exact MulAction.mem_orbit_iff.2 ⟨e * a, by rw [mul_smul, ha]⟩
  rw [← hT] at hmem
  obtain ⟨j, hj, hjrow⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hmem)
  have hjN : j < O.N := Finset.mem_range.1 hj
  obtain ⟨hj1, hj2, -⟩ := row_good Γ g hg h hn j hjN
  have hσk : ∀ (k : ℕ) (hk : k < O.m), bget σ (O.row p)[k]! =
      ((((e : Equiv.Perm (Fin n)) ⟨(O.row p)[k]!, hp1 k hk⟩ : Fin n)) : ℕ) :=
    fun k hk => hσ.apply (hp1 k hk)
  have hlt : ∀ k < O.m, bget σ (O.row p)[k]! < n := fun k hk => by
    rw [hσk k hk]
    exact Fin.is_lt _
  have hinj : ∀ k₁ < O.m, ∀ k₂ < O.m,
      bget σ (O.row p)[k₁]! = bget σ (O.row p)[k₂]! → k₁ = k₂ := by
    intro k₁ hk₁ k₂ hk₂ he
    rw [hσk k₁ hk₁, hσk k₂ hk₂] at he
    exact hp2 k₁ hk₁ k₂ hk₂ (congrArg Fin.val ((e : Equiv.Perm (Fin n)).injective (Fin.ext he)))
  have himg : O.imgHash σ p = O.rowHash j := by
    rw [imgHash_eq_sum hlt hinj, imgFinset_eq_smul hσ hp1, ← hjrow, rowHash_eq_sum hj1 hj2]
  have hact : O.act σ p = j := by
    unfold act
    rw [himg]
    exact F.find_spec j hjN
  exact ⟨by rw [hact]; exact hjN, by rw [hact, hjrow]⟩

end Rows

theorem fix_smul_listFinset {n : ℕ} {O : BigOmega} {letters : Array ByteArray} {fix : List ℕ}
    (Γ : Subgroup (Equiv.Perm (Fin n))) (u : ℕ → Equiv.Perm (Fin n))
    (hu : ∀ l < letters.size, u l ∈ Γ ∧ RepB n letters[l]! (u l))
    (h : bigOK O letters fix = true) :
    ∀ (l : ℕ) (hl : l ∈ fix), (⟨u l, (hu l (fix_lt_of_bigOK h hl)).1⟩ : Γ) •
      listFinset n O.X0 = listFinset n O.X0 := by
  intro l hl
  have F := bigFacts h
  have hgl := hu l (F.fix_lt l hl)
  have hsub : (⟨u l, hgl.1⟩ : Γ) • listFinset n O.X0 ⊆ listFinset n O.X0 := by
    intro y hy
    obtain ⟨c, hc, rfl⟩ := Finset.mem_smul_finset.1 hy
    obtain ⟨k, hk, hkc⟩ := mem_listFinset.1 hc
    have hcont := F.fix_maps l hl k hk
    have h1 : bget letters[l]! O.X0[k]! = (((u l) c : Fin n) : ℕ) := by
      rw [hkc]
      exact hgl.2.2 c
    rw [h1] at hcont
    obtain ⟨k', hk', hk'eq⟩ := exists_index_of_contains hcont
    exact mem_listFinset.2 ⟨k', hk', hk'eq⟩
  exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_smul_finset])


theorem u32Entry_actAll {O : BigOmega} {letters : Array ByteArray} {fix : List ℕ}
    (h : bigOK O letters fix = true) (σ : ByteArray) {chunk : ℕ} (hc : 0 < chunk) {p : ℕ}
    (hp : p < O.N) : u32Entry (O.actAll σ chunk) p = O.act σ p := by
  rw [actAll_spec_mod (bigFacts h).toTreeFacts σ hc hp]
  exact Nat.mod_eq_of_lt (find_lt (bigFacts h).N_lt _)

section ActAll

variable {n : ℕ} {O : BigOmega} {letters : Array ByteArray} {fix : List ℕ}
  (Γ : Subgroup (Equiv.Perm (Fin n))) (g : ℕ → Equiv.Perm (Fin n))
  (hg : ∀ l < O.tg.size, g l ∈ Γ ∧ RepB n O.tg[l]! (g l))
  (h : bigOK O letters fix = true) (hn : O.n = n)

include hg h hn

theorem actAll_spec (hcard : (MulAction.orbit Γ (listFinset n O.X0)).ncard ≤ O.N)
    {σ : ByteArray} {e : Γ} (hσ : RepB n σ (e : Equiv.Perm (Fin n))) {chunk : ℕ} (hc : 0 < chunk)
    {p : ℕ} (hp : p < O.N) :
    u32Entry (O.actAll σ chunk) p = O.act σ p ∧ u32Entry (O.actAll σ chunk) p < O.N ∧
      rowFinset n O (u32Entry (O.actAll σ chunk) p) = e • rowFinset n O p := by
  obtain ⟨h1, h2⟩ := act_spec Γ g hg h hn hcard hσ hp
  rw [u32Entry_actAll h σ hc hp]
  exact ⟨rfl, h1, h2⟩

end ActAll

end BigOmega

end CFSG.YGroups.DCE
