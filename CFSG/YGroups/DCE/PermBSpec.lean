module

public import Certificates.Data.CFSGNative.YGroups.DCE.PermB
public import CFSG.Monster.B.Co2.PermArr

public section

namespace CFSG.YGroups.DCE

open CFSG.Monster.B.Co2

@[expose] def RepB (n : ℕ) (b : ByteArray) (g : Equiv.Perm (Fin n)) : Prop :=
  b.size = 2 * n ∧ ∀ x : Fin n, bget b x = (g x : ℕ)

theorem get!_eq_getElem! (b : ByteArray) (i : ℕ) : b.get! i = b[i]! := by
  by_cases h : i < b.size
  · rw [getElem!_pos b i h]
    cases b
    show _[i]! = _
    rw [getElem!_pos _ i h]
    rfl
  · rw [getElem!_neg b i h]
    cases b
    show _[i]! = _
    rw [getElem!_neg _ i h]

theorem bget_eq (b : ByteArray) (x : ℕ) :
    bget b x = b[2 * x]!.toNat + 256 * b[2 * x + 1]!.toNat := by
  rw [bget, get!_eq_getElem!, get!_eq_getElem!]

theorem bget_push_push_of_lt (b : ByteArray) (lo hi : UInt8) {x : ℕ} (hx : 2 * x + 2 ≤ b.size) :
    bget ((b.push lo).push hi) x = bget b x := by
  rw [bget_eq, bget_eq,
    ByteArray.getElem!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
    ByteArray.getElem!_push_lt _ _ _ (by omega),
    ByteArray.getElem!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
    ByteArray.getElem!_push_lt _ _ _ (by omega)]

theorem bget_push_push_of_eq (b : ByteArray) (lo hi : UInt8) {x : ℕ} (hx : b.size = 2 * x) :
    bget ((b.push lo).push hi) x = lo.toNat + 256 * hi.toNat := by
  have h1 : ((b.push lo).push hi)[2 * x]! = lo := by
    rw [ByteArray.getElem!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega), ← hx]
    exact ByteArray.getElem!_push_eq b lo
  have h2 : ((b.push lo).push hi)[2 * x + 1]! = hi := by
    have := ByteArray.getElem!_push_eq (b.push lo) hi
    rwa [ByteArray.size_push, hx] at this
  rw [bget_eq, h1, h2]

theorem bofFn_eq_foldl (n : ℕ) (f : ℕ → ℕ) :
    bofFn n f = (List.range n).foldl
      (fun b x => (b.push (UInt8.ofNat (f x % 256))).push (UInt8.ofNat (f x / 256 % 256)))
      ByteArray.empty := by
  unfold bofFn
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
  rfl

theorem bofFn_succ (n : ℕ) (f : ℕ → ℕ) :
    bofFn (n + 1) f = ((bofFn n f).push (UInt8.ofNat (f n % 256))).push
      (UInt8.ofNat (f n / 256 % 256)) := by
  rw [bofFn_eq_foldl, bofFn_eq_foldl, List.range_succ, List.foldl_append]
  rfl

theorem bofFn_spec (n : ℕ) (f : ℕ → ℕ) :
    (bofFn n f).size = 2 * n ∧ ∀ x < n, bget (bofFn n f) x = f x % 65536 := by
  induction n with
  | zero =>
    refine ⟨?_, fun x hx => absurd hx (Nat.not_lt_zero _)⟩
    rw [bofFn_eq_foldl]
    rfl
  | succ n ih =>
    obtain ⟨hs, hg⟩ := ih
    rw [bofFn_succ]
    refine ⟨by simp only [ByteArray.size_push, hs]; omega, fun x hx => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hlt | rfl
    · rw [bget_push_push_of_lt _ _ _ (by omega), hg x hlt]
    · rw [bget_push_push_of_eq _ _ _ hs]
      simp only [UInt8.toNat_ofNat']
      omega

theorem size_bofFn (n : ℕ) (f : ℕ → ℕ) : (bofFn n f).size = 2 * n :=
  (bofFn_spec n f).1

theorem bget_bofFn_mod {n : ℕ} {f : ℕ → ℕ} {x : ℕ} (hx : x < n) :
    bget (bofFn n f) x = f x % 65536 :=
  (bofFn_spec n f).2 x hx

theorem bget_bofFn {n : ℕ} {f : ℕ → ℕ} {x : ℕ} (hx : x < n) (hf : f x < 65536) :
    bget (bofFn n f) x = f x := by
  rw [bget_bofFn_mod hx, Nat.mod_eq_of_lt hf]

theorem binvCand_eq_foldl (n : ℕ) (t : ByteArray) :
    binvCand n t = (List.range n).foldl
      (fun r x => (r.set! (2 * bget t x) (UInt8.ofNat (x % 256))).set! (2 * bget t x + 1)
        (UInt8.ofNat (x / 256 % 256)))
      (ByteArray.mk (Array.replicate (2 * n) 0)) := by
  unfold binvCand
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
  rfl

theorem size_binvCand (n : ℕ) (t : ByteArray) : (binvCand n t).size = 2 * n := by
  have key : ∀ (l : List ℕ) (r : ByteArray),
      (l.foldl (fun r x => (r.set! (2 * bget t x) (UInt8.ofNat (x % 256))).set!
        (2 * bget t x + 1) (UInt8.ofNat (x / 256 % 256))) r).size = r.size := by
    intro l
    induction l with
    | nil => intro r; rfl
    | cons a l ih => intro r; rw [List.foldl_cons, ih, ByteArray.size_set!, ByteArray.size_set!]
  rw [binvCand_eq_foldl, key]
  exact Array.size_replicate ..

theorem RepB.size_eq {n : ℕ} {b : ByteArray} {g : Equiv.Perm (Fin n)} (hb : RepB n b g) :
    b.size = 2 * n :=
  hb.1

theorem RepB.apply {n : ℕ} {b : ByteArray} {g : Equiv.Perm (Fin n)} (hb : RepB n b g) {x : ℕ}
    (hx : x < n) : bget b x = (g ⟨x, hx⟩ : ℕ) :=
  hb.2 ⟨x, hx⟩

theorem RepB.lt {n : ℕ} {b : ByteArray} {g : Equiv.Perm (Fin n)} (hb : RepB n b g) {x : ℕ}
    (hx : x < n) : bget b x < n := by
  rw [hb.apply hx]
  exact (g _).2

theorem RepB.unique {n : ℕ} {b : ByteArray} {g h : Equiv.Perm (Fin n)} (hg : RepB n b g)
    (hh : RepB n b h) : g = h :=
  Equiv.ext fun x => Fin.ext ((hg.2 x).symm.trans (hh.2 x))

theorem repB_bcomp {n : ℕ} {t u : ByteArray} {g h : Equiv.Perm (Fin n)} (hn : n ≤ 65536)
    (ht : RepB n t g) (hu : RepB n u h) : RepB n (bcomp n t u) (g * h) := by
  refine ⟨size_bofFn n _, fun x => ?_⟩
  rw [bcomp, bget_bofFn x.2 (by rw [hu.2 x, ht.2 (h x)]; exact lt_of_lt_of_le (g _).2 hn),
    hu.2 x, ht.2 (h x)]
  rfl

theorem repB_bid {n : ℕ} (hn : n ≤ 65536) : RepB n (bid n) 1 := by
  refine ⟨size_bofFn n _, fun x => ?_⟩
  rw [bid, bget_bofFn x.2 (lt_of_lt_of_le x.2 hn)]
  rfl

theorem repB_bofArr {n : ℕ} {a : Array ℕ} {g : Equiv.Perm (Fin n)} (hn : n ≤ 65536)
    (ha : Rep n a g) : RepB n (bofArr n a) g := by
  refine ⟨size_bofFn n _, fun x => ?_⟩
  rw [bofArr, bget_bofFn x.2 (by rw [ha x]; exact lt_of_lt_of_le (g x).2 hn), ha x]

theorem repB_inv_of_bisInv {n : ℕ} {t r : ByteArray} {g : Equiv.Perm (Fin n)} (ht : RepB n t g)
    (hr : r.size = 2 * n) (h : bisInv n t r = true) : RepB n r g⁻¹ := by
  refine ⟨hr, fun x => ?_⟩
  set y := g⁻¹ x with hy
  have hgy : g y = x := by simp [y]
  have hspec := allLt_iff.1 h y y.2
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hspec
  rw [ht.2 y, hgy] at hspec
  exact hspec.2

theorem repB_binv {n : ℕ} {t : ByteArray} {g : Equiv.Perm (Fin n)} (ht : RepB n t g)
    (h : bisInv n t (binvCand n t) = true) : RepB n (binvCand n t) g⁻¹ :=
  repB_inv_of_bisInv ht (size_binvCand n t) h

theorem bEq_iff {n : ℕ} {t u : ByteArray} {g h : Equiv.Perm (Fin n)} (ht : RepB n t g)
    (hu : RepB n u h) : bEq n t u = true ↔ g = h := by
  rw [bEq, allLt_iff]
  constructor
  · intro H
    refine Equiv.ext fun x => Fin.ext ?_
    have := H x x.2
    rwa [beq_iff_eq, ht.2 x, hu.2 x] at this
  · rintro rfl i hi
    rw [beq_iff_eq, ht.apply hi, hu.apply hi]

end CFSG.YGroups.DCE
