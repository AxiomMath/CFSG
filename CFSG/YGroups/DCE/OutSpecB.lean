module

public import Certificates.Data.CFSGNative.YGroups.DCE.EngineB
public import CFSG.YGroups.DCE.PermBSpec
public import CFSG.YGroups.DoubleCosetPoints
public import Batteries.Data.ByteArray
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.YGroups.DCE.B

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.YGroups.DCE

private def u32push (b : ByteArray) (v : ℕ) : ByteArray :=
  (((b.push (UInt8.ofNat (v % 256))).push (UInt8.ofNat ((v / 256) % 256))).push
    (UInt8.ofNat ((v / 65536) % 256))).push (UInt8.ofNat ((v / 16777216) % 256))

private theorem u32get_eq (b : ByteArray) (x : ℕ) :
    u32get b x = b[4 * x]!.toNat + 256 * b[4 * x + 1]!.toNat + 65536 * b[4 * x + 2]!.toNat +
      16777216 * b[4 * x + 3]!.toNat := by
  unfold u32get
  simp only [get!_eq_getElem!]

private theorem getElem!_push4_lt (b : ByteArray) (a₀ a₁ a₂ a₃ : UInt8) {i : ℕ}
    (hi : i < b.size) : ((((b.push a₀).push a₁).push a₂).push a₃)[i]! = b[i]! := by
  rw [ByteArray.getElem!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
    ByteArray.getElem!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
    ByteArray.getElem!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
    ByteArray.getElem!_push_lt _ _ _ hi]

private theorem u32get_push4_of_lt (b : ByteArray) (a₀ a₁ a₂ a₃ : UInt8) {x : ℕ}
    (hx : 4 * x + 4 ≤ b.size) :
    u32get ((((b.push a₀).push a₁).push a₂).push a₃) x = u32get b x := by
  rw [u32get_eq, u32get_eq, getElem!_push4_lt _ _ _ _ _ (by omega),
    getElem!_push4_lt _ _ _ _ _ (by omega), getElem!_push4_lt _ _ _ _ _ (by omega),
    getElem!_push4_lt _ _ _ _ _ (by omega)]

private theorem u32get_push4_of_eq (b : ByteArray) (a₀ a₁ a₂ a₃ : UInt8) {x : ℕ}
    (hx : b.size = 4 * x) :
    u32get ((((b.push a₀).push a₁).push a₂).push a₃) x =
      a₀.toNat + 256 * a₁.toNat + 65536 * a₂.toNat + 16777216 * a₃.toNat := by
  rw [u32get_eq]
  have h0 : ((((b.push a₀).push a₁).push a₂).push a₃)[4 * x]! = a₀ := by
    rw [ByteArray.getElem!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.getElem!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.getElem!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega), ← hx]
    exact ByteArray.getElem!_push_eq b a₀
  have h1 : ((((b.push a₀).push a₁).push a₂).push a₃)[4 * x + 1]! = a₁ := by
    rw [ByteArray.getElem!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
      ByteArray.getElem!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega)]
    have := ByteArray.getElem!_push_eq (b.push a₀) a₁
    rwa [ByteArray.size_push, hx] at this
  have h2 : ((((b.push a₀).push a₁).push a₂).push a₃)[4 * x + 2]! = a₂ := by
    rw [ByteArray.getElem!_push_lt _ _ _ (by simp only [ByteArray.size_push]; omega)]
    have := ByteArray.getElem!_push_eq ((b.push a₀).push a₁) a₂
    rwa [ByteArray.size_push, ByteArray.size_push, hx] at this
  have h3 : ((((b.push a₀).push a₁).push a₂).push a₃)[4 * x + 3]! = a₃ := by
    have := ByteArray.getElem!_push_eq (((b.push a₀).push a₁).push a₂) a₃
    rwa [ByteArray.size_push, ByteArray.size_push, ByteArray.size_push, hx] at this
  rw [h0, h1, h2, h3]

private theorem size_u32push (b : ByteArray) (v : ℕ) : (u32push b v).size = b.size + 4 := by
  simp only [u32push, ByteArray.size_push]

private theorem u32get_u32push_of_lt (b : ByteArray) (v : ℕ) {x : ℕ} (hx : 4 * x + 4 ≤ b.size) :
    u32get (u32push b v) x = u32get b x :=
  u32get_push4_of_lt _ _ _ _ _ hx

private theorem u32get_u32push_of_eq (b : ByteArray) (v : ℕ) {x : ℕ} (hx : b.size = 4 * x) :
    u32get (u32push b v) x = v % 2 ^ 32 := by
  rw [u32push, u32get_push4_of_eq _ _ _ _ _ hx]
  simp only [UInt8.toNat_ofNat']
  omega

private theorem u32fold_spec (f : ℕ → ℕ) (lo m : ℕ) :
    ((List.range' lo m).foldl (fun b x => u32push b (f x)) ByteArray.empty).size = 4 * m ∧
    ∀ i < m, u32get ((List.range' lo m).foldl (fun b x => u32push b (f x)) ByteArray.empty) i =
      f (lo + i) % 2 ^ 32 := by
  induction m with
  | zero =>
    refine ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨hs, hg⟩ := ih
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨by rw [size_u32push, hs]; omega, fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | rfl
    · rw [u32get_u32push_of_lt _ _ (by omega), hg i hlt]
    · rw [u32get_u32push_of_eq _ _ hs]
      simp

private theorem u32chunk_eq_foldl (f : ℕ → ℕ) (lo hi : ℕ) :
    u32chunk f lo hi =
      (List.range' lo (hi - lo)).foldl (fun b x => u32push b (f x)) ByteArray.empty := by
  unfold u32chunk
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.add_sub_cancel, Nat.div_one, bind_pure]
  rfl

private theorem u32chunk_spec (f : ℕ → ℕ) (lo hi : ℕ) :
    (u32chunk f lo hi).size = 4 * (hi - lo) ∧
      ∀ i < hi - lo, u32get (u32chunk f lo hi) i = f (lo + i) % 2 ^ 32 := by
  rw [u32chunk_eq_foldl]
  exact u32fold_spec f lo (hi - lo)

private theorem getElem!_append_left (a b : ByteArray) {i : ℕ} (hi : i < a.size) :
    (a ++ b)[i]! = a[i]! := by
  have h : i < (a ++ b).size := by rw [ByteArray.size_append]; omega
  rw [getElem!_pos (a ++ b) i h, getElem!_pos a i hi]
  exact ByteArray.getElem_append_left hi

private theorem getElem!_append_right (a b : ByteArray) {i : ℕ} (hi : a.size ≤ i)
    (hi' : i < a.size + b.size) : (a ++ b)[i]! = b[i - a.size]! := by
  have h : i < (a ++ b).size := by rw [ByteArray.size_append]; exact hi'
  rw [getElem!_pos (a ++ b) i h, getElem!_pos b (i - a.size) (by omega)]
  exact ByteArray.getElem_append_right hi

private theorem u32get_append_left (a b : ByteArray) {x : ℕ} (hx : 4 * x + 4 ≤ a.size) :
    u32get (a ++ b) x = u32get a x := by
  rw [u32get_eq, u32get_eq, getElem!_append_left _ _ (by omega),
    getElem!_append_left _ _ (by omega), getElem!_append_left _ _ (by omega),
    getElem!_append_left _ _ (by omega)]

private theorem u32get_append_right (a b : ByteArray) {x lo : ℕ} (ha : a.size = 4 * lo)
    (hlo : lo ≤ x) (hx : 4 * (x - lo) + 4 ≤ b.size) :
    u32get (a ++ b) x = u32get b (x - lo) := by
  rw [u32get_eq, u32get_eq, getElem!_append_right _ _ (by omega) (by omega),
    getElem!_append_right _ _ (by omega) (by omega),
    getElem!_append_right _ _ (by omega) (by omega),
    getElem!_append_right _ _ (by omega) (by omega)]
  have e0 : 4 * x - a.size = 4 * (x - lo) := by omega
  have e1 : 4 * x + 1 - a.size = 4 * (x - lo) + 1 := by omega
  have e2 : 4 * x + 2 - a.size = 4 * (x - lo) + 2 := by omega
  have e3 : 4 * x + 3 - a.size = 4 * (x - lo) + 3 := by omega
  rw [e0, e1, e2, e3]

private theorem u32ofFn_eq_foldl (N T : ℕ) (f : ℕ → ℕ) :
    u32ofFn N T f = (List.range T).foldl (fun acc t =>
      acc ++ u32chunk f (min N (t * (N / T + 1))) (min N ((t + 1) * (N / T + 1))))
        ByteArray.empty := by
  unfold u32ofFn
  simp only [List.foldl_map]
  rfl

private theorem u32prefix_spec (N sz : ℕ) (f : ℕ → ℕ) (t : ℕ) :
    ((List.range t).foldl (fun acc s =>
      acc ++ u32chunk f (min N (s * sz)) (min N ((s + 1) * sz))) ByteArray.empty).size =
        4 * min N (t * sz) ∧
    ∀ x < min N (t * sz), u32get ((List.range t).foldl (fun acc s =>
      acc ++ u32chunk f (min N (s * sz)) (min N ((s + 1) * sz))) ByteArray.empty) x =
        f x % 2 ^ 32 := by
  induction t with
  | zero =>
    refine ⟨by simp, fun x hx => absurd hx ?_⟩
    simp
  | succ t ih =>
    obtain ⟨hs, hg⟩ := ih
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hcs, hcg⟩ := u32chunk_spec f (min N (t * sz)) (min N ((t + 1) * sz))
    have hle : min N (t * sz) ≤ min N ((t + 1) * sz) := by
      have : t * sz ≤ (t + 1) * sz := Nat.mul_le_mul_right _ (Nat.le_succ t)
      omega
    refine ⟨by rw [ByteArray.size_append, hs, hcs]; omega, fun x hx => ?_⟩
    by_cases hxl : x < min N (t * sz)
    · rw [u32get_append_left _ _ (by omega), hg x hxl]
    · rw [u32get_append_right _ _ hs (by omega) (by omega), hcg _ (by omega)]
      congr 2
      omega

theorem u32get_u32ofFn {N T : ℕ} (hT : 0 < T) (f : ℕ → ℕ) {x : ℕ} (hx : x < N) :
    u32get (u32ofFn N T f) x = f x % 2 ^ 32 := by
  rw [u32ofFn_eq_foldl]
  have hN : N ≤ T * (N / T + 1) := by
    have h1 := Nat.div_add_mod N T
    have h2 := Nat.mod_lt N hT
    rw [Nat.mul_add, Nat.mul_one]
    omega
  exact (u32prefix_spec N (N / T + 1) f T).2 x (by rw [Nat.min_eq_left hN]; exact hx)

theorem u32get_u32ofFn_of_lt {N T : ℕ} (hT : 0 < T) (f : ℕ → ℕ) {x : ℕ} (hx : x < N)
    (hf : f x < 2 ^ 32) : u32get (u32ofFn N T f) x = f x := by
  rw [u32get_u32ofFn hT f hx, Nat.mod_eq_of_lt hf]

private theorem foldl_add_range (f : ℕ → ℕ) (m init : ℕ) :
    (List.range m).foldl (fun a j => a + f j) init = init + ∑ j ∈ Finset.range m, f j := by
  induction m generalizing init with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
      Finset.sum_range_succ]
    ring

private theorem foldl_mul_range (f : ℕ → ℕ) (m init : ℕ) :
    (List.range m).foldl (fun a j => a * f j) init = init * ∏ j ∈ Finset.range m, f j := by
  induction m generalizing init with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
      Finset.prod_range_succ]
    ring

theorem EnvB.chainBound_eq {E : EnvB} (st : RSt E) (fin : NodeFin) :
    E.chainBound st fin = ∏ l ∈ Finset.range fin.chain.size, E.levelLen st fin.chain l := by
  rw [EnvB.chainBound, foldl_mul_range, one_mul]

theorem EnvB.finalOK_spec {E : EnvB} {prog : Array Ins} {fins : Array (ℕ × NodeFin)}
    {ord bound : ℕ} (h : E.finalOK prog fins ord bound = true) :
    E.C.N < 2 ^ 32 ∧ 0 < fins.size ∧ fins[0]!.1 = 0 ∧
    (∀ l < fins.size,
      E.nodeCovered (replay E prog) (fins.map (·.1)) fins[l]!.1 fins[l]!.2 = true ∧
      ∀ m < fins[l]!.2.chain.size,
        E.levelOKB (replay E prog) fins[l]!.1 fins[l]!.2.chain m = true) ∧
    ∑ l ∈ Finset.range fins.size, ord / E.chainBound (replay E prog) fins[l]!.2 ≤ bound := by
  unfold EnvB.finalOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨-, hN⟩, hnn⟩, h0⟩, hall⟩, hcount⟩ := h
  refine ⟨hN, hnn, h0, fun l hl => ?_, ?_⟩
  · have := allLt_spec hall hl
    simp only [Bool.and_eq_true] at this
    exact ⟨this.1, fun m hm => allLt_spec this.2 hm⟩
  · rwa [foldl_add_range, zero_add] at hcount

private theorem forest_cover {N : ℕ} (orb spar dep roots wit fpts : Array ℕ)
    (Q : ℕ → ℕ → Prop) (hrefl : ∀ x, Q x x) (hsymm : ∀ x y, Q x y → Q y x)
    (htrans : ∀ x y z, Q x y → Q y z → Q x z)
    (hroot : ∀ x < N, spar[x]! = N → orb[x]! < roots.size ∧ roots[orb[x]!]! = x)
    (hstep : ∀ x < N, spar[x]! ≠ N →
      spar[x]! < N ∧ dep[spar[x]!]! < dep[x]! ∧ Q spar[x]! x ∧ orb[spar[x]!]! = orb[x]!)
    (hcov : ∀ k < roots.size, wit[k]! < fpts.size ∧ orb[fpts[wit[k]!]!]! = k)
    (hfpts : ∀ t < fpts.size, fpts[t]! < N) :
    ∀ x < N, ∃ t < fpts.size, Q fpts[t]! x := by
  have hA : ∀ d, ∀ x < N, dep[x]! = d →
      ∃ r < N, spar[r]! = N ∧ orb[r]! = orb[x]! ∧ Q r x := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro x hx hd
      by_cases hr : spar[x]! = N
      · exact ⟨x, hx, hr, rfl, hrefl x⟩
      · obtain ⟨hlt, hdep, hQx, horb⟩ := hstep x hx hr
        obtain ⟨r, hrN, hrr, hro, hQr⟩ := ih (dep[spar[x]!]!) (hd ▸ hdep) (spar[x]!) hlt rfl
        exact ⟨r, hrN, hrr, hro.trans horb, htrans _ _ _ hQr hQx⟩
  intro x hx
  obtain ⟨r, hr, hrr, hro, hQr⟩ := hA _ x hx rfl
  obtain ⟨hk, hrk⟩ := hroot r hr hrr
  obtain ⟨hw, hwo⟩ := hcov (orb[r]!) hk
  refine ⟨wit[orb[r]!]!, hw, ?_⟩
  obtain ⟨r', hr', hrr', hro', hQr'⟩ := hA _ (fpts[wit[orb[r]!]!]!) (hfpts _ hw) rfl
  obtain ⟨-, hrk'⟩ := hroot r' hr' hrr'
  have hrr'' : r' = r := by
    rw [← hrk', hro', hwo, hrk]
  rw [hrr''] at hQr'
  exact htrans _ _ _ (hsymm _ _ hQr') hQr

private theorem EnvB.omegaPerms_getElem! {E : EnvB} (st : RSt E) (fin : NodeFin) {g : ℕ}
    (hg : g < (E.fgensOf st fin).size) :
    (E.omegaPerms st fin)[g]! = E.C.actAll ((E.fgensOf st fin)[g]'hg).1.2 := by
  have hg' : g < (E.omegaPerms st fin).size := by simpa [EnvB.omegaPerms] using hg
  rw [getElem!_pos _ g hg']
  simp only [EnvB.omegaPerms, Array.getElem_map]

theorem EnvB.nodeCovered_spec {E : EnvB} {st : RSt E} {live : Array ℕ} {j : ℕ} {fin : NodeFin}
    (h : E.nodeCovered st live j fin = true) (Q : ℕ → ℕ → Prop) (hrefl : ∀ x, Q x x)
    (hsymm : ∀ x y, Q x y → Q y x) (htrans : ∀ x y z, Q x y → Q y z → Q x z)
    (hQ : ∀ w ∈ E.fgensOf st fin, w.1.1 = j → ∀ y < E.C.N, Q y (u32get (E.C.actAll w.1.2) y)) :
    (∀ w ∈ E.fgensOf st fin, w.1.1 = j) ∧
    (∀ f ∈ E.coverOf st fin, f.1.i = j ∧ f.1.k ∈ live ∧ f.1.p < E.C.N) ∧
    ∀ x < E.C.N, ∃ f ∈ E.coverOf st fin, Q f.1.p x := by
  unfold EnvB.nodeCovered at h
  rcases hF : forestOf E.C.N (E.omegaPerms st fin) with ⟨orb, spar, sgen, dep, roots⟩
  simp only [hF, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨-, hgens⟩, hfacts⟩, hpar⟩, hroots⟩ := h
  have hgens' : ∀ w ∈ E.fgensOf st fin, w.1.1 = j := by
    intro w hw
    have := Array.all_eq_true_iff_forall_mem.1 hgens w hw
    simpa using this
  have hfacts' : ∀ f ∈ E.coverOf st fin, f.1.i = j ∧ f.1.k ∈ live ∧ f.1.p < E.C.N := by
    intro f hf
    have := Array.all_eq_true_iff_forall_mem.1 hfacts f hf
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact ⟨this.1.1, Array.contains_iff_mem.1 this.1.2, this.2⟩
  have hpar' := parLt_spec (by norm_num) hpar
  refine ⟨hgens', hfacts', ?_⟩
  have hsz : (E.omegaPerms st fin).size = (E.fgensOf st fin).size := by
    simp [EnvB.omegaPerms]
  have hfp : ((E.coverOf st fin).map fun f => f.1.p).size = (E.coverOf st fin).size := by
    simp
  have hfpget : ∀ t (ht : t < (E.coverOf st fin).size),
      ((E.coverOf st fin).map fun f => f.1.p)[t]! = ((E.coverOf st fin)[t]'ht).1.p := by
    intro t ht
    rw [getElem!_pos _ t (by simpa using ht)]
    simp
  have key := forest_cover orb spar dep roots
    (coverWitness roots.size orb ((E.coverOf st fin).map fun f => f.1.p))
    ((E.coverOf st fin).map fun f => f.1.p) Q hrefl hsymm htrans
    (by
      intro x hx hr
      have := hpar' x hx
      rw [ite_eq_left hr] at this
      simpa using this)
    (by
      intro x hx hr
      have := hpar' x hx
      rw [ite_eq_right hr] at this
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := this
      refine ⟨h1, h2, ?_, h5⟩
      have h3' : sgen[x]! < (E.fgensOf st fin).size := hsz ▸ h3
      rw [EnvB.omegaPerms_getElem! st fin h3'] at h4
      have hmem : (E.fgensOf st fin)[sgen[x]!]'h3' ∈ E.fgensOf st fin := Array.getElem_mem h3'
      have := hQ _ hmem (hgens' _ hmem) spar[x]! h1
      rwa [h4] at this)
    (by
      intro k hk
      have := allLt_spec hroots hk
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
      obtain ⟨⟨-, h1⟩, h2⟩ := this
      exact ⟨by rwa [hfp], h2⟩)
    (by
      intro t ht
      rw [hfp] at ht
      rw [hfpget t ht]
      exact (hfacts' _ (Array.getElem_mem ht)).2.2)
  intro x hx
  obtain ⟨t, ht, hQt⟩ := key x hx
  rw [hfp] at ht
  rw [hfpget t ht] at hQt
  exact ⟨(E.coverOf st fin)[t], Array.getElem_mem ht, hQt⟩

section Level

variable {E : EnvB}

private def levelGens (st : RSt E) (chain : Array (ℕ × Array ℕ)) (l : ℕ) : Array (WEltB E) :=
  (chain[l]!).2.filterMap fun w => RSt.get st.ws w

private def levelRec (st : RSt E) (chain : Array (ℕ × Array ℕ)) (l : ℕ) :
    Array ℕ × Array ℕ × Array ℕ × Array ℕ :=
  orbitRec E.C.n (chain[l]!).1 ((levelGens st chain l).map (·.1.2))

private theorem levelLen_eq (st : RSt E) (chain : Array (ℕ × Array ℕ)) (l : ℕ) :
    E.levelLen st chain l = (levelRec st chain l).1.size := rfl

private structure LevelFactsB (st : RSt E) (j : ℕ) (chain : Array (ℕ × Array ℕ)) (l : ℕ) :
    Prop where
  β_lt : (chain[l]!).1 < E.C.n
  pts_pos : 0 < (levelRec st chain l).1.size
  pts_zero : (levelRec st chain l).1[0]! = (chain[l]!).1
  sg_node : ∀ s ∈ levelGens st chain l, s.1.1 = j
  sg_fix : ∀ s ∈ levelGens st chain l, ∀ m < l, bget s.1.2 (chain[m]!).1 = (chain[m]!).1
  pts_lt : ∀ t < (levelRec st chain l).1.size, (levelRec st chain l).1[t]! < E.C.n
  pos_pts : ∀ t < (levelRec st chain l).1.size,
    (levelRec st chain l).2.1[(levelRec st chain l).1[t]!]! = t
  tree : ∀ t < (levelRec st chain l).1.size, t ≠ 0 →
    ∃ t' < t, ∃ s ∈ levelGens st chain l,
      bget s.1.2 ((levelRec st chain l).1[t']!) = (levelRec st chain l).1[t]!

private theorem levelOKB_spec {st : RSt E} {j : ℕ} {chain : Array (ℕ × Array ℕ)} {l : ℕ}
    (h : E.levelOKB st j chain l = true) : LevelFactsB st j chain l := by
  unfold EnvB.levelOKB at h
  rcases hc : chain[l]! with ⟨β, sl⟩
  rcases hO : orbitRec E.C.n β ((sl.filterMap fun w => RSt.get st.ws w).map (·.1.2)) with
    ⟨pts, pos, tp, tl⟩
  simp only [hc, hO, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hsz, hβ⟩, hposz⟩, hne⟩, h0⟩, hsg⟩, hpts⟩ := h
  have hg : levelGens st chain l = sl.filterMap fun w => RSt.get st.ws w := by
    simp [levelGens, hc]
  have hR : levelRec st chain l = (pts, pos, tp, tl) := by
    simp only [levelRec, hg, hc, hO]
  rw [← hg] at hsg hpts hsz hO
  have hmap : ∀ i (hi : i < (levelGens st chain l).size),
      ((levelGens st chain l).map (·.1.2))[i]! = ((levelGens st chain l)[i]'hi).1.2 := by
    intro i hi
    rw [getElem!_pos _ i (by simpa using hi)]
    simp
  have hsg' : ∀ s ∈ levelGens st chain l,
      s.1.1 = j ∧ ∀ m < l, bget s.1.2 (chain[m]!).1 = (chain[m]!).1 := by
    intro s hs
    have := Array.all_eq_true_iff_forall_mem.1 hsg s hs
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    refine ⟨this.1, fun m hm => ?_⟩
    simpa using allLt_spec this.2 hm
  refine ⟨?_, ?_, ?_, fun s hs => (hsg' s hs).1, fun s hs => (hsg' s hs).2, ?_, ?_, ?_⟩
  · rw [hc]
    exact hβ
  · rw [hR]
    exact Nat.pos_of_ne_zero hne
  · rw [hR, hc]
    exact h0
  · intro t ht
    rw [hR] at ht ⊢
    have := allLt_spec hpts ht
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact this.1.1
  · intro t ht
    rw [hR] at ht ⊢
    have := allLt_spec hpts ht
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact this.1.2
  · intro t ht ht0
    rw [hR] at ht ⊢
    have := allLt_spec hpts ht
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true] at this
    rcases this.2 with h0' | ⟨⟨⟨⟨htl, -⟩, hlt⟩, hpp⟩, hs⟩
    · exact absurd h0' ht0
    · refine ⟨pos[tp[pts[t]!]!]!, hlt, (levelGens st chain l)[tl[pts[t]!]!]'htl,
        Array.getElem_mem htl, ?_⟩
      rw [hmap _ htl] at hs
      show bget _ (pts[pos[tp[pts[t]!]!]!]!) = pts[t]!
      rw [hpp]
      exact hs

end Level

def stabSub {G Eg Ω : Type*} [Group G] [Group Eg] [MulAction Eg Ω]
    (S : SymGen.Setup G Eg Ω) (g : G) : Subgroup Eg where
  carrier := {e | g * S.ψ e * g⁻¹ ∈ S.H}
  mul_mem' {a b} ha hb := by
    have := S.H.mul_mem ha hb
    rwa [show g * S.ψ a * g⁻¹ * (g * S.ψ b * g⁻¹) = g * S.ψ (a * b) * g⁻¹ by
      rw [map_mul]; group] at this
  one_mem' := by
    show g * S.ψ 1 * g⁻¹ ∈ S.H
    rw [map_one, mul_one, mul_inv_cancel]
    exact S.H.one_mem
  inv_mem' {a} ha := by
    have := S.H.inv_mem ha
    rwa [show (g * S.ψ a * g⁻¹)⁻¹ = g * S.ψ a⁻¹ * g⁻¹ by rw [map_inv]; group] at this

theorem mem_stabSub {G Eg Ω : Type*} [Group G] [Group Eg] [MulAction Eg Ω]
    (S : SymGen.Setup G Eg Ω) (g : G) (e : Eg) :
    e ∈ stabSub S g ↔ g * S.ψ e * g⁻¹ ∈ S.H :=
  Iff.rfl

private theorem index_mul_card_map {Eg : Type*} [Group Eg] [Finite Eg] {n : ℕ}
    (ρ : Eg →* Equiv.Perm (Fin n)) (P : Subgroup Eg) (hker : ρ.ker ≤ P) :
    P.index * Nat.card (P.map ρ) = Nat.card ρ.range := by
  have h1 : (P.map ρ).relIndex ρ.range = P.index := by
    rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map, top_sup_eq,
      Subgroup.relIndex_top_right, sup_of_le_left hker]
  have h2 := Subgroup.relIndex_mul_card (H := P.map ρ) (K := ρ.range)
  rwa [inf_of_le_left (Subgroup.map_le_range ρ P), h1] at h2

private theorem le_ncard_orbit {n m : ℕ} (K : Subgroup (Equiv.Perm (Fin n))) (β : Fin n)
    (p : Fin m → Fin n) (hinj : Function.Injective p)
    (hp : ∀ t : Fin m, p t = β ∨ ∃ t' : Fin m, t' < t ∧ ∃ g ∈ K, g (p t') = p t) :
    m ≤ (MulAction.orbit K β).ncard := by
  have hmem : ∀ t : Fin m, p t ∈ MulAction.orbit K β := by
    intro t
    induction t using WellFoundedLT.induction with
    | _ t ih =>
    rcases hp t with h | ⟨t', ht', g, hg, hgt⟩
    · rw [h]
      exact MulAction.mem_orbit_self β
    · obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.1 (ih t' ht')
      exact MulAction.mem_orbit_iff.2 ⟨⟨g, hg⟩ * k, by
        rw [mul_smul, hk]
        exact hgt⟩
  have h1 : Set.range p ⊆ MulAction.orbit K β := by
    rintro _ ⟨t, rfl⟩
    exact hmem t
  calc m = (Set.range p).ncard := by
        rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ,
          Nat.card_eq_fintype_card, Fintype.card_fin]
    _ ≤ _ := Set.ncard_le_ncard h1 (Set.toFinite _)

private theorem index_le_div_of_levels {Eg : Type*} [Group Eg] [Finite Eg] {n : ℕ}
    (ρ : Eg →* Equiv.Perm (Fin n)) (P : Subgroup Eg) (hker : ρ.ker ≤ P) {ord : ℕ}
    (hord : Nat.card ρ.range = ord) (k : ℕ) (β m : ℕ → ℕ) (pts : ℕ → ℕ → ℕ)
    (Y : ℕ → Set (Equiv.Perm (Fin n)))
    (hβ : ∀ l < k, β l < n)
    (hY : ∀ l < k, ∀ g ∈ Y l, g ∈ P.map ρ)
    (hfix : ∀ l < k, ∀ g ∈ Y l, ∀ i < l, ∀ h : β i < n, (g ⟨β i, h⟩ : ℕ) = β i)
    (hm : ∀ l < k, 0 < m l)
    (hpts : ∀ l < k, ∀ t < m l, pts l t < n)
    (hinj : ∀ l < k, ∀ t₁ < m l, ∀ t₂ < m l, pts l t₁ = pts l t₂ → t₁ = t₂)
    (htree : ∀ l < k, ∀ t < m l, pts l t = β l ∨
      ∃ t' < t, ∃ g ∈ Y l, ∀ h : pts l t' < n, (g ⟨pts l t', h⟩ : ℕ) = pts l t) :
    P.index ≤ ord / ∏ l ∈ Finset.range k, m l := by
  classical
  have hpos : 0 < ∏ l ∈ Finset.range k, m l :=
    Finset.prod_pos fun l hl => hm l (Finset.mem_range.1 hl)
  have hcard := index_mul_card_map ρ P hker
  rw [hord] at hcard
  have hle : ∏ l ∈ Finset.range k, m l ≤ Nat.card (P.map ρ) := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · rw [hk, Finset.range_zero, Finset.prod_empty]
      exact Nat.card_pos
    · have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) (hβ 0 hk)
      let β' : ℕ → Fin n := fun l => if h : β l < n then ⟨β l, h⟩ else ⟨0, hn0⟩
      have hβ' : ∀ l < k, ((β' l : Fin n) : ℕ) = β l := by
        intro l hl
        simp only [β', dite_eq_left (hβ l hl)]
      refine card_ge_of_chain (P.map ρ) k β' Y hY ?_ m ?_
      · intro l hl y hy i hi
        apply Fin.ext
        have := hfix l hl y hy i hi (hβ i (by omega))
        rw [hβ' i (by omega)]
        have h2 : β' i = ⟨β i, hβ i (by omega)⟩ := Fin.ext (hβ' i (by omega))
        rw [h2]
        exact this
      · intro l hl
        refine le_ncard_orbit (Subgroup.closure (Y l)) (β' l)
          (fun t => ⟨pts l t.1, hpts l hl t.1 t.2⟩) ?_ ?_
        · intro a b hab
          exact Fin.ext (hinj l hl a.1 a.2 b.1 b.2 (congrArg Fin.val hab))
        · intro t
          rcases htree l hl t.1 t.2 with h0 | ⟨t', ht', g, hg, hgt⟩
          · left
            exact Fin.ext (by rw [hβ' l hl]; exact h0)
          · right
            refine ⟨⟨t', lt_trans ht' t.2⟩, ht', g, Subgroup.subset_closure hg, ?_⟩
            exact Fin.ext (hgt (hpts l hl t' (lt_trans ht' t.2)))
  rw [Nat.le_div_iff_mul_le hpos]
  calc P.index * ∏ l ∈ Finset.range k, m l ≤ P.index * Nat.card (P.map ρ) :=
        Nat.mul_le_mul_left _ hle
    _ = ord := hcard

theorem index_stabSub_le {G Eg Ω : Type*} [Group G] [Group Eg] [MulAction Eg Ω]
    [Finite Eg] {E : EnvB} (st : RSt E) (j : ℕ) (fin : NodeFin)
    (hl : ∀ l < fin.chain.size, E.levelOKB st j fin.chain l = true)
    (S : SymGen.Setup G Eg Ω) (ρ : Eg →* Equiv.Perm (Fin E.C.n)) (x : ℕ → G)
    (hW : ∀ j a, E.W j a → ∃ e, RepB E.C.n a (ρ e) ∧ x j * S.ψ e * (x j)⁻¹ ∈ S.H)
    (hker : ∀ j e, ρ e = 1 → x j * S.ψ e * (x j)⁻¹ ∈ S.H)
    {ord : ℕ} (hord : Nat.card ρ.range = ord) :
    (stabSub S (x j)).index ≤ ord / E.chainBound st fin := by
  have hf : ∀ l < fin.chain.size, LevelFactsB st j fin.chain l := fun l hl' =>
    levelOKB_spec (hl l hl')
  have hsg : ∀ l < fin.chain.size, ∀ s ∈ levelGens st fin.chain l,
      ∃ e ∈ stabSub S (x j), RepB E.C.n s.1.2 (ρ e) := by
    intro l hl' s hs
    have hsW : E.W j s.1.2 := by
      have := s.2
      rwa [(hf l hl').sg_node s hs] at this
    obtain ⟨e, hrep, he⟩ := hW j _ hsW
    exact ⟨e, (mem_stabSub S _ _).2 he, hrep⟩
  rw [EnvB.chainBound_eq]
  refine index_le_div_of_levels ρ (stabSub S (x j))
    (fun e he => (mem_stabSub S _ _).2 (hker j e (MonoidHom.mem_ker.1 he))) hord fin.chain.size
    (fun l => (fin.chain[l]!).1) (fun l => E.levelLen st fin.chain l)
    (fun l t => (levelRec st fin.chain l).1[t]!)
    (fun l => {g | ∃ s ∈ levelGens st fin.chain l, RepB E.C.n s.1.2 g})
    (fun l hl' => (hf l hl').β_lt) ?_ ?_ (fun l hl' => (hf l hl').pts_pos)
    (fun l hl' t ht => (hf l hl').pts_lt t ht) ?_ ?_
  · rintro l hl' g ⟨s, hs, hrep⟩
    obtain ⟨e, he, hre⟩ := hsg l hl' s hs
    exact ⟨e, he, hre.unique hrep⟩
  · rintro l hl' g ⟨s, hs, hrep⟩ i hi hβi
    rw [← hrep.apply hβi]
    exact (hf l hl').sg_fix s hs i hi
  · intro l hl' t₁ ht₁ t₂ ht₂ h12
    have h1 := (hf l hl').pos_pts t₁ ht₁
    have h2 := (hf l hl').pos_pts t₂ ht₂
    rw [← h1, ← h2]
    exact congrArg _ h12
  · intro l hl' t ht
    by_cases ht0 : t = 0
    · left
      rw [ht0]
      exact (hf l hl').pts_zero
    · right
      obtain ⟨t', ht', s, hs, hst⟩ := (hf l hl').tree t ht ht0
      obtain ⟨e, -, hre⟩ := hsg l hl' s hs
      refine ⟨t', ht', ρ e, ⟨s, hs, hre⟩, fun h => ?_⟩
      rw [← hre.apply h]
      exact hst

end CFSG.YGroups.DCE.B

namespace CFSG.YGroups.DCE

open CFSG.Monster.B.Co2

theorem index_le_of_finalOK {G Eg Ω : Type*} [Group G] [Group Eg] [MulAction Eg Ω] [Finite Eg]
    (E : B.EnvB) (S : SymGen.Setup G Eg Ω) {n : ℕ} (hn : E.C.n = n) (hn' : n ≤ 65536)
    (ρ : Eg →* Equiv.Perm (Fin n)) (pt : ℕ → Ω) (x : ℕ → G)
    (hW : ∀ j a, E.W j a → ∃ e, RepB n a (ρ e) ∧ x j * S.ψ e * (x j)⁻¹ ∈ S.H)
    (hV : ∀ i p k a, E.V i p k a → p < E.C.N ∧ ∃ e, S.RCoset (x i * S.T (pt p)) (x k * S.ψ e))
    (hactAll : ∀ (σ : ByteArray) (e : Eg), RepB n σ (ρ e) → ∀ p < E.C.N,
      B.u32get (E.C.actAll σ) p < E.C.N ∧ pt (B.u32get (E.C.actAll σ) p) = e • pt p)
    (hpt : ∀ ω : Ω, ∃ p < E.C.N, pt p = ω) (hx0 : x 0 ∈ S.H)
    (hker : ∀ j e, ρ e = 1 → x j * S.ψ e * (x j)⁻¹ ∈ S.H)
    (ord bound : ℕ) (hord : Nat.card ρ.range = ord)
    (hgen : Subgroup.closure ((S.H : Set G) ∪ {S.t}) = ⊤)
    (prog : Array B.Ins) (fins : Array (ℕ × B.NodeFin))
    (h : E.finalOK prog fins ord bound = true) :
    S.H.FiniteIndex ∧ S.H.index ≤ bound := by
  classical
  subst hn
  obtain ⟨-, hnn, hroot, hcl, hcount⟩ := B.EnvB.finalOK_spec h
  let st := B.replay E prog
  let live : Array ℕ := fins.map (·.1)
  let x' : ℕ → G := fun l => x fins[l]!.1
  have hx0' : x' 0 ∈ S.H := by
    show x fins[0]!.1 ∈ S.H
    rw [hroot]
    exact hx0
  let Q : ℕ → ℕ → ℕ → Prop := fun j a b => ∃ e ∈ B.stabSub S (x j), e • pt a = pt b
  have hrefl : ∀ j a, Q j a a := fun j a => ⟨1, one_mem _, one_smul _ _⟩
  have hsymm : ∀ j a b, Q j a b → Q j b a := fun j a b ⟨e, he, hab⟩ =>
    ⟨e⁻¹, inv_mem he, by rw [← hab, inv_smul_smul]⟩
  have htrans : ∀ j a b c, Q j a b → Q j b c → Q j a c := fun j a b c ⟨e₁, he₁, h₁⟩ ⟨e₂, he₂, h₂⟩ =>
    ⟨e₂ * e₁, mul_mem he₂ he₁, by rw [mul_smul, h₁, h₂]⟩
  have hQ : ∀ j (fin : B.NodeFin), ∀ w ∈ E.fgensOf st fin, w.1.1 = j →
      ∀ y < E.C.N, Q j y (B.u32get (E.C.actAll w.1.2) y) := by
    intro j fin w _ hwj y hy
    have hwW : E.W j w.1.2 := by
      have := w.2
      rwa [hwj] at this
    obtain ⟨e, hrep, he⟩ := hW j _ hwW
    obtain ⟨-, hpe⟩ := hactAll w.1.2 e hrep y hy
    exact ⟨e, (B.mem_stabSub S _ _).2 he, hpe.symm⟩
  have hnode : ∀ l < fins.size,
      (∀ f ∈ E.coverOf st fins[l]!.2, f.1.i = fins[l]!.1 ∧ f.1.k ∈ live ∧ f.1.p < E.C.N) ∧
      ∀ y < E.C.N, ∃ f ∈ E.coverOf st fins[l]!.2, Q fins[l]!.1 f.1.p y := by
    intro l hl
    obtain ⟨-, hfacts, hcov⟩ := B.EnvB.nodeCovered_spec (hcl l hl).1 (Q fins[l]!.1)
      (hrefl _) (hsymm _) (htrans _) (hQ _ _)
    exact ⟨hfacts, hcov⟩
  let R : ℕ → Finset Ω := fun l =>
    ((E.coverOf st fins[l]!.2).toList.map fun f => pt f.1.p).toFinset
  have hmemR : ∀ l (q : Ω), q ∈ R l ↔ ∃ f ∈ E.coverOf st fins[l]!.2, pt f.1.p = q := by
    intro l q
    simp [R]
  have hR : ∀ l < fins.size, ∀ p : Ω, ∃ q ∈ R l, ∃ e ∈ B.stabSub S (x' l), e • q = p := by
    intro l hl ω
    obtain ⟨p, hp, rfl⟩ := hpt ω
    obtain ⟨f, hf, e, he, hee⟩ := (hnode l hl).2 p hp
    exact ⟨pt f.1.p, (hmemR l _).2 ⟨f, hf, rfl⟩, e, he, hee⟩
  have hpos : ∀ k ∈ live, ∃ l', l' < fins.size ∧ fins[l']!.1 = k := by
    intro k hk
    obtain ⟨a, ha, rfl⟩ := Array.mem_map.1 hk
    obtain ⟨l', hl', rfl⟩ := Array.mem_iff_getElem.1 ha
    exact ⟨l', hl', by rw [getElem!_pos fins l' hl']⟩
  have htgt : ∀ l < fins.size, ∀ q ∈ R l, ∃ k, ∃ e : Eg, k < fins.size ∧
      S.RCoset (x' l * S.T q) (x' k * S.ψ e) := by
    intro l hl q hq
    obtain ⟨f, hf, rfl⟩ := (hmemR l q).1 hq
    obtain ⟨hi, hk, -⟩ := (hnode l hl).1 f hf
    obtain ⟨-, e, he⟩ := hV f.1.i f.1.p f.1.k f.1.a f.2
    obtain ⟨l', hl', hl'k⟩ := hpos _ hk
    refine ⟨l', e, hl', ?_⟩
    show S.RCoset (x fins[l]!.1 * S.T (pt f.1.p)) (x fins[l']!.1 * S.ψ e)
    rw [hl'k, ← hi]
    exact he
  choose! tgt u htgt1 htgt2 using htgt
  have hmain := S.index_le_of_points fins.size x' hx0' (fun l => B.stabSub S (x' l))
    (fun l _ e he => he) R hR tgt u (fun l hl q hq => ⟨htgt1 l hl q hq, htgt2 l hl q hq⟩) hgen hnn
  refine ⟨hmain.1, ?_⟩
  calc S.H.index ≤ ∑ l ∈ Finset.range fins.size, (B.stabSub S (x' l)).index := hmain.2
    _ ≤ ∑ l ∈ Finset.range fins.size, ord / E.chainBound st fins[l]!.2 :=
        Finset.sum_le_sum fun l hl => B.index_stabSub_le st fins[l]!.1 fins[l]!.2
          (hcl l (Finset.mem_range.1 hl)).2 S ρ x hW hker hord
    _ ≤ bound := hcount

end CFSG.YGroups.DCE
