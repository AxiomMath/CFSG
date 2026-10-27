module

public import Certificates.Kernel.BabyMonster.CTIB.QK
public import Certificates.Kernel.BabyMonster.CTIB.CosetQLin
public import CFSG.Certificates.Kernel.CoPairSound
public import Certificates.Kernel.BabyMonster.CTIB.InnerTab

public section

namespace CertificateChecks.KernelBM.CTIB.Hist

open CFSG.Monster.B.CTIB CFSG.Monster.B.CTIB.Native CFSG.KC.Bfs CFSG.KC.BM CFSG.KC.BM.CosetQ
  CertificateChecks.KernelBM.CTIB CertificateChecks.KernelBM.CTIB.CosetQ
  CertificateChecks.KernelBM.CTIB.QK CertificateChecks.KernelBM.CTIB.Inner

open Classical

@[expose] def bt (a b : ℕ) : Bool := corr (gArr ()) a b ^^ corr (gArr ()) b a

theorem bt_comm (a b : ℕ) : bt a b = bt b a := Bool.xor_comm _ _

theorem bt_xor_right (a b c : ℕ) : bt a (b ^^^ c) = (bt a b ^^ bt a c) := by
  simp only [bt, corr_xor_left, corr_xor_right]
  cases corr (gArr ()) a b <;> cases corr (gArr ()) a c <;> cases corr (gArr ()) b a <;>
    cases corr (gArr ()) c a <;> rfl

theorem bt_xor_left (a b c : ℕ) : bt (a ^^^ b) c = (bt a c ^^ bt b c) := by
  rw [bt_comm, bt_xor_right, bt_comm c, bt_comm c]

theorem bt_zero_right (a : ℕ) : bt a 0 = false := by
  simp only [bt, corr_zero_left, corr_zero_right, Bool.xor_false]

theorem toNat_xor (a b : Bool) : (a ^^ b).toNat = a.toNat ^^^ b.toNat := by
  cases a <;> cases b <;> rfl

theorem toNat_inj {a b : Bool} (h : a.toNat = b.toNat) : a = b := by
  cases a <;> cases b <;> simp_all

theorem g_xor {k : ℕ} (_hk : k < 2) (a b : ℕ) :
    censusAct k (a ^^^ b) = censusAct k a ^^^ censusAct k b := by
  unfold censusAct CFSG.Monster.B.Max2.Native.act22
  exact CFSG.KC.CoPair.actGo_xor _ a b 22

theorem g_zero {k : ℕ} (hk : k < 2) : censusAct k 0 = 0 := by
  have h := g_xor hk 0 0
  rw [Nat.xor_self] at h
  rw [h, Nat.xor_self]

theorem g_lt {k : ℕ} (hk : k < 2) (v : ℕ) : censusAct k v < 2 ^ 22 := by
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · have h := censusAct_pB false v
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    rw [← h]
    exact CFSG.KC.F2W.vmF_lt _ _ _
  · have h := censusAct_pB true v
    simp only [↓reduceIte] at h
    rw [← h]
    exact CFSG.KC.F2W.vmF_lt _ _ _

@[expose] noncomputable def btB (a b : ℕ) : ℕ := Nat.xor (betaK LOq a b) (betaK LOq b a)

theorem btB_eq (a b : ℕ) : btB a b = (bt a b).toNat := by
  rw [btB, lo_eq, betaK_eq _ symG, betaK_eq _ symG, bt, toNat_xor]
  rfl

@[expose] noncomputable def btK : Bool :=
  allLt 22 fun i => allLt 22 fun j =>
    Nat.beq (btB (CFSG.KC.M1F2.vmF 22 pR1 (2 ^ i)) (CFSG.KC.M1F2.vmF 22 pR1 (2 ^ j))) (btB (2 ^ i) (2 ^ j)) &&
    Nat.beq (btB (CFSG.KC.M1F2.vmF 22 pR2 (2 ^ i)) (CFSG.KC.M1F2.vmF 22 pR2 (2 ^ j))) (btB (2 ^ i) (2 ^ j))

theorem btK_ok : btK = true := by quickRfl

theorem btK_neg : (allLt 22 fun i => allLt 22 fun j =>
    Nat.beq (btB (CFSG.KC.M1F2.vmF 22 pR1 (2 ^ i)) (2 ^ j)) (btB (2 ^ i) (2 ^ j))) = false := by
  decide +kernel

theorem g_pB {k : ℕ} (hk : k < 2) (v : ℕ) :
    censusAct k v = CFSG.KC.M1F2.vmF 22 (if k = 0 then pR1 else pR2) v := by
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · have h := censusAct_pB false v
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact h.symm
  · have h := censusAct_pB true v
    simp only [↓reduceIte] at h
    exact h.symm

theorem bt_basis {k : ℕ} (hk : k < 2) {i j : ℕ} (hi : i < 22) (hj : j < 22) :
    bt (censusAct k (2 ^ i)) (censusAct k (2 ^ j)) = bt (2 ^ i) (2 ^ j) := by
  have h := allLt_true.1 (allLt_true.1 btK_ok i hi) j hj
  rw [Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq] at h
  apply toNat_inj
  rw [← btB_eq, ← btB_eq, g_pB hk, g_pB hk]
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · exact h.1
  · exact h.2

theorem bt_act {k : ℕ} (hk : k < 2) {a b : ℕ} (ha : a < 2 ^ 22) (hb : b < 2 ^ 22) :
    bt (censusAct k a) (censusAct k b) = bt a b := by
  have add2 : ∀ x, ∀ u < 2 ^ 22, ∀ v < 2 ^ 22, (bt x (censusAct k (u ^^^ v))).toNat =
      (bt x (censusAct k u)).toNat ^^^ (bt x (censusAct k v)).toNat := fun x u _ v _ => by
    rw [g_xor hk, bt_xor_right, toNat_xor]
  have add2' : ∀ x, ∀ u < 2 ^ 22, ∀ v < 2 ^ 22, (bt x (u ^^^ v)).toNat =
      (bt x u).toNat ^^^ (bt x v).toNat := fun x u _ v _ => by rw [bt_xor_right, toNat_xor]
  have hj : ∀ j < 22, ∀ a < 2 ^ 22, bt (censusAct k a) (censusAct k (2 ^ j)) = bt a (2 ^ j) := by
    intro j hj a ha
    apply toNat_inj
    refine additive_ext (f := fun a => (bt (censusAct k a) (censusAct k (2 ^ j))).toNat)
      (f' := fun a => (bt a (2 ^ j)).toNat) (fun u _ v _ => ?_) (fun u _ v _ => ?_) ?_ ?_
      (fun i hi => ?_) ha
    · simp only [g_xor hk, bt_xor_left, toNat_xor]
    · simp only [bt_xor_left, toNat_xor]
    · simp only [g_zero hk, bt_comm 0, bt_zero_right]
      rfl
    · simp only [bt_comm 0, bt_zero_right]
      rfl
    · simp only [bt_basis hk hi hj]
  apply toNat_inj
  refine additive_ext (f := fun b => (bt (censusAct k a) (censusAct k b)).toNat)
    (f' := fun b => (bt a b).toNat) (add2 _) (add2' _) ?_ ?_ (fun j hj' => ?_) hb
  · simp only [g_zero hk, bt_zero_right]
    rfl
  · simp only [bt_zero_right]
    rfl
  · simp only [hj j hj' a ha]

@[expose] noncomputable def S (k : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ 22)).filter fun x => Reach censusAct 2 (rootOf k) x

section Orbits

variable (hC : CensusLists)
include hC

theorem mem_S {k : ℕ} (hk : k < 5) {x : ℕ} : x ∈ S k ↔ Reach censusAct 2 (rootOf k) x := by
  rw [S, Finset.mem_filter, Finset.mem_range]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨T, hT, -, hv, -⟩ := census_orbit hC hk
  exact cvalid_lt (hv x ((hT x).1 h)).1

theorem S_valid {k : ℕ} (hk : k < 5) {x : ℕ} (hx : x ∈ S k) : 0 < x ∧ x < 2 ^ 22 := by
  rw [mem_S hC hk] at hx
  obtain ⟨T, hT, -, hv, -⟩ := census_orbit hC hk
  have h := (hv x ((hT x).1 hx)).1
  exact ⟨cvalid_pos h, cvalid_lt h⟩

theorem card_S {k : ℕ} (hk : k < 5) : (S k).card = Inner.sizeOf k := by
  obtain ⟨T, hT, hcard, -, -⟩ := census_orbit hC hk
  have e : S k = T := by
    ext x
    rw [mem_S hC hk, hT]
  rw [e, hcard]

theorem S_disj {j k : ℕ} (hj : j < 5) (hk : k < 5) {x : ℕ} (h1 : x ∈ S j) (h2 : x ∈ S k) : j = k :=
  by_contra fun hne => census_disj hC hj hk hne ((mem_S hC hj).1 h1) ((mem_S hC hk).1 h2)

theorem S_cover {x : ℕ} (h0 : 0 < x) (h1 : x < 2 ^ 22) : ∃ k < 5, x ∈ S k := by
  obtain ⟨k, hk, h⟩ := (innerTab_facts hC).2.2.2 x h0 h1
  exact ⟨k, hk, (mem_S hC hk).2 h⟩

theorem tab_S {k : ℕ} (hk : k < 5) {x : ℕ} (hx : x ∈ S k) : innerTab[x]! = k + 1 :=
  (innerTab_facts hC).2.1 k hk x ((mem_S hC hk).1 hx)

theorem S_closed {k j : ℕ} (hk : k < 5) (hj : j < 2) {x : ℕ} (hx : x ∈ S k) :
    censusAct j x ∈ S k :=
  (mem_S hC hk).2 (.step j hj ((mem_S hC hk).1 hx))

theorem S_inj {k j : ℕ} (hk : k < 5) (hj : j < 2) : ∀ x ∈ S k, ∀ y ∈ S k,
    censusAct j x = censusAct j y → x = y := fun x hx y hy e =>
  censusAct_inj hj (S_valid hC hk hx).2 (S_valid hC hk hy).2 e

theorem S_surj {k j : ℕ} (hk : k < 5) (hj : j < 2) {y : ℕ} (hy : y ∈ S k) :
    ∃ v ∈ S k, censusAct j v = y := by
  obtain ⟨n, hn⟩ := iter_back (fun x hx => S_closed hC hk hj hx) (S_inj hC hk hj) hy
  rw [Function.iterate_succ_apply'] at hn
  exact ⟨_, iter_mem (fun x hx => S_closed hC hk hj hx) hy n, hn⟩

theorem g_mem {k j : ℕ} (hk : k < 5) (hj : j < 2) {x : ℕ} (hx : x < 2 ^ 22) :
    censusAct j x ∈ S k ↔ x ∈ S k := by
  refine ⟨fun h => ?_, S_closed hC hk hj⟩
  obtain ⟨v, hv, e⟩ := S_surj hC hk hj h
  rwa [censusAct_inj hj (S_valid hC hk hv).2 hx e] at hv

end Orbits

@[expose] def Inv (R : ℕ → ℕ → Prop) : Prop :=
  ∀ j < 2, ∀ a v, a < 2 ^ 22 → v < 2 ^ 22 → (R (censusAct j a) (censusAct j v) ↔ R a v)


@[expose] noncomputable def cnt (R : ℕ → ℕ → Prop) (k a : ℕ) : ℕ := ((S k).filter (R a)).card

section Counts

variable (hC : CensusLists) {R : ℕ → ℕ → Prop} (hR : Inv R)
include hC hR

theorem cnt_g {k j a : ℕ} (hk : k < 5) (hj : j < 2) (ha : a < 2 ^ 22) :
    cnt R k (censusAct j a) = cnt R k a := by
  classical
  unfold cnt
  have e : (S k).filter (R (censusAct j a)) = ((S k).filter (R a)).image (censusAct j) := by
    ext y
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hy, hr⟩
      obtain ⟨v, hv, rfl⟩ := S_surj hC hk hj hy
      exact ⟨v, Finset.mem_filter.2 ⟨hv, (hR j hj a v ha (S_valid hC hk hv).2).1 hr⟩, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      rw [Finset.mem_filter] at hv
      exact ⟨S_closed hC hk hj hv.1, (hR j hj a v ha (S_valid hC hk hv.1).2).2 hv.2⟩
  convert congrArg Finset.card e using 1
  exact (Finset.card_image_of_injOn fun x hx y hy e =>
    S_inj hC hk hj x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1 e).symm

theorem cnt_const {k x a : ℕ} (hk : k < 5) (hx : x < 5) (ha : a ∈ S x) :
    cnt R k a = cnt R k (rootOf x) := by
  have h := (mem_S hC hx).1 ha
  clear ha
  induction h with
  | root => rfl
  | @step y j hj hy ih =>
    rw [cnt_g hC hR hk hj (S_valid hC hx ((mem_S hC hx).2 hy)).2, ih]

theorem double (hsym : ∀ a v, R a v ↔ R v a) {x y : ℕ} (hx : x < 5) (hy : y < 5) :
    Inner.sizeOf x * cnt R y (rootOf x) = Inner.sizeOf y * cnt R x (rootOf y) := by
  classical
  have h1 : ∑ a ∈ S x, cnt R y a = Inner.sizeOf x * cnt R y (rootOf x) := by
    rw [Finset.sum_congr rfl fun a ha => cnt_const hC hR hy hx ha, Finset.sum_const, card_S hC hx,
      smul_eq_mul]
  have h2 : ∑ v ∈ S y, cnt R x v = Inner.sizeOf y * cnt R x (rootOf y) := by
    rw [Finset.sum_congr rfl fun v hv => cnt_const hC hR hx hy hv, Finset.sum_const, card_S hC hy,
      smul_eq_mul]
  rw [← h1, ← h2]
  unfold cnt
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun a _ => by
    simp only [hsym a v]

end Counts

theorem card_filter_map (L : List ℕ) (f : ℕ → ℕ) (hnd : (L.map f).Nodup) (P : ℕ → Prop) :
    ((L.map f).toFinset.filter P).card = (L.filter fun a => decide (P (f a))).length := by
  have e : (L.map f).toFinset.filter P = ((L.map f).filter fun x => decide (P x)).toFinset := by
    ext x
    simp [List.mem_filter]
  rw [e, List.toFinset_card_of_nodup (hnd.filter _), List.filter_map, List.length_map]
  rfl

@[expose] def Rc (c a v : ℕ) : Prop := bt a v = false ∧ a ^^^ v ∈ S c

theorem Rc_sym (c a v : ℕ) : Rc c a v ↔ Rc c v a := by
  rw [Rc, Rc, bt_comm, Nat.xor_comm]

theorem Rc_inv (hC : CensusLists) {c : ℕ} (hc : c < 5) : Inv (Rc c) := by
  intro j hj a v ha hv
  rw [Rc, Rc, bt_act hj ha hv, ← g_xor hj, g_mem hC hc hj (Nat.xor_lt_two_pow ha hv)]

@[expose] noncomputable def pairOK (r a e : ℕ) : Bool :=
  if e = 0 then (eV a == r || btB r (eV a) == 1)
  else (walkOK e && eV e == (eV a ^^^ r) && btB r (eV a) == 0)

@[expose] noncomputable def zall (r : ℕ) : List ℕ → List ℕ → Bool
  | a :: L, e :: W => pairOK r a e && zall r L W
  | [], [] => true
  | _, _ => false

@[expose] noncomputable def zcnt (c : ℕ) : List ℕ → List ℕ → ℕ
  | _ :: L, e :: W => (if e ≠ 0 ∧ eRec e = c then 1 else 0) + zcnt c L W
  | _, _ => 0

theorem pairOK_spec (hC : CensusLists) {r a e c : ℕ} (hc : c < 5) (h : pairOK r a e = true) :
    Rc c r (eV a) ↔ (e ≠ 0 ∧ eRec e = c) := by
  unfold pairOK at h
  by_cases he : e = 0
  · rw [ite_eq_left he, Bool.or_eq_true, beq_iff_eq, beq_iff_eq, btB_eq] at h
    simp only [he, ne_eq, not_true_eq_false, false_and, iff_false, Rc, not_and]
    intro hb hm
    rcases h with h | h
    · rw [h, Nat.xor_self] at hm
      exact absurd (S_valid hC hc hm).1 (Nat.lt_irrefl 0)
    · rw [hb] at h
      exact absurd h (by decide)
  · rw [ite_eq_right he, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, btB_eq] at h
    obtain ⟨⟨hw, hv⟩, hb⟩ := h
    have hk : eRec e < 5 := by
      simp only [walkOK, Bool.and_eq_true, Nat.blt_eq] at hw
      exact hw.1
    have hmem : eV e ∈ S (eRec e) := by
      rw [mem_S hC hk]
      simp only [walkOK, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hw
      rw [← hw.2, eWalk, rootsL_eq _ hk]
      exact reach_walk _ _ _
    have hb' : bt r (eV a) = false := toNat_inj hb
    rw [hv, Nat.xor_comm] at hmem
    simp only [Rc, hb', true_and, ne_eq, he, not_false_eq_true]
    exact ⟨fun h => (S_disj hC hk hc hmem h), fun h => h ▸ hmem⟩

theorem zcnt_eq (hC : CensusLists) {r c : ℕ} (hc : c < 5) :
    ∀ (L W : List ℕ), zall r L W = true →
      zcnt c L W = (L.filter fun a => decide (Rc c r (eV a))).length
  | a :: L, e :: W, h => by
    classical
    rw [zall, Bool.and_eq_true] at h
    rw [zcnt, zcnt_eq hC hc L W h.2, List.filter_cons]
    have hs := pairOK_spec hC hc h.1
    by_cases hr : Rc c r (eV a)
    · rw [ite_eq_left (hs.1 hr), ite_eq_left (decide_eq_true hr), List.length_cons]
      omega
    · rw [ite_eq_right (fun h' => hr (hs.2 h')), ite_eq_right (by simpa using hr)]
      omega
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (by simp [zall])
  | _ :: _, [], h => absurd h (by simp [zall])

end CertificateChecks.KernelBM.CTIB.Hist

end
