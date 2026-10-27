module

public import Certificates.Kernel.Co1M.K78A
public import Certificates.Kernel.Co1M.K78B
public import Certificates.Kernel.Co1M.K78C
public import Certificates.Kernel.Co1M.K78D
public import Certificates.Kernel.Co1M.K78E
public import Certificates.Kernel.Co1M.K78L
public import Certificates.Kernel.Co1M.Orb98280
public import Certificates.Kernel.Co1Cover.Bridge
public import CFSG.Sporadic.Co1.Module.U6OddLitInputs
public import CFSG.Certificates.Kernel.SortTreeSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Monster.GMS.U6OddSylow
public import CFSG.Sporadic.Co1.Module.U6OddForest
public import CFSG.Sporadic.Co1.Module.U6OddProg
public import CFSG.Sporadic.Co1.Module.U6OddTuple

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KD.Co1M CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.InvFam CFSG.KC.SortTree
  CFSG.KC.U6Odd CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.Module.U6Odd CFSG.Sporadic.Co1.U6OddNative
  CFSG.Sporadic.SmallF2.Native

@[expose] noncomputable def w78 : U6W where
  R := R78
  RT := RT78
  X := X78
  w11 := ⟨F1178, Y1178, W1178, PV1178, LB1178,
    [⟨recT t11aL78 6 46, 4, 15, 64, 324⟩, ⟨recT t11bL78 6 40, 3, 10, 64, 11⟩]⟩
  w7 := ⟨F778, Y778, W778, PV778, LB778,
    [⟨recT t7aL78 6 46, 4, 15, 64, 324⟩, ⟨recT t7bL78 6 42, 3, 12, 64, 42⟩,
      ⟨recT t7cL78 6 32, 2, 3, 64, 1⟩]⟩
  w5 := ⟨F578, Y578, W578, PV578, LB578,
    [⟨recT t5aL78 6 46, 4, 15, 64, 390⟩, ⟨recT t5bL78 6 43, 3, 13, 64, 96⟩,
      ⟨recT t5cL78 6 32, 2, 3, 64, 1⟩]⟩
  cl11 := ⟨recT cl11L78 5 587, 4, 6, 32, 2⟩
  n5 := ⟨recT n5L78 5 588, 4, 7, 32, 4⟩
  s0 := ⟨recT s0L78 5 592, 4, 10, 32, 23⟩
  e0 := recT e0L78 6 30
  c0 := recT c0L78 5 60

theorem c78_spec {act : Nat → Nat → Nat} {ng root : Nat} {rec : Nat → Nat}
    {n wv wl wp B lo cnt : Nat} (h : chunksK act ng root rec n wv wl wp B lo cnt = true) :
    ∀ j < cnt, chunkOK act ng (fun _ => true) root rec n wv wl wp B (lo + j) = true :=
  (allN_iff _ _).1 h

theorem c78_one {act : Nat → Nat → Nat} {ng root wv n : Nat} {T : STree} (hcov : n ≤ T.C * T.B)
    (h : chunksK act ng root T.tab n wv T.wl T.wp T.B 0 T.C = true) : T.OK act ng root wv n :=
  ⟨hcov, fun c hc => by simpa using c78_spec h c hc⟩

theorem c78_six {act : Nat → Nat → Nat} {ng root wv n m : Nat} {T : STree} (hC : T.C = 6 * m)
    (hcov : n ≤ T.C * T.B)
    (h0 : chunksK act ng root T.tab n wv T.wl T.wp T.B 0 m = true)
    (h1 : chunksK act ng root T.tab n wv T.wl T.wp T.B m m = true)
    (h2 : chunksK act ng root T.tab n wv T.wl T.wp T.B (2 * m) m = true)
    (h3 : chunksK act ng root T.tab n wv T.wl T.wp T.B (3 * m) m = true)
    (h4 : chunksK act ng root T.tab n wv T.wl T.wp T.B (4 * m) m = true)
    (h5 : chunksK act ng root T.tab n wv T.wl T.wp T.B (5 * m) m = true) :
    T.OK act ng root wv n := by
  refine ⟨hcov, fun c hc => ?_⟩
  rw [hC] at hc
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · omega
    · exact h
  have hq : c / m < 6 := (Nat.div_lt_iff_lt_mul hm).2 (by linarith)
  have hr : c % m < m := Nat.mod_lt _ hm
  have e : c = c / m * m + c % m := (Nat.div_add_mod' c m).symm
  obtain ⟨q, hqd⟩ : ∃ q, q = c / m := ⟨_, rfl⟩
  rw [← hqd] at hq e
  have key : ∀ (lo : ℕ), chunksK act ng root T.tab n wv T.wl T.wp T.B lo m = true → lo + c % m = c →
      chunkOK act ng (fun _ => true) root T.tab n wv T.wl T.wp T.B c = true := by
    intro lo h hlo
    have := c78_spec h _ hr
    rwa [hlo] at this
  interval_cases q
  · exact key 0 h0 (by omega)
  · exact key m h1 (by omega)
  · exact key (2 * m) h2 (by omega)
  · exact key (3 * m) h3 (by omega)
  · exact key (4 * m) h4 (by omega)
  · exact key (5 * m) h5 (by omega)

theorem c78_two {act : Nat → Nat → Nat} {ng root wv n m : Nat} {T : STree} (hC : T.C = 2 * m)
    (hcov : n ≤ T.C * T.B)
    (h0 : chunksK act ng root T.tab n wv T.wl T.wp T.B 0 m = true)
    (h1 : chunksK act ng root T.tab n wv T.wl T.wp T.B m m = true) : T.OK act ng root wv n := by
  refine ⟨hcov, fun c hc => ?_⟩
  rw [hC] at hc
  by_cases h : c < m
  · simpa using c78_spec h0 c h
  · have hc' : m + (c - m) = c := by omega
    have := c78_spec h1 (c - m) (by omega)
    rwa [hc'] at this

theorem lab78 : labU6 = labK78 := by
  funext w
  unfold labU6 Pairs.tyLab labK78
  have e : Pairs.inPts (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 w =
      CFSG.KC.Co1M.orbMemK 98280 (CFSG.KC.VecK.lk CertificateChecks.KernelVec.Co1.S 32) 17 w :=
    cm_orb_inPts w
  rw [e]

theorem prime11 : Nat.Prime data11.p := by
  change Nat.Prime 11
  norm_num

theorem prime7 : Nat.Prime data7.p := by
  change Nat.Prime 7
  norm_num

theorem prime5 : Nat.Prime data5.p := by
  change Nat.Prime 5
  norm_num

theorem beq_of {a b : Nat} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem notB_ne {a b : Nat} (h : notB (Nat.beq a b) = true) : a ≠ b := fun e => by
  rw [e, Nat.beq_refl] at h
  exact Bool.false_ne_true h

theorem w78_p11 : PrimeOK w78 data11 w78.w11 := by
  obtain ⟨g1, g2⟩ := andB_true_iff.1 k78_g11
  obtain ⟨g2, g3⟩ := andB_true_iff.1 g2
  obtain ⟨f1, f2⟩ := andB_true_iff.1 k78_fix11
  exact {
    lenLv := rfl
    lenSz := rfl
    idx := by quickRfl
    base := by quickRfl
    fix := fun i hi => by
      have hi' : i < 2 := hi
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · exact (andB_true_iff.1 k78_lv11).1
      · exact (andB_true_iff.1 k78_lv11).2
    tree := fun i hi => by
      have hi' : i < 2 := hi
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · exact c78_six (m := 54) rfl (by decide) k78_t11a_0 k78_t11a_1 k78_t11a_2 k78_t11a_3
          k78_t11a_4 k78_t11a_5
      · exact c78_one (by decide) k78_t11b
    prod := by decide
    prime := prime11
    gpow := beq_of g1
    gne := notB_ne g2
    gcanon := beq_of (by quickRfl)
    gfix := g3
    fixc := f1
    fixl := f2
    shape := rfl
    blt := by quickRfl
    bfix := by quickRfl
    labT := by rw [lab78]; exact k78_labT11
    tup := k78_tup11 }

theorem w78_p7 : PrimeOK w78 data7 w78.w7 := by
  obtain ⟨g1, g2⟩ := andB_true_iff.1 k78_g7
  obtain ⟨g2, g3⟩ := andB_true_iff.1 g2
  obtain ⟨f1, f2⟩ := andB_true_iff.1 k78_fix7
  obtain ⟨l0, l1⟩ := andB_true_iff.1 k78_lv7
  obtain ⟨l1, l2⟩ := andB_true_iff.1 l1
  exact {
    lenLv := rfl
    lenSz := rfl
    idx := by quickRfl
    base := by quickRfl
    fix := fun i hi => by
      have hi' : i < 3 := hi
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
      · exact l0
      · exact l1
      · exact l2
    tree := fun i hi => by
      have hi' : i < 3 := hi
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
      · exact c78_six (m := 54) rfl (by decide) k78_t7a_0 k78_t7a_1 k78_t7a_2 k78_t7a_3
          k78_t7a_4 k78_t7a_5
      · exact c78_one (by decide) k78_t7b
      · exact c78_one (by decide) k78_t7c
    prod := by decide
    prime := prime7
    gpow := beq_of g1
    gne := notB_ne g2
    gcanon := beq_of (by quickRfl)
    gfix := g3
    fixc := f1
    fixl := f2
    shape := rfl
    blt := by quickRfl
    bfix := by quickRfl
    labT := by rw [lab78]; exact k78_labT7
    tup := k78_tup7 }

theorem w78_p5 : PrimeOK w78 data5 w78.w5 := by
  obtain ⟨g1, g2⟩ := andB_true_iff.1 k78_g5
  obtain ⟨g2, g3⟩ := andB_true_iff.1 g2
  obtain ⟨f1, f2⟩ := andB_true_iff.1 k78_fix5
  obtain ⟨l0, l1⟩ := andB_true_iff.1 k78_lv5
  obtain ⟨l1, l2⟩ := andB_true_iff.1 l1
  exact {
    lenLv := rfl
    lenSz := rfl
    idx := by quickRfl
    base := by quickRfl
    fix := fun i hi => by
      have hi' : i < 3 := hi
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
      · exact l0
      · exact l1
      · exact l2
    tree := fun i hi => by
      have hi' : i < 3 := hi
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
      · exact c78_six (m := 65) rfl (by decide) k78_t5a_0 k78_t5a_1 k78_t5a_2 k78_t5a_3
          k78_t5a_4 k78_t5a_5
      · exact c78_two (m := 48) rfl (by decide) k78_t5b_0 k78_t5b_1
      · exact c78_one (by decide) k78_t5c
    prod := by decide
    prime := prime5
    gpow := beq_of g1
    gne := notB_ne g2
    gcanon := beq_of (by quickRfl)
    gfix := g3
    fixc := f1
    fixl := f2
    shape := rfl
    blt := by quickRfl
    bfix := by quickRfl
    labT := by rw [lab78]; exact k78_labT5
    tup := k78_tup5 }

theorem w78_prog : progK 24 w78.R prog 2 = true := by quickRfl

theorem w78_seeds : andB (Nat.beq (w78.reg 0) CertificateChecks.KernelCo1Cover.R0)
    (Nat.beq (w78.reg 1) CertificateChecks.KernelCo1Cover.R1) = true := by quickRfl

theorem ok78 : U6OK w78 := by
  obtain ⟨c1, c2⟩ := andB_true_iff.1 k78_cl
  obtain ⟨c2, c3⟩ := andB_true_iff.1 c2
  obtain ⟨n1, n2⟩ := andB_true_iff.1 k78_n
  obtain ⟨s1, s2⟩ := andB_true_iff.1 k78_s
  have hl := k78_lab
  simp only [Bool.and_eq_true] at hl
  exact {
    rA := by
      rw [CertificateChecks.KernelCo1Cover.rowsA_eq, ← beq_of (andB_true_iff.1 w78_seeds).1]
    rB := by
      rw [CertificateChecks.KernelCo1Cover.rowsB_eq, ← beq_of (andB_true_iff.1 w78_seeds).2]
    prog := w78_prog
    tr := k78_tr
    p11 := w78_p11
    p7 := w78_p7
    p5 := w78_p5
    clIdx := by quickRfl
    clFix := c1
    clInv := c2
    clLen := rfl
    clCanon := beq_of c3
    cl := c78_one (by decide) k78_clT
    nIdx := by quickRfl
    nLen := rfl
    nFix := n1
    nNorm := n2
    nT := c78_one (by decide) k78_nT
    sIdx := by quickRfl
    sLen := rfl
    sFix := s1
    sOrd := s2
    sT := c78_one (by decide) k78_sT
    sC := k78_sC
    sW := k78_sW
    sB := ble_iff.1 k78_sB
    l2 := by rw [lab78]; exact beq_of hl.1
    l12 := by rw [lab78]; exact beq_of hl.2 }

end CertificateChecks.KernelCo1M

end
