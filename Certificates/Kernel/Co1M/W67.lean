module

public import Certificates.Kernel.Co1M.K67T
public import Certificates.Kernel.Co1Cover.Bridge
public import CFSG.Sporadic.Co1.Module.CoTwoLitInputs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Sporadic.Co1.Module.InvFam
public import Certificates.Kernel.Co1B.Tri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KD.Co1M CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.InvFam CFSG.KC.SortTree
  CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.Module.CoTwo CFSG.Sporadic.SmallF2.Native

@[expose] noncomputable def w67 : CoTwoW where
  RA := RA67
  RTA := RTA67
  RS := RS67
  RTS := RTS67
  LV := LV67
  SZ := SZ67
  T := [⟨recT l0L67 6 40, 3, 9, 64, 5⟩, ⟨recT l1L67 6 38, 3, 7, 64, 2⟩,
    ⟨recT l2L67 6 36, 3, 5, 64, 1⟩, ⟨recT l3L67 6 29, 1, 1, 64, 1⟩,
    ⟨recT l4L67 6 34, 2, 5, 64, 1⟩, ⟨recT l5L67 6 29, 1, 2, 64, 1⟩,
    ⟨recT l6L67 6 27, 1, 1, 64, 1⟩, ⟨recT l7L67 6 29, 2, 2, 64, 1⟩]
  TY := ⟨recT tyL67 6 46, 4, 16, 64, 736⟩

theorem c67_beq {a b : Nat} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem c67_one {act : Nat → Nat → Nat} {ng root wv n : Nat} {T : STree} (hcov : n ≤ T.C * T.B)
    (h : chunksK act ng root T.tab n wv T.wl T.wp T.B 0 T.C = true) : T.OK act ng root wv n :=
  ⟨hcov, fun c hc => by simpa using (allN_iff _ _).1 h c hc⟩

theorem c67_slices {act : Nat → Nat → Nat} {ng root wv n : Nat} {T : STree} {Q : Nat}
    (hC : T.C ≤ Q * 100) (hcov : n ≤ T.C * T.B)
    (h : ∀ q < Q, chunksK act ng root T.tab n wv T.wl T.wp T.B (Nat.mul q 100) 100 = true) :
    T.OK act ng root wv n := by
  refine ⟨hcov, fun c hc => ?_⟩
  have hq : c / 100 < Q := by omega
  have hr : c % 100 < 100 := Nat.mod_lt _ (by norm_num)
  have h1 := (allN_iff _ _).1 (h _ hq) _ hr
  have e : Nat.add (Nat.mul (c / 100) 100) (c % 100) = c := by
    change c / 100 * 100 + c % 100 = c
    omega
  rwa [e] at h1

theorem w67_progA : progK 24 RA67 progA 2 = true := by quickRfl

theorem w67_progS : progK 24 RS67 progS 2 = true := by quickRfl

theorem w67_small : andB (Nat.beq (getL 0 RA67 0) CertificateChecks.KernelCo1Cover.R0)
    (andB (Nat.beq (getL 0 RA67 1) CertificateChecks.KernelCo1Cover.R1)
    (andB (Nat.beq (getL 0 RS67 0) (getL 0 RA67 13)) (Nat.beq (getL 0 RS67 1) (getL 0 RA67 18))))
    = true := by quickRfl

theorem w67_tr : andB (allN (lenL RA67) (fun i => Nat.beq (trK 24 (getL 0 RA67 i)) (getL 0 RTA67 i)))
    (allN (lenL RS67) (fun i => Nat.beq (trK 24 (getL 0 RS67 i)) (getL 0 RTS67 i))) = true := by
  quickRfl

theorem w67_regs : andB (fixAllK RTA67 [9, 10, 14, 15] [2, y₀code])
    (andB (fixAllK RTA67 [19, 20] [2]) (andB (fixAllK RTA67 [13, 18] [y₀code])
    (andB (invPairsK RA67 [9, 10, 14, 15, 19, 20] [11, 12, 16, 17, 21, 22])
    (andB (commK RA67 13 11 12 9 10) (andB (commK RA67 18 16 17 14 15)
      (commK RA67 23 21 22 19 20)))))) = true := by quickRfl

theorem w67_lv : andB (bndK (lenL RS67) LV67.flatten) (andB (bndK (2 ^ 24) baseS)
    (andB (fixAllK RTS67 (LV67.getD 0 []) (baseS.take 0)) (andB (fixAllK RTS67 (LV67.getD 1 []) (baseS.take 1))
    (andB (fixAllK RTS67 (LV67.getD 2 []) (baseS.take 2)) (andB (fixAllK RTS67 (LV67.getD 3 []) (baseS.take 3))
    (andB (fixAllK RTS67 (LV67.getD 4 []) (baseS.take 4)) (andB (fixAllK RTS67 (LV67.getD 5 []) (baseS.take 5))
    (andB (fixAllK RTS67 (LV67.getD 6 []) (baseS.take 6))
      (fixAllK RTS67 (LV67.getD 7 []) (baseS.take 7)))))))))) = true := by quickRfl

theorem ok67 : CoTwoOK w67 := by
  obtain ⟨a0, a1⟩ := andB_true_iff.1 w67_small
  obtain ⟨a1, s0⟩ := andB_true_iff.1 a1
  obtain ⟨s0, s1⟩ := andB_true_iff.1 s0
  obtain ⟨tA, tS⟩ := andB_true_iff.1 w67_tr
  obtain ⟨fP, r⟩ := andB_true_iff.1 w67_regs
  obtain ⟨fE, r⟩ := andB_true_iff.1 r
  obtain ⟨fY, r⟩ := andB_true_iff.1 r
  obtain ⟨iv, cm⟩ := andB_true_iff.1 r
  obtain ⟨ix, l⟩ := andB_true_iff.1 w67_lv
  obtain ⟨bs, l⟩ := andB_true_iff.1 l
  obtain ⟨f0, l⟩ := andB_true_iff.1 l
  obtain ⟨f1, l⟩ := andB_true_iff.1 l
  obtain ⟨f2, l⟩ := andB_true_iff.1 l
  obtain ⟨f3, l⟩ := andB_true_iff.1 l
  obtain ⟨f4, l⟩ := andB_true_iff.1 l
  obtain ⟨f5, l⟩ := andB_true_iff.1 l
  obtain ⟨f6, f7⟩ := andB_true_iff.1 l
  exact {
    rA := by
      rw [CertificateChecks.KernelCo1Cover.rowsA_eq, ← c67_beq a0]
      rfl
    rB := by
      rw [CertificateChecks.KernelCo1Cover.rowsB_eq, ← c67_beq a1]
      rfl
    progA := w67_progA
    s0 := c67_beq s0
    s1 := c67_beq s1
    progS := w67_progS
    trA := tA
    trS := tS
    fixP := fP
    fixE := fE
    fixY := fY
    inv := iv
    comm := cm
    lenLV := rfl
    idx := ix
    base := bs
    fix := fun j hj => by
      have hj' : j < 8 := hj
      interval_cases j
      · exact f0
      · exact f1
      · exact f2
      · exact f3
      · exact f4
      · exact f5
      · exact f6
      · exact f7
    tree := fun j hj => by
      have hj' : j < 8 := hj
      interval_cases j
      · exact c67_one (by decide) k67_l0
      · exact c67_one (by decide) k67_l1
      · exact c67_one (by decide) k67_l2
      · exact c67_one (by decide) k67_l3
      · exact c67_one (by decide) k67_l4
      · exact c67_one (by decide) k67_l5
      · exact c67_one (by decide) k67_l6
      · exact c67_one (by decide) k67_l7
    prod := by decide
    ty := c67_slices (Q := 8) (by decide) (by decide) TYx67.all }

end CertificateChecks.KernelCo1M

end
