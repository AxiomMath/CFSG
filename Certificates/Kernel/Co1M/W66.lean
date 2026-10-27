module

public import Certificates.Kernel.Co1M.K66T3
public import Certificates.Kernel.Co1M.K66T4
public import Certificates.Kernel.Co1M.K66C
public import Certificates.Kernel.Co1M.K78L
public import Certificates.Kernel.Co1M.Orb98280
public import Certificates.Kernel.Co1Cover.Bridge
public import CFSG.Sporadic.Co1.Module.CoTwoAutLitInputs
public import CFSG.Certificates.Kernel.SortTreeSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Monster.GMS.Leech.Linear
public import CFSG.Sporadic.Co1.Module.CoTwoData
public import CFSG.Sporadic.Co1.Module.CoTwoPerfect
public import CFSG.Sporadic.Co1.Module.OddFacts
public import Certificates.Data.CFSGNative.Co1.CoTwoAutData
public import Certificates.Data.CFSGNative.Co1.CoTwoAutOrbit
public import Certificates.Kernel.Co1B.Tri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KD.Co1M CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.InvFam CFSG.KC.SortTree
  CFSG.KC.CoTwoAut CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.Module.CoTwoAut
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative

@[expose] noncomputable def w66 : AutW where
  R0 := R0v66
  R1 := R1v66
  W3 := [W3a66, W3b66]
  W4 := [W4a66, W4b66]
  G3 := G366
  GT3 := GT366
  G4 := G466
  GT4 := GT466
  T3 := [⟨recT t30L66 6 40, 5, 10, 64, 9⟩, ⟨recT t31L66 6 47, 6, 16, 64, 593⟩,
    ⟨recT t32L66 6 47, 6, 16, 64, 760⟩, ⟨recT t33L66 6 45, 6, 14, 64, 175⟩]
  Rt3 := Rt366
  Sz3 := Sz366
  P3 := recT p3L66 6 20
  T4 := [⟨recT t40L66 6 46, 5, 16, 64, 759⟩, ⟨recT t41L66 6 46, 5, 16, 64, 768⟩,
    ⟨recT t42L66 6 40, 5, 10, 64, 9⟩]
  Rt4 := Rt466
  Sz4 := Sz466
  P4 := recT p4L66 6 20

theorem c66_slices {act : Nat → Nat → Nat} {ng root wv n : Nat} {T : STree} {Q : Nat}
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

theorem covAt_congr {Ts : List (Nat → Nat)} {szs : List Nat} {P pt pt' : Nat → Nat} {n i : Nat}
    (h : pt i = pt' i) : covAt Ts szs P pt n i = covAt Ts szs P pt' n i := by
  unfold covAt
  rw [h]

theorem c66_cov {Ts : List (Nat → Nat)} {szs : List Nat} {P : Nat → Nat}
    (h : ∀ s < 24, covK Ts szs P (CFSG.KC.VecK.lk CertificateChecks.KernelVec.Co1.Pt 32) 98280
      (Nat.mul s 4096) 4096 = true) :
    ∀ i < 98280, covAt Ts szs P (fun i => (orbitOf 2 98280).pts[i]!) 98280 i = true := by
  intro i hi
  have hs : i / 4096 < 24 := by omega
  have hr : i % 4096 < 4096 := Nat.mod_lt _ (by norm_num)
  have h1 := (allN_iff _ _).1 (h _ hs) _ hr
  have e : Nat.add (Nat.mul (i / 4096) 4096) (i % 4096) = i := by
    change i / 4096 * 4096 + i % 4096 = i
    omega
  rw [e] at h1
  have ep : (fun i => (orbitOf 2 98280).pts[i]!) i =
      CFSG.KC.VecK.lk CertificateChecks.KernelVec.Co1.Pt 32 i := cm_orb_twin.2.1 i hi
  rw [covAt_congr ep]
  exact h1

theorem labA_eq : labA = labK78 := by
  funext w
  unfold labA Pairs.tyLab labK78
  have e : Pairs.inPts (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 w =
      CFSG.KC.Co1M.orbMemK 98280 (CFSG.KC.VecK.lk CertificateChecks.KernelVec.Co1.S 32) 17 w :=
    cm_orb_inPts w
  rw [e]

theorem w66_labs : (Nat.beq (labK78 14717452) 2 && Nat.beq (labK78 10075731) 1) = true := by
  quickRfl

theorem w66_ex : (bilN (transposeRows 24 f0Rows) 1336 code4 ||
    labK78 (1336 ^^^ code4) == 3) = true := by
  quickRfl

theorem w66_seeds : andB (Nat.beq R0v66 CertificateChecks.KernelCo1Cover.R0)
    (Nat.beq R1v66 CertificateChecks.KernelCo1Cover.R1) = true := by quickRfl

theorem beq66 {a b : Nat} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem w66_f3 : ForestOK w66.GT3 w66.T3 w66.Rt3 w66.Sz3 w66.P3 546 ex3 where
  lenT := rfl
  lenR := rfl
  roots := by quickRfl
  trees := fun j hj => by
    have hj' : j < 4 := hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · exact c66_slices (Q := 1) (by decide) (by decide) T30x66.all
    · exact c66_slices (Q := 6) (by decide) (by decide) T31x66.all
    · exact c66_slices (Q := 8) (by decide) (by decide) T32x66.all
    · exact c66_slices (Q := 2) (by decide) (by decide) T33x66.all
  big := fun j hj => by
    have hj' : j < 4 := hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
      exact Or.inl (by decide)
  cov := c66_cov C3x66.all

theorem w66_f4 : ForestOK w66.GT4 w66.T4 w66.Rt4 w66.Sz4 w66.P4 553 ex4 where
  lenT := rfl
  lenR := rfl
  roots := by quickRfl
  trees := fun j hj => by
    have hj' : j < 3 := hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · exact c66_slices (Q := 8) (by decide) (by decide) T40x66.all
    · exact c66_slices (Q := 8) (by decide) (by decide) T41x66.all
    · exact c66_slices (Q := 1) (by decide) (by decide) T42x66.all
  big := fun j hj => by
    have hj' : j < 3 := hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · exact Or.inl (by decide)
    · exact Or.inl (by decide)
    · refine Or.inr ?_
      unfold ex4
      rw [labA_eq]
      exact w66_ex
  cov := c66_cov C4x66.all

theorem ok66 : AutOK w66 := by
  obtain ⟨g1, g2⟩ := andB_true_iff.1 k66_gens
  obtain ⟨g2, g3⟩ := andB_true_iff.1 g2
  obtain ⟨g3, g4⟩ := andB_true_iff.1 g3
  obtain ⟨t3, t4⟩ := andB_true_iff.1 k66_tr
  obtain ⟨f3, f4⟩ := andB_true_iff.1 k66_fix
  have hl := w66_labs
  simp only [Bool.and_eq_true] at hl
  exact {
    rA := by
      rw [CertificateChecks.KernelCo1Cover.rowsA_eq, ← beq66 (andB_true_iff.1 w66_seeds).1]
      rfl
    rB := by
      rw [CertificateChecks.KernelCo1Cover.rowsB_eq, ← beq66 (andB_true_iff.1 w66_seeds).2]
      rfl
    lenW := ⟨rfl, rfl, rfl, rfl⟩
    letters := by decide
    words3 := fun l hl => by
      rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
      · exact beq66 g1
      · exact beq66 g2
    words4 := fun l hl => by
      rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
      · exact beq66 g3
      · exact beq66 g4
    tr3 := fun l hl => beq66 ((allN_iff _ _).1 t3 l hl)
    tr4 := fun l hl => beq66 ((allN_iff _ _).1 t4 l hl)
    fix3 := fun l hl => beq66 ((allN_iff _ _).1 f3 l hl)
    fix4 := fun l hl => beq66 ((allN_iff _ _).1 f4 l hl)
    f3 := w66_f3
    f4 := w66_f4
    l3 := by rw [labA_eq]; exact beq66 hl.1
    l4 := by rw [labA_eq]; exact beq66 hl.2 }

end CertificateChecks.KernelCo1M

end
