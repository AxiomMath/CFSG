module

public import Certificates.Kernel.Co1M.Orb98280
public import Certificates.Kernel.LocalComp.BlockGen
public import CFSG.Monster.GMS.ASegConnCo1Inputs
import CFSG.Certificates.Kernel.Common.HexTree
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Monster.GMS.Leech.Linear
public import CFSG.Sporadic.Co1.Module.OddFacts
public import CFSG.Sporadic.Co1.Module.Pairs
public import Certificates.Certificate10073Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M.Diam

open CFSG.KLie.CT CFSG.KC.Co1M CFSG.KC.VecK CertificateChecks.KernelVec.Co1

@[expose] def WText : String := include_str "Diam10028/wit.hex"

@[expose] noncomputable def WT : Nat → Nat := by hex_tree WText 417792 8471227474054886659 272

@[expose] noncomputable def W (p : Nat) : Nat := fget (WT (Nat.shiftRight p 6)) (Nat.land p 63) 17

@[expose] noncomputable def P (i : Nat) : Nat := lk Pt 32 i

@[expose] noncomputable def M (w : Nat) : Bool := orbMemK 98280 (lk S 32) 17 w

@[expose] noncomputable def diamAt (p : Nat) : Bool :=
  orB (M (Nat.xor (P 0) (P p))) (andB (Nat.blt (W p) 98280)
    (andB (M (Nat.xor (P 0) (P (W p)))) (M (Nat.xor (P p) (P (W p))))))

theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

open CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.Module.Pairs
  CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Monster.GMS.ASegConn in
theorem diam_ok (h : ∀ p < 98280, diamAt p = true) : diamCheck = true := by
  have hget : ∀ i < 98280, (orbitOf 2 98280).pts[i]! = P i := CertificateChecks.KernelCo1M.cm_orb_twin.2.1
  have hin : ∀ w, inPts (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 w = M w :=
    fun w => CertificateChecks.KernelCo1M.cm_orb_inPts w
  unfold diamCheck diamCheckT
  simp only [hin]
  rw [List.all_eq_true]
  intro p hp
  rw [List.mem_range] at hp
  have hd := h p hp
  unfold diamAt at hd
  rw [orB_eq, Bool.or_eq_true] at hd
  rw [Bool.or_eq_true, hget 0 (by decide), hget p hp]
  rcases hd with hd | hd
  · exact Or.inl hd
  · right
    rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq] at hd
    obtain ⟨hq, h1, h2⟩ := hd
    rw [List.any_eq_true]
    refine ⟨P (W p), ?_, h2⟩
    rw [List.mem_map]
    refine ⟨W p, ?_, hget _ hq⟩
    rw [List.mem_filter, List.mem_range, hget _ hq]
    exact ⟨hq, h1⟩

end CertificateChecks.KernelCo1M.Diam

end
