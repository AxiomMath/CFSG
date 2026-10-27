module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi22Tests
public import CFSG.Certificates.Kernel.Census.RootConjSound
public import Certificates.Data.Kernel.Census.PackedRootBit
import Certificates.Kernel.Census.Fi22Roots
import Certificates.Kernel.Sporadic.Fi22.X2069Final
import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Census.Sound
import Certificates.Kernel.Census.Fi22RDefs
import Certificates.Kernel.Census.Fi22PkU
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2Pair
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2Roots
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

set_option maxRecDepth 400000

namespace Certificates

open CertificateChecks

open CFSG.KC.Census CFSG.KS CFSG.ComponentClassification.RankTwoSporadic.Fi22
open CertificateChecks.KernelCensus.Fi22K

theorem fi22InXK_sound (P : Nat) (h : inXK P = true) : fi22InPT (unpackP 3510 12 P) = true := by
  unfold inXK at h
  obtain ⟨h0, h12⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hr, hs⟩ := (bAnd_iff _ _).1 h12
  exact Raw.siftK_soundR KernelSpor.Fi22X.bindsP KernelSpor.Fi22X.permP KernelSpor.Fi22PC.hl rfl
    (Nat.eq_of_beq_eq_true h0) hr hs

theorem fi22UK_eq : Nat.beq fi22UK KernelSpor.Fi22X.GO = true := by quickRfl

theorem fi22UK_canon : canon1 3510 12 fi22UK = true := by quickRfl

theorem fi22InWK_sound (P : Nat) (h : inWK P = true) : fi22InRT (unpackP 3510 12 P) = true := by
  unfold fi22InRT
  cases hx : inXK P with
  | true => rw [fi22InXK_sound P hx, Bool.true_or]
  | false =>
    unfold inWK at h
    rw [hx] at h
    have hu := fi22InXK_sound _ h
    have hU : unpackP 3510 12 KernelSpor.Fi22X.GO = CFSG.Monster.B.Fischer.fi22GraphOuterArr :=
      KernelSpor.Fi22X.go_eq.symm
    rw [unpackP_pc (by norm_num) (by norm_num) fi22UK_canon, Nat.eq_of_beq_eq_true fi22UK_eq,
      hU] at hu
    rw [hu, Bool.or_true]

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.Fi22 CFSG.KC.Census in
public theorem certificate15010 : ∃ (inX inW : ℕ → Bool) (ks : List ℕ) (rs : List RootConjP),
    (∀ P, inX P = true → fi22InPT (unpackP 3510 12 P) = true) ∧
    (∀ P, inW P = true → fi22InRT (unpackP 3510 12 P) = true) ∧
    rs.all (canonR 3510 12) = true ∧
    prootsConjOKB 3510 12 fi22PS inX inW false 2 ks rs = true ∧
    prootsConjOKB 3510 12 fi22PS inX inW true 1 ks rs = true ∧
    rs.map (fun r => pfix 3510 12 r.x) = [694, 182, 54] ∧
    rs.map (fun r => r.xs.length) = [17, 18, 17] :=
  ⟨inXK, inWK, fi22Ks, fi22RootsC, fi22InXK_sound, fi22InWK_sound, canon_ok, rootsII_ok,
    roots17_ok, fixes, lens⟩

end Certificates
