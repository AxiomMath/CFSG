module

public import CFSG.Certificates.Kernel.E27Orth.Glue
public import Certificates.Kernel.E27Orth.O10m

public section

namespace CertificateChecks.KernelE27Orth.O10m

open CFSG.KC.Misc.Spec CFSG.KD.E27Orth Subgroup Matrix CFSG.Assembly.LowTwoRank

theorem o10m131005_form : ∀ a b, pkMat 10 U (eMc 4 a) (eMc 4 b) = umM 4 a b := by decide +kernel

theorem o10m131005_quad (v : Fin (5 - 1) ⊕ Fin (5 - 1) ⊕ Fin 2 → ZMod 2) :
    StatedQuadMinus 5 (ZMod 2) 1 1 v = qf (pkMat 10 U) (v ∘ (eMc 4).symm) :=
  quadMinus_eq (eMc 4) U o10m131005_form v

theorem o10m131005_fact :
    ∃ S : Subgroup ↥(StatedOmega (StatedQuadMinus 5 (ZMod 2) 1 1)), Nat.card S = 729 ∧
      ∀ s ∈ S, orderOf s = 3 → 81 ∣ Nat.card ↥(S ⊓ centralizer
        ({s} : Set ↥(StatedOmega (StatedQuadMinus 5 (ZMod 2) 1 1)))) :=
  kill_glue (StatedQuadMinus 5 (ZMod 2) 1 1) (eMc 4) o10m131005_quad (k := 6) (by norm_num)
    o10m131005_om o10m131005_base o10m131005_tree o10m131005_key o10m131005_left
    o10m131005_conj o10m131005_rep

end CertificateChecks.KernelE27Orth.O10m

end
