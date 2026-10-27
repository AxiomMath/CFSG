module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinL42Inputs
import Certificates.Kernel.LocalQT.Small.C4046

public section

namespace Certificates

open CFSG.KD.LQT.C4046 in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Unc25G2 CFSG.QuasithinUnique.Unc25G2.A8 in
open Equiv CFSG.QuasithinUnique.Unc25G2.Tbl in
theorem certificate4046 : (List.range 8 ∈ P0tabs ∧
          (∀ a ∈ P0tabs, ∀ b ∈ P0tabs, mulT a b ∈ P0tabs) ∧
          (∀ a ∈ P0tabs, invT 8 a ∈ P0tabs) ∧
          (∀ σ ∈ P0perm, Perm.sign σ = 1) ∧
          P0perm.toFinset.card = 64 ∧
          (∀ x ∈ allTabs, (∀ v ∈ V0, mulT x v = mulT v x) → x ∈ V0) ∧
          (∀ x ∈ allTabs, x ≠ List.range 8 → (∀ p ∈ P0tabs, mulT x p = mulT p x) → x = CFSG.QuasithinUnique.Unc25G2.Tbl.tbl t0) ∧
          ((∀ v ∈ V0, mulT (mulT (CFSG.QuasithinUnique.Unc25G2.Tbl.tbl g0) v) (invT 8 (CFSG.QuasithinUnique.Unc25G2.Tbl.tbl g0)) ∈ V0) ∧
            (∀ v ∈ V0, mulT (mulT (invT 8 (CFSG.QuasithinUnique.Unc25G2.Tbl.tbl g0)) v) (CFSG.QuasithinUnique.Unc25G2.Tbl.tbl g0) ∈ V0) ∧
            mulT (CFSG.QuasithinUnique.Unc25G2.Tbl.tbl g0) (CFSG.QuasithinUnique.Unc25G2.Tbl.tbl t0) ≠ mulT (CFSG.QuasithinUnique.Unc25G2.Tbl.tbl t0) (CFSG.QuasithinUnique.Unc25G2.Tbl.tbl g0)) ∧
          Perm.sign g0 = 1) :=
  CFSG.KC.LQT.S.s4046 _ _ _ hp ht hg hk

end Certificates
