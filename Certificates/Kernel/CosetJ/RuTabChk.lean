module

public import Certificates.Kernel.CosetJ.RuTabData
public import CFSG.Certificates.Kernel.GMS78RuWSound
public import CFSG.Certificates.Kernel.Orders.Ru.Data.Const
public import CFSG.Certificates.Kernel.Orders.Ru.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.OrdSound

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCosetJ.RuTab

open CFSG.KC.Ord CFSG.KC.GMSW

theorem roots : rootsOK RG (CFSG.KC.Ord.validM (nat_lit 2) (nat_lit 4704) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H) (nat_lit 1) (nat_lit 6) = true := by quickRfl

theorem invs : invsOK RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) (CFSG.KC.Ord.validM (nat_lit 2) (nat_lit 4704) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H) (nat_lit 5) CFSG.KD.OrdRu.ONE = true := by
  quickRfl

theorem bindA : Nat.beq (RG (nat_lit 1)) (CFSG.KD.OrdRu.RW (nat_lit 1)) = true := by quickRfl

theorem bindB : Nat.beq (RG (nat_lit 2)) (CFSG.KD.OrdRu.RW (nat_lit 2)) = true := by quickRfl

theorem RI_bd : relsBounded RI (nat_lit 5) = true := by quickRfl

theorem RI_len : Nat.beq (lenRels RI) (nat_lit 3) = true := by quickRfl

theorem RI_c0 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RI (nat_lit 5) CFSG.KD.OrdRu.ONE (nat_lit 0) (nat_lit 2) = true := by
  quickRfl

theorem RI_c1 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RI (nat_lit 5) CFSG.KD.OrdRu.ONE (nat_lit 2) (nat_lit 1) = true := by
  quickRfl

theorem RI_all : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RI (nat_lit 5) CFSG.KD.OrdRu.ONE (nat_lit 0) (nat_lit 3) = true :=
  relsAll_join (c := nat_lit 3) (RI_c0) RI_c1 rfl rfl

theorem RT_bd : relsBounded RT (nat_lit 5) = true := by quickRfl

theorem RT_len : Nat.beq (lenRels RT) (nat_lit 20) = true := by quickRfl

theorem RT_c0 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RT (nat_lit 5) CFSG.KD.OrdRu.ONE (nat_lit 0) (nat_lit 5) = true := by
  quickRfl

theorem RT_c1 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RT (nat_lit 5) CFSG.KD.OrdRu.ONE (nat_lit 5) (nat_lit 1) = true := by
  quickRfl

theorem RT_c2 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RT (nat_lit 5) CFSG.KD.OrdRu.ONE (nat_lit 6) (nat_lit 1) = true := by
  quickRfl

theorem RT_c3 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RT (nat_lit 5) CFSG.KD.OrdRu.ONE (nat_lit 7) (nat_lit 1) = true := by
  quickRfl

theorem RT_c4 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RT (nat_lit 5) CFSG.KD.OrdRu.ONE (nat_lit 8) (nat_lit 1) = true := by
  quickRfl

theorem RT_c5 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RT (nat_lit 5) CFSG.KD.OrdRu.ONE (nat_lit 9) (nat_lit 3) = true := by
  quickRfl

theorem RT_c6 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RT (nat_lit 5) CFSG.KD.OrdRu.ONE (nat_lit 12) (nat_lit 1) = true := by
  quickRfl

theorem RT_c7 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RT (nat_lit 5) CFSG.KD.OrdRu.ONE (nat_lit 13) (nat_lit 1) = true := by
  quickRfl

theorem RT_c8 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RT (nat_lit 5) CFSG.KD.OrdRu.ONE (nat_lit 14) (nat_lit 1) = true := by
  quickRfl

theorem RT_c9 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RT (nat_lit 5) CFSG.KD.OrdRu.ONE (nat_lit 15) (nat_lit 1) = true := by
  quickRfl

theorem RT_c10 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RT (nat_lit 5) CFSG.KD.OrdRu.ONE (nat_lit 16) (nat_lit 1) = true := by
  quickRfl

theorem RT_c11 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RT (nat_lit 5) CFSG.KD.OrdRu.ONE (nat_lit 17) (nat_lit 1) = true := by
  quickRfl

theorem RT_c12 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RT (nat_lit 5) CFSG.KD.OrdRu.ONE (nat_lit 18) (nat_lit 1) = true := by
  quickRfl

theorem RT_c13 : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RT (nat_lit 5) CFSG.KD.OrdRu.ONE (nat_lit 19) (nat_lit 1) = true := by
  quickRfl

theorem RT_all : relsAll RG (CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28) (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM) RT (nat_lit 5) CFSG.KD.OrdRu.ONE (nat_lit 0) (nat_lit 20) = true :=
  relsAll_join (c := nat_lit 20) (relsAll_join (c := nat_lit 19) (relsAll_join (c := nat_lit 18) (relsAll_join (c := nat_lit 17) (relsAll_join (c := nat_lit 16) (relsAll_join (c := nat_lit 15) (relsAll_join (c := nat_lit 14) (relsAll_join (c := nat_lit 13) (relsAll_join (c := nat_lit 12) (relsAll_join (c := nat_lit 9) (relsAll_join (c := nat_lit 8) (relsAll_join (c := nat_lit 7) (relsAll_join (c := nat_lit 6) (RT_c0) RT_c1 rfl rfl) RT_c2 rfl rfl) RT_c3 rfl rfl) RT_c4 rfl rfl) RT_c5 rfl rfl) RT_c6 rfl rfl) RT_c7 rfl rfl) RT_c8 rfl rfl) RT_c9 rfl rfl) RT_c10 rfl rfl) RT_c11 rfl rfl) RT_c12 rfl rfl) RT_c13 rfl rfl

end CertificateChecks.KernelCosetJ.RuTab

end
