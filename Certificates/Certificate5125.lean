module

public import CFSG.GH74.KGroups.ClassCount
public import CFSG.GH74.KGroups.M11Inputs
import Certificates.Kernel.Misc.KGroups.M11Facts

public section

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.KGroups in
open CFSG.GH74.KGroups.M11 in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint in
theorem certificate5125 : (Q.check = true ∧ Q.orderCertificate = 7920)
    ∧ (orderOf m11gA = 2 ∧ orderOf m11gB = 4 ∧ PairInv ws m11gA m11gB)
    ∧ (m11x0 ∈ NativeSporadic.M11 ∧ orderOf m11x0 = 3)
    ∧ Nat.card {x // x ∈ NativeSporadic.M11 ∧ orderOf x = 2} = 165
    ∧ centCard NativeSporadic.M11 m11gA = 48
    ∧ Nat.card {y // y ∈ NativeSporadic.M11 ∧ orderOf y = 4 ∧ PairInv ws m11gA y} = 48
    ∧ (∀ σ ∈ NativeSporadic.M11, σ * m11gA = m11gA * σ → σ * m11gB = m11gB * σ → σ = 1)
    ∧ Nat.card {x // x ∈ NativeSporadic.M11 ∧ orderOf x = 3} = 440
    ∧ centCard NativeSporadic.M11 m11x0 = 18
    ∧ E9At NativeSporadic.M11 m11gA
    ∧ Cent3At NativeSporadic.M11 m11x0 := KernelMisc.M11K.facts

end Certificates
