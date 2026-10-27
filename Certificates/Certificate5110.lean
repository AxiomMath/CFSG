module

public import CFSG.GH74.KGroups.CoverJ2TablesInputs
import Certificates.Kernel.J2Cover.G5110

public section

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.KGroups in
open CFSG.GH74.KGroups.J2 in
open CFSG.ComponentClassification.J2Cover.Models in
theorem certificate5110 : (∀ p ∈ uList, p.1 < 2 ∧ p.2 < 128)
    ∧ (uList.Nodup)
    ∧ (uList.length = 64)
    ∧ (((0, 0) : ℕ × ℕ) ∈ uList)
    ∧ (∀ p ∈ uList, ∀ q ∈ uList, CFSG.GH74.KGroups.J2.mulM p q ∈ uList)
    ∧ (∀ p ∈ uList, ∃ q ∈ uList, CFSG.GH74.KGroups.J2.mulM p q = (0, 0))
    ∧ (nElt ∈ uList)
    ∧ (CFSG.GH74.KGroups.J2.mulM nElt nElt = (0, 0))
    ∧ (nElt ≠ (0, 0))
    ∧ (∀ p ∈ uList, CFSG.GH74.KGroups.J2.mulM nElt p = CFSG.GH74.KGroups.J2.mulM p nElt)
    ∧ (∀ p ∈ uList, CFSG.GH74.KGroups.J2.mulM p p = (0, 0) ∨ CFSG.GH74.KGroups.J2.mulM p p = nElt)
    ∧ (∀ p ∈ uList, ∀ q ∈ uList,
    CFSG.GH74.KGroups.J2.mulM p q = CFSG.GH74.KGroups.J2.mulM (0, 0) (CFSG.GH74.KGroups.J2.mulM q p) ∨ CFSG.GH74.KGroups.J2.mulM p q = CFSG.GH74.KGroups.J2.mulM nElt (CFSG.GH74.KGroups.J2.mulM q p)) := KernelJ2Cover.facts5110

end Certificates
